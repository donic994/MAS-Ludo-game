from collections import namedtuple, deque
import random
from .painter import PaintBoard, present_6_die_name
import time
from os import linesep
import jsonpickle
from spade.agent import Agent
from spade.behaviour import OneShotBehaviour
from spade.behaviour import CyclicBehaviour
from spade.message import Message
from spade.template import Template
from spade.container import Container
from spade.web import WebApp
from spade.trace import TraceStore
from threading import Event
import ludo.DATA as data

import asyncio
import aiosasl
import aioxmpp
import aioxmpp.ibr as ibr
from aioxmpp.dispatcher import SimpleMessageDispatcher

# This is piece or a token in ludo game
# Simple class has only index, colour and id attributes
Pawn = namedtuple("Pawn", "index colour id")


class Player(Agent):
    '''Knows (holds) his pawns,
     also know his colour
    and choose which pawn to move
    if more than one are possible
    '''

    def __init__(self, colour, jid, password, verify_security=False):
        self.jid = aioxmpp.JID.fromstr(jid)
        self.password = password
        self.verify_security = verify_security

        self.behaviours = []
        self._values = {}

        self.conn_coro = None
        self.stream = None
        self.client = None
        self.message_dispatcher = None
        self.presence = None
        self.loop = None

        self.container = Container()
        self.container.register(self)

        self.loop = self.container.loop

        # Web service
        self.web = WebApp(agent=self)
        self.traces = TraceStore(size=1000)
        self._alive = Event()

        self.colour = colour
        self.finished = False
        # initialize four pawns with
        # id (first leter from colour and index (from 1 to 4))
        self.pawns = [Pawn(i, self.colour, self.__getitem__() + str(i))
                      for i in range(1, 5)]

    def __getitem__(self):
        return self.colour[0].upper()

    def __str__(self):
        return "({})".format(self.colour)

    def choose_pawn(self, pawns, dice):
        index = random.randint(0, len(pawns)-1)
        if dice == 6:
            return pawns[len(pawns)-1].index
        else:
            return pawns[index].index

    class WaitTurn(CyclicBehaviour):
        async def run(self):
            print("Player waiting for turn")
            allowedPawns = []
            dice = 1
            # wait for a message for 10 seconds
            msg = await self.receive(timeout=10)
            if msg:
                print(self.agent.colour + " player received message with content: {}".format(
                    jsonpickle.decode(msg.body)))
                allowedPawns = jsonpickle.decode(msg.body)[0]
                dice = jsonpickle.decode(msg.body)[1]
            else:
                print("Did not received any message after 10 seconds Waiting turn...")

            if(allowedPawns != []):
                chosenPawn = self.agent.choose_pawn(allowedPawns, dice)
            else:
                chosenPawn = self.agent.choose_pawn(self.agent.pawns, dice)

            msg = Message(to=data.ludoBoard)
            msg.set_metadata("ludoMETA", "informPlayer")
            msg.body = jsonpickle.encode(chosenPawn)

            await self.send(msg)

            # stop agent from behaviour
            await asyncio.sleep(1)

        async def on_end(self):
            await self.agent.stop()

    async def setup(self):
        print("Player started")

        b = self.WaitTurn()
        template = Template()
        template.set_metadata("ludoMETA", "getIndex")
        self.add_behaviour(b, template)


class Board():
    '''
    Knows where are pawns.
    Pawns are assigned with position numbers.
    Can move (change position number) pawn.
    Knows other things like
    what distance pawn must past to reach end.
    It just board. It does not know rules of the game.
    '''

    # common (shared) squares for all pawns
    BOARD_SIZE = 56

    # save (private) positions (squares) for each colour
    # This is squares just before pawn finished
    BOARD_COLOUR_SIZE = 6

    COLOUR_ORDER = ['yellow', 'blue', 'red', 'green']

    # distance between two neighbour colours
    # (The distance from start square of one colour
    # to start square of next colour)
    COLOUR_DISTANCE = 14

    def __init__(self):
        # fn1353c
        # get dict of start position for every colour
        Board.COLOUR_START = {
            colour: 2 + index * Board.COLOUR_DISTANCE for
            index, colour in enumerate(Board.COLOUR_ORDER)}
        # get dict of end position for every colour
        Board.COLOUR_END = {
            colour: index * Board.COLOUR_DISTANCE
            for index, colour in enumerate(Board.COLOUR_ORDER)}
        Board.COLOUR_END['yellow'] = Board.BOARD_SIZE

        # dict where key is pawn and
        # value is two size tuple holds position
        # Position is combination of
        # common (share) square and coloured (private) square.
        self.pawns_possiotion = {}

        # painter is used to visually represent
        # the board and position of the pawns
        self.painter = PaintBoard()

        # pool means before start1353
        self.board_pool_position = (0, 0)

    def set_pawn(self, pawn, position):
        '''save position'''
        self.pawns_possiotion[pawn] = position

    def put_pawn_on_board_pool(self, pawn):
        self.set_pawn(pawn, self.board_pool_position)

    def is_pawn_on_board_pool(self, pawn):
        '''return True of False'''
        return self.pawns_possiotion[pawn] == self.board_pool_position

    def put_pawn_on_starting_square(self, pawn):
        start = Board.COLOUR_START[pawn.colour.lower()]
        position = (start, 0)
        self.set_pawn(pawn, position)

    def can_pawn_move(self, pawn, rolled_value):
        '''check if pawn can outside board colour size'''
        common_poss, private_poss = self.pawns_possiotion[pawn]
        if private_poss + rolled_value > self.BOARD_COLOUR_SIZE:
            return False
        return True

    def move_pawn(self, pawn, rolled_value):
        '''change pawn position, check
        if pawn reach his color square
        '''
        common_poss, private_poss = self.pawns_possiotion[pawn]
        end = self.COLOUR_END[pawn.colour.lower()]
        if private_poss > 0:
            # pawn is already reached own final squares
            private_poss += rolled_value
        elif common_poss <= end and common_poss + rolled_value > end:
            # pawn is entering in own squares
            private_poss += rolled_value - (end - common_poss)
            common_poss = end
        else:
            # pawn will be still in common square
            common_poss += rolled_value
            if common_poss > self.BOARD_SIZE:
                common_poss = common_poss - self.BOARD_SIZE
        position = common_poss, private_poss
        self.set_pawn(pawn, position)

    def does_pawn_reach_end(self, pawn):
        '''if pawn must leave game'''
        common_poss, private_poss = self.pawns_possiotion[pawn]
        if private_poss == self.BOARD_COLOUR_SIZE:
            return True
        return False

    def get_pawns_on_same_postion(self, pawn):
        '''return list of pawns on same position'''
        position = self.pawns_possiotion[pawn]
        return [curr_pawn for curr_pawn, curr_postion in
                self.pawns_possiotion.items()
                if position == curr_postion]

    def paint_board(self):
        '''painter object expect dict of
        key - occupied positions and
        value - list of pawns on that position
        '''
        positions = {}
        for pawn, position in self.pawns_possiotion.items():
            common, private = position
            if not private == Board.BOARD_COLOUR_SIZE:
                positions.setdefault(position, []).append(pawn)
        return self.painter.paint(positions)


class Die():

    MIN = 1
    MAX = 6

    @staticmethod
    def throw():
        return random.randint(Die.MIN, Die.MAX)


class Game(Agent):
    '''Knows the rules of the game.
    Knows for example what to do when 
    one pawn reach another
    or pawn reach end or 
    player roll six and so on
    '''

    def __init__(self, jid, password, verify_security=False):

        self.jid = aioxmpp.JID.fromstr(jid)
        self.password = password
        self.verify_security = verify_security

        self.behaviours = []
        self._values = {}

        self.conn_coro = None
        self.stream = None
        self.client = None
        self.message_dispatcher = None
        self.presence = None
        self.loop = None

        self.container = Container()
        self.container.register(self)

        self.loop = self.container.loop

        # Web service
        self.web = WebApp(agent=self)

        self.traces = TraceStore(size=1000)

        self._alive = Event()

        self.players = deque()
        self.standing = []
        self.board = Board()
        # is game finished
        self.finished = False
        # last rolled value from die (dice)
        self.rolled_value = None
        # player who last rolled die
        self.curr_player = None
        # curr_player's possible pawn to move
        self.allowed_pawns = []
        # curr_player's chosen pawn to move
        self.picked_pawn = None
        # used for nicer print
        self.prompted_for_pawn = False
        # chosen index from allowed pawn
        self.index = None
        # jog pawn if any
        self.jog_pawns = []
        # agents that represent players
        self.playerAgents = []

    def add_player(self, player):
        self.players.append(player)
        for pawn in player.pawns:
            self.board.put_pawn_on_board_pool(pawn)

    def get_available_colours(self):
        '''if has available colour on boards'''
        used = [player.colour for player in self.players]
        available = set(self.board.COLOUR_ORDER) - set(used)
        return sorted(available)

    def _get_next_turn(self):
        '''Get next player's turn.
        It is underscore because if called 
        outside the class will break order
        '''
        if not self.rolled_value == Die.MAX:
            self.players.rotate(-1)
        return self.players[0]

    def get_pawn_from_board_pool(self, player):
        '''when pawn must start'''
        for pawn in player.pawns:
            if self.board.is_pawn_on_board_pool(pawn):
                return pawn

    def get_allowed_pawns_to_move(self, player, rolled_value):
        ''' return all pawns of a player which rolled value
        from die allowed to move the pawn
        '''
        allowed_pawns = []
        if rolled_value == Die.MAX:
            pawn = self.get_pawn_from_board_pool(player)
            if pawn:
                allowed_pawns.append(pawn)
        for pawn in player.pawns:
            if not self.board.is_pawn_on_board_pool(pawn) and\
                    self.board.can_pawn_move(pawn, rolled_value):
                allowed_pawns.append(pawn)
        return sorted(allowed_pawns, key=lambda pawn: pawn.index)

    def get_board_pic(self):
        return self.board.paint_board()

    def _jog_foreign_pawn(self, pawn):
        pawns = self.board.get_pawns_on_same_postion(pawn)
        for p in pawns:
            if p.colour != pawn.colour:
                self.board.put_pawn_on_board_pool(p)
                self.jog_pawns.append(p)

    def _make_move(self, player, pawn):
        '''tell the board to move pawn.
        After move ask board if pawn reach end or
        jog others pawn. Check if pawn and player finished.
        '''
        if self.rolled_value == Die.MAX and\
                self.board.is_pawn_on_board_pool(pawn):
            self.board.put_pawn_on_starting_square(pawn)
            self._jog_foreign_pawn(pawn)
            return
        self.board.move_pawn(pawn, self.rolled_value)
        if self.board.does_pawn_reach_end(pawn):
            player.pawns.remove(pawn)
            if not player.pawns:
                self.standing.append(player)
                self.players.remove(player)
                if len(self.players) == 1:
                    self.standing.extend(self.players)
                    self.finished = True
        else:
            self._jog_foreign_pawn(pawn)

    def prompt_choose_pawn(self):

        text = present_6_die_name(self.game.rolled_value,
                                  str(self.game.curr_player))
        text += linesep + "has more than one possible pawns to move."
        text += " Choose pawn" + linesep
        pawn_options = ["{} - {}".format(index + 1, pawn.id)
                        for index, pawn
                        in enumerate(self.game.allowed_pawns)]
        text += linesep.join(pawn_options)
        index = self.validate_input(
            text, int, range(1, len(self.game.allowed_pawns) + 1))
        self.prompted_for_pawn = True
        return index - 1

    def print_info_after_turn(self):
        '''it used game attributes to print info'''
        pawns_id = [pawn.id for pawn in self.allowed_pawns]
        # nicer print of dice
        message = present_6_die_name(self.rolled_value,
                                     str(self.curr_player))
        message += linesep
        if self.allowed_pawns and self.picked_pawn != None:
            message_moved = "{} is moved. ".format(
                self.picked_pawn.id)
            if self.prompted_for_pawn:
                self.prompted_for_pawn = False
                print(message_moved)
                return
            message += "{} possible pawns to move.".format(
                " ".join(pawns_id))
            message += " " + message_moved
            if self.jog_pawns:
                message += "Jog pawn "
                message += " ".join([pawn.id for pawn in self.jog_pawns])
        else:
            message += "No possible pawns to move."
        print(message)

    def print_board(self):
        print(self.get_board_pic())

    def start_players(self):
        self.get("players")

    def start_player_agent(self, agent):
        agent.start()

    def play_turn(self):
        '''this is main method which must be used to play game.
        Method ask for next player's turn, roll die, ask player
        to choose pawn, move pawn.
        ind and rolled_val are suitable to be used when
        game must be replicated (recorded)
        ind is chosen index from allowed pawns
        '''

        self.jog_pawns = []
        self.curr_player = self._get_next_turn()
        self.rolled_value = Die.throw()
        self.allowed_pawns = self.get_allowed_pawns_to_move(
            self.curr_player, self.rolled_value)

        self.InformPlayer()


    def choose_pawn(self, index):
        for pawn in self.allowed_pawns:
            if pawn.index == index:
                return pawn
            else:
                return self.allowed_pawns[0]

    class InformPlayer(CyclicBehaviour):
        async def run(self):
            print("Game running")
            if(self.agent.curr_player != None):
                currentPlayer = self.agent.curr_player.jid
                reciever = currentPlayer[0]+"@"+currentPlayer[1]

                msg = Message(to=reciever)
                msg.set_metadata("ludoMETA", "getIndex")
                msg.body = jsonpickle.encode(
                    [self.agent.allowed_pawns, self.agent.rolled_value])
                await self.send(msg)

                # wait for a message for 10 seconds
                msg = await self.receive(timeout=10)
                #player = self.get("players")
                if msg:
                    print("Ludo Board received message with content: {}".format(
                        jsonpickle.decode(msg.body)))

                    if self.agent.allowed_pawns != []:
                        self.agent.index = int(msg.body)

                        self.agent.picked_pawn = self.agent.choose_pawn(
                            self.agent.index)
                        self.agent._make_move(
                            self.agent.curr_player, self.agent.picked_pawn)
                    else:
                        self.agent.index = -1
                        self.agent.picked_pawn = None

                    self.agent.print_info_after_turn()
                    self.agent.print_board()
                else:
                    print(
                        "Did not received any message after 10 seconds Get Pawn Index")

                # stop agent from behaviour
                await asyncio.sleep(1)

        async def on_end(self):
            await self.agent.stop()

    async def setup(self):
        print("Game started")
        b = self.InformPlayer()
        template = Template()
        template.set_metadata("ludoMETA", "informPlayer")
        self.add_behaviour(b, template)
