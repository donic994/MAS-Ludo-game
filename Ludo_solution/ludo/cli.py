from .game import Player, Game
from .painter import present_6_die_name
from os import linesep
import ludo.DATA as data
import time
from itertools import cycle


class CLIGame():

    def __init__(self):
        self.prompt_end = "> "
        self.game = Game(data.ludoBoard, data.password)
        # used for nicr print
        self.prompted_for_pawn = False
        self.playerAgents = []

    def validate_input(self, prompt, desire_type, allawed_input=None,
                       error_mess="Invalid Option!", str_len=None):

        prompt += linesep + self.prompt_end
        while True:
            choice = input(prompt)
            if not choice:
                print(linesep + error_mess)
                continue
            try:
                choice = desire_type(choice)
            except ValueError:
                print(linesep + error_mess)
                continue
            if allawed_input:
                if choice in allawed_input:
                    break
                else:
                    print("Invalid Option!")
                    continue
            elif str_len:
                min_len, max_len = str_len
                if min_len < len(choice) < max_len:
                    break
                else:
                    print(linesep + error_mess)
            else:
                break
        print()
        return choice

    def prompt_for_player(self):
        ''' get player attributes from input,
        initial player instance and
        add player to the game
        '''
        available_colours = self.game.get_available_colours()
        text = linesep.join(["choose type of player",
                             "0 - computer/agent"])
        choice = self.validate_input(text, int, (0))

        if choice == 0:
            # automatically assign colours
            colour = available_colours.pop()
            ['yellow', 'blue', 'red', 'green']
            if(colour == 'yellow'):
                player = Player(colour, data.yellowPlayer, data.password)
            if(colour == 'blue'):
                player = Player(colour, data.bluePlayer, data.password)
            if(colour == 'red'):
                player = Player(colour, data.redPlayer, data.password)
            if(colour == 'green'):
                player = Player(colour, data.greenPlayer, data.password)
        self.game.add_player(player)

    def prompt_for_players(self):
        '''put all players in the game'''
        counts = ("first", "second", "third", "fourth last")
        text_add = "Add {} player"
        for i in range(2):
            print(text_add.format(counts[i]))
            self.prompt_for_player()
            print("Player added")

        text = linesep.join(["Choose option:",
                             "0 - add player",
                             "1 - start game with {} players"])
        for i in range(2, 4):
            choice = self.validate_input(text.format(str(i)), int, (0, 1))
            if choice == 1:
                break
            elif choice == 0:
                print(text_add.format(counts[i]))
                self.prompt_for_player()
                print("Player added")

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

    def print_players_info(self):
        word = "start" if self.game.rolled_value is None else "continue"
        print("Game {} with {} players:".format(
              word,
              len(self.game.players)))
        for player in self.game.players:
            print(player)
        print()

    def print_info_after_turn(self):
        '''it used game attributes to print info'''
        pawns_id = [pawn.id for pawn in self.game.allowed_pawns]
        # nicer print of dice
        message = present_6_die_name(self.game.rolled_value,
                                     str(self.game.curr_player))
        message += linesep
        if self.game.allowed_pawns and self.game.picked_pawn != None:
            message_moved = "{} is moved. ".format(
                self.game.picked_pawn.id)
            if self.prompted_for_pawn:
                self.prompted_for_pawn = False
                print(message_moved)
                return
            message += "{} possible pawns to move.".format(
                " ".join(pawns_id))
            message += " " + message_moved
            if self.game.jog_pawns:
                message += "Jog pawn "
                message += " ".join([pawn.id for pawn in self.game.jog_pawns])
        else:
            message += "No possible pawns to move."
        print(message)

    def print_standing(self):
        standing_list = ["{} - {}".format(index + 1, player)
                         for index, player in enumerate(self.game.standing)]
        message = "Standing:" + linesep + linesep.join(standing_list)
        print(message)

    def print_board(self):
        print(self.game.get_board_pic())


    def load_players_for_new_game(self):
        self.prompt_for_players()
        self.print_players_info()

    def add_player_agents(self):
        for player in self.game.players:
            self.playerAgents.append(player)

    def start_player_agents(self):
        for player in self.game.players:
            player.start()

    def stop_player_agents(self):
        for agent in self.playerAgents:
            agent.stop()

    def start_game_agent(self):
        players = []
        for agent in self.playerAgents:
            agent.start()
            self.game.set(agent.name, agent)
            players.append(agent)
        self.game.set("players", cycle(players))

        future = self.game.start(auto_register=False)
        future.result()

    def play_game(self):
        self.add_player_agents()
        self.start_game_agent()

        try:
            while self.game.is_alive() and not self.game.finished:
                time.sleep(1)
                self.game.play_turn()
            print("Game finished")
            self.print_standing()
            self.stop_player_agents()
            self.game.stop()
        except (KeyboardInterrupt, EOFError):
            self.stop_player_agents()
            self.game.stop()
            print("Agents finished")

            print(linesep + "Exiting game. ")
            raise

    def start(self):
        '''main method, starting cli'''
        print()
        self.load_players_for_new_game()
        self.play_game()


if __name__ == '__main__':
    CLIGame().start()
