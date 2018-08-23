from excepthook import uncaught_exception, install_thread_excepthook
from ChatExchange import chatexchange
from datetime import datetime
import sys
sys.excepthook = uncaught_exception
install_thread_excepthook()

import getpass
import StringIO
import urllib2, urllib
import json
import random
import traceback
import HTMLParser
unescape = HTMLParser.HTMLParser().unescape

import re
import os
import time
import sqlite3

import requests
from requests.auth import HTTPBasicAuth
from helpers import log, log_exception

# Define an enum structure that we can use to define our own enums
def enum(*sequential, **named):
    enums = dict(zip(sequential, range(len(sequential))), **named)
    return type('Enum', (), enums)
    
# Holds all info related to a single clue
class clue:
    def __init__(self):
        self.number = -1  # The clue number as chosen by the setter
        self.message = None # A reference to the chat message containing the clue
        self.setter_id = -1 # The SE chat ID of the setter of the clue
        self.setter_name = "" # The SE chat name of the setter of the clue
        self.clue_text = "" # The actual text of the clue (bare text)
        self.guess = "" # The guess (if any) currently awaiting confimation
        self.guesser_name = "" # The username of the user who made the guess
        self.contacts = {} # A dictionary of players who have contacted this clue (id:timestamp)
        self.set_state(Clue_state.None) # The state of the clue starts out as None. 
        self.timestamp = None # The time the clue was set (UTC)
        self.warned = False # Indicates whether the bot has already prompted the user to declare this clue alive/dead after a letter has been given up.
    
    # Sets the state to one of the values in enum Clue_state
    def set_state(self, state): 
        self.state = state 
        self.state_timestamp = datetime.utcnow() # The UTC time that the clue entered this state
        self.warned = False # If the clue changes state, it's eligible for another warning.
        if TESTING: print("Clue #%s: state changed to %s" % (self.number, state))

    def set_guess(self, guess, user_name):
        self.guess = guess.upper()
        self.guesser_name = user_name
        self.guess_timestamp = datetime.utcnow() # The UTC time that the guess was made
        self.guess_warned = False
        
# Enums to keep track of the clue state and the game state.
Clue_state = enum("None", "Set", "Passed", "Schroedinger", "Solved", "Dead") # Schroedinger means a pass happened, and the clue hasn't been declared alive or dead.
Game_state = enum("None", "Guessing", "Passed", "WaitingForLetter", "Finished")

TESTING = False  # Enables verbose debug output to console, and disables user checking for various clue/guess/contact events.  Also changes the chat room used. Should be turned off for production.
SCHROEDINGER_TIMEOUT = 90 # The time before the bot reminds a user to indicate whether their clue is alive or dead (in seconds)
GUESS_TIMEOUT = 30 # The time before the bot reminds a clue setter to confirm/deny a guess that has been made.
WAVE_DEATH = 1800 # The number of seconds before a wave is considered "expired"
WAVES_FOR_PING = 3 # The number of waves o/ required to trigger an auto-ping
MAX_CLUES = 10
DEFAULT_MUTE_LENGTH = 600
CONTACT_THRESHOLD = 5

client = None # The ChatExchange client reference
room = None # The ChatExchange room reference
my_user = None # This bot's user ID
shutdown = False # Indicates whether the bot has been shut down
clues = {} # Holds all the active clues, indexed by clue number
dead_clues = [] # Holds all dead/solved clues.
whitelist = set()  # Users who are allowed to command the bot
pinglist = set() # Users who want to be notified when a new game is starting.

game_state = Game_state.None
users = {}
num_contact_guesses = 0 # How many guesses have been made after a pass (by those who contacted the clue)
verbose = True # When true, the bot talks more.

# Unique IDs for the database tables
game_id = -1
clue_id = -1
guess_id = -1
contact_id = -1
defence_id = -1

# Defender info
defender_id = -1 # Chat ID
defender_name = ""
defending_text = "" # The portion of the word being defended
defending_message = None # A reference to the message containing the defended text
defending_timestamp = None # The time the message was posted.

muted_timestamp = None # When the bot was told to !shutup
mute_length = DEFAULT_MUTE_LENGTH # Seconds until the bot may speak again.

waves = {} # Timestamps of the most recent waves ( o/ ) posted in the room.

# Regular expression match patterns for the various game-related inputs:
clue_number = "\d+(?:\.\d+)?'*"

clue_pattern = re.compile(r"\s*(%s(?:,\s*%s)*)[:).]?\s*<b>(.*)</b>.*" % (clue_number, clue_number), re.IGNORECASE)
defender_pattern = re.compile(r"\s*.*defending:?\s*<b>([A-Z ]+)</b>\s*$", re.IGNORECASE)
guess_pattern = re.compile(r"\s*(%s)[:).]?(?: is| it's(?: not)?)?\s*([^?]+)" % (clue_number), re.IGNORECASE)
yes_pattern = re.compile(ur"\s*(%s)[:).]?\s*((?:y|ok|yes|yep|(?:(?:(?:.+ )is )?(?:c|<b>c</b>)orrect|right)|\u2713+|\u2714+)(?:\s+.*)?)" % (clue_number), re.IGNORECASE)
no_pattern = re.compile(r"\s*(%s)[:).]?\s*((?:n|no|nope|x|(?:(?:.+ )is )?wrong|(?:(?:.+ )is )?(?:(?:inc|<b>inc</b>|<b>in</b>c|)orrect|(?:not|<b>not</b>) (?:correct|right))(?:\s+.*)?))" % (clue_number), re.IGNORECASE)
contact_pattern = re.compile(r"\s*(?:contact|c)\s*(%s(?:,\s*%s)*)" % (clue_number, clue_number), re.IGNORECASE)
uncontact_pattern = re.compile(r"\s*(?:uncontact|u|uc)\s*(%s(?:,\s*%s)*)" % (clue_number, clue_number), re.IGNORECASE)
pass_pattern = re.compile(r"\s*(?:I )?(?:am )?pass(?:ing)?(?: on)?\s*(%s)" % (clue_number), re.IGNORECASE)
dies_pattern = re.compile(r"\s*(%s)[:).]?\s*((?:dies|(?:(?:is )?dead|done)|was)(?:[\s:;.]+.*)?)" % (clue_number), re.IGNORECASE)
lives_pattern = re.compile(r"\s*(%s)[:).]?\s*((?:lives|(?:is )?(?:still)?alive|(?:stays|remains)(?: alive)?|continues|survives)(?:[\s:;.]+.*)?)" % (clue_number), re.IGNORECASE)
wave_pattern = re.compile(r"\s*(\\(?:o|O|0)|(?:o|O|0)/|<code>(\\0|0/)</code>)\s*", re.IGNORECASE)

def main():
    global room, my_user, client, whitelist, pinglist

    # Check if a whitelist/pinglist` exists in the DB.  If no, initialize it in the DB; if yes, load it from the DB.
    whitelist = init_list(whitelist, "whitelist")
    pinglist = init_list(pinglist, "pinglist")

    # Set ChatExchange variables
    host_id = 'stackexchange.com'
    room_id = -1
    if TESTING:
        room_id = '80561'  # My sandbox
    else:
        room_id = '53490'  # Contact

    # Get username and password to log in to ChatExchange.
    if 'ChatExchangeU' in os.environ:
        email = os.environ['ChatExchangeU']
    else:
        email = raw_input("Email: ")
    if 'ChatExchangeP' in os.environ:
        password = os.environ['ChatExchangeP']
    else:
        password = getpass.getpass("Password: ")

    # Initialize connection and log in
    client = chatexchange.client.Client(host_id)
    client.login(email, password)
    my_user = client.get_me()
    room = client.get_room(room_id)
    room.join()
    room.watch(on_message)

    log('info', "(You are now in room #%s on %s.)" % (room_id, host_id))

    # Continue to loop, reading each message posted to the room
    while not shutdown:
        message = raw_input("<< ")
        
    # Log out of ChatExchange
    client.logout()

# Do this each time a message is posted/edited
def on_message(message, client):
    if isinstance(message, chatexchange.events.MessagePosted) \
            or isinstance(message, chatexchange.events.MessageEdited):

        # Access levels for different commands
        is_bot = (message.user.id == my_user.id)
        is_super_user = (is_bot or message.user.is_moderator)
        is_trusted_user = (is_super_user or message.user.id in whitelist)

        try:
            # Remove all weird HTML encodings (like &amp; for &)
            input = unescape(message.content)
            
            # This will fail if there are any unicode characters in the input. Mostly a problem with check mark.
            # Not a concern when TESTING is False.
            if TESTING: print(">> (%s / %s) %s" % (message.user.name, repr(message.user.id), input))

            # Match the input using all the patterns defined above, to determine what type of input it is
            clue_match = re.match(clue_pattern, input)
            defender_match = re.match(defender_pattern, input)
            guess_match = re.match(guess_pattern, input)
            yes_match = re.match(yes_pattern, input)
            no_match = re.match(no_pattern, input)
            contact_match = re.match(contact_pattern, input)
            uncontact_match = re.match(uncontact_pattern, input)
            pass_match = re.match(pass_pattern, input)
            dies_match = re.match(dies_pattern, input)
            lives_match = re.match(lives_pattern, input)
            
            # Negation of guess
            if not is_bot and no_match is not None:
                if TESTING: print("Matched negation for #%s" % (guess_match.groups()[0].strip()))
                deny_guess(no_match.groups()[0].strip(), no_match.groups()[1].strip(), message.user)
                    
            # Confirmation of guess
            elif not is_bot and yes_match is not None:
                if TESTING: print("Matched affirmation for #%s" % (yes_match.groups()[0].strip()))
                confirm_guess(yes_match.groups()[0].strip(), yes_match.groups()[1].strip(), message.user)
                    
            # Confirmation that clue dies
            elif not is_bot and dies_match is not None:
                if TESTING: print("Matched death for %s" % (dies_match.groups()[0].strip()))
                kill_clue(dies_match.groups()[0].strip(), dies_match.groups()[1].strip(), message.user, True)
            
            # Confirmation that clue lives
            elif not is_bot and lives_match is not None:
                if TESTING: print("Matched life for %s" % (lives_match.groups()[0].strip()))
                confirm_life(lives_match.groups()[0].strip(), lives_match.groups()[1].strip(), message.user)
            
            # Clue
            elif not is_bot and clue_match is not None:
                numbers = [number.strip() for number in clue_match.groups()[0].split(',')]
                for number in numbers:
                    if TESTING: print("Matched clue %s: %s" % (number, clue_match.groups()[1]))
                    add_clue(message, number, clue_match.groups()[1].strip())
                
            # "Defending" message
            elif not is_bot and defender_match is not None:
                if TESTING: print("Matched defender: %s, defending %s" % (message.user.name, defender_match.groups()[0].strip()))
                repin_defender(message, defender_match.groups()[0].strip())
                
            # Guess
            elif not is_bot and guess_match is not None:
                if TESTING: print("Matched guess %s for #%s" % (guess_match.groups()[1].strip(), guess_match.groups()[0].strip()))
                add_guess(guess_match.groups()[0].strip(), guess_match.groups()[1].strip(), message.user)
                    
            # Contact
            elif not is_bot and contact_match is not None:
                if TESTING: print("Matched contact for #%s" % (contact_match.groups()[0].strip()))
                add_contact(message, [number.strip() for number in contact_match.groups()[0].strip().split(',')])
                    
            # Uncontact
            elif not is_bot and uncontact_match is not None:
                if TESTING: print("Matched uncontact for #%s" % (uncontact_match.groups()[0].strip()))
                remove_contact(message, [number.strip() for number in uncontact_match.groups()[0].strip().split(',')])
                
            # Pass
            elif not is_bot and pass_match is not None:
                if TESTING: print("Matched pass for #%s" % (pass_match.groups()[0].strip()))
                pass_clue(message, pass_match.groups()[0].strip())
                    
            ### Bot commands ###
            
            # Reset (unstar/unpin) all current game messages, and reset game variables
            elif is_trusted_user and input.lower().strip() == "!reset":
                if TESTING: print("Matched !reset command")
                reset()
                
            # List active clues, including authors, contacts, and Schroedinger status
            elif is_trusted_user and input.lower().strip() =="!clues":
                if TESTING: print("Matched !clues command")
                display_clues(False)
                
            # List any active unstarred clues
            elif is_trusted_user and input.lower().strip() =="!unstarred":
                if TESTING: print("Matched !unstarred command")
                display_clues(True)
                
            # List all contacted clues with who contacted them, or those who contacted a specific clue
            elif is_trusted_user and input.lower().startswith("!contacts"):
                if TESTING: print("Matched !contacts command")
                display_contacts(input.lower())
                
            # Silence the bot for a given length of time
            elif is_trusted_user and input.lower().startswith("!shutup"):
                if TESTING: print("Matched !shutup command")
                mute(input)
                
            # Waken a bot that has been silenced
            elif is_trusted_user and input.lower().strip() == "!speak":
                if TESTING: print("Matched !speak command")
                unmute()
                
            # Enable/disable more game messages from the bot, mostly when things go wrong
            elif is_trusted_user and input.lower().startswith("!verbose"):
                if TESTING: print("Matched !verbose command")
                toggle_verbosity(input[9:])

            # If the bot recognized a pass in error, reverse the pass.
            elif is_trusted_user and input.lower().strip() == "!unpass":
                reverse_pass()
            
            # Remove a clue that was added in error.  Similar to "<clue> dies", but will work for clues you don't own.
            elif is_trusted_user and input.lower().startswith("!kill"):
                kill_clue(input[6:], "", message.user, True)
                
            # Remove a contact that was added in error.  Similar to "uncontact <clue>", but can remove someone else's contact.
            elif is_trusted_user and input.lower().startswith("!uncontact"):
                tokens = input.split(" ")
                if len(tokens) != 2: send_message("Syntax: **`!uncontact <clueNum>`**")
                remove_contact(message, [tokens[1]], True) # remove all contacts for this clue
            
            # Notify everyone in the pinglist of a game/potential game
            elif is_super_user and input.lower().strip() == "!ping":
                if TESTING: print("Matched !ping command")
                ping()
                
            # Add/remove or list users on the whitelist
            elif is_super_user and input.lower().startswith("!whitelist"):
                if TESTING: print("Matched !whitelist command")
                modify_list(whitelist, input[11:], "whitelist")

            # Add/remove or list users on the pinglist
            elif is_trusted_user and input.lower().startswith("!pinglist"):
                if TESTING: print("Matched !pinglist command")
                modify_list(pinglist, input[10:], "pinglist")
    
            # Output a list of commands, and a brief introduction to the bot
            elif input.lower().strip() == "!help":
                if TESTING: print("Matched !help command")
                info()
                
            # Shut down the bot remotely
            elif is_super_user and input.lower().strip() == "!shutdown":
                print("Matched !shutdown command")
                shutdown = True
                
            # Count the number of people waving in the room.  If enough, ping others to join.
            elif re.match(wave_pattern, input) is not None:
                if TESTING: print("Matched wave")
                waves[message.user.id] = datetime.utcnow()
                
            # Check for invalid command/insufficient permissions.
            elif input[0] == "!" :
                if not is_trusted_user:
                    if verbose: send_message("I'm sorry, I've been told not to listen to you. Try asking a mod to add you to the whitelist.")
                else:
                    if verbose: send_message("I don't recognize that command, or you don't have sufficient permission.  Type `!help` for a list of valid commands.")

        except:
            log_exception(*sys.exc_info())
            #traceback.print_exc()
            #print ""
        
        # If clues haven't been confirmed as alive/dead after a certain time has elapsed since the last new letter, let the clue setter know.
        if verbose: check_clue_status()
        
        # If someone hasn't confirmed/denied a guess after a certain time has elapsed, let them know.
        if verbose: check_guess_status()
        
        # Check if a sufficient number of people have waved in the last while, to warrant pinging other users.
        check_waves()

# Someone has posted a new clue.
def add_clue(msg, number, text):
    global clues, clue_id
    if game_state == Game_state.Passed:
        send_message("%s has passed on clue #%s. Please don't post any new clues until the pass has been resolved. I recommend deleting this clue, and reposting after the pass is resolved. (I am ignoring it.)" % (defender_name, number))
    elif game_state == Game_state.WaitingForLetter:
        send_message("We are waiting on %s to provide a new letter. Please don't post any new clues until they have done so. I recommend deleting this clue (I am ignoring it)" % (defender_name))
    elif game_state == Game_state.Finished:
        if verbose: send_message("The game is over. No clues are being accepted.")
    elif game_state == Game_state.Guessing:
        if msg.user.id == defender_id and not TESTING:
            send_message("You are the defender -- you can't post clues!")
        elif number in clues:
            send_message("There is already an active clue #%s.  Please edit or repost with a different number." % (number))
        else: # Initialize a new clue instance
            c = clue()
            c.number = number
            c.setter_id  = msg.user.id
            c.setter_name = msg.user.name
            c.timestamp = msg.time_stamp
            c.message = msg.message
            c.clue_text = text
            c.set_state(Clue_state.Set)
            clues[number] = c
            if TESTING: print("Message has %s stars" % (msg.message.stars))
            if msg.message.stars == 0: # Sometimes a single message contains several clues (e.g. 4,5: Fifth space on a Monopoly board = READING RAILROAD). Only attempt to star if it hasn't already been starred.
                msg.message.star()
            
            # If there are too many active clues, give an appropriate message.
            if len(clues) >= MAX_CLUES:
                if verbose: send_message("There are now %s unsolved clues.  Please don't post any more clues until some have been resolved." % (len(clues)))
                total_contacts = 0
                # Count the total number of contacts on all clues
                for cl in clues.itervalues():
                    total_contacts += len(cl.contacts)
                # If there are a lot of contacts, suggest that the defender pass
                if total_contacts >= CONTACT_THRESHOLD:
                    if verbose: send_message("%s, there are a total of %s contacts on existing clues.  You might want to think about passing if you can't solve any of them. (Use `!contacts` to see current contacts.)" % (defender_name, total_contacts))
                # Otherwise, suggest that people focus on solving clues
                else:
                    if verbose: send_message("There aren't very many contacts on existing clues.  Why don't you focus on solving some of them instead of posting more?")

    else: # Should never happen
        print("Add clue in None state")

        
# Someone has posted a new guess.  Generally anything that starts with a number and doesn't match something else (confirmation/denial, death/life, etc.) is considered a guess.
def add_guess(number, guess, guesser):
    guess = guess.upper()
    global clues, num_contact_guesses

    # Can't make another guess if there is a guess outstanding.
    if clues[number].guess != "":
        send_message("We are currently waiting on %s to confirm or deny %s's guess for clue #%s.  Please wait until that has been done before making another guess." % (clues[number].setter_name, clues[number].guesser_name, number))

    # Regular game progress
    elif game_state == Game_state.Guessing:
        # Defender posted the guess, and game state is Guessing
        if guesser.id == defender_id or TESTING:
            add_defender_guess(clues[number], guess, guesser)
        # Someone else posted the guess when they shouldn't be guessing.
        else:
            if number in clues:
                if verbose: send_message("You can't make guesses right now; that's the defender's job.  Wait till a clue has been passed.")
            else:
                if verbose: send_message("Clue text must be **bold** (surround it with `**` or `__`).  Please try again.")
    # Defender has passed.  
    elif game_state == Game_state.Passed:
        # Still allow guesses by the defender on other clues, even while pass is pending.
        if guesser.id == defender_id and not TESTING:
            if number not in clues:
                if verbose: send_message("There doesn't appear to be an active clue with the number %s, so you can't make a guess." % (number))
            elif clues[number].state == Clue_state.Set:
                add_defender_guess(clues[number], guess, guesser)
            else:
                if verbose: send_message("You passed on clue #%s.  Please refrain from making guesses until the pass is resolved." % (number))
        # Someone tries to post a guess for another clue
        elif number not in clues or clues[number].state != Clue_state.Passed:
            send_message("%s has passed on clue #%s. We are currently only accepting guesses for that clue from those who have contacted it." % (defender_name, number))
        # The guesser is someone who contacted this clue
        elif guesser.id in clues[number].contacts.keys():
            clues[number].set_guess(guess, guesser.name)
            num_contact_guesses += 1
            if TESTING: print("Guess for clue #%s:\n%s" % (number, guess))
        # The guesser didn't contact this clue
        else:
            if verbose: send_message("You haven't contacted clue #%s.  Only those who have contacted the clue may guess.  (To see who has contacted it, use **`!contacts %s`**)" % (number, number))
    elif game_state == Game_state.WaitingForLetter:
        send_message("We are currently waiting for %s to provide an additional letter.  No guesses (or clues) are being accepted right now." % (defender_name))
    elif game_state == Game_state.Finished:
        if verbose: send_message("The game is over.  No more guesses are being accepted.")
    else: # Should never happen
        print("Guess in None state")

# Helper function to process a valid guess by the defender.
def add_defender_guess(clue, guess, guesser):
    start_of_guess = guess.strip()[:len(defending_text)] # Grab the first X letters of the guess, where X is the length of the currently defended text
    # Trying to guess for a non-existent clue
    if clue.number not in clues:
        if verbose: send_message("There doesn't appear to be an active clue with the number %s, so you can't make a guess." % (clue.number))
    # Guess doesn't start with the right letters
    elif start_of_guess != defending_text:
        send_message("The word being defended starts with **%s**.  Your guess starts with **%s**.  Try again." % (defending_text, start_of_guess))
    # Valid guess
    else:
        clue.set_guess(guess, guesser.name)
        if TESTING: print("Guess for clue #%s:\n%s" % (clue.number, guess))

# Someone is confirming a guess
def confirm_guess(number, text, user):
    global clues, dead_clues
    # Trying to confirm a guess that doesn't exist
    if number not in clues:
        send_message("There is no clue #%s.  What exactly are you confirming?" % (number))
    # Someone trying to confirm a guess for a clue they didn't set
    elif user.id != clues[number].setter_id:
        add_guess(number, text, user) #If this isn't the setter of the clue, they're probably guessing, not confirming.
    # Someone trying to confirm a guess for their clue, when no guess has been made.
    elif clues[number].guess == "":
        send_message("There was no guess made for #%s.  What exactly are you confirming?" % (number))
    # Someone properly confirming a guess for their own clue
    else:
        remove_clue(clues[number], Clue_state.Solved)
        # Check if this correct guess was for a passed clue.  If so, the defender needs to give up a letter.
        if game_state == Game_state.Passed:
            num_contact_guesses = 0
            set_game_state(Game_state.WaitingForLetter)
            if verbose: send_message("You guessed correctly.  %s must give up a letter!" % (defender_name))
        
        if TESTING: print("Clues: %s" % (clues))
        if TESTING: print("Dead: %s" % (dead_clues))

# Someone is indicating that a guess is incorrect.
def deny_guess(number, text, user):
    global clues
    
    # Trying to deny a guess that doesn't exist.
    if number not in clues:
        send_message("There is no clue #%s.  What exactly are you denying?" % (number))
    # Someone trying to deny a guess for a clue they didn't set
    elif user.id != clues[number].setter_id:
        add_guess(number, text, user) #If this isn't the setter of the clue, they're probably guessing, not denying.
    # Someone trying to deny a guess for their clue, when no guess has been made.
    elif clues[number].guess == "":
        send_message("There was no guess made for #%s.  What exactly are you denying?" % (number))
    # Someone properly denying a guess for their own clue, when the defender has passed
    elif game_state == Game_state.Passed and num_contact_guesses >= len(clues[number].contacts):  #This is the last contacter to guess
        send_message("It looks like no one guessed right.  Clue #%s is now dead. Carry on." % (number))
        print("Last contact's guess was wrong.  Clue is dead.  Resuming regular game.")
        clues[number].set_guess("", "")
        remove_clue(clues[number], Clue_state.Dead, Game_state.Guessing)
        
        if TESTING: print("Clues: %s" % (clues))
        if TESTING: print("Dead: %s" % (dead_clues))
    # Someone properly denying a guess for their own clue in Guessing state, or for not-the-last guess when the defender has passed
    else:
        clues[number].set_guess("", "")

# Someone has contacted a clue
def add_contact(msg, numbers):
    global clues
    # We allow multiple contacts in a single message.  Loop through them and process each one.
    for number in numbers:
        number = number.strip()
        # Trying to contact a non-existent clue
        if number not in clues:
            send_message("There doesn't appear to be an active clue with the number %s, therefore you can't contact it." % (number))
        # Trying to contact one's own clue
        elif clues[number].setter_id == msg.user.id and not TESTING:
            send_message("You can't contact your own clue!")
        # Valid contact.  Add to the list
        else:
            clues[number].contacts[msg.user.id] = msg.user.name
            if TESTING: print("Contacts for clue #%s:\n%s" % (number, clues[number].contacts.values()))

# Someone has uncontacted a clue
def remove_contact(msg, numbers, remove_all = False):
    global clues
    # We allow multiple uncontacts in a single message.  Loop through them and process each one.
    for number in numbers:
        number = number.strip()
        # Trying to uncontact a non-existent clue
        if number not in clues:
            if verbose: send_message("There doesn't appear to be an active clue with the number %s, therefore you can't uncontact it." % (number))
        # We are using a bot command to remove all contacts
        elif remove_all:
            clues[number].contacts = {}
            if verbose: send_message("Cleared all contacts for clue #%s." % (number))
        # The contact exists.  Remove it.
        elif msg.user.id in clues[number].contacts.keys():
                del clues[number].contacts[msg.user.id]
                if TESTING: print("Contacts for clue #%s:\n%s" % (number, clues[number].contacts.values()))
        # The contact does not exist
        else:
            if verbose: send_message("You can't uncontact a clue you never contacted! (#%s)" % (number))

# Someone has declared a clue dead after a new letter has been revealed
def kill_clue(number, text, user, override = False):
    global clues
    # Trying to kill a non-existent clue
    if number not in clues:
        send_message("There is no clue #%s." % (number))
    # The owner of the clue is legit killing it (can be in any game state), or someone issued the !kill command
    elif clues[number].setter_id == user.id or override:
        remove_clue(clues[number], Clue_state.Dead)
    else: #someone else is saying it dies.  More likely to be a guess.
        add_guess(number, text, user)
        
# Someone has declared a clue still alive after a new letter has been revealed
def confirm_life(number, text, user):
    global clues
    # Trying to confirm a non-existent clue
    if number not in clues:
        send_message("There is no clue #%s." % (number))
    # The owner of the clue is declaring it legit
    elif clues[number].setter_id == user.id:
        clues[number].set_state(Clue_state.Set)
        clues[number].warned = False
    else: #someone else is saying it lives.  More likely to be a guess.
        add_guess(number, text, user)

# The defender has passed on a clue
def pass_clue(msg, number):
    global clues
    # Make sure it's the defender passing.
    if msg.user.id != defender_id:
        send_message("Only the defender can pass on clues.")
    # Trying to pass on a non-existent clue
    elif number not in clues:
        send_message("There is no current clue #%s. Try passing on an *existing* clue!" % (number))
    else:
        # Go into "pass" mode. Let the contacter(s) know that they need to guess.
        clues[number].set_state(Clue_state.Passed)
        set_game_state(Game_state.Passed)
        # Trying to pass when a clue hasn't been contacted (we do it anyway, but mention it just in case)
        if len(clues[number].contacts) == 0:
            if verbose: send_message("...but clue #%s hasn't been contacted!?  Ok, I guess you know what you're doing... (You can `!unpass` if you made a mistake.)" % (number))
        else:
            pass_msg = "Clue #%s (**%s**) was contacted by: ***%s***. Make your guess" \
                    % (number, clues[number].clue_text, ", ".join(user for user in clues[number].contacts.values()))
            if len(clues[number].contacts) > 1:
                pass_msg += "es (one each)"
            pass_msg += "!"
            if verbose: send_message(pass_msg)
        
# Reverse a pass that was made in error
def reverse_pass():
    number = -1
    # Find a clue that has a state of "Passed" (there should only be one)
    for clue in clues.itervalues():
        if clue.state == Clue_state.Passed:
            clue.set_state(Clue_state.Set)
            number = clue.number
    if number == -1 or game_state != Game_state.Passed:
        # If we didn't find a clue, or the game is not in the "Passed" state
        send_message('There is nothing to undo.  No clues are currently "passed".')
    else:
        set_game_state(Game_state.Guessing)
        send_message("Okay, I've cleaned up your mess.  Clue #%s is no longer passed.  Next time, say what you mean!" % (number))
        
# The defender has posted a (new) letter.
def repin_defender(msg, text):
    global defending_message, defending_text, defending_timestamp, defender_name, defender_id, waves
    # Try to unpin the existing "defending" message
    try:
        defending_message.cancel_stars()
        time.sleep(1.1)
    # If it can't be unpinned, there probably isn't one, and this is the start of a new game.
    except:
        reset()
        waves = {}
        if TESTING: print("No defender pinned")
        
    toggle_pinning(msg.message) # Pin the new "defending" message
    
    # Set the globals that have the defence data
    defending_message = msg.message
    defending_text = text.upper().strip().replace(" ", "")
    defender_id = msg.user.id
    defender_name = msg.user.name
    defending_timestamp = msg.time_stamp
    
    set_game_state(Game_state.Guessing)
    
    # Set all extant clues to "uncertain" status
    for clue in clues.itervalues():
        clue.set_state(Clue_state.Schroedinger)

# Helper function to invalidate a clue
def remove_clue(clue, new_clue_state, new_game_state = None):
    clue.set_state(new_clue_state)
    dead_clues.append(clue)
    message = clue.message # Temporary copy of message, to be used for unstarring below
    del clues[clue.number] # Remove the clue from the list of active clues
    
    # Only cancel the star if there are no other clues in the same message (e.g. "4,5: Fifth space on a Monopoly board" for READING RAILROAD)
    if not any([clue.message == message for clue in clues.itervalues()]):
        message.cancel_stars()
    if new_game_state is not None:
        set_game_state(new_game_state)

# List active clues, along with their status
def display_clues(only_unstarred):
    clue_list = ""
    for c in clues.itervalues():
        # Loop through all clues, or only those without a star, depending on the value of only_unstarred
        if c.message.stars == 0 or not only_unstarred:
            this_clue = "%s: %s (by %s)" % (c.number, c.clue_text, c.setter_name)
            if c.guess != "":
                this_clue += " (waiting for confirmation of guess %s by %s)" % (c.guess, c.guesser_name)
            if len(c.contacts) > 0: # Clue has been contacted
                this_clue += " (contacted by %s)" % (", ".join(user for user in c.contacts.values()))
            if c.state == Clue_state.Schroedinger: # Clue owner hasn't confirmed alive/dead.
                this_clue += " (status uncertain)"
            clue_list += this_clue + "\n"
    if clue_list != "":
        send_message(clue_list, False) # No length check; message could easily be over 500 chars, and that's ok.
    elif only_unstarred:
        send_message("There are no active unstarred clues.  (Good work!)")
    else:
        send_message("There are no active clues." )
    
# List the contacts for a given clue or for all clues    
def display_contacts(command):

    #Display contacts for a specific clue.
    if len(command) > 9:
        number = command[10:]
        
        # Try converting the text after "!contacts" (minus apostrophes) into a number. If it doesn't work, the command is invalid.
        try: 
            c = float(number.replace("'", "")) # Remove apostrophes before trying to convert to float
        except:
            send_message("Syntax of the **`!contacts`** command:  **`!contacts <optional clue number>`**")
        
        if c is not None: # We got a valid number
            if TESTING: print(clues.keys())
            if TESTING: print(number)
            if number not in clues.keys():
                send_message("There is no active clue with the number %s" % (number))
            elif len(clues[number].contacts) == 0:
                send_message("There are no current contacts for clue number %s" % (number))
            else:
                send_message("Clue #%s is currently contacted by: %s" % (number, ", ".join(user for user in clues[number].contacts.values())))
    
    else: #Display all clues and contacts
        output = ""
        for c in clues.keys():
            if len(clues[c].contacts) > 0:
                output += "  #%s by %s\n" % (c, ", ".join(user for user in clues[c].contacts.values()))
        # Add a message if there are no contacts
        if output == "":
            snark = ""
            if len(clues) == 0:
                snark = ", which makes sense, since there are *no active clues*"
            send_message("There are currently **no** contacted clues%s!  C'mon, people!  Pick it up!" % (snark))
            if len(clues) > 10:
                send_message("Maybe stop trying to come up with *more clues*, and try to solve some of the existing ones instead?")
        else:
            send_message("The following clues are currently contacted:\n" + output)

# Reset the game state.  Unstar any messages from the previous game.
def reset():
    global defending_message, defending_timestamp, defender, defender_id, clues, dead_clues
    for c in clues.keys():
        clues[c].message.cancel_stars()
        time.sleep(1.1)
    if defending_message is not None:
        defending_message.cancel_stars()
    clues = {}
    dead_clues = []
    defending_message = None
    defending_timestamp = None
    defender = ""
    defender_id = -1

# Move to a different game state, as defined by the Game_state enum
def set_game_state(state):
    global game_state
    game_state = state
    print("Game state changed to %s" % (state))

# Post a message to the room, provided the bot has not been told to !shutup
# By default, the message can't be more than 500 characters, or it will fail silently.  Setting length_check to False allows longer messages.
def send_message(message, length_check=True):
    if muted_timestamp is None or (datetime.utcnow() - muted_timestamp).total_seconds() > mute_length:
        room.send_message(message, length_check)

# Stop the bot from posting any messages to the room.
# Can specify a time period (in minutes) or use the default of 10.
def mute(input):
    global muted_timestamp, mute_length
    minutes = 10
    if len(input) > 7: # Number of minutes has been specified
        arg = input[8:]
        # If number of minutes can't be converted to a float, it wasn't entered correctly.
        try:
            minutes = float(arg)
        except:
            send_message("You must specify a number of minutes, or just use **`!shutup`** on its own to default to 10 minutes.")
            
    mute_length = minutes * 60
    send_message("Ok, I won't say anything else for %s minutes, unless you tell me to **`!speak`**.  I will continue to star/unstar clues as I'm able, and I'll still keep track of the game." % (minutes))
    muted_timestamp = datetime.utcnow()
    log("info", "Muted for %s minutes." % (minutes))

# If the bot has been muted, cancel the mute.    
def unmute():
    global muted_timestamp, mute_length
    muted_timestamp = None
    mute_length = 600
    send_message("Your wish is my command.  What can I do for you?")

# Disable extraneous messages from the bot.  Only messages directly related to gameplay will be posted.
def toggle_verbosity(setting):
    global verbose
    if setting == "0" or setting == "off":
        verbose = False
        send_message("Ok. After this, I'll only speak if you really need to know something. You can make me more chatty with **`!verbose on`**. Or you can silence me entirely with **`!shutup`**.")
    elif setting == "1" or setting == "on":
        verbose = True
        send_message("Ok. I love talking!  We can talk about all sorts of things!  I love Contact.  Do you?  Do you like defending or attacking better?  I'm never sure which one I like the most, but being a bot, I'll probably never get a chance to do either.  So sad. In verbose mode, I'll make sure to inform you whenever you're out of line, keep you abreast of game developments, and maybe throw in a few witticisms here and there just for fun. I love to talk! (**`!verbose off`** turns off verbose mode.)")
    elif setting is None or setting == "":
        send_message("Verbose mode is currently %s. You can turn it %s with **`!verbose %s`**." % ("on" if verbose else "off", "off" if verbose else "on", "off" if verbose else "on"))
    else:
        send_message("Usage: **`!verbose [on|off]`**.")

# Check for clues with "uncertain" status (haven't been confirmed alive/dead after a new letter has been given).
# If it's been long enough since the new letter has been given, remind the setter that they need to indicate whether the clue is still alive.
def check_clue_status():
    users_to_warn = {} # Make a list so we don't give multiple warnings for multiple clues by the same user
    for clue in clues.itervalues():
        if clue.state == Clue_state.Schroedinger and not clue.warned and (datetime.utcnow() - clue.state_timestamp).total_seconds() > SCHROEDINGER_TIMEOUT:
            setter = clue.setter_name.replace(" ", "") # We're pinging them, so no spaces.

            # Either make a new list or add to the existing one.
            if setter not in users_to_warn:
                users_to_warn[setter] = [clue.number]
            else:
                users_to_warn[setter].append(clue.number)
            clue.warned = True # So that we don't keep warning about the same clue
            
    # Send one message for each user who has outstanding clues
    for setter in users_to_warn.iterkeys():
        nums = users_to_warn[setter] # All clues for this user
        # Get the proper wording for one vs. many clues
        clue_text = "clue #%s is" % (nums[0])
        if len(nums) > 1:
            clue_text = "clues #%s and #%s are" % (", #".join(number for number in nums[0:len(nums) - 1]), nums[len(nums) - 1]) # Join all but the last, then put the last one after the "and"
        send_message("@%s, it's been more than %s minutes since %s provided a new letter, and you still haven't indicated whether %s alive or dead." % (setter, SCHROEDINGER_TIMEOUT / 60.0, defender_name, clue_text))

# Check for guesses that haven't been responded to.  If enough time has elapsed since the guess was made, notify the clue setter.
def check_guess_status():
    for clue in clues.itervalues():
        if clue.guess != "" and clue.guess_warned == False and (datetime.utcnow() - clue.guess_timestamp).total_seconds() > GUESS_TIMEOUT:
            send_message("@%s, %s guessed *%s* for clue #%s.  Please confirm or deny the guess." % (clue.setter_name.replace(" ", ""), clue.guesser_name, clue.guess, clue.number))
            clue.guess_warned = True
            
# Monitor the "waves" ("o/", "O/", "0/", etc.) posted in the room.
# If several people wave (indicating a desire to play) within a certain time period, intiate a "ping" (notify all users on the pinglist).
def check_waves():
    wavecount = 0
    # Check how many waves occurred in the last while (wave timestamps are recorded when they are posted)
    for wave in waves.itervalues():
        if (datetime.utcnow() - wave).total_seconds() < WAVE_DEATH:  # Within the time specified by WAVE_DEATH
            wavecount += 1
    if wavecount > WAVES_FOR_PING:  # We have enough waves
        send_message("There are %s people waiting to play Contact!  Want to join?" % (wavecount))
        ping() # Ping everyone on the pinglist

# Print a help message
def info():
    send_message("""    Hello! I'm %s, a bot to help with the game of Contact. 
    I will try to keep track of the game state and keep the game moving. If you're on my whitelist, you can use the following commands to communicate with me (some are mod-only): 
     !clues                    - list all active clues
     !contacts [clueNum]       - list contacts for a specific clue or all clues
     !unpass                   - undo a "pass" if you made a mistake
     !kill                     - remove a clue from the list of active clues. This will kill anyone's clue, not just your own.
     !uncontact clueNum        - remove all contacts for clue "clueNum"
     !shutup [minutes]         - silence me completely for the specified amount of time (defaults to 10 min)
     !speak                    - undo a !shutup command
     !verbose [on|off]         - in verbose mode, I'll comment more on game events. No parameter lists the current state
     !whitelist [[+|-]userNum] - add/remove a user from the whitelist, or list users on the whitelist
     !pinglist [[+|-]userName] - add/remove a user from the pinglist, or list users on the pinglist
     !ping                     - ping all users on the pinglist to indicate that you want to start a game
     !shutdown                 - shut me down permanently. I will need to be restarted by the bot owner""" % (my_user.name), False)

def modify_list(list_var, param, table_name):
    if param != "":
        if param[0] == "+":
            add_list(list_var, param[1:], table_name)
        elif param[0] == "-":
            remove_list(list_var, param[1:], table_name)
        else:
            add_list(list_var, param, table_name)
    else:
        show_list(list_var)

  
def add_list(list_var, param, table_name):
    list_var.add(param)
    try:
        send_message("Adding %s to the %s." % (str(param) + " (" + client.get_user(int(param)).name + ")", table_name))
    except:
        send_message("Adding %s to the %s." % (param, table_name))

    db = sqlite3.connect('temp.db')
    db.execute('INSERT INTO {} (user) values (?)'.format(table_name), (param,))
    db.commit()
    db.close()

def remove_list(list_var, param, table_name):
    if param not in list_var:
        send_message("%s is not on the %s." % (param, table_name))
    else:
        list_var.remove(param)
        try:
            send_message("Removing %s from the %s." % (str(param) + " (" + client.get_user(int(param)).name + ")", table_name))
        except:
            send_message("Removing %s from the %s." % (param, table_name))

        db = sqlite3.connect('temp.db')
        db.execute('DELETE FROM {} WHERE user = ?'.format(table_name), (param,))
        db.commit()
        db.close()

def cooldown(seconds):
    def inner(fn):
        def ret_fn(*args, **kwargs):
            if time.time() > ret_fn.last_time_stamp + seconds:
                fn(*args, **kwargs)
                ret_fn.last_time_stamp = time.time()

        ret_fn.last_time_stamp = 0
        return ret_fn
    return inner

@cooldown(1)
def toggle_pinning(msg):
    ret_val = msg._client._br.toggle_pinning(msg.id)
    if TESTING: print("Toggle: %s" % (ret_val))

@cooldown(1)
def add_star(msg):
    ret_val = msg.message._client._br.toggle_starring(msg.id)
    if TESTING: print("Add star: %s" % (ret_val))

@cooldown(10)
def ping():
    for x in range(0, len(pinglist), 10):
        send_message( " ".join('@'+name for name in pinglist[x:x+10]) )

@cooldown(10)
def show_list(list_var):
    list = ""
    try:
        list = ", ".join(str(x) + " (" + client.get_user(int(x)).name + ")" for x in list_var)
    except:
        list = ", ".join(x for x in list_var)
    send_message(list, False) #Allow more than 500 chars
    if len(list) > 500:
        send_message("That list is getting kind of long.  You might want to consider pruning those who are no longer active...")
        
def init_list(list_var, table_name):
    db = sqlite3.connect('temp.db')
    
    results = db.execute("SELECT * FROM sqlite_master WHERE type='table' AND name='%s'" % (table_name));
    if not results.fetchall():
        db.execute('CREATE TABLE %s (user int)' % (table_name))
        db.commit()
        db.close()

        db = sqlite3.connect('temp.db', isolation_level=None)
        db.executemany('INSERT INTO {} (user) values (?)'.format(table_name), [(x,) for x in list_var])
        db.commit()
    else:
        results = db.execute("SELECT * FROM %s" % (table_name))
        list_var = set([x[0] for x in results.fetchall()])
        log('debug', "%s: %s" % (table_name, list_var))

    db.close()
    return list_var
    
main()
