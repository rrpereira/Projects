import ast
import collections
import os
import sys
# Using undetected_chromedriver in spite of webdriver because this way chrome doesn't know this is an automated tool
import undetected_chromedriver as uc
# getpass() asks the user for a password and hides whatever is written
from getpass import getpass
# from selenium import webdriver
from selenium.webdriver.common.by import By
from selenium.webdriver.common.keys import Keys
from selenium.webdriver.support import expected_conditions as EC
from selenium.webdriver.support.ui import WebDriverWait
from time import sleep


class InstaBot:

    __driver = None
    __wait = None

    # Instantiate the class and open the browser
    def __init__(self):
        prefs = {"profile.managed_default_content_settings.images": 2}
        chrome_options = uc.ChromeOptions()
        chrome_options.add_experimental_option("prefs", prefs)
        # self.driver = uc.Chrome(chrome_options=chrome_options) # change between this and the one below
        self.driver = uc.Chrome()  # change between this and the one above
        # Each time the bot waits for an element to appear/be clickable, it waits no more than 60 seconds by default, throwing a TimeoutException after that
        self.wait = WebDriverWait(self.driver, 10)

    def load_cookies(self):
        # Before loading cookies the program must navigate to a website (it's the only way for it to work)
        self.driver.get("https://instagram.com")
        try:
            file = open("../data/cookies", "r")
            cookies = file.read().split("\n")
            cookies.pop()
            for cookie in cookies:
                # Converting string cookie into a dictionary and adding it to the browser cookies
                self.driver.add_cookie(ast.literal_eval(cookie))
            file.close()
        except Exception as e:
            print("Cookies were not loaded. Check the following exception:")
            print(e)
            return False
        return True

    def store_cookies(self):
        try:
            cookies = self.driver.get_cookies()
            file = open("../data/cookies", "w")
            for cookie in cookies:
                file.write(str(cookie)+"\n")
            file.close()
        except Exception as e:
            print("Cookies were not stored. Check the following exception:")
            print(e)

    # Tries to login with cookies, otherwise tries to login with credentials
    def login(self, username, password):
        searchBarInput = "//span[contains(text(), 'Search')]"
        self.login_with_cookies()
        try:
            # Tries to find the search bar (which means the user is logged in)
            self.driver.find_element_by_xpath(searchBarInput)
        except:
            print("Couldn't login with cookies. Trying login with credentials...")
            try:
                self.login_with_credentials(username, password)
                self.driver.find_element_by_xpath(searchBarInput)
            except:
                print("Couldn't login with credentials.")
                quit()

    # Turn off notifications
    def turn_off_notifications(self):
        try:
            notNowButton = "//button[contains(text(), 'Not Now')]"
            self.wait.until(EC.element_to_be_clickable(
                (By.XPATH, notNowButton)))
            self.driver.find_element_by_xpath(notNowButton).click()
        except Exception as e:
            print("Couldn't turn off notifications. Check the following exception:")
            print(e)

    # Accept (necessary) cookies
    def accept_necessary_cookies(self):
        acceptAllButton = "//button[contains(text(), 'Accept')]"
        manageDataSettingsButton = "//button[contains(text(), 'Manage Data Settings')]"
        acceptCookiesButton = "//button[contains(text(), 'Accept Cookies')]"
        # todo this might not be enough to counter instagram anti bot measures
        generalAcceptCookiesButton = "//button[contains(text(), \"Only allow essential cookies\")]"

        try:
            self.wait.until(EC.element_to_be_clickable(
                (By.XPATH, acceptAllButton)))
            self.driver.find_element_by_xpath(
                manageDataSettingsButton).click()
            self.wait.until(EC.element_to_be_clickable(
                (By.XPATH, acceptCookiesButton)))
            self.driver.find_element_by_xpath(acceptCookiesButton).click()
        except Exception as e:
            print("Couldn't accept necessary cookies. Check the following exception:")
            print(e)

        try:
            self.wait.until(EC.element_to_be_clickable(
                (By.XPATH, generalAcceptCookiesButton)))
            self.driver.find_element_by_xpath(
                generalAcceptCookiesButton).click()
        except Exception as e:
            print("Couldn't accept general cookies. Check the following exception:")
            print(e)
            quit()

    # Login using previously stored cookies
    def login_with_cookies(self):
        if self.load_cookies() == True:
            self.driver.get("https://instagram.com")
            self.turn_off_notifications()

    # Login using user credentials
    def login_with_credentials(self, username, password):
        usernameInput = "//input[@name=\"username\"]"
        passwordInput = "//input[@name=\"password\"]"
        loginButton = "//button[@type=\"submit\"]"

        self.accept_necessary_cookies()

        # Wait until password input is visible
        self.wait.until(EC.presence_of_element_located(
            (By.XPATH, passwordInput)))

        # Insert username and password
        self.driver.find_element_by_xpath(usernameInput).send_keys(username)
        self.driver.find_element_by_xpath(passwordInput).send_keys(password)

        # Wait/click for/in login button
        self.wait.until(EC.element_to_be_clickable((By.XPATH, loginButton)))
        self.driver.find_element_by_xpath(loginButton).click()

        self.turn_off_notifications()

    # Stores cookies and closes the browser
    def close_bot(self):
        self.store_cookies()
        self.driver.close()

    def sleep_between_comments(slef):
        sleep(30)

    # Assumes the driver is already in the post and comments it
    def comment_post(self, comment):
        commentInput = "//textarea[@aria-label=\"Add a comment…\"]"
        postButton = "//button[contains(text(), 'Post')]"
        # Wait for the comment text area to be clickable
        self.wait.until(EC.element_to_be_clickable((By.XPATH, commentInput)))
        # Find the comment text area, click it, check if it is clear, write the comment and post it
        def entry(): return self.driver.find_element_by_xpath(commentInput)
        entry().click()
        if entry().get_attribute('value') != "":
            raise ValueError('The comment text area is not clear.')
        entry().send_keys(comment)
        self.driver.find_element_by_xpath(postButton).click()

    # Writes multiple comments with usernames in a post
    def multiple_comments_with_usernames(self, post, usernames, numberOfComments, numberOfMentionsInComment):
        commentInput = "//textarea[@aria-label=\"Add a comment…\"]"
        file = open("../data/failedUsernames", "a")
        commentsCounter = 0

        self.driver.get(post)

        while len(usernames) >= numberOfMentionsInComment and commentsCounter < numberOfComments:
            try:
                self.comment_post(
                    ' '.join(usernames[0:numberOfMentionsInComment]))
                del usernames[:numberOfMentionsInComment]
                commentsCounter = commentsCounter + 1
                # Remove the previous line written in stdout
                if commentsCounter != 1:
                    sys.stdout.write('\x1b[1A')
                    sys.stdout.write('\x1b[2K')
                print(commentsCounter, "coments done.")
                self.sleep_between_comments()
            except ValueError as e:
                os.system('play -nq -t alsa synth {} sine {}'.format(1, 200))
                self.driver.find_element_by_xpath(commentInput).clear()
                file.write(
                    ' '.join(usernames[0:numberOfMentionsInComment]) + " ")
                del usernames[:numberOfMentionsInComment]
                print("Couldn't comment. Check the following exception:")
                print(e)

        file.close()

    def store_usernames_in_file(self, usernames):
        try:
            file = open("../data/usernames", "a")
            file.write(' '.join(usernames) + " ")
            file.close()
        except Exception as e:
            print("Usernames were not stored. Check the following exception:")
            print(e)

    def load_usernames_in_file(self):
        try:
            file = open("../data/usernames", "r")
            usernames = file.read().split(" ")
            file.close()
            return usernames
        except Exception as e:
            print("Usernames were not loaded. Check the following exception:")
            print(e)

    # Collect user followers or users that the user is following (depending on mode)
    def collect_user_followers_or_following(self, userProfile, mode):
        followingButton = "//a[contains(@href,'/" + mode + "')]"
        scrollBar = "//div[@class=\"isgrP\"]"
        # loadingUsers = ".//li[@class = \"wo9IH QN7kB \"]/*[name() = \"svg\"][@aria-label = \"Loading...\"]" #this is the xpath to the cogwheel that appears when scrolling down followers/following
        self.driver.get("https://www.instagram.com/" + userProfile + "/")
        self.driver.find_element_by_xpath(followingButton).click()

        # Wait for the scroll bar to appear
        self.wait.until(EC.visibility_of_element_located(
            (By.XPATH, scrollBar)))

        # Scroll the followers all the way down to the bottom
        last_ht, ht = 0, 1
        while last_ht != ht:
            last_ht = ht
            sleep(1)
            ht = self.driver.execute_script("""
					arguments[0].scrollTo(0, arguments[0].scrollHeight);
					return arguments[0].scrollHeight;
					""", self.driver.find_element_by_xpath(scrollBar))

        # Get all the "a" html tags that contain the usernames
        aTags = self.driver.find_elements_by_tag_name('a')

        # Extract usernames from "a" tags and store them in a file
        self.store_usernames_in_file(
            ['@' + name.text for name in aTags if name.text != ''])

    # Check if the comment is valid given the "a" element wich contains the usernames mentions and the minimum number of mentions
    def is_valid_comment(self, mentions, numberOfMentionsInComment):
        return len(list(set([x.text for x in mentions]))) >= numberOfMentionsInComment

    # Check the top commentators
    def top_commentators(self, post, numberOfMentionsInComment, topNumber):
        self.driver.get(post)

        # Comments "invisible" scrollbar
        scrollBar = "//ul[@class=\"XQXOT    pXf-y \"]"
        # "View replies" button
        viewRepliesButton = ".//button[@class=\"sqdOP yWX7d    y3zKF     \"]//span[contains(text(), 'View')]"
        # The elements that are part of a comment (which includes the username and the text) (by comment, it means standard comments and also replies)
        commentDiv = ".//ul[@class=\"Mr508 \"]//div[@class=\"C4VMK\"]"
        commentatorA = ".//a[@class=\"sqdOP yWX7d     _8A5w5   ZIAjV \"]"
        mentionsA = ".//a[@class=\"notranslate\"]"
        # Button to load more comments
        moreButton = ".//div[@class = \"QBdPU \"]/*[name() = \"svg\"][@aria-label = \"Load more comments\"]"

        # Wait for the scroll bar to appear
        self.wait.until(EC.element_to_be_clickable(
            (By.XPATH, scrollBar)))

        # This loop scrools through the comments all the way down to the bottom
        while True:
            # Scroll down
            self.driver.execute_script(
                """arguments[0].scrollTo(0, arguments[0].scrollHeight);return arguments[0].scrollHeight;""", self.driver.find_element_by_xpath(
                    scrollBar))
            # Apparently this is not needed
            # self.wait.until(EC.visibility_of_element_located(
            #    (By.XPATH, loadCommentsDiv)))
            # self.wait.until(EC.invisibility_of_element_located(
            #    (By.XPATH, loadCommentsDiv)))
            try:
                # Try to find the button to load more comments
                self.wait.until(EC.element_to_be_clickable(
                    (By.XPATH, moreButton)))
                self.driver.find_element_by_xpath(moreButton).click()
            except:
                # Breaks the infinite loop when the load button can't be found
                break

        # Replies appear bellow other comments after clicking the "View replies" button, but if there are many replies to one comment, one click might not be enough to display them all - we have to click the button until it disappears. Therefore, the bot collects all of the existing "View replies" buttons (find_elements_by_xpath) function and iterates over all of them to click them (for loop). After this, it collects again the remaining "View replies" buttons. If there are still buttons to be clicked (while loop condition) it will iterate over them again, and so on.
        while len(replies := self.driver.find_elements_by_xpath(
                viewRepliesButton)):
            for reply in replies:
                reply.click()

        # Get all the "div" elements (each containing info related with each comment)
        commentDivElements = self.driver.find_elements_by_xpath(
            commentDiv)
        commentators = [x.find_element_by_xpath(commentatorA).text
                        for x in commentDivElements
                        if self.is_valid_comment(
            x.find_elements_by_xpath(mentionsA), numberOfMentionsInComment)]

        # Print the message with the top 10 commentators
        topCommentators = collections.Counter(
            commentators).most_common(topNumber)
        print("Here are the top", topNumber, "commentators:")
        for x in range(len(topCommentators)):
            print(str(x+1) + "º. " + topCommentators[x][0] + " (" +
                  str(round(topCommentators[x][1]/len(commentators)*100, 2)) + "%)")
        print("Total: " + str(len(commentators)) + " comentários.")


# Elements to be used during the program execution

# Username with which the login will be done
username = input("Enter your username : ")
# Password corresponding to the previous username
password = getpass()
# Give away post to comment or to analyse
post = "https://www.instagram.com/<user>/<post_id>/"
# Profile used to collect usernames
userProfile = "<user_id>"
# Required mentions per comment
numberOfMentionsInComment = 3
# The number of comments to be done
numberOfComments = 100
# The top number of commentators
topNumber = 10
# The place where we want to collect usernames from followers/following
mode = "followers"


# Call functions here

session = InstaBot()
# usernames = session.load_usernames_in_file()
# session.login(username, password)
# session.top_commentators(post, numberOfComments, topNumber)
# session.collect_user_followers_or_following(userProfile, mode)
# session.multiple_comments_with_usernames(post, usernames, numberOfComments, numberOfMentionsInComment)
# session.close_bot()
