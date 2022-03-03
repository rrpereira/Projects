# Instabot

Instabot is a software tool that interacts with Instagram ®. The main goal of this tool was initially to automate the process of commenting on giveaway posts. This type of contest happens quite frequently on Instagram ® and it consists in choosing a random comment between all the comments made on that giveaway post. The person who did the chosen comment wins the announced prize. Therefore, the more a user comments on that post, the more probability he has to win the prize.  

## Tools

[<img src="https://user-images.githubusercontent.com/36520545/156653017-a174ead3-0d54-4b7d-a273-3d2537330b11.png" width="100" height="100">](https://www.python.org/) [<img src="https://user-images.githubusercontent.com/36520545/156652120-8822fa40-107e-45e1-a2cd-f759825134d7.jpg" width="100" height="100">](https://www.selenium.dev/)

<!-- Abstract -->


## Code explanation

* Functions
    + \_\_init\_\_(self) - Instantiates the class and open the browser.  
    + load_cookies(self) - Tries to go to the file containing the cookies of the previous execution.
    + store_cookies(self) - Stores in a file the cookies of the current execution.
    + login(self, username, password) - Loads cookies and tries to login with them, otherwise, given two strings, the username and the password, the program tries to login with those.
    + turn_off_notifications(self) - Clicks in the button to turn off notifications.
    + accept_necessary_cookies(self) - Clicks in the button to accept sharing cookies.
    + login_with_cookies(self) - This functions calls **load_cookies(self)** and does other minor tasks.
    + login_with_credentials(self, username, password) - This functions searches for username and password input boxes to write the given username and password strings.
    + close_bot(self) - This function calls **store_cookies(self)** and closes the browser after that.
    + sleep_between_comments(slef) - This functions simply pauses the execution of the program for a certain ammount of seconds.   
    + comment_post(self, comment) - Assuming that the browser is already located in a post, the program searches for a text area html element and writes the given comment.
    + multiple_comments_with_usernames(self, post, usernames, numberOfComments, numberOfMentionsInComment) - This function does multiple comments. It removes the usernames used in the comment from the stored usernames, builds a comment with them, and comments the post. If it is unable to post the comment, the usernames are stored in a specific file.
    + store_usernames_in_file(self, usernames) - Stores usernames to be used later in the comments.
    + load_usernames_in_file(self) - Loads usernames to be used later in the comments.
    + collect_user_followers_or_following(self, userProfile, mode) - Collects usernames from a given user profile. The usernames are collected either from his followers or from the users he is following. After that this function calls **store_usernames_in_file(self, usernames)**.
    + is_valid_comment(self, mentions, numberOfMentionsInComment) - Checks if a comment is valid according to the required number of mentions.
    + top_commentators(self, post, numberOfMentionsInComment, topNumber) - This function loads all of the comments and their replies to assess who is the person with more comments. 

* Variables
    + username - Asks the user to write its Instagram username.
    + password - Asks the user to write its Instagram password.
    + post - Stores a string containing the link of the post to comment/analyse.
    + userProfile - Stores the username from which the usernames used in the comments will be collected.
    + numberOfMentionsInComment - Stores the number of mentions in a comment.
    + numberOfComments - Stores the number of comments to be done.
    + topNumber - Stores the number x, where x is the x top commentators
    + mode - Stores the string "following" or "followers", meaning that the program will either collect users from the "followers" or from the "following.




## Setup

The user has to create a "data" folder at the same level of instabot (this project) folder - information resulting from the execution of the program will be saved here. The user has to change the [instabot.py](instabot.py) variables at the bottom of this file.

## Execution

```
python3 instabot.py
```


### Commenting a post 

![Normal execution](.media/noerrorsexecution.gif)


### Collecting usernames

![Execution with counterexample](.media/executionwitherrors.gif)


### Analysing the top 10 commentators

![Execution with counterexample](.media/executionwitherrors.gif)
