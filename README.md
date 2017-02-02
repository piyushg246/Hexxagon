# Hexxagon

Hexxagon is a two player board game which is played on a 6X7 grid of cells. Each player has an allocated color, Red ( First Player ) or White ( Second Player ) being conventional.
The board is customised. Instead of square board, there will be a rectangular board with hexagonal cells. 

The game will end after 100 moves ( 50 moves for each player ) or when any of the players don't have any move left. At the end of the game the player with majority of stone will win.

We will play it on an 6X7 grid. The top left of the grid is [0,0] and the bottom right is [5,6]. The rule is that a cell[i,j] is adjacent to any of cells which share same side.

Input:
The input will be a 6X7 matrix consisting only of 0,1 and 2. Next line will contain an integer denoting the total number of moves till the current state of the board. Next line contains an integer - 1 or 2 which is your player id.
The y-coordinate increases from left to right, and x-coordinate increases from top to bottom.

The cell marked 0 means it doesn't contain any stones. The cell marked 1 means it contains first player's stone which is Red in color. The cell marked 2 means it contains second player's stone which is white in color.

Output:
In the first line print the coordinates of the cell separated by space, the piece he / she wants to spread or jump. In the next line print the coordinates of the cell in which the piece will spread or jump. 
You must take care that you don't print invalid coordinates. 
For example, [1,1] might be a valid coordinate in the game play if [1,1] is adjacent or is at two spaces away from the piece that you are going to move, 
but [9,10] will never be. Also if you play an invalid move or your code exceeds the time/memory limit while determining the move, you lose the game.

Starting state:

The starting state of the game is the state of the board before the game starts
1 0 0 0 0 0 2
0 0 0 0 0 0 0
0 0 0 0 0 0 0
0 0 0 0 0 0 0
0 0 0 0 0 0 0
2 0 0 0 0 0 1
0

First Input: 

This is the input give to the first player at the start of the game
1 0 0 0 0 0 2
0 0 0 0 0 0 0
0 0 0 0 0 0 0
0 0 0 0 0 0 0
0 0 0 0 0 0 0
2 0 0 0 0 0 1
0
1

The time limit is 1 second and memory limit is 256MB.

For better understanding, see : 
https://www.hackerearth.com/problem/multiplayer/hexxagon/
( Problem for the battle of Bots 8 competition )
The AI code file takes as input a board state, a player id and output the move coordinates.
It also displays the depth of the search tree.


I won runner-up prize in Battle of Bots 8.
I have improved the code a bit and I am now able to reach much higher depths for deciding the best move.
