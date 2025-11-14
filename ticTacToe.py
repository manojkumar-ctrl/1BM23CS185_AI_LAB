board = {
    1: ' ', 2: ' ', 3: ' ',
    4: ' ', 5: ' ', 6: ' ',
    7: ' ', 8: ' ', 9: ' '
}

def printBoard(board):
    print(board[1] + '|' + board[2] + '|' + board[3])
    print('-+-+-')
    print(board[4] + '|' + board[5] + '|' + board[6])
    print('-+-+-')
    print(board[7] + '|' + board[8] + '|' + board[9])
    print('\n')

def spaceFree(pos):
    if board[pos] == ' ':
        return True
    else:
        return False

def checkWin():
    # Rows
    if board[1] == board[2] == board[3] != ' ':
        return True
    elif board[4] == board[5] == board[6] != ' ':
        return True
    elif board[7] == board[8] == board[9] != ' ':
        return True
    # Diagonals
    elif board[1] == board[5] == board[9] != ' ':
        return True
    elif board[3] == board[5] == board[7] != ' ':
        return True
    # Columns
    elif board[1] == board[4] == board[7] != ' ':
        return True
    elif board[2] == board[5] == board[8] != ' ':
        return True
    elif board[3] == board[6] == board[9] != ' ':
        return True
    else:
        return False

def checkMoveForWin(move):
    # Same checks as checkWin but for a particular move ('X' or 'O')
    if board[1] == board[2] == board[3] == move:
        return True
    elif board[4] == board[5] == board[6] == move:
        return True
    elif board[7] == board[8] == board[9] == move:
        return True
    elif board[1] == board[5] == board[9] == move:
        return True
    elif board[3] == board[5] == board[7] == move:
        return True
    elif board[1] == board[4] == board[7] == move:
        return True
    elif board[2] == board[5] == board[8] == move:
        return True
    elif board[3] == board[6] == board[9] == move:
        return True
    else:
        return False

def checkDraw():
    for key in board.keys():
        if board[key] == ' ':
            return False
    return True

def insertLetter(letter, position):
    if spaceFree(position):
        board[position] = letter
        printBoard(board)

        if checkWin():
            if letter == 'X':
                print('Bot wins!')
            else:
                print('You win!')
            exit()
        elif checkDraw():
            print('Draw!')
            exit()
    else:
        print('Position taken, please pick a different position.')
        position = int(input('Enter new position: '))
        insertLetter(letter, position)

player = 'O'
bot = 'X'

def playerMove():
    position = int(input('Enter position for O (1-9): '))
    insertLetter(player, position)

def compMove():
    bestScore = -1000
    bestMove = 0
    for key in board.keys():
        if board[key] == ' ':
            board[key] = bot
            score = minimax(board, False)
            board[key] = ' '
            if score > bestScore:
                bestScore = score
                bestMove = key
    insertLetter(bot, bestMove)

def minimax(board, isMaximizing):
    if checkMoveForWin(bot):
        return 1
    elif checkMoveForWin(player):
        return -1
    elif checkDraw():
        return 0

    if isMaximizing:
        bestScore = -1000
        for key in board.keys():
            if board[key] == ' ':
                board[key] = bot
                score = minimax(board, False)
                board[key] = ' '
                if score > bestScore:
                    bestScore = score
        return bestScore
    else:
        bestScore = 1000
        for key in board.keys():
            if board[key] == ' ':
                board[key] = player
                score = minimax(board, True)
                board[key] = ' '
                if score < bestScore:
                    bestScore = score
        return bestScore

printBoard(board)

while not checkWin() and not checkDraw():
    playerMove()
    if not checkWin() and not checkDraw():
        compMove()
