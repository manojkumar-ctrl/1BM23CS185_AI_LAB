# 8 Puzzle Problem using Iterative Deepening Search (IDS)

from copy import deepcopy

# Define the goal state
goal_state = [[1, 2, 3],
              [4, 5, 6],
              [7, 8, 0]]  # 0 represents the blank space

# Find the blank (0) position
def find_blank(state):
    for i in range(3):
        for j in range(3):
            if state[i][j] == 0:
                return i, j

# Generate all possible next moves
def generate_moves(state):
    moves = []
    x, y = find_blank(state)
    directions = [(-1, 0), (1, 0), (0, -1), (0, 1)]  # Up, Down, Left, Right

    for dx, dy in directions:
        new_x, new_y = x + dx, y + dy
        if 0 <= new_x < 3 and 0 <= new_y < 3:
            new_state = deepcopy(state)
            # Swap blank with the new position
            new_state[x][y], new_state[new_x][new_y] = new_state[new_x][new_y], new_state[x][y]
            moves.append(new_state)
    return moves

# Check if goal state is reached
def is_goal(state):
    return state == goal_state

# Depth-Limited Search (DFS up to depth limit)
def depth_limited_search(state, depth, limit, path, visited):
    if is_goal(state):
        return path
    if depth >= limit:
        return None
   
    visited.add(tuple(map(tuple, state)))  # Convert list of lists to tuple for hashing
   
    for move in generate_moves(state):
        move_tuple = tuple(map(tuple, move))
        if move_tuple not in visited:
            result = depth_limited_search(move, depth + 1, limit, path + [move], visited)
            if result:
                return result
    return None

# Iterative Deepening Search
def iterative_deepening_search(initial_state):
    depth = 0
    while True:
        print(f"Trying depth limit = {depth}")
        visited = set()
        result = depth_limited_search(initial_state, 0, depth, [initial_state], visited)
        if result:
            return result
        depth += 1

# Function to print a 3x3 puzzle
def print_puzzle(state):
    for row in state:
        print(row)
    print()

# Example: initial state from your PDF
initial_state = [[1, 2, 3],
                 [0, 4, 6],
                 [7, 5, 8]]

print("Initial State:")
print_puzzle(initial_state)

solution = iterative_deepening_search(initial_state)

print("Goal Found! Solution Path:")
for step, state in enumerate(solution):
    print(f"Step {step}:")
    print_puzzle(state)
