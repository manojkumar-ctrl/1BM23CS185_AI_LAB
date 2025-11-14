from heapq import heappush, heappop

# Goal state for 8-puzzle
GOAL_STATE = (1, 2, 3,
              4, 5, 6,
              7, 0, 8)  # 0 represents the blank tile

# Directions for moving the blank tile (row, col)
DIRECTIONS = {'Up': -3, 'Down': 3, 'Left': -1, 'Right': 1}

def misplaced_tiles(state):
    """Heuristic: count of misplaced tiles compared to the goal."""
    return sum(1 for i in range(9) if state[i] != 0 and state[i] != GOAL_STATE[i])

def manhattan_distance(state):
    """Heuristic: sum of Manhattan distances of tiles from their goal positions."""
    distance = 0
    for i, tile in enumerate(state):
        if tile == 0:
            continue
        goal_pos = GOAL_STATE.index(tile)
        current_row, current_col = divmod(i, 3)
        goal_row, goal_col = divmod(goal_pos, 3)
        distance += abs(current_row - goal_row) + abs(current_col - goal_col)
    return distance

def get_neighbors(state):
    """Generate neighboring states from the current state by sliding the blank tile."""
    neighbors = []
    zero_pos = state.index(0)

    row, col = divmod(zero_pos, 3)

    def swap_positions(s, i, j):
        lst = list(s)
        lst[i], lst[j] = lst[j], lst[i]
        return tuple(lst)

    # Possible moves: up, down, left, right
    moves = []
    if row > 0:
        moves.append(zero_pos - 3)  # Up
    if row < 2:
        moves.append(zero_pos + 3)  # Down
    if col > 0:
        moves.append(zero_pos - 1)  # Left
    if col < 2:
        moves.append(zero_pos + 1)  # Right

    for move in moves:
        neighbors.append(swap_positions(state, zero_pos, move))

    return neighbors

def reconstruct_path(came_from, current):
    path = []
    while current in came_from:
        current, action = came_from[current]
        path.append(current)
    return path[::-1]

def a_star(start_state, heuristic='manhattan'):
    """A* search for 8-puzzle with heuristic choice."""
    if heuristic == 'manhattan':
        h_func = manhattan_distance
    elif heuristic == 'misplaced':
        h_func = misplaced_tiles
    else:
        raise ValueError("Heuristic must be 'manhattan' or 'misplaced'")

    open_set = []
    heappush(open_set, (h_func(start_state), 0, start_state))
    came_from = {}

    g_score = {start_state: 0}
    closed_set = set()

    while open_set:
        _, cost, current = heappop(open_set)

        if current == GOAL_STATE:
            # Reconstruct path
            path = []
            while current in came_from:
                prev_state, _ = came_from[current]
                path.append(current)
                current = prev_state
            path.append(start_state)
            return path[::-1]

        closed_set.add(current)

        for neighbor in get_neighbors(current):
            if neighbor in closed_set:
                continue

            tentative_g_score = g_score[current] + 1

            if neighbor not in g_score or tentative_g_score < g_score[neighbor]:
                came_from[neighbor] = (current, None)
                g_score[neighbor] = tentative_g_score
                f_score = tentative_g_score + h_func(neighbor)
                heappush(open_set, (f_score, tentative_g_score, neighbor))

    return None  # No solution found

def print_state(state):
    for i in range(0, 9, 3):
        print(state[i:i+3])
    print()

if __name__ == '__main__':
    # Example start state (scrambled)
    start = (1, 2, 3,
             4, 5, 0,
             7, 8, 6)

    print("Solving with Misplaced Tiles heuristic:")
    path = a_star(start, heuristic='misplaced')
    if path:
        print(f"Number of moves: {len(path) - 1}")
        for step in path:
            print_state(step)
    else:
        print("No solution found.")

    print("Solving with Manhattan Distance heuristic:")
    path = a_star(start, heuristic='manhattan')
    if path:
        print(f"Number of moves: {len(path) - 1}")
        for step in path:
            print_state(step)
    else:
        print("No solution found.")
