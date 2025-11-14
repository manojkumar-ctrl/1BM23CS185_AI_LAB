import heapq
from itertools import count
from copy import deepcopy

GOAL = [
    [1, 2, 3],
    [8, 0, 4],
    [7, 6, 5]
]

def misplaced(puzzle):
    count = 0
    for i in range(3):
        for j in range(3):
            if puzzle[i][j] != 0 and puzzle[i][j] != GOAL[i][j]:
                count += 1
    return count

def get_blank_position(puzzle):
    for i in range(3):
        for j in range(3):
            if puzzle[i][j] == 0:
                return i, j

def get_neighbors(puzzle):
    x, y = get_blank_position(puzzle)
    moves = [(-1, 0, 'U'), (1, 0, 'D'), (0, -1, 'L'), (0, 1, 'R')]
    neighbors = []

    for dx, dy, move in moves:
        nx, ny = x + dx, y + dy
        if 0 <= nx < 3 and 0 <= ny < 3:
            new_puzzle = deepcopy(puzzle)
            new_puzzle[x][y], new_puzzle[nx][ny] = new_puzzle[nx][ny], new_puzzle[x][y]
            neighbors.append((new_puzzle, move))

    return neighbors

def print_matrix(matrix):
    for row in matrix:
        print(" ".join(str(cell) for cell in row))
    print()

def print_with_heuristic(matrix, g):
    h = misplaced(matrix)
    f = g + h
    print_matrix(matrix)
    print(f"h = {h}, g = {g}, f = {f}")
    return f

class Node:
    def __init__(self, state, depth, parent=None, move=None):
        self.state = state
        self.depth = depth
        self.h = misplaced(state)
        self.f = self.h + self.depth
        self.parent = parent
        self.move = move  # Move made to get here (L, R, U, D)

def reconstruct_path(node):
    path = []
    current = node
    while current.parent is not None:
        path.append(current.move)
        current = current.parent
    path.reverse()
    return path

def print_space_tree(start_state):
    counter = count()
    open_heap = []
    start_node = Node(start_state, 0)
    heapq.heappush(open_heap, (start_node.f, next(counter), start_node))
    visited = set()

    while open_heap:
        _, _, current = heapq.heappop(open_heap)
        state_key = tuple(tuple(row) for row in current.state)
        if state_key in visited:
            continue
        visited.add(state_key)

        print("Current Node:")
        print_with_heuristic(current.state, current.depth)
        print("-" * 30)
        if current.state == GOAL:
            print("🎯 Goal reached!")
            path = reconstruct_path(current)
            print("Path to goal:", " -> ".join(path))
            return

        children = []
        for neighbor, move in get_neighbors(current.state):
            key = tuple(tuple(row) for row in neighbor)
            if key not in visited:
                child_node = Node(neighbor, current.depth + 1, current, move)
                children.append(child_node)

        if not children:
            print("No more children.\n")
            continue

        print("Children:")
        for child in children:
            print_with_heuristic(child.state, child.depth)
            print()

        print("=" * 30)
        next_node = min(children, key=lambda n: n.f)
        heapq.heappush(open_heap, (next_node.f, next(counter), next_node))


start_state = [
    [2, 8, 3],
    [1, 6, 4],
    [7, 0, 5]
]

print_space_tree(start_state)
