import random

# Function to calculate the number of attacking pairs (heuristic)
def calculate_cost(state):
    cost = 0
    n = len(state)
    for i in range(n):
        for j in range(i + 1, n):
            # Same column or same diagonal
            if state[i] == state[j] or abs(state[i] - state[j]) == abs(i - j):
                cost += 1
    return cost

# Generate a random initial state
def random_state(n):
    return [random.randint(0, n - 1) for _ in range(n)]

# Generate all neighbors (each possible move for one queen)
def get_neighbors(state):
    neighbors = []
    n = len(state)
    for i in range(n):
        for j in range(n):
            if state[i] != j:
                neighbor = state.copy()
                neighbor[i] = j
                neighbors.append(neighbor)
    return neighbors

# Hill Climbing algorithm
def hill_climbing(n):
    current = random_state(n)
    current_cost = calculate_cost(current)
    step = 0

    print(f"Initial State: {current}, Cost = {current_cost}")

    while True:
        neighbors = get_neighbors(current)
        neighbor_costs = [calculate_cost(neighbor) for neighbor in neighbors]

        # Find the neighbor with the lowest cost
        min_cost = min(neighbor_costs)
        best_neighbors = [neighbors[i] for i in range(len(neighbors)) if neighbor_costs[i] == min_cost]
        next_state = random.choice(best_neighbors)
       
        print(f"Step {step}: Current = {current}, Cost = {current_cost}")
        print(f" -> Best Neighbor = {next_state}, Cost = {min_cost}\n")
        step += 1

        # If no better neighbor found, stop
        if min_cost >= current_cost:
            print("Reached a local optimum.")
            return current, current_cost
       
        current = next_state
        current_cost = min_cost

# Run for 4-Queens
solution, cost = hill_climbing(4)

print("\nFinal Solution:")
print(f"State: {solution}, Cost = {cost}")

# Print the board visually
def print_board(state):
    n = len(state)
    for i in range(n):
        row = ""
        for j in range(n):
            row += "Q " if state[i] == j else ". "
        print(row)
    print()

print("Final Board:")
print_board(solution)
