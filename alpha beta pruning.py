import math

# Alpha-Beta Pruning function
def alpha_beta(node, depth, maximizingPlayer, values, alpha=-math.inf, beta=math.inf):
    """
    node: current node index in the values array
    depth: current depth
    maximizingPlayer: True if MAX node, False if MIN node
    values: list of leaf node values (full binary tree)
    alpha, beta: pruning parameters
    """

    # If leaf node reached
    if depth == max_depth:
        return values[node]

    if maximizingPlayer:
        max_eval = -math.inf
        for i in range(2):  # two children for binary tree
            child_index = node * 2 + i
            eval = alpha_beta(child_index, depth + 1, False, values, alpha, beta)
            max_eval = max(max_eval, eval)
            alpha = max(alpha, eval)
            if beta <= alpha:
                break  # prune
        return max_eval
    else:  # Minimizing player
        min_eval = math.inf
        for i in range(2):
            child_index = node * 2 + i
            eval = alpha_beta(child_index, depth + 1, True, values, alpha, beta)
            min_eval = min(min_eval, eval)
            beta = min(beta, eval)
            if beta <= alpha:
                break  # prune
        return min_eval


# -------------------------------
# Example Usage
# -------------------------------

# Leaf node values (binary tree, left to right)
values = [3, 5, 6, 9, 1, 2, 0, -1]

# Calculate maximum depth from number of leaves (binary tree)
max_depth = int(math.log2(len(values)))

# Run alpha-beta starting from root (index 0)
optimal_value = alpha_beta(0, 0, True, values)

print("Leaf values:", values)
print("Optimal value (MAX player):", optimal_value)
