import itertools

# Define all possible truth values
values = [False, True]

# Define propositional variables
variables = ['A', 'B', 'C']

# Generate all possible combinations of A, B, C
print(f"{'A':<6}{'B':<6}{'C':<6}{'A∨C':<8}{'B∨¬C':<8}{'KB':<8}{'α=A∨B':<8}")
print("-" * 50)

entails = True  # Will check if KB entails α

for A, B, C in itertools.product(values, repeat=3):
    # Compute expressions
    A_or_C = A or C
    B_or_notC = B or (not C)
    KB = A_or_C and B_or_notC
    alpha = A or B

    print(f"{str(A):<6}{str(B):<6}{str(C):<6}{str(A_or_C):<8}{str(B_or_notC):<8}{str(KB):<8}{str(alpha):<8}")

    # Check entailment condition: whenever KB is True, α must be True
    if KB and not alpha:
        entails = False

# Final result
print("\nConclusion:")
if entails:
    print("KB entails α (KB ⊨ α)")
else:
    print("KB does NOT entail α (KB ⊭ α)")
