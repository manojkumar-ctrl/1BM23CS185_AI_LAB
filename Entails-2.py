# Propositional Logic Truth Table Evaluation
# KB = { Q → P, P → ¬Q, Q ∨ R }

from itertools import product

# Helper functions for logical operations
def implies(a, b):
    return (not a) or b

def neg(a):
    return not a

# Generate all combinations of truth values for P, Q, R
print(f"{'P':^5}{'Q':^5}{'R':^5}{'Q→P':^8}{'P→¬Q':^8}{'Q∨R':^8}{'KB True?':^10}")
print("-" * 50)

models = [] # store models where KB is true

for P, Q, R in product([False, True], repeat=3):
    q_imp_p = implies(Q, P)
    p_imp_notq = implies(P, neg(Q))
    q_or_r = Q or R

    # Knowledge base is true if all three are true
    kb_true = q_imp_p and p_imp_notq and q_or_r

    if kb_true:
        models.append((P, Q, R))

    print(f"{P!s:^5}{Q!s:^5}{R!s:^5}{q_imp_p!s:^8}{p_imp_notq!s:^8}{q_or_r!s:^8}{kb_true!s:^10}")

print("\nModels where KB is True:")
for m in models:
    print(f"P={m[0]}, Q={m[1]}, R={m[2]}")

# Check entailments
entails_R = all(R for (P, Q, R) in models)
entails_R_imp_P = all((not R) or P for (P, Q, R) in models)
entails_Q_imp_notR = all((not Q) or (not R) for (P, Q, R) in models)

print("\nEntailment Results:")
print(f"KB ⊨ R ? {' Yes' if entails_R else ' No'}")
print(f"KB ⊨ (R → P) ? {' Yes' if entails_R_imp_P else ' No'}")
print(f"KB ⊨ (Q → ¬R) ? {' Yes' if entails_Q_imp_notR else 'No'}")
