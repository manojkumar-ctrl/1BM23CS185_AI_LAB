# ======================================================
#  FULLY WORKING FIRST-ORDER LOGIC CNF CONVERTER
#  No SymPy. No errors. Supports P(x), Q(y), R(x,y)
# ======================================================

import itertools

counter = itertools.count()

def new_const():
    return f"c{next(counter)}"

def new_func(args):
    name = f"f{next(counter)}"
    arg_str = ",".join(args)
    return f"{name}({arg_str})"


# Data structure: expressions are Python tuples
# ------------------------------------------------------
# ("not", A)
# ("and", A, B)
# ("or",  A, B)
# ("forall", var, body)
# ("exists", var, body)
# ("pred", "P", ["x"])  --> P(x)


def pred(name, *args):
    return ("pred", name, list(args))


# ------------------------------------------------------
# Remove → and ↔
# ------------------------------------------------------
def remove_implications(expr):
    t = expr[0]

    if t == "forall" or t == "exists":
        return (t, expr[1], remove_implications(expr[2]))

    if t in ("and", "or"):
        return (t, remove_implications(expr[1]), remove_implications(expr[2]))

    if t == "implies":
        P = remove_implications(expr[1])
        Q = remove_implications(expr[2])
        return ("or", ("not", P), Q)

    if t == "iff":
        P = remove_implications(expr[1])
        Q = remove_implications(expr[2])
        return ("and",
                ("or", ("not", P), Q),
                ("or", ("not", Q), P))

    if t == "not":
        return ("not", remove_implications(expr[1]))

    return expr


# ------------------------------------------------------
# NNF Conversion
# ------------------------------------------------------
def nnf(expr):
    t = expr[0]

    if t == "not":
        inner = expr[1]
        if inner[0] == "not":
            return nnf(inner[1])
        if inner[0] == "and":
            return ("or", nnf(("not", inner[1])), nnf(("not", inner[2])))
        if inner[0] == "or":
            return ("and", nnf(("not", inner[1])), nnf(("not", inner[2])))
        if inner[0] == "forall":
            v = inner[1]
            return ("exists", v, nnf(("not", inner[2])))
        if inner[0] == "exists":
            v = inner[1]
            return ("forall", v, nnf(("not", inner[2])))
        return ("not", nnf(inner))

    elif t == "and" or t == "or":
        return (t, nnf(expr[1]), nnf(expr[2]))

    elif t == "forall" or t == "exists":
        return (t, expr[1], nnf(expr[2]))

    return expr


# ------------------------------------------------------
# Skolemization
# ------------------------------------------------------
def skolemize(expr, universals=None):
    if universals is None:
        universals = []

    t = expr[0]

    if t == "forall":
        return ("forall", expr[1], skolemize(expr[2], universals + [expr[1]]))

    if t == "exists":
        v = expr[1]
        if universals:
            sk = new_func(universals)
        else:
            sk = new_const()
        return skolemize(subst(expr[2], v, sk), universals)

    if t == "and" or t == "or":
        return (t, skolemize(expr[1], universals),
                    skolemize(expr[2], universals))

    if t == "not":
        return ("not", skolemize(expr[1], universals))

    return expr


# helper substitution
def subst(expr, var, value):
    t = expr[0]

    if t == "pred":
        new_args = [value if a == var else a for a in expr[2]]
        return ("pred", expr[1], new_args)

    if t in ("not",):
        return ("not", subst(expr[1], var, value))

    if t in ("and", "or"):
        return (t, subst(expr[1], var, value), subst(expr[2], var, value))

    if t in ("forall", "exists"):
        return (t, expr[1], subst(expr[2], var, value))

    return expr


# ------------------------------------------------------
# Drop universal quantifiers
# ------------------------------------------------------
def drop_forall(expr):
    if expr[0] == "forall":
        return drop_forall(expr[2])
    return expr


# ------------------------------------------------------
# Distribute OR over AND
# ------------------------------------------------------
def distribute(expr):
    t = expr[0]

    if t == "and":
        return ("and", distribute(expr[1]), distribute(expr[2]))

    if t == "or":
        A = distribute(expr[1])
        B = distribute(expr[2])

        if A[0] == "and":
            return ("and",
                    distribute(("or", A[1], B)),
                    distribute(("or", A[2], B)))

        if B[0] == "and":
            return ("and",
                    distribute(("or", A, B[1])),
                    distribute(("or", A, B[2])))

        return ("or", A, B)

    return expr


# ------------------------------------------------------
# Pretty print
# ------------------------------------------------------
def show(expr):
    t = expr[0]

    if t == "pred":
        name = expr[1]
        args = ",".join(expr[2])
        return f"{name}({args})"

    if t == "not":
        return f"¬{show(expr[1])}"

    if t == "and":
        return f"({show(expr[1])} ∧ {show(expr[2])})"

    if t == "or":
        return f"({show(expr[1])} ∨ {show(expr[2])})"

    if t == "forall":
        return f"∀{expr[1]} {show(expr[2])}"

    if t == "exists":
        return f"∃{expr[1]} {show(expr[2])}"

    return str(expr)


# ------------------------------------------------------
# FULL CNF PIPELINE
# ------------------------------------------------------
def to_cnf(expr):
    print("Original:", show(expr))
    expr = remove_implications(expr)
    print("After removing →, ↔:", show(expr))
    expr = nnf(expr)
    print("NNF:", show(expr))
    expr = skolemize(expr)
    print("Skolemized:", show(expr))
    expr = drop_forall(expr)
    print("After dropping ∀:", show(expr))
    expr = distribute(expr)
    print("CNF:", show(expr))
    return expr


# ======================================================
# EXAMPLE: ∀x (P(x) → ∃y (Q(y) ∧ R(x,y)))
# ======================================================

expr = (
    "forall", "x",
    ("implies",
        pred("P", "x"),
        ("exists", "y",
            ("and",
                pred("Q", "y"),
                pred("R", "x", "y")
            )
         )
    )
)

print("\n========= CNF OUTPUT =========\n")
to_cnf(expr)
