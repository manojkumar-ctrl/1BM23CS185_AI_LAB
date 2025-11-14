import re

def is_variable(x):
    """Return True if x is a variable (starts with lowercase letter)."""
    return isinstance(x, str) and x and x[0].islower()

def is_constant(x):
    """Return True if x is a constant (starts with uppercase letter)."""
    return isinstance(x, str) and x and x[0].isupper()

def parse_term(term_str):
    """Parse a string like f(x, g(y)) into nested Python tuples."""
    term_str = term_str.strip()
    if '(' not in term_str:
        return term_str
    functor, args_str = term_str.split('(', 1)
    args_str = args_str[:-1]  # remove final ')'
    args = split_args(args_str)
    return (functor.strip(), [parse_term(arg) for arg in args])

def split_args(args_str):
    """Split arguments at commas, respecting nested parentheses."""
    args, depth, current = [], 0, ''
    for ch in args_str:
        if ch == ',' and depth == 0:
            args.append(current.strip())
            current = ''
        else:
            if ch == '(':
                depth += 1
            elif ch == ')':
                depth -= 1
            current += ch
    if current.strip():
        args.append(current.strip())
    return args

def occurs_check(var, x, subst):
    """Check if variable var occurs in x under current substitution."""
    if var == x:
        return True
    elif is_variable(x) and x in subst:
        return occurs_check(var, subst[x], subst)
    elif isinstance(x, tuple):
        functor, args = x
        return any(occurs_check(var, arg, subst) for arg in args)
    return False

def unify(x, y, subst=None):
    """Unify two terms x and y, returning a substitution dict or None."""
    if subst is None:
        subst = {}

    if x == y:
        return subst

    elif is_variable(x):
        return unify_var(x, y, subst)

    elif is_variable(y):
        return unify_var(y, x, subst)

    elif isinstance(x, tuple) and isinstance(y, tuple):
        fx, argsx = x
        fy, argsy = y
        if fx != fy or len(argsx) != len(argsy):
            return None
        for a, b in zip(argsx, argsy):
            subst = unify(apply_subst(a, subst), apply_subst(b, subst), subst)
            if subst is None:
                return None
        return subst

    else:
        return None

def unify_var(var, x, subst):
    """Handle variable unification."""
    if var in subst:
        return unify(subst[var], x, subst)
    elif is_variable(x) and x in subst:
        return unify(var, subst[x], subst)
    elif occurs_check(var, x, subst):
        return None
    else:
        subst[var] = x
        return subst

def apply_subst(term, subst):
    """Recursively apply a substitution to a term."""
    if is_variable(term):
        return apply_subst(subst[term], subst) if term in subst else term
    elif isinstance(term, tuple):
        f, args = term
        return (f, [apply_subst(a, subst) for a in args])
    else:
        return term


# --- Example Usage ---
if __name__ == "__main__":
    term1 = parse_term("f(x, g(y))")
    term2 = parse_term("f(A, g(B))")

    result = unify(term1, term2)
    if result:
        print("Unifier:", result)
    else:
        print("Failed to unify.")
