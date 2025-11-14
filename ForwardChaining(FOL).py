GPT-5 minimal forward chaining for your PPT problem

def parse_fact(line):
    name = line.split("(")[0]
    args = line[line.index("(")+1: line.index(")")].split(",")
    args = [a.strip() for a in args]
    return (name, tuple(args))


def forward_chain(facts, rules, goal):
    # facts is a set of (pred, args)
    changed = True
    while changed:
        changed = False
        for rule in rules:
            conds, conclusion = rule
            # can we satisfy all conds?
            if all(c in facts for c in conds):
                if conclusion not in facts:
                    facts.add(conclusion)
                    changed = True
    return (goal in facts)


# ========== main I/O ==========

print("enter facts one per line. blank line to stop")
facts = set()
while True:
    x = input()
    if x.strip()=="":
        break
    facts.add(parse_fact(x.strip()))

print("enter rules one per line:  IF a & b & c THEN d")
print("blank line to stop")
rules=[]
while True:
    x=input()
    if x.strip()=="":
        break
    left,right = x.split("THEN")
    conds = [parse_fact(c.strip()) for c in left.replace("IF","").split("&")]
    conclusion = parse_fact(right.strip())
    rules.append((conds,conclusion))

goal = parse_fact(input("enter goal fact to check: ").strip())

answer = forward_chain(facts, rules, goal)

print("RESULT:", answer)
