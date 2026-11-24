"""Exact three-level frontier and unrestricted depth-five separation for C5(Maj3)."""
from itertools import combinations_with_replacement, product

def target(mask):
    majorities = [sum(mask >> (i + j) & 1 for j in (0, 5, 10)) >= 2 for i in range(5)]
    return any(majorities[i] and majorities[(i+1)%5] for i in range(5))

def extremal_rows():
    positives, negatives = [], []
    for x in range(1<<15):
        if target(x):
            if all(not target(x^(1<<i)) for i in range(15) if x>>i&1):
                positives.append(x)
        elif all(target(x|(1<<i)) for i in range(15) if not x>>i&1):
            negatives.append(x)
    assert (len(positives),len(negatives)) == (45,135)
    return negatives + positives

def step(signatures):
    result = set()
    for a,b in combinations_with_replacement(signatures,2):
        result.add(a|b)
        result.add(a&b)
    return result

def generators():
    permutations = [list(range(15)) for _ in range(12)]
    for i in range(15):
        group, copy = i%5, i//5
        permutations[0][i] = (group+1)%5 + 5*copy
        permutations[1][i] = (-group)%5 + 5*copy
        if copy < 2:
            permutations[2+2*group][i] = group + 5*(1-copy)
        if copy > 0:
            permutations[3+2*group][i] = group + 5*(3-copy)
    return permutations

def action_tables(rows):
    index = {row:i for i,row in enumerate(rows)}
    tables = []
    for permutation in generators():
        action = [index[sum(1<<permutation[i] for i in range(15) if x>>i&1)] for x in rows]
        assert sorted(action[:135]) == list(range(135))
        assert sorted(action[135:]) == list(range(135,180))
        table = []
        for k in range(0,len(action),8):
            table.append([sum(1 << j for i,j in enumerate(action[k:k+8]) if b>>i&1)
                          for b in range(256)])
        tables.append(table)
    return tables

def apply_action(sig,table):
    output = 0
    for byte in table:
        output |= byte[sig&255]
        sig >>= 8
    return output

def orbit_representatives(signatures,tables):
    todo = set(signatures)
    result = []
    while todo:
        first = todo.pop()
        result.append(first)
        stack = [first]
        while stack:
            member = stack.pop()
            for g in tables:
                image = apply_action(member,g)
                if image in todo:
                    todo.remove(image)
                    stack.append(image)
    return result

def frontier(pairs):
    return sorted(point for point in pairs if not any(
        point != other and point[0] <= other[0] and point[1] <= other[1]
        for other in pairs))

def relaxed_step(previous):
    candidates = set()
    for (p,b),(q,c) in product(previous,repeat=2):
        candidates.add((min(45,p+q), min(b,c)))
        candidates.add((min(p,q),min(135,b+c)))
    return frontier(candidates)

def main():
    rows = extremal_rows()
    primaries = {sum((x>>i&1)<<j for j,x in enumerate(rows)) for i in range(15)}
    depth2 = step(step(primaries))
    reps = orbit_representatives(depth2,action_tables(rows))
    print(f'Depth 2: {len(depth2)} signatures, {len(reps)} symmetry orbits')
    mask = (1<<135)-1
    def score(x):
        return (x>>135).bit_count(), 135-(x&mask).bit_count()
    counts = set()
    for a in reps:
        for b in depth2:
            counts.add(score(a&b))
            counts.add(score(a|b))
    upper = frontier(counts)
    print('Depth 3 exact:',upper)
    for depth in (4,5,6):
        upper = relaxed_step(upper)
        print(f'Depth {depth} upper:',upper)
        if depth == 5:
            assert upper == [(36,135),(44,120),(45,108)]

if __name__ == '__main__':
    main()
