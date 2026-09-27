"""How many residue patterns mod 8 can eight whole-number speeds have (occupancy of the 8 slots, multiplicities summing
to 8), up to rotation (adding a constant to every speed) and reflection (reversing the speeds), and also up to
multiplying by a unit of Z/8 (rescaling by an odd factor permutes the slots)?  Grouped by the number of empty slots."""
from itertools import combinations_with_replacement
from collections import Counter, defaultdict
def canon(occ, units=False):
    forms = []
    mults = (1, 3, 5, 7) if units else (1,)
    for u in mults:
        o = [0] * 8
        for i, c in enumerate(occ): o[(u * i) % 8] += c
        for sh in range(8):
            r = tuple(o[(i + sh) % 8] for i in range(8))
            forms += [r, tuple(reversed(r))]
    return min(forms)
pats = set()
for combo in combinations_with_replacement(range(8), 8):
    occ = [0] * 8
    for x in combo: occ[x] += 1
    pats.add(tuple(occ))
A = {canon(p) for p in pats}; B = {canon(p, True) for p in pats}
byempty = Counter(sum(1 for c in p if c == 0) for p in A)
byemptyB = Counter(sum(1 for c in p if c == 0) for p in B)
print(f"occupancy patterns: {len(pats)}; up to rotation+mirror: {len(A)}; also up to odd rescaling: {len(B)}")
print("up to rotation+mirror, by number of empty slots:", dict(sorted(byempty.items())))
print("also up to odd rescaling, by number of empty slots:", dict(sorted(byemptyB.items())))
print("one empty slot (one doubled), up to rotation+mirror+odd rescaling:", sorted(p for p in B if sum(1 for c in p if c == 0) == 1))
