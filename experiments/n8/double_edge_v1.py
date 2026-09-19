"""The AP's coincidence points are DOUBLY tight (reading u at +1, reading 8-u at -1).
EdgeWitness gives only one tight constraint.  Does every profile have a DOUBLE-edge witness?

If so the candidate family shrinks from 12 residue classes to their pairwise intersections (CRT).
"""
from itertools import combinations

def I(b): return (-(-(b-1)//8), (7*b-1)//8)
def ok(q, m, bs): return all(I(b)[0] <= q % b <= I(b)[1] for b in bs + [m])
def tightness(q, m, bs):
    return sum(1 for b in bs + [m] if q % b in I(b))

tot = 0; no1 = 0; no2 = 0; no3 = 0
best = {}
ex2 = []
for m in range(24, 240):
    ds = [d for d in range(2, m) if m % d == 0]
    if len(ds) < 5: continue
    for c in combinations(ds, 5):
        bs = sorted(c)
        S = [q for q in range(m) if ok(q, m, bs)]
        if not S: continue
        tot += 1
        mx = max(tightness(q, m, bs) for q in S)
        best[mx] = best.get(mx, 0) + 1
        if mx < 1: no1 += 1
        if mx < 2:
            no2 += 1
            if len(ex2) < 5: ex2.append((m, bs, S))
        if mx < 3: no3 += 1
print(f"divisor-closed profiles with a witness, m < 240 : {tot:,}\n")
print(f"  max tightness achieved over the witness set: {dict(sorted(best.items()))}")
print(f"\n  profiles with NO 1-tight witness : {no1:,}   (EdgeWitness says 0)")
print(f"  profiles with NO 2-tight witness : {no2:,}   ({100*no2/tot:.3f}%)")
print(f"  profiles with NO 3-tight witness : {no3:,}   ({100*no3/tot:.3f}%)")
if ex2:
    print(f"\n  profiles where no witness is doubly tight:")
    for m, bs, S in ex2[:5]:
        print(f"     m={m} b={bs}  witnesses={S[:8]}{'...' if len(S)>8 else ''}")
