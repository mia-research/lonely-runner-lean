"""The two-patterns statement, properly: is there always a witness lying on BOTH patterns?
  +1 pattern at modulus b :  q mod b = L(b)
  -1 pattern at modulus b :  q mod b = U(b)
(a single modulus with L=U supplies both -- the degenerate coincidence)

Distinguish from 'two tight constraints', which is FALSE (1.615% have none).
"""
from itertools import combinations

def I(b): return (-(-(b-1)//8), (7*b-1)//8)
def ok(q, m, bs): return all(I(b)[0] <= q % b <= I(b)[1] for b in bs + [m])
def onL(q, m, bs): return any(q % b == I(b)[0] for b in bs + [m])
def onU(q, m, bs): return any(q % b == I(b)[1] for b in bs + [m])

tot = 0; noboth = 0; nodistinct = 0; ex = []
for m in range(24, 240):
    ds = [d for d in range(2, m) if m % d == 0]
    if len(ds) < 5: continue
    for c in combinations(ds, 5):
        bs = sorted(c)
        S = [q for q in range(m) if ok(q, m, bs)]
        if not S: continue
        tot += 1
        if not any(onL(q, m, bs) and onU(q, m, bs) for q in S):
            noboth += 1
            if len(ex) < 4: ex.append((m, bs, S))
        # stricter: two DISTINCT moduli, one at L and one at U
        strict = False
        for q in S:
            Ls = {b for b in bs+[m] if q % b == I(b)[0]}
            Us = {b for b in bs+[m] if q % b == I(b)[1]}
            if Ls and Us and (Ls | Us) != (Ls & Us): strict = True; break
            if len(Ls | Us) >= 2: strict = True; break
        if not strict: nodistinct += 1
print(f"divisor-closed profiles with a witness, m < 240 : {tot:,}\n")
print(f"  NO witness lying on both patterns          : {noboth:,}  ({100*noboth/tot:.3f}%)")
print(f"  NO witness on both via DISTINCT moduli     : {nodistinct:,}  ({100*nodistinct/tot:.3f}%)")
for m, bs, S in ex: print(f"     e.g. m={m} b={bs} S={S[:6]}")
