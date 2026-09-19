"""Claim: every divisor-closed profile has a witness q with q mod b in {L(b), U(b)} for some
modulus b among the six.  Verify exhaustively, and ask WHICH b supplies it."""
from itertools import combinations
from collections import Counter

def I(b): return (-(-(b-1)//8), (7*b-1)//8)
def ok(q, m, bs):
    return all(I(b)[0] <= q % b <= I(b)[1] for b in bs + [m])

def edge_witness(m, bs):
    """Search only the edge family; return (q, b, which_end) or None."""
    for b in bs + [m]:
        L, U = I(b)
        for e, lab in ((L, 'L'), (U, 'U')):
            q = e
            while q < m:
                if ok(q, m, bs): return q, b, lab
                q += b
    return None

tot = 0; miss = 0; who = Counter(); end = Counter(); rankc = Counter()
ex = []
for m in range(24, 320):
    ds = [d for d in range(2, m) if m % d == 0]
    if len(ds) < 5: continue
    for c in combinations(ds, 5):
        bs = sorted(c)
        if not any(q for q in range(m) if ok(q, m, bs)): continue
        tot += 1
        r = edge_witness(m, bs)
        if r is None:
            miss += 1
            if len(ex) < 4: ex.append((m, bs))
        else:
            q, b, lab = r
            who[b == m] += 1; end[lab] += 1
            allb = bs + [m]
            rankc[sorted(allb).index(b)] += 1
print(f"divisor-closed profiles with a witness, exhaustive m < 320 : {tot:,}")
print(f"  NO edge witness : {miss:,}   ({100*miss/tot:.4f}%)")
for e in ex: print("     ", e)
print(f"\n  supplied by b = m (the range modulus) : {who[True]:,}  ({100*who[True]/max(tot-miss,1):.2f}%)")
print(f"  supplied by a proper modulus          : {who[False]:,}")
print(f"  which end: L {end['L']:,}   U {end['U']:,}")
print(f"  rank of the supplying modulus (0 = smallest of the six): "
      + "  ".join(f"{k}:{100*v/max(tot-miss,1):.1f}%" for k,v in sorted(rankc.items())))
