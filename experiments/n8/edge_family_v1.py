"""Witnesses hug interval EDGES.  Is every witness at an edge for SOME modulus?

Edge for modulus b:  q mod b = L(b)  or  q mod b = U(b),  where I(b) = [L,U].
If every witness is an edge point for some b, the witness set lies in a FINITE NAMED family:
    { q : q = L(b) or U(b)  (mod b) }  over the six moduli
-- which is a candidate family the extremal analysis never included.
"""
from itertools import combinations
from collections import Counter

def I(b): return (-(-(b-1)//8), (7*b-1)//8)
def sols(m, bs):
    c = [(b,)+I(b) for b in bs] + [(m,)+I(m)]
    return [q for q in range(m) if all(lo <= q % b <= hi for b,lo,hi in c)]

tot = 0; noedge = 0; cnt = Counter(); prof = 0
first_noedge = []
for m in range(24, 200):
    ds = [d for d in range(2, m) if m % d == 0]
    if len(ds) < 5: continue
    for c in combinations(ds, 5):
        bs = sorted(c); S = sols(m, bs)
        if not S: continue
        prof += 1
        anyedge = False
        for q in S:
            tot += 1
            e = sum(1 for b in bs+[m] if q % b in I(b))
            cnt[e] += 1
            if e == 0: noedge += 1
            else: anyedge = True
        if not anyedge and len(first_noedge) < 4:
            first_noedge.append((m, bs))
print(f"profiles {prof:,}   witnesses {tot:,}\n")
print("  number of moduli at which the witness sits exactly on an interval edge:")
for k in sorted(cnt):
    print(f"     {k} edges : {cnt[k]:>10,}  ({100*cnt[k]/tot:6.2f}%)")
print(f"\n  witnesses at NO edge at all : {noedge:,}  ({100*noedge/tot:.2f}%)")
print(f"  => is every witness an edge point for some modulus? {noedge == 0}")
if first_noedge:
    print("  profiles where NO witness is an edge point:")
    for e in first_noedge: print("     ", e)
else:
    print("  every profile has at least one edge witness.")
