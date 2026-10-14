"""Part 1 is false: (1/2,1/2,1/5) shadows, 256 configurations.  The right object is which RESIDUES
each mover blocks.  A mover (w, f=p/q) is bad on a subset of Z/q; shadowing = the three cover.

Enumerate over all denominators up to Q and characterise."""
from fractions import Fraction as F
from itertools import product, combinations_with_replacement
from collections import Counter

def badset(w, f):
    """residues k mod q on which the mover is in the way"""
    q = f.denominator; rho = F(w) + f
    out = set()
    for k in range(q):
        x = k*f + rho/8
        if abs(x - F(round(float(x)))) < F(1,8): out.add(k)
    return out, q

def shadowed(cfg):
    from math import lcm
    L = lcm(*[f.denominator for _, f in cfg])
    bs = [badset(w, f) for w, f in cfg]
    return all(any(k % q in B for B, q in bs) for k in range(L))

Q = 8
FR = [F(p, q) for q in range(2, Q+1) for p in range(1, q) if F(p,q).denominator == q]
print(f"fractional parts with denominator <= {Q}: {len(FR)}")
tot = 0; sh = Counter(); shex = []
for fs in combinations_with_replacement(FR, 3):
    for ws in product(range(8), repeat=3):
        cfg = list(zip(ws, fs)); tot += 1
        if shadowed(cfg):
            sh[tuple(sorted(str(f) for f in fs))] += 1
            if len(shex) < 4: shex.append(cfg)
print(f"configurations tested: {tot:,}")
print(f"shadowing: {sum(sh.values()):,}  in {len(sh)} fractional-part multisets\n")
print("  multisets that can shadow (top 14):")
for k, v in sh.most_common(14): print(f"     {k}  x{v}")
print()
# the real characterisation: how many movers block a FULL residue class of some modulus?
print("  KEY: a mover blocks a full class mod q iff its bad set is all of Z/q.")
full = [(w, f) for f in FR for w in range(8) if badset(w, f)[0] == set(range(f.denominator))]
print(f"     movers blocking ALL residues: {len(full)}   {[(w,str(f)) for w,f in full][:6]}")
half = [(w, f) for f in FR for w in range(8) if f.denominator == 2 and badset(w, f)[0]]
print(f"     half-movers blocking one parity: {len(half)}  -> two on opposite parities cover Z")
