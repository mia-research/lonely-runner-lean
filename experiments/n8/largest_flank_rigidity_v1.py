"""Route A: is a shadowing cover of the largest flank RIGID, and does exists_clear_step force rationality?

Flank e, threshold 1/8. Opening k sits at t = (k + 1/8)/e; a difference d with ratio rho = d/e is in the
way there iff circDist(rho*(k + 1/8)) < 1/8. Shadowing = every opening blocked by someone.

(1) Verify the A=0 cover: do {1,3,4,5,7}/8 block every opening of the flank at 8?
(2) Coverage budget: how many residues does one rational ratio a/c block, out of c? (the arc is 1/4 of
    the circle, so ~c/4 - the question is how tight the total is.)
(3) The essential-ratio lemma, empirically: along a residue class left to ONE ratio, an irrational ratio
    always has a clear opening (exists_clear_step), so it cannot be essential.
(4) How special is the eighth pattern: search 5-subsets of ratios with denominator dividing c that shadow.
"""
from fractions import Fraction as F
from itertools import combinations
import random
TH = F(1, 8)
def cd(x):
    f = x % 1
    return min(f, 1 - f)
def blocks(rho, k):
    return cd(rho * (k + TH)) < TH
print("(1) the A=0 cover at the largest flank (e = 8): ratios m/8, m in {1,3,4,5,7}")
pat = [F(m, 8) for m in (1, 3, 4, 5, 7)]
allk = True
for k in range(8):                      # period 8: (m/8)*8 = m is an integer
    who = [str(r) for r in pat if blocks(r, k)]
    print(f"    k={k}: {'blocked by ' + ','.join(who) if who else 'FREE'}")
    if not who: allk = False
print(f"    -> shadows every opening: {allk}")
print()
print("(2) coverage budget: residues blocked by a single ratio a/c, out of c")
for c in (2, 3, 4, 5, 6, 7, 8, 12, 16):
    tot = []
    for a in range(1, c + 1):
        if F(a, c).denominator != c: continue
        tot.append(sum(1 for k in range(c) if blocks(F(a, c), k)))
    if tot:
        print(f"    c={c:2}: blocked residues per ratio {sorted(set(tot))}  (c/4 = {c/4:.2f})")
print()
print("(3) essential-ratio lemma: an irrational ratio cannot hold a residue class alone")
rng = random.Random(3)
import math
bad = 0
for _ in range(300):
    rho = rng.uniform(0.01, 0.99)
    if abs(rho - round(rho)) < 1e-12: continue
    L = rng.choice([2, 3, 4, 6, 8]); r = rng.randrange(L)
    # does rho block EVERY k = r + L*j ?  (it must, to be essential on that class)
    holds = all(min((rho * (r + L * j + 0.125)) % 1, 1 - (rho * (r + L * j + 0.125)) % 1) < 0.125
                for j in range(4000))
    if holds: bad += 1
print(f"    irrational ratios that blocked a whole class over 4000 openings: {bad} of 300")
print("    (exists_clear_step proves this is 0 for every non-integer rho*L; the search agrees)")
print()
print("(4) which 5-subsets of ratios with denominator dividing c shadow the flank?")
for c in (8, 12, 16):
    cands = [F(a, c) for a in range(1, c) if True]
    cands = sorted(set(cands))
    found = []
    for sub in combinations(cands, 5):
        if all(any(blocks(r, k) for r in sub) for k in range(c)):
            found.append(sub)
    print(f"    c={c:2}: {len(found)} shadowing 5-subsets of the {len(cands)} ratios a/{c}")
    if found and c == 8:
        for s in found: print(f"           {[str(x) for x in s]}")
    elif found:
        norm = set()
        for s in found:
            norm.add(tuple(sorted(str(x) for x in s)))
        ex = sorted(norm)[:4]
        for s in ex: print(f"           e.g. {list(s)}")
