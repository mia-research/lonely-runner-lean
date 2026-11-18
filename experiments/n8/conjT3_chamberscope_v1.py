# conjT3_chamberscope_v1 -- scope the chamber count per skeleton.
# Signature = the labeled zone-merge structure: for each reading r (idx 0..4 = rho2..rho6)
# the list of zone indices k with Z(rho_r,k) meeting [1,7], PLUS the merge pattern of
# overlapping zones (which labeled zones overlap/touch, in sorted edge order).
# Two tuples in the same skeleton with the same signature have the same K6 components
# up to the exact rational values, and the same certificate combinatorics.
# Chamber proxy: distinct signatures over a dense exact sample. [scope only]
import random, itertools, sys
from fractions import Fraction as F
from taillemma_lib_v1 import zones_of

CELLS = ['P','S1','G1','S2','E']
CELLBOUNDS = {'P': (F(10,10),F(7)), 'S1': (F(7),F(9)), 'G1': (F(9),F(15)), 'S2': (F(15),F(17)), 'E': (F(17),F(17))}
def cell_of(x):
    if x <= F(7): return 'P'
    if x < F(9): return 'S1'
    if x <= F(15): return 'G1'
    if x < F(17): return 'S2'
    return 'E'
skels = []
def gen(pref):
    if len(pref)==5:
        if pref[-1]!='P': skels.append(tuple(pref))
        return
    for c in CELLS:
        if pref and CELLS.index(c)<CELls_index(pref[-1]) if False else (pref and CELLS.index(c) < CELLS.index(pref[-1])): continue
        gen(pref+[c])
gen([])

def signature(rho_small):
    # labeled zone list meeting [1,7]
    lz = []
    for idx, r in enumerate(rho_small):
        for a,b,j in zones_of(r):
            a2,b2 = max(a,F(1)), min(b,F(7))
            if a2 < b2: lz.append((a2,b2,idx,j))
    lz.sort()
    # merge pattern: walk sorted labeled zones, record overlap classes
    sig = []
    cur_end = None; cur = []
    for a,b,idx,j in lz:
        if cur_end is None or a > cur_end:
            if cur: sig.append(tuple(sorted(cur)))
            cur = [(idx,j)]; cur_end = b
        else:
            cur.append((idx,j)); cur_end = max(cur_end,b)
    if cur: sig.append(tuple(sorted(cur)))
    return tuple(sig)

random.seed(7)
def sample_point(cells):
    # vertices-ish + interior random rationals with small denominators
    if random.random() < 0.3:
        # near-corner: pick endpoints of cells
        pt = []
        for c in cells:
            lo,hi = CELLBOUNDS[c]
            pt.append(random.choice([lo,hi]) if lo!=hi else lo)
        return tuple(pt)
    pt = []
    for c in cells:
        lo,hi = CELLBOUNDS[c]
        if lo==hi: pt.append(lo)
        else:
            pt.append(F(random.randint(int(lo*40), int(hi*40)-1), 40))
    return tuple(pt)

total_sigs = 0; per_skel = []
for s in skels:
    sigs = set()
    N = 400
    for _ in range(N):
        rho = sample_point(s)
        # enforce nondecreasing rho2..rho6 (skeleton cells are nondecreasing in cell order; values may violate)
        if any(rho[i] > rho[i+1] for i in range(4)): continue
        sigs.add(signature(rho))
    per_skel.append((len(sigs), s))
    total_sigs += len(sigs)

per_skel.sort(reverse=True)
print("skeletons:", len(skels), "| total distinct signatures:", total_sigs)
print("max per skeleton:", per_skel[:5])
print("median:", sorted(x[0] for x in per_skel)[len(per_skel)//2])
print("mean: %.1f" % (total_sigs/len(skels)))
