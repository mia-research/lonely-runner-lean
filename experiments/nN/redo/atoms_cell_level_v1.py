# Are the R* atoms properties of the cells or of the member list?  Exact: for members at an atom, jitter within the same cell
# (accept only if the exact path equals the cell's path) and read R* and the opener's reading.
import pickle, random, sys
from fractions import Fraction as F
from collections import Counter
exec(open('outcome_classes_v2.py').read().split('\nif __name__ ==')[0])
T = pickle.load(open('terminals5_J2.pkl', 'rb')); got = pickle.load(open('cell_members_J2.pkl', 'rb'))
ATOMS = [F(49,17), F(49,15), F(41,15), F(11,5), F(41,17), F(25,7)]
rnd = random.Random(7); res = {a: [] for a in ATOMS}; cells_at = {a: [] for a in ATOMS}
for i, rho in got:
    o = outcome(rho)
    if o['R'] in res: cells_at[o['R']].append((i, rho, o))
for a in ATOMS:
    C = cells_at[a]; print(f"atom R*={a} ({float(a):.4f}): members {len(C)}; distinct cells {len({i for i,_,_ in C})}; opener readings {Counter(str(rho[o['opener'][0]-1]) for i,rho,o in C).most_common(4)}")
    # per atom: sample 150 cells, jitter 40 times each, collect distinct R* of accepted jittered members
    spread = []; moved = 0; tried = 0
    for i, rho, o in rnd.sample(C, min(150, len(C))):
        p = T[i][0]; Rs = {o['R']}
        for t in range(40):
            sc = rnd.choice((1e-9, 1e-7, 1e-5, 1e-3))
            v = [F(1)] + [x + F(rnd.uniform(-1, 1) * sc) for x in rho[1:]]
            if sorted(v) != v or len(set(v)) < 7: continue
            oo = outcome(v)
            if oo['path'] == tuple(p): Rs.add(oo['R'])
        tried += 1; moved += (len(Rs) > 1); spread.append(len(Rs))
    print(f"   cells tested {tried}: R* takes more than one exact value inside the same cell in {moved}")
