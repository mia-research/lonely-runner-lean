import pickle, random, sys
from fractions import Fraction as F
from collections import Counter
exec(open('outcome_classes_v2.py').read().split('\nif __name__ ==')[0])
T = pickle.load(open('terminals5_J2.pkl','rb')); rnd = random.Random(int(sys.argv[1])); N = int(sys.argv[2])
def q(x): return F(round(x*10**8), 10**8)
cells_s = [t for t in T if t[0] and t[0][-1][0] in (2,5) and t[2] >= 6.9]
cells_1 = [t for t in T if t[0] and t[0][-1][0] == 1]
print("cells for closer-1 search (opener rank 2 or 5, Rhi>=6.9):", len(cells_s), " opener-1 cells:", len(cells_1))
found = {}; seen = Counter(); TARGET = {(1,6),(1,7),(2,1),(5,1)}
for t in range(N):
    if rnd.random() < 0.6 and cells_s:
        p, lo, hi, rng, w = rnd.choice(cells_s); s, j = p[-1]
        R = 7 - rnd.choice((1e-4,1e-3,3e-3,1e-2,3e-2))*rnd.random()
        rho = [q(rnd.uniform(*rng[y])) if y not in (0, s-1) else (F(1) if y == 0 else q((8*j+1)/R)) for y in range(7)]
    else:
        p, lo, hi, rng, w = rnd.choice(cells_1)
        rho = [F(1)] + [q(rnd.uniform(*rng[y])) for y in range(1,7)]
    rho = sorted(rho)
    if len(set(rho)) < 7 or rho[0] != 1: continue
    o = outcome(rho)
    if not o['opener']: continue
    k = (o['opener'][0], o['closer'][0]); seen[k] += 1
    if k in TARGET and k not in found and o['width'] > 0: found[k] = ([str(x) for x in rho], o['path'][-3:], float(o['R']), o['closer'], float(o['width']), o['nmoves'])
print("evaluations", N, "pairs seen", len(seen), "found", sorted(found))
for k, v in sorted(found.items()): print(k, v)
print("still not found:", sorted(TARGET - set(found)))
