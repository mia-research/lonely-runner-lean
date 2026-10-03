# Constructive search for the (opener rank, closer rank) pairs absent from the J=2 members and not excluded by the closer lemma.
import pickle, random, sys
from fractions import Fraction as F
from collections import Counter
exec(open('outcome_classes_v2.py').read().split('\nif __name__ ==')[0])
TARGET = {(1,2),(1,3),(1,6),(1,7),(2,1),(3,1),(4,1),(5,1),(7,1)}
got = pickle.load(open('cell_members_J2.pkl','rb')); rnd = random.Random(int(sys.argv[1]) if len(sys.argv)>1 else 1)
seeds = [r for i, r in got]
found = {}; seen = Counter(); N = int(sys.argv[2]) if len(sys.argv)>2 else 60000
def q(x): return F(round(x*10**6), 10**6)
for t in range(N):
    base = rnd.choice(seeds); sc = rnd.choice((1e-4,1e-3,1e-2,5e-2,0.2,0.5))
    mode = rnd.random()
    rho = [F(1)] + [q(float(x)*(1+rnd.uniform(-sc,sc))) for x in base[1:]]
    if mode < 0.2:  # re-draw 1-2 readings freely
        for y in rnd.sample(range(1,7), rnd.choice((1,2))): rho[y] = q(rnd.uniform(1.2, 17))
    rho = sorted(rho)
    if len(set(rho)) < 7 or rho[0] != 1: continue
    o = outcome(rho)
    if not o['opener']: continue
    k = (o['opener'][0], o['closer'][0]); seen[k] += 1
    if k in TARGET and k not in found and o['width'] > 0: found[k] = ([str(x) for x in rho], o['path'], float(o['R']), o['closer'], float(o['width']))
print("evaluations", N, "pairs seen", len(seen), "targets found", sorted(found))
for k, v in sorted(found.items()): print(k, v)
print("still not found:", sorted(TARGET - set(found)))
