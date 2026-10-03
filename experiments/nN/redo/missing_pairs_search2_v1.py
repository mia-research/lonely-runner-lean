import random, sys
from fractions import Fraction as F
from collections import Counter
exec(open('outcome_classes_v2.py').read().split('\nif __name__ ==')[0])
def A(l): return [F(x) for x in l]
seeds = {
 'open1': [A(['1','2546089/1000000','3436441/1000000','528523/125000','4662687/1000000','2973493/500000','93273/12500']),
           A(['1','507097/200000','3305773/1000000','1029181/250000','575027/125000','2825221/500000','1449347/200000'])],
 'close1': [A(['1','1377881/500000','3592651/1000000','2196343/500000','4937377/1000000','3071937/500000','3855013/500000']),
            A(['1','2890719/1000000','63287/15625','14738/3125','6491/1250','6557929/1000000','7430499/1000000']),
            A(['1','1472713/500000','3856339/1000000','4790229/1000000','522397/100000','3241063/500000','1018659/125000'])]}
TARGET = {(1,6),(1,7),(2,1),(5,1)}; rnd = random.Random(int(sys.argv[1])); N = int(sys.argv[2]); found = {}; seen = Counter()
def q(x): return F(round(x*10**7), 10**7)
for t in range(N):
    fam = rnd.choice(list(seeds)); base = rnd.choice(seeds[fam]); sc = rnd.choice((1e-4,1e-3,3e-3,1e-2,3e-2,1e-1))
    rho = [F(1)] + [q(float(x)*(1+rnd.uniform(-sc,sc))) for x in base[1:]]
    if rnd.random() < 0.3:
        y = rnd.randrange(1,7); rho[y] = q(float(rho[y])*(1+rnd.uniform(-0.3,0.3)))
    rho = sorted(rho)
    if len(set(rho)) < 7 or rho[0] != 1: continue
    o = outcome(rho)
    if not o['opener']: continue
    k = (o['opener'][0], o['closer'][0]); seen[k] += 1
    if k in TARGET and k not in found and o['width'] > 0: found[k] = ([str(x) for x in rho], o['path'][-4:], float(o['R']), o['closer'], float(o['width']), o['nmoves'])
print("evaluations", N, "pairs seen", len(seen), "found", sorted(found))
for k, v in sorted(found.items()): print(k, v)
print("still not found:", sorted(TARGET - set(found)))
