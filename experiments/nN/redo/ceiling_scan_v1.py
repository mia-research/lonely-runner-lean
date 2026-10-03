# Exact line scans: for gate-crossing seeds, vary ONE reading over a range and record where the gate is crossed (landing > 7).
import pickle, random, sys
from fractions import Fraction as F
exec(open('outcome_classes_v2.py').read().split('\nif __name__ ==')[0])
seeds = list(pickle.load(open('stress_seeds_v1.pkl', 'rb')).keys())
rnd = random.Random(int(sys.argv[1])); NS = int(sys.argv[2]); step = F(1, int(sys.argv[3]))
# pick seeds with the largest rho_7 and rho_6 first (the ones nearest the claimed ceiling) plus random ones
seeds.sort(key=lambda r: -r[6]); pick = seeds[:NS // 2] + rnd.sample(seeds[NS // 2:], NS // 2)
res = {'r7': [], 'r6': [], 'r5': []}; best = {'r7': (F(0), None), 'r6': (F(0), None), 'r5': (F(0), None)}
for rho in pick:
    for name, y, top in (('r7', 6, F(40)), ('r6', 5, F(20)), ('r5', 4, F(14))):
        lo = rho[y - 1] + F(1, 10**6) if y > 1 else F(1)
        x = rho[y]; mx = F(0)
        # scan upward from the seed's own value; the neighbours must stay ordered, so for r6/r5 allow the higher readings to be re-sorted
        v = rho[y] - 4 * step
        while v <= top:
            if v > 1:
                r = sorted(rho[:y] + (v,) + rho[y + 1:]) if False else sorted([w for i, w in enumerate(rho) if i != y] + [v])
                if len(set(r)) == 7 and r[0] == 1:
                    o = outcome(r)
                    if o['R'] > 7:
                        # record the value of the SCANNED reading (not the sorted rank): the largest value of this reading at which the gate is crossed
                        if v > mx: mx = v
            v += step
        res[name].append(mx)
        if mx > best[name][0]: best[name] = (mx, rho)
for name in res:
    L = sorted(res[name]); print(name, "scanned seeds", len(L), "| largest value of the scanned reading at which the gate was crossed: %.4f" % float(L[-1]), "| median over seeds %.4f" % float(L[len(L)//2]), "| number of seeds crossing above 16.21: %d" % sum(1 for x in L if x > F(1621, 100)))
    print("   attaining arrangement:", [str(x) for x in best[name][1]])
