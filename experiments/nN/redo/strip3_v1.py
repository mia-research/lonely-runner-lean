# Three deformed runners of the AP.  Strip structure in three dimensions.
#  n_band = number of deformed runners with reading in the slot band at R = 1 (rho mod 8 in (-1, 1), i.e. rho in (7,9) or (15,17) ...).
#  n_band = 0: the landing is R = 1.   n_band = 1: compare with the one-runner catalogue (the same runner moved, the others at the AP).
import sys, random
from fractions import Fraction as F
from collections import Counter
sys.argv = [sys.argv[0]]
exec(open('ap_single_mover_map_v1.py').read().split('\nif __name__ ==')[0])
rnd = random.Random(321)
base = [F(x) for x in range(1, 8)]
def inband(r): m = r % 8; return m < 1 or m > 7
def q(x): return F(round(x * 1000), 1000)
cnt = Counter(); mism = []
for trial in range(2400):
    movers = sorted(rnd.sample(range(1, 7), 3))                      # not the smallest runner
    rho = list(base)
    for i in movers: rho[i] = q(rnd.uniform(1.05, 17.5))
    if len(set(rho)) < 7: continue
    nb = sum(1 for i in movers if inband(rho[i]))
    L = lonely_set(rho); R = L[0][0]
    if nb == 0:
        cnt[("0 in band", "landing = 1" if R == 1 else "landing != 1")] += 1
    elif nb == 1:
        a = next(i for i in movers if inband(rho[i]))
        single = list(base); single[a] = rho[a]; R1 = lonely_set(single)[0][0]
        cnt[("1 in band", "= one-runner catalogue" if R == R1 else ("> catalogue" if R > R1 else "< catalogue"))] += 1
        if R != R1 and len(mism) < 8: mism.append((a + 1, float(rho[a]), [(i + 1, float(rho[i])) for i in movers if i != a], float(R1), float(R)))
    else:
        cnt[("%d in band" % nb, "landing > 1" if R > 1 else "landing = 1")] += 1
for k, v in sorted(cnt.items()): print("  %-10s %-26s %d" % (k[0], k[1], v))
print("examples where the one-runner catalogue value is not the landing (band runner, its reading; others (index, reading); catalogue R*; actual R*):")
for m in mism: print("   ", m)
