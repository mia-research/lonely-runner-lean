# Readings in (1/m)Z, m odd: the blocking pattern is symmetric about 4m (R <-> 8m-R).  Exact: (a) verify the symmetry of the blocking
# status on random exact points; (b) maximise the landing over such arrangements by exact hill-climb on the numerators; compare with 4m.
import sys, random
from fractions import Fraction as F
exec(open('outcome_classes_v2.py').read().split('\nif __name__ ==')[0])
def blocked(rho, R):
    for r in rho:
        p = (R * r) % 8
        if min(p, 8 - p) < 1: return True
    return False
rnd = random.Random(int(sys.argv[2]) if len(sys.argv) > 2 else 1); m = int(sys.argv[1]); NMAX = int(sys.argv[3]) if len(sys.argv) > 3 else 25
def arr(nums): return [F(1)] + [F(n, m) for n in nums]
# (a) symmetry
bad = 0; tot = 0
for t in range(300):
    nums = sorted(rnd.sample(range(m + 1, NMAX * m), 6)); rho = arr(nums)
    for k in range(40):
        R = F(rnd.randint(1, 8 * m * 50), 50)
        if 8 * m - R >= 0: tot += 1; bad += blocked(rho, R) != blocked(rho, 8 * m - R)
print(f"m={m}: symmetry of blocking status about {4*m}: {bad} violations in {tot} exact checks")
# (b) hill-climb on the landing
best = F(0); bestarr = None
for restart in range(int(sys.argv[4]) if len(sys.argv) > 4 else 30):
    nums = sorted(rnd.sample(range(m + 1, NMAX * m), 6)); cur = outcome(arr(nums))['R']
    for it in range(400):
        n2 = list(nums); i = rnd.randrange(6); n2[i] = max(m + 1, min(NMAX * m, n2[i] + rnd.choice((-3, -2, -1, 1, 2, 3, rnd.randint(-m, m)))))
        if len(set(n2)) < 6: continue
        n2.sort(); r = outcome(arr(n2))['R']
        if r >= cur: nums, cur = n2, r
    if cur > best: best, bestarr = cur, list(nums)
print(f"m={m}: best landing found {float(best):.4f} (= {best}) at readings 1, " + ", ".join(str(F(n, m)) for n in bestarr) + f"; bound 4m = {4*m}; ratio {float(best)/(4*m):.3f}")
