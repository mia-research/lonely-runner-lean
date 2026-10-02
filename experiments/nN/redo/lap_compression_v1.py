# Does adding a whole lap to a reading ever make the landing LATER?  For random arrangements A and a reading y with rho_y > 9 (so that rho_y - 8 > 1 and stays above d_min),
# compare R*(A) with R*(A') where A' has rho_y - 8.  Count cases R*(A) > R*(A') (+ tolerance), report the largest excess.
import sys, random, math
sys.argv = [sys.argv[0]]
exec(open('extremes_deep_v1.py').read().split('\nif __name__ ==')[0])
def land(rho):
    rho = sorted(rho); m = rho[0]; rho = [x / m for x in rho]; R, n = fpath(rho); return R, n
rnd = random.Random(331); tot = viol = 0; worst = (0, None); byfam = {}
def gen(kind):
    if kind == 0: return [1.0] + sorted(rnd.uniform(1.0, rnd.choice((12, 20, 40))) for _ in range(6))
    if kind == 1:                                   # deformed AP with some readings lapped
        r = [float(k) + rnd.uniform(-0.4, 0.8) * rnd.choice((0, 1)) + 8 * rnd.choice((0, 0, 1, 2)) * rnd.choice((0, 1)) for k in range(1, 8)]
        return sorted(max(1.0001, x) for x in r)
    if kind == 2:                                   # near-extremal family plus laps
        base = [1.0, 2.37, 3.15, 4.2, 5.22, 5.8, 7.45]; return [1.0] + sorted(b + rnd.uniform(-0.1, 0.1) + 8 * rnd.choice((0, 0, 1)) for b in base[1:])
for kind in (0, 1, 2):
    for _ in range(6000):
        A = gen(kind)
        if len(set(A)) < 7 or A[0] != 1.0: continue
        RA, nA = land(A)
        if nA >= 10**6: continue
        for y in range(1, 7):
            if A[y] > 9.0:
                B = list(A); B[y] -= 8.0
                if min(B) < 1.0 or len(set(B)) < 7: continue
                RB, nB = land(B)
                if nB >= 10**6: continue
                tot += 1; byfam.setdefault(kind, [0, 0]); byfam[kind][0] += 1
                if RA > RB + 1e-9:
                    viol += 1; byfam[kind][1] += 1
                    if RA - RB > worst[0]: worst = (RA - RB, (A, y, RA, RB))
print("pairs (A, A with one reading reduced by a whole lap):", tot, "; landing later in A than in A':", viol)
print("by family (pairs, A later):", byfam)
if worst[1]: A, y, RA, RB = worst[1]; print("largest excess %.4f: A = %s, reading index %d lowered by 8: R*(A) = %.4f, R*(A') = %.4f" % (worst[0], [round(x, 4) for x in A], y + 1, RA, RB))
