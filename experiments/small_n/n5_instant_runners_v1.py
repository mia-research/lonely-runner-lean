"""n=5: for arrangements with R_final > 3 (found by annealing, exact rationals, unrounded), the runners in the way at
the own-AP instants R = 1, 2, 3: is there always a choice of three different runners, one per instant?  Records each
runner's AP index residue (a mod 5) and drift n'*e at the instant it covers, and how many instants each runner covers."""
from fractions import Fraction as F
import math, random, collections
from multiprocessing import Pool
def near(x): return math.floor(x + F(1, 2))
def cascade(s):
    R = F(1)
    while True:
        best = R; who = False
        for sx in s:
            v = sx * R; N = near(v / 5)
            if abs(v - 5 * N) < 1:
                c = F(5 * N + 1) / sx
                if c > best: best, who = c, True
        if not who: return R
        R = best
def inway(s, R): return [i for i, sx in enumerate(s) if abs(sx * R - 5 * near(sx * R / 5)) < 1]
def job(seed):
    rng = random.Random(seed); found = []
    for restart in range(30):
        cur = sorted(1 + F(rng.randint(0, 12000), 1000) for _ in range(3)); cs = cascade(cur)
        for it in range(1500):
            sc = [F(1, 10), F(1, 100), F(1, 1000)][it * 3 // 1500]
            new = sorted(max(F(1), x + sc * F(rng.randint(-100, 100), 100)) for x in cur)
            if len(set(new)) < 3: continue
            ns = cascade(new)
            if ns >= cs or rng.random() < 0.02: cur, cs = new, ns
            if cs > 3: found.append((cs, list(cur)))
    return found
if __name__ == '__main__':
    with Pool() as p: allf = [x for r in p.map(job, range(32)) for x in r]
    uniq = {}
    for R, s in allf: uniq[tuple(s)] = R
    print('arrangements with R > 3:', len(uniq))
    sdr_fail = 0; multi = collections.Counter(); cover = collections.Counter(); maxR = F(0)
    for s, R in uniq.items():
        maxR = max(maxR, R)
        sets = [inway(list(s), F(k)) for k in (1, 2, 3)]
        # system of distinct representatives
        ok = any(len({x, y, z}) == 3 for x in sets[0] for y in sets[1] for z in sets[2])
        if not ok: sdr_fail += 1
        for k, st in zip((1, 2, 3), sets):
            for i in st:
                a = near(s[i]); e = s[i] - a
                cover[(k, a % 5, 'e>0' if e > 0 else 'e<0' if e < 0 else 'e=0')] += 1
        cnt = collections.Counter(i for st in sets for i in st)
        multi[max(cnt.values())] += 1
    print('max R among them', float(maxR))
    print('arrangements with no choice of three different runners for instants 1, 2, 3:', sdr_fail)
    print('largest number of instants covered by one runner (count of arrangements):', dict(multi))
    print('in-way at instant k by (k, index mod 5, deviation sign):')
    for key, c in sorted(cover.items()): print('   ', key, c)
