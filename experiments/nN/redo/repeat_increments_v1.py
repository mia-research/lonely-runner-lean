"""The extra R each repeat adds.  In each relay, a REPEAT is a setting by a runner that has already set in that relay.
Record R = 8 d_min t at each repeat's setting instant (the start of its move) and at the relay's end; the increments
between successive repeats (bound -> 1st repeat, 1st -> 2nd, ...).  Do they shrink?  Exact.  Sets: exhaustive readings
<= 24 (relays with a repeat), the wide random sample, and the longest relays found (hard_cases_v1)."""
import itertools, random, re
from fractions import Fraction as F
from math import floor
from collections import Counter
from multiprocessing import Pool
from arrangement_lib import nd

E8 = F(1, 8)

def repeat_Rs(ds):
    m = min(ds); t = F(1, 8 * m); seen = set(); Rs = []
    while True:
        way = [d for d in ds if nd(d * t) < E8]
        if not way: return Rs, 8 * m * t
        ex = {d: (F(floor(d * t - E8) + 1) + E8) / d for d in way}
        s = max(ex, key=lambda x: ex[x])
        if s in seen: Rs.append(8 * m * t)
        seen.add(s); t = ex[s]

def summary(ds):
    Rs, Rend = repeat_Rs(ds)
    if not Rs: return None
    pts = [F(1)] + Rs
    inc = [pts[i + 1] - pts[i] for i in range(len(pts) - 1)]
    shrink = all(inc[i + 1] <= inc[i] for i in range(len(inc) - 1))
    return len(Rs), shrink, [float(x) for x in inc], float(Rend)

def exh(first):
    out = []
    for rest in itertools.combinations(range(first + 1, 25), 6):
        r = summary(list((first,) + rest))
        if r: out.append(r)
    return out

def wide(seed):
    rnd = random.Random(seed); out = []
    for _ in range(2500):
        m = rnd.randint(1, 20); T = sorted({m} | set(rnd.sample(range(m + 1, 2001), 6)))
        if len(T) == 7:
            r = summary(T)
            if r: out.append(r)
    return out

def report(name, rows):
    n = len(rows)
    nrep = Counter(min(r[0], 8) for r in rows)
    multi = [r for r in rows if r[0] >= 2]
    print(f"{name}: relays with a repeat {n}; number of repeats {sorted(nrep.items())}")
    if multi:
        print(f"  with >= 2 repeats: {len(multi)}; increments shrink along the relay in {sum(r[1] for r in multi)}")
        first = [r[2][0] for r in multi]; second = [r[2][1] for r in multi]
        print(f"  first increment (bound -> 1st repeat): max {max(first):.3f}; second (1st -> 2nd): max {max(second):.3f}; "
              f"second < first in {sum(1 for r in multi if r[2][1] < r[2][0])}")
        allinc = Counter()
        for r in multi:
            for i, x in enumerate(r[2][:6]): allinc[i] = max(allinc[i], x)
        print(f"  largest increment by repeat index: {[(i + 1, round(v, 3)) for i, v in sorted(allinc.items())]}")

if __name__ == '__main__':
    with Pool() as pool:
        E = [x for p in pool.map(exh, range(1, 19)) for x in p]
        W = [x for p in pool.map(wide, range(16)) for x in p]
    report("exhaustive, readings <= 24", E)
    report("wide sample", W)
    H = []
    for line in open('hard_cases_v1.out'):
        mm = re.search(r'V (\[[^\]]*\])', line)
        if mm:
            V = eval(mm.group(1)); r = summary(sorted(v - V[0] for v in V[1:]))
            if r: H.append(r)
    report("longest relays (hard_cases_v1)", H)
    for r in H[:5]: print(f"    increments {[round(x, 3) for x in r[2]]}; end R {r[3]:.3f}")
