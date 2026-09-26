"""Follow the chain of nudges (the cascade's relay) from the bound.  Each move i goes from t_i to t_(i+1) (the latest
exit of the readings in the slot): the scale factor lambda_i = t_(i+1)/t_i, and each reading moves forward by
d (t_(i+1) - t_i).  At each step the readings newly in the slot are classed edge (clear before, moved < 3/4 over the
edge 7/8), wrap (moved >= 3/4) or back (was a setter earlier in the chain).  Per chain: length; whether the lambda_i
decrease; whether a setter repeats; whether a wrap occurs.  Exact.  Sets: exhaustive readings <= 24, and the wide
random sample (d_min 1..20, readings to 2000)."""
import itertools, random, sys
from fractions import Fraction as F
from math import floor
from collections import Counter
from multiprocessing import Pool
from arrangement_lib import nd

E8 = F(1, 8)

def chain(T):
    t = F(1, 8 * T[0]); lams = []; setters = []; kinds = Counter(); pushed = set()
    while True:
        way = [d for d in T if nd(d * t) < E8]
        if not way: return lams, setters, kinds
        ex = {d: (F(floor(d * t - E8) + 1) + E8) / d for d in way}
        s = max(ex, key=lambda x: ex[x]); t1 = ex[s]
        for d in T:
            if d not in way and nd(d * t1) < E8:
                kinds['back' if d in setters else ('edge' if d * (t1 - t) < F(3, 4) else 'wrap')] += 1
        lams.append(t1 / t); setters.append(s); t = t1

def summarise(T):
    lams, setters, kinds = chain(T)
    if not lams: return None
    dec = all(lams[i + 1] <= lams[i] for i in range(len(lams) - 1))
    rep = len(setters) != len(set(setters))
    return len(lams), dec, rep, kinds['wrap'] > 0, kinds['back'] > 0, float(max(lams)), float(lams[-1])

def exh(first):
    c = Counter()
    for rest in itertools.combinations(range(first + 1, 25), 6):
        r = summarise((first,) + rest)
        if r: c[(min(r[0], 6), r[1], r[2], r[3], r[4])] += 1
    return c

def wide(seed):
    rnd = random.Random(seed); c = Counter()
    for _ in range(2500):
        m = rnd.randint(1, 20); T = sorted({m} | set(rnd.sample(range(m + 1, 2001), 6)))
        if len(T) != 7: continue
        r = summarise(tuple(T))
        if r: c[(min(r[0], 6), r[1], r[2], r[3], r[4])] += 1
    return c

def report(name, c):
    n = sum(c.values())
    print(f"{name}: relays {n}")
    print(f"  length (capped 6): {sorted(Counter({k[0]: 0 for k in c}).items()) and sorted(Counter(k for k in [] ).items())}", end='')
    L = Counter();
    for k, v in c.items(): L[k[0]] += v
    print(f"{sorted(L.items())}")
    for label, idx in (('the lambdas decrease along the chain', 1), ('a setter repeats', 2), ('a wrap occurs', 3), ('a setter comes back', 4)):
        print(f"  {label}: {sum(v for k, v in c.items() if k[idx])}")
    print(f"  among chains of length >= 2: lambdas decrease {sum(v for k, v in c.items() if k[0] >= 2 and k[1])} of {sum(v for k, v in c.items() if k[0] >= 2)}")

if __name__ == '__main__':
    with Pool() as pool:
        ce = Counter(); [ce.update(x) for x in pool.map(exh, range(1, 19))]
        cw = Counter(); [cw.update(x) for x in pool.map(wide, range(16))]
    report("exhaustive, readings <= 24", ce)
    report("wide, d_min 1..20, readings to 2000", cw)
