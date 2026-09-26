"""Owner: perturb the repeaters with the cascade and see why they repeat.  Relays (readings <= 24) where a setter sets
twice; move ONLY the repeater's reading by e in [-1, 1], exact steps of 1/64 (the other readings fixed).  Per case: the
interval of e (containing 0) over which the repeater still sets twice; R along it; at each end of the interval, why the
repeat stops -- 'isolated before it returns' (the relay ends before the repeater's next zone), or 'not in the way when
reached' (the relay reaches that zone but the repeater is not the latest exit / not in the slot).  Exact."""
import itertools, random
from fractions import Fraction as F
from math import floor
from collections import Counter
from multiprocessing import Pool
from arrangement_lib import nd

E8 = F(1, 8)

def relay(ds):
    t = F(1, 8 * min(ds)); setters = []
    while True:
        way = [d for d in ds if nd(d * t) < E8]
        if not way: return setters, t
        ex = {d: (F(floor(d * t - E8) + 1) + E8) / d for d in way}
        s = max(ex, key=lambda x: ex[x]); setters.append((s, t, ex[s])); t = ex[s]

def study(T):
    setters, t = relay(list(T))
    c = Counter(x[0] for x in setters); rep = next(s for s, n in c.items() if n > 1)
    i = T.index(rep); R0 = 8 * T[0] * t
    res = {}
    for j in range(-64, 65):
        e = F(j, 64); ds = list(T); ds[i] = rep + e
        if len(set(ds)) < 7 or min(ds) <= 0: continue
        st, tt = relay(ds)
        n = sum(1 for s, _, _ in st if s == ds[i])
        res[j] = (n >= 2, 8 * min(ds) * tt, st, tt, ds[i])
    # interval of j around 0 where the repeat persists
    lo = 0
    while lo - 1 in res and res[lo - 1][0]: lo -= 1
    hi = 0
    while hi + 1 in res and res[hi + 1][0]: hi += 1
    why = []
    for jj in (lo - 1, hi + 1):
        if jj not in res: why.append('edge of scan'); continue
        rep_now, R, st, tt, dr = res[jj]
        first = next(x for x in st if x[0] == dr) if any(x[0] == dr for x in st) else None
        if first is None: why.append('never sets')
        else:
            # after its first setting (exit at first[2]), the next entry of the repeater
            nxt = (floor(dr * first[2] + E8) + 1 - E8) / dr
            why.append('isolated before it returns' if tt <= nxt else 'not in the way when reached')
    return (hi - lo + 1) / 64, why, float(R0), float(max(v[1] for k, v in res.items() if lo <= k <= hi)), float(min(v[1] for v in res.values() if not v[0]) if any(not v[0] for v in res.values()) else 0)

def picks():
    out = []
    for T in itertools.combinations(range(1, 25), 7):
        st, t = relay(list(T))
        if len(st) != len(set(s for s, _, _ in st)): out.append(T)
    return out

if __name__ == '__main__':
    P = picks(); random.Random(97).shuffle(P); P = P[:400]
    with Pool() as pool: res = pool.map(study, P)
    w = Counter(); why = Counter(); Rwith = []; Rwithout = []
    for width, wy, R0, Rmax, Rno in res:
        w[min(int(width * 8), 16)] += 1
        for x in wy: why[x] += 1
        Rwith.append(Rmax); Rwithout.append(Rno)
    print(f"repeat relays studied: {len(res)}")
    print(f"  width of the repeat interval in the repeater's reading (eighths of a unit, capped 16): {sorted(w.items())}")
    print(f"  why the repeat stops at the interval's ends: {dict(why)}")
    import statistics
    print(f"  R with the repeat: median {statistics.median(Rwith):.3f}, max {max(Rwith):.3f}; R once the repeat is gone (smallest seen): median {statistics.median(Rwithout):.3f}")
