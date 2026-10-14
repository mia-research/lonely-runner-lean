"""Fine-shape generator (denominator 2520): uniform, log-uniform, and late walks.
Deterministic seeds.  Output: fine_shapes.txt, one set per line (n0..n6), tag."""
import random, sys
from core import *
D = 2520
SEED = (1, 2.3509, 3.2412, 4.1886, 5.2223, 5.7871, 7.4378)  # given; only rounded to ints below

def late(ns):
    L = landing(ns)
    return L is not None and L[0] >= 9, L

def rnd_uniform(rng):
    while True:
        n6 = rng.randint(7 * D + 1, 9 * D)
        mids = sorted(rng.sample(range(D + 1, n6), 5))
        return (D, *mids, n6)

def rnd_log(rng):
    import math
    while True:
        n6 = rng.randint(7 * D + 1, 9 * D)
        # log-uniform mids, exact ints after rounding (generation only, no decision)
        mids = sorted(set(int(round(D * math.exp(rng.random() * math.log(n6 / D)))) for _ in range(5)))
        if len(mids) == 5 and mids[0] > D and mids[-1] < n6:
            return (D, *mids, n6)

def walk(rng, start, steps, tag, out, want=2000, maxstep=40):
    cur = start; got = 0; tries = 0
    seen = set()
    while got < want and tries < 400000:
        tries += 1
        nxt = list(cur)
        for _ in range(rng.randint(1, 3)):
            i = rng.randint(1, 6)
            nxt[i] += rng.randint(-maxstep, maxstep)
        nxt = tuple(nxt)
        if not is_band(nxt):
            continue
        lt, L = late(nxt)
        if lt:
            cur = nxt
            if nxt not in seen:
                seen.add(nxt); out.append((nxt, tag)); got += 1
    return got, tries

if __name__ == "__main__":
    rng = random.Random(20260927)
    out = []
    for _ in range(3000):
        out.append((rnd_uniform(rng), 'unif'))
    for _ in range(2000):
        out.append((rnd_log(rng), 'log'))
    # late seed: search the neighbourhood of the rounded seed for a late start
    base = tuple(int(round(x * D)) for x in SEED)
    start = None
    best = None
    r2 = random.Random(7)
    for t in range(200000):
        c = tuple([D] + [base[i] + r2.randint(-30, 30) for i in range(1, 7)])
        if is_band(c) and late(c)[0]:
            start = c; break
    print("rounded seed", base, "late?", late(base), "start", start, flush=True)
    if start:
        g, tr = walk(rng, start, 0, 'late', out, want=3000)
        print("late walk collected", g, "tries", tr, flush=True)
    # further late seeds found by search_late.py (exact descent), walked the same way
    extra = [(2520, 8361, 10674, 12044, 13306, 14783, 18969), (2520, 8891, 11171, 12653, 13911, 15740, 19865),
             (2520, 9325, 13063, 15580, 17785, 20492, 22227), (2520, 7033, 9586, 12306, 15762, 17607, 22555),
             (2520, 6648, 8917, 10790, 12076, 14979, 18575)]
    for j, st in enumerate(extra):
        assert is_band(st) and late(st)[0]
        g, tr = walk(rng, st, 0, 'late%d' % (j + 2), out, want=600)
        print("late seed", j + 2, "collected", g, "tries", tr, flush=True)
    with open('fine_shapes.txt', 'w') as f:
        for ns, tag in out:
            f.write(' '.join(map(str, ns)) + ' ' + tag + '\n')
    print("total", len(out))
