"""E153 v2 (protected run): six readings G (least = 1), from a start A in [1, AMAX], lonely inside
A.([1,7] u [9,15] u ... ) -- how many of a slow runner's blocks does the worst start need?  Exact.
Protections: progress file six_blocks_v2.progress (one line per finished chunk, early positives flagged 'NEEDS>2'),
checkpoint six_blocks_v2.ckpt (json of finished chunks; rerun resumes), positive control first (a late band shape's
fast group from its own start must need the 2nd block; the run aborts if it does not)."""
import itertools, json, os, random, sys
from fractions import Fraction as F
from multiprocessing import Pool
sys.path.insert(0, '../band_cert_v1'); from core import clear_set
AMAX = F(12); MB = 4; RMAX = int(AMAX * (8 * (MB - 1) + 7)) + 2
PROG = 'six_blocks_v2.progress'; CKPT = 'six_blocks_v2.ckpt'
def lonely_set(G):
    s = sorted(F(x) / min(G) for x in G)
    return clear_set(s, F(1), F(RMAX))
def blocks_needed(L, A):
    for m in range(MB):
        lo, hi = A * (8 * m + 1), A * (8 * m + 7)
        if any(a <= hi and b >= lo for a, b in L): return m + 1
    return MB + 1
def worst(G, Amin=F(1)):
    L = lonely_set(G); cands = {Amin}
    for a, b in L:
        for e in (a, b):
            for j in range(MB):
                for q in (8 * j + 1, 8 * j + 7):
                    A = e / q
                    if Amin <= A <= AMAX: cands.add(A)
    cands = sorted(cands); pts = cands + [(x + y) / 2 for x, y in zip(cands, cands[1:])]
    w = (0, None)
    for A in pts:
        n = blocks_needed(L, A)
        if n > w[0]: w = (n, A)
    return w
def control():
    # a late band shape from the same walk as E121/E128 (seed 41), verified by the cascade to land past R = 7; its six
    # fast readings from their own start A = g1 / d_min must then need the slow runner's second block.
    from math import floor
    E8 = F(1, 8)
    def nd(x):
        x = x % 1
        return min(x, 1 - x)
    def casc(T):
        t = F(1, 8)
        while True:
            way = [d for d in T if nd(d * t) < E8]
            if not way: return 8 * t
            t = max((F(floor(d * t - E8) + 1) + E8) / d for d in way)
    D1 = 27720; rng = random.Random(41)
    T = [int(round(x * D1)) for x in (1, 2.3509, 3.2412, 4.1886, 5.2223, 5.7871, 7.4378)]
    for step in range(3000):
        U = list(T); i = rng.randrange(1, 7); U[i] += rng.randrange(-500, 501); U = sorted(set(U))
        if len(U) < 7 or U[0] != D1 or not (7 * D1 < U[-1] < 9 * D1): continue
        s = [F(d, D1) for d in U]
        if clear_set(s, F(1), F(7)): continue
        T = U
        R = casc(s)
        if R > 7:
            G = s[1:]; return blocks_needed(lonely_set(G), G[0] / s[0]), [float(x) for x in s], float(R)
    return None, None, None
def chunk(first):
    best = (0, None, None); flagged = []
    for rest in itertools.combinations(range(first + 1, 21), 5):
        G = (first,) + rest; n, A = worst(G)
        if n > 2: flagged.append((G, str(A), n))
        if n > best[0]: best = (n, G, str(A))
    with open(PROG, 'a') as f:
        f.write("chunk %d done: most blocks %d at %s A=%s%s\n" % (first, best[0], best[1], best[2], (' NEEDS>2 ' + str(flagged[:5])) if flagged else ''))
    return first, best, flagged
if __name__ == '__main__':
    c, shape, R = control()
    with open(PROG, 'a') as f: f.write("positive control: late band shape %s (cascade R* = %s); its six from their own start need %s blocks (expected 2)\n" % (shape, R, c))
    if c != 2: print("CONTROL FAILED", c, shape, R); sys.exit(1)
    done = json.load(open(CKPT)) if os.path.exists(CKPT) else {}
    todo = [a for a in range(1, 16) if str(a) not in done]
    with Pool(8) as p:
        for first, best, flagged in p.imap_unordered(chunk, todo):
            done[str(first)] = [best[0], best[1], best[2], [list(x[:1]) + list(x[1:]) for x in flagged[:20]]]
            json.dump(done, open(CKPT, 'w'))
    tot = max(done.values(), key=lambda v: v[0])
    print("6-sets of readings <= 20, starts A in [1, 12]: most blocks needed = %d at %s A = %s" % (tot[0], tot[1], tot[2]))
    print("sets needing more than 2 blocks:", sum(len(v[3]) for v in done.values()), [v[3][:3] for v in done.values() if v[3]][:5])
    with open(PROG, 'a') as f: f.write("ALLDONE\n")
