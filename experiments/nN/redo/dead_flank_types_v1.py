"""E397 (2026-10-05), dead_flank_types_v1: the dead flanks of whole-number 7-sets as covering systems, and their minimal covers.
Owner: "Ok try and prove it" (the classification of every dead flank, and that not all seven flanks can be dead).
SETUP (exact, whole numbers; derived by hand): flank e (a reading) is DEAD iff every opening k >= 0 has a walker j in the way:
(8k+1) x_j mod 8e outside [e, 7e].  With g = gcd(x_j, e), q = e/g, p = x_j/g, walker j blocks exactly the openings k in a union of
residue classes mod q (one interval of length q/4 of m = p k mod q).  So a flank is dead iff its walkers' class sets cover Z/e.
RECORDED: over every 7-subset of [1, N] with gcd 1: the number of dead flanks per set (histogram); the sets with all seven dead
(none expected); for each dead flank the minimal covering subsets of walkers, as sorted tuples of (q, p mod 8, class count);
the number of distinct minimal-cover types and the most frequent ones.
Exact (integers).
"""
import itertools, math, sys
from collections import Counter
from multiprocessing import Pool

N = int(sys.argv[1]) if len(sys.argv) > 1 else 24
MASK = {}
for e in range(1, N + 1):
    for x in range(1, N + 1):
        if x == e:
            continue
        m = 0
        for k in range(e):
            r = ((8 * k + 1) * x) % (8 * e)
            if r < e or r > 7 * e:
                m |= 1 << k
        MASK[(e, x)] = m

def info(S):
    dead = []
    types = []
    for e in S:
        full = (1 << e) - 1
        w = [x for x in S if x != e]
        ms = [MASK[(e, x)] for x in w]
        orall = 0
        for m in ms: orall |= m
        if orall != full:
            continue
        dead.append(e)
        best = None
        for size in range(1, 7):
            found = []
            for sub in itertools.combinations(range(6), size):
                o = 0
                for i in sub: o |= ms[i]
                if o == full:
                    found.append(sub)
            if found:
                best = (size, found); break
        size, found = best
        for sub in found:
            t = []
            for i in sub:
                x = w[i]; g = math.gcd(x, e); q = e // g; p = x // g
                t.append((q, p % 8, bin(ms[i]).count("1") * q // e))
            types.append((e, tuple(sorted(t))))
    return len(dead), types

def work(chunk):
    hist = Counter(); typ = Counter(); alls = []
    for S in chunk:
        g = 0
        for x in S: g = math.gcd(g, x)
        if g != 1: continue
        n, ts = info(S)
        hist[n] += 1
        if n == 7: alls.append(S)
        for e, t in ts: typ[t] += 1
    return hist, typ, alls

if __name__ == '__main__':
    sets = list(itertools.combinations(range(1, N + 1), 7))
    chunks = [sets[i:i + 4000] for i in range(0, len(sets), 4000)]
    hist = Counter(); typ = Counter(); alls = []
    with Pool(4) as pool:
        for h, t, a in pool.map(work, chunks):
            hist.update(h); typ.update(t); alls += a
    o = open('dead_flank_types_v1.out', 'w'); o.write(__doc__ + "\n")
    o.write("N = %d: sets with gcd 1: %d; dead flanks per set: %s; sets with all seven dead: %d\n" % (N, sum(hist.values()), dict(sorted(hist.items())), len(alls)))
    o.write("distinct minimal-cover types (over all dead flanks): %d\n" % len(typ))
    for t, c in typ.most_common(40):
        o.write("  %6d  %s\n" % (c, t))
    o.close(); print(open('dead_flank_types_v1.out').read()[len(__doc__):][:4500])
