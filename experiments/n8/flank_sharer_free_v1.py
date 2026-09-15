"""Hypothesis from the one-free-flank cases: a runner that is an exact slot-sharer of some flank (d_s a multiple of n·d_e) has its
own flank unshadowed. Test over every n-subset (order 8: [1,20]; order 5: [1,30]), every runner, every such sharer pair.
Also: in runners with at most two free flanks, which differences the free flanks are (largest difference? a sharer?)."""
import itertools, sys
from collections import Counter
from multiprocessing import Pool
from flank_near_extreme_v1 import blocks_all
def job(args):
    n, v = args
    pairs = held = 0; fails = []; freekind = Counter()
    for i in range(n):
        ds = [abs(x - v[i]) for x in v if x != v[i]]
        flanks = sorted(set(ds))
        freeset = {e for e in flanks if not blocks_all(e, [d for d in ds if d != e], n)}
        sharers = {s for s in flanks for e in flanks if s != e and s % (n * e) == 0}
        for s in sharers:
            pairs += 1
            if s in freeset: held += 1
            elif len(fails) < 3: fails.append((v, v[i], s))
        if len(freeset) <= 2:
            for e in freeset:
                freekind[('largest' if e == max(flanks) else 'not largest', 'sharer' if e in sharers else 'not sharer')] += 1
    return pairs, held, fails, freekind
if __name__ == '__main__':
    for n, V in ((8, 20), (5, 30)):
        P = H = 0; F = []; K = Counter()
        with Pool() as pool:
            for p, h, f, k in pool.imap_unordered(job, [(n, v) for v in itertools.combinations(range(1, V + 1), n)], chunksize=300):
                P += p; H += h; K.update(k)
                if len(F) < 5: F += f
        print(f'n={n}: sharer runners (runner, subject) {P}; own flank free {H}; not free {P - H}; examples not free {F[:5]}')
        print(f'   free flanks of runners with at most two free flanks, by (largest difference?, sharer?): {dict(K)}')
        sys.stdout.flush()
