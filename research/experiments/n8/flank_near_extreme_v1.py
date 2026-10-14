"""Structure of the near-extreme cases: runners with at most two unshadowed flanks (order 8, every 8-subset of [1,20]; order 5,
every 5-subset of [1,30], at most one). For every shadowed flank e of such a runner: the smallest set of other runners that
blocks every opening of e (openings t_k = (nk+1)/(n·e), k mod e decides, integer speeds, exact), and the reduced denominators
c = e/gcd(d, e) of their ratios d/e. Classification of a shadowed flank:
  dead  — one runner with integer ratio ≡ 0 mod n;
  small — smallest blocking set has 2 or 3 runners (the pair / triple rungs);
  wide  — smallest blocking set has 4 or more runners (where the flank sum criterion can fail).
Also: for the free flanks, the ratio structure (number of non-integer ratios)."""
import itertools, sys
from collections import Counter
from multiprocessing import Pool
def blocks_all(e, ds, n):
    M = n * e
    for k in range(e):
        if all(e <= (d * (n * k + 1)) % M <= (n - 1) * e for d in ds): return False
    return True
def analyse(ds, n):
    flanks = sorted(set(ds)); free = []; shad = []
    for e in flanks:
        others = [d for d in ds if d != e]
        if not blocks_all(e, others, n): free.append(e); continue
        best = None
        for size in range(1, len(others) + 1):
            for S in itertools.combinations(others, size):
                if blocks_all(e, list(S), n): best = S; break
            if best: break
        dens = tuple(sorted(e // __import__('math').gcd(d, e) for d in best))
        kind = 'dead' if len(best) == 1 else ('small' if len(best) <= 3 else 'wide')
        shad.append((e, kind, len(best), dens))
    return free, shad
def job(args):
    n, v, maxfree = args
    out = []
    for i in range(n):
        ds = [abs(x - v[i]) for x in v if x != v[i]]
        free, shad = analyse(ds, n)
        if len(free) <= maxfree: out.append((v, i, free, shad))
    return out
if __name__ == '__main__':
    import math
    for n, V, maxfree in ((8, 20, 2), (5, 30, 1)):
        kinds = Counter(); sigs = Counter(); wide_examples = []; freecnt = Counter(); rows = 0
        with Pool() as pool:
            for out in pool.imap_unordered(job, [(n, v, maxfree) for v in itertools.combinations(range(1, V + 1), n)], chunksize=300):
                for v, i, free, shad in out:
                    rows += 1; freecnt[len(free)] += 1
                    for e, kind, size, dens in shad:
                        kinds[kind] += 1; sigs[(kind, dens)] += 1
                        if kind == 'wide' and len(wide_examples) < 5: wide_examples.append((v, i, e, dens))
        print(f'n={n}: {rows} runners with at most {maxfree} free flank(s) ({dict(freecnt)}); shadowed flanks by kind: {dict(kinds)}')
        print('   most common (kind, denominators of the smallest blocking set):', sigs.most_common(12))
        print('   wide examples (speeds, subject index, flank, denominators):', wide_examples)
        sys.stdout.flush()
