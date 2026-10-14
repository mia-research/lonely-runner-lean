"""How close do arrangements come to every flank shadowed? Integer speeds, threshold 1/n. For a subject and a flank e (one of
its differences), the openings t_k = (n·k + 1)/(n·d_e) repeat in k with period d_e, so k = 0..d_e−1 decides exactly. A flank
is shadowed when every opening has some runner in the way (circle distance < 1/n; coord_iff in integers). Counts, per runner,
the number of flanks NOT shadowed (distinct differences); Existence holds exactly when that number is at least 1."""
import itertools, sys
from collections import Counter
from multiprocessing import Pool
def unshadowed(ds, n):
    free = []
    for e in sorted(set(ds)):
        M = n * e                       # t_k = (n k + 1)/(n e): runner d at position d(nk+1)/(ne); clear iff residue in [e, (n−1)e]
        ok = False
        for k in range(e):
            if all(e <= (d * (n * k + 1)) % M <= (n - 1) * e for d in ds):
                ok = True; break
        if ok: free.append(e)
    return free
def job(args):
    n, v = args
    res = []
    for i in range(n):
        ds = [abs(x - v[i]) for x in v if x != v[i]]
        res.append((len(unshadowed(ds, n)), len(set(ds)), i))
    return v, res
if __name__ == '__main__':
    for n, V in ((5, 30), (8, 20)):
        cnt = Counter(); worst = []
        with Pool() as pool:
            for v, res in pool.imap_unordered(job, [(n, v) for v in itertools.combinations(range(1, V + 1), n)], chunksize=300):
                for u, tot, i in res:
                    cnt[u] += 1
                    if u <= 1: worst.append((u, tot, v, i))
        print(f'n={n}, all subsets of [1,{V}], every runner: number of unshadowed flanks -> runners: {dict(sorted(cnt.items()))}')
        print(f'   runners with exactly one unshadowed flank: {sum(1 for w in worst if w[0] == 1)}; examples: {worst[:6]}')
        sys.stdout.flush()
