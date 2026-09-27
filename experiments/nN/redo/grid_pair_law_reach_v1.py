"""E129: what GridPairLawN.grid_pair_law settles on its own (its exact hypotheses).  Reference grid through reading j at
scale lam = s_j/m (m <= M); x_i = s_i/lam; n_i = round(x_i) >= 1; class pair (c, c') odd, c + c' = 0 mod 8, c, c' <= CMAX;
exactly one reading with c n = 1 (a) and one with c n = 7 (b) mod 8, every other residue in 2..6; deviations after
rescaling by n_a/x_a and by n_b/x_b at most 1/max(c,c').  Exact.  Reports coverage and the failure reasons."""
import itertools, sys
from fractions import Fraction as F
from collections import Counter
from multiprocessing import Pool
M = 4; CMAX = 63
def rnd(q): return int((q + F(1, 2)) // 1)
def settles(s):
    reasons = Counter()
    for m in range(1, M + 1):
        for j in range(7):
            lam = s[j] / m; x = [v / lam for v in s]; n = [rnd(v) for v in x]
            if min(n) < 1: continue
            for c in range(1, CMAX + 1, 2):
                for c2 in range(1, CMAX + 1, 2):
                    if (c + c2) % 8: continue
                    res = [(c * v) % 8 for v in n]
                    if 0 in res: reasons['a reading captured (c n = 0 mod 8)'] += 1; continue
                    A = [i for i, r in enumerate(res) if r == 1]; B = [i for i, r in enumerate(res) if r == 7]
                    if len(A) != 1 or len(B) != 1: reasons['an edge empty or doubled'] += 1; continue
                    a, b = A[0], B[0]; C = max(c, c2)
                    ok = all(abs(x[i] * F(n[a]) / x[a] - n[i]) <= F(1, C) and abs(x[i] * F(n[b]) / x[b] - n[i]) <= F(1, C) for i in range(7))
                    if ok: return None
                    reasons['deviation beyond 1/C'] += 1
    return reasons
N = int(sys.argv[1]); SMAX = int(sys.argv[2])
def chunk(first):
    cov = Counter(); why = Counter()
    for rest in itertools.combinations(range(first + 1, N + 1), 6):
        T = (first,) + rest
        if not (7 * T[0] < T[-1] <= SMAX * T[0]): continue
        r = settles([F(d, T[0]) for d in T])
        cov[r is None] += 1
        if r is not None: why[max(r, key=r.get) if r else 'no candidate'] += 1
    return cov, why
if __name__ == '__main__':
    cov = Counter(); why = Counter()
    with Pool(10) as p:
        for c, w in p.imap_unordered(chunk, range(1, N - 5)): cov.update(c); why.update(w)
    print("readings <= %d, spread (7, %d]: settled by grid_pair_law alone: %d of %d" % (N, SMAX, cov[True], cov[True] + cov[False]))
    print("  commonest obstruction among the unsettled:", why.most_common())
