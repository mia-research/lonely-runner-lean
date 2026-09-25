"""Is the dyadic grid special, or is it the comb effect?  On the v1 EightResidual: is S lonely at
some point of the grid (1/M)Z for M = 2^K (dyadic), against M = 2^K - 1, 2^K + 1, 3*2^(K-2)
(same mesh, other arithmetic), and the dyadic grid shifted by a random offset.  Exact for the
unshifted grids (integer arithmetic)."""
import itertools, collections, sys, os, random
random.seed(3)
N = int(sys.argv[1]) if len(sys.argv) > 1 else 30
exec(open(os.path.join(os.path.dirname(__file__) or ".", "eight_residual_count_v1.py")).read().split("t0 = time.time()")[0])
def grid_hit(S, M):
    return any(all(M <= 8 * ((d * a) % M) <= 7 * M for d in S) for a in range(1, M))
def shifted_hit(S, M, off):
    for a in range(M):
        t = (a + off) / M
        if all(min((d * t) % 1, 1 - (d * t) % 1) >= 1 / 8 for d in S): return True
    return False
res = collections.Counter(); n = 0
for S in itertools.combinations(range(1, N + 1), 7):
    if not any(d % 2 for d in S): continue
    if not all(any(d % q == 0 for d in S) for q in (5, 6, 7, 8)): continue
    if not max(S) > 7 * min(S): continue
    if sum(4 if d % 8 == 4 else 2 for d in S if d % 8) < 8: continue
    if any(free_flank8(S, e) for e in S if e % 8 == 0): continue
    if shifted(S): continue
    s = sorted(S)
    if s[-1] > 7 * s[-2]: continue
    if first_lap(S) or minus_seven(S): continue
    n += 1
    for K in (5, 6):
        for name, M in ((f"2^{K}", 2**K), (f"2^{K}-1", 2**K - 1), (f"2^{K}+1", 2**K + 1), (f"3*2^{K-2}", 3 * 2**(K - 2))):
            res[(K, name)] += not grid_hit(S, M)
        res[(K, f"2^{K} shifted")] += not shifted_hit(S, 2**K, random.random())
print(f"N = {N}: v1 residual {n} sets; FAILURES (no grid point lonely):")
for k in sorted(res): print("  ", k, res[k])
