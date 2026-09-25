"""On EightResidual (all shapes) among 7-subsets of [1,N]: is the largest non-multiple of 8 a
certifying flank (Theorem 10)?  For the sets where it is not, which ranks of non-multiple
flanks certify (rank 1 = largest non-multiple)."""
import itertools, collections, sys, time
N = int(sys.argv[1]) if len(sys.argv) > 1 else 30
exec(open(__import__("os").path.join(__import__("os").path.dirname(__file__) or ".", "eight_residual_count_v1.py")).read().split("t0 = time.time()")[0])
def works(S, e):
    return any(all(e <= (d*(8*j+1)) % (8*e) <= 7*e for d in S) for j in range(e))
t0=time.time(); tot=collections.Counter(); exc=[]; rank=collections.Counter()
for S in itertools.combinations(range(1, N+1), 7):
    if not any(d%2 for d in S): continue
    if not all(any(d%q==0 for d in S) for q in (5,6,7,8)): continue
    if not max(S) > 7*min(S): continue
    if sum(4 if d%8==4 else 2 for d in S if d%8) < 8: continue
    if any(free_flank8(S,e) for e in S if e%8==0): continue
    if shifted(S): continue
    s = sorted(S)
    if s[-1] > 7*s[-2]: continue
    if first_lap(S) or minus_seven(S): continue
    M = sum(1 for d in S if d%8==0); E = sorted((d for d in S if d%8), reverse=True)
    tot[M] += 1
    if works(S, E[0]): tot[(M,'max-E flank works')] += 1; continue
    exc.append(S)
    ok = [i+1 for i, e in enumerate(E) if works(S, e)]
    rank[tuple(ok[:2])] += 1
print(f"N={N}", dict(sorted(tot.items(), key=str)))
print("exceptions:", len(exc), " certifying non-multiple ranks (first two):", dict(rank))
print("first exceptions:", exc[:8]); print(f"{time.time()-t0:.0f}s")
