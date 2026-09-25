"""Powered test of the candidate (largest flank e with no prime factor <= 7 always has a lonely
opening): for fixed e, EVERY 6-subset of [1, M] together with e.  Controls with a factor <= 7 must
show failures, or the test has no power."""
import itertools, sys, time
def works(S, e):
    for j in range(e):
        A = 8 * j + 1
        if all(e <= (d * A) % (8 * e) <= 7 * e for d in S): return True
    return False
M = int(sys.argv[1]) if len(sys.argv) > 1 else 30
for e in [int(x) for x in sys.argv[2:]] or [120, 125, 126, 121, 127]:
    t0 = time.time(); fail = []; n = 0
    for S in itertools.combinations(range(1, M + 1), 6):
        n += 1
        if not works(S, e): fail.append(S)
    rough = all(e % p for p in (2, 3, 5, 7))
    print(f"e = {e} ({'no factor <= 7' if rough else 'factor <= 7'}): {len(fail)} failures of {n} six-subsets of [1,{M}]  {fail[:3]}  ({time.time()-t0:.0f}s)", flush=True)
