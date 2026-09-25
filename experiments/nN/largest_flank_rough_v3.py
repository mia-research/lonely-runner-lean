"""Exhaustive: for each e in [A, B], every 6-subset of [1, e-1] with e as largest; does the flank e
have a lonely opening (Theorem 10)?  Failures per e, split by whether e has a prime factor <= 7."""
import itertools, sys, time
def works(S, e):
    for j in range(e):
        A = 8 * j + 1
        if all(e <= (d * A) % (8 * e) <= 7 * e for d in S): return True
    return False
A, B = int(sys.argv[1]), int(sys.argv[2])
for e in range(A, B + 1):
    t0 = time.time(); fails = [S for S in itertools.combinations(range(1, e), 6) if not works(S, e)]
    rough = all(e % p for p in (2, 3, 5, 7))
    print(f"e = {e:3d} {'NO factor <= 7' if rough else 'factor <= 7   '}: {len(fails):7d} failures  {fails[:2]}  ({time.time()-t0:.0f}s)", flush=True)
