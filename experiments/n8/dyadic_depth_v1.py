"""
Runs the test pre-registered in docs/n8/PREREG_DYADIC_DEPTH_v1.md.
Exact integer arithmetic; no floating point in any decision.

kappa(T) = least k >= 3 with some odd a s.t. ||v a/2^k|| >= 1/8 for all v in T.
Residual hard case R = sets holding a multiple of 5, of 6, of 7 and of 8, gcd 1.

Positive control: identical sampler with the threshold raised from 1/8 to 1/7.
LRC(8) is false at 1/7, so unsettled sets MUST appear.  Zero failures there means
the harness is broken and the main number is void.
"""
import random, sys
from math import gcd

def kappa(T, kmax, num=1, den=8):
    """least k with a dyadic witness at threshold num/den; None if none <= kmax."""
    for k in range(3, kmax+1):
        mod = 1 << k
        for a in range(1, mod, 2):
            ok = True
            for v in T:
                r = (v*a) % mod
                d = r if r <= mod-r else mod-r
                if d*den < num*mod: ok = False; break
            if ok: return k
    return None

def draw(V, rng):
    while True:
        T = tuple(sorted(rng.sample(range(1, V+1), 7)))
        if not all(any(v % q == 0 for v in T) for q in (5,6,7,8)): continue
        g = 0
        for v in T: g = gcd(g, v)
        if g != 1: continue
        return T

def run(V, N, kmax, num, den, seed):
    rng = random.Random(seed)
    dist, fails = {}, []
    for _ in range(N):
        T = draw(V, rng)
        k = kappa(T, kmax, num, den)
        if k is None: fails.append(T)
        else: dist[k] = dist.get(k,0)+1
    return dist, fails

if __name__ == "__main__":
    N, KMAX = 20000, 16
    print(f"MAIN  threshold 1/8, N={N}/V, kmax={KMAX}")
    for V in (50, 100, 200, 400, 800):
        d, f = run(V, N, KMAX, 1, 8, seed=1000+V)
        mx = max(d) if d else None
        print(f"  V={V:4d}  max kappa={mx}  dist={dict(sorted(d.items()))}  unsettled={len(f)}", flush=True)
        for T in f[:5]: print("      UNSETTLED", T)
    print(f"\nPOSITIVE CONTROL  threshold 1/7 (LRC(8) false at 1/7 -- failures MUST appear)")
    for V in (50, 200):
        d, f = run(V, 2000, KMAX, 1, 7, seed=7000+V)
        print(f"  V={V:4d}  settled={sum(d.values())}  UNSETTLED={len(f)}  "
              f"{'CONTROL FIRES' if f else '*** CONTROL DID NOT FIRE -- harness broken ***'}", flush=True)
