"""Is the certificate's cap `R < n-1` a framework object, or the first window in lap coordinates?

v1 of this script had a defect -- its iteration never advanced `t`, so every arrangement whose cascade
actually moved was counted as non-terminating and dropped. Its headline figure ("100% inside the
window") was therefore computed from the 0-step cases alone. Corrected here; `first_window_nativeness_v1.out`
is kept as the record of the defect.

OBJECT_REGISTER_v1 section 0: laps `u = d_min * t`, readings `s_j = d_j/d_min`.
ORDER5_GROWTH_v2 section 2: `R = n * m * t` with `m = d_min`. Hence `R = n * u` exactly, and

    cap  R < n - 1   <=>   u < (n-1)/n ,   with the cascade opening at u = 1/n,

i.e. the cap is exactly "u stays in the first window [1/n, (n-1)/n]" -- register item 15, MISPLACED.

Measured here with framework objects only and the native cascade (LRC/Cascade/Iteration.lean,
transcribed verbatim), no cap and no window imposed: where does the first lonely instant fall?

Stratified by ratio, because one stratum is trivial and the register already owns the reason:
at u = 1/n the phase of `d_j` is `d_j/(n*d_min)`, clear iff `d_min <= d_j mod n*d_min <= (n-1)*d_min`,
so for `d_j <= n*d_min` the subject is lonely at the opening instant iff every `d_j <= (n-1)*d_min`.
That is the register's **ceiling** object. Verified separately below.
"""
import os, sys, random
from fractions import Fraction as F

n = int(os.environ.get('ORDER', 8))
INV_N = F(1, n); NDIFF = n - 1; CAP_U = F(n - 1, n)

def fract(x):          return x - (x.numerator // x.denominator)
def circDist(x):       return min(fract(x), 1 - fract(x))
def inWay(d, t):       return circDist(d * t) < INV_N
def ceil_(x):          return -((-x.numerator) // x.denominator)
def nextOpening(d, t): return (F(ceil_(d * t - INV_N)) + INV_N) / d
def Lonely(ds, s):     return all(INV_N <= circDist(d * s) for d in ds)
def move(ds, t):
    acc = t
    for d in ds:
        if inWay(d, t):
            o = nextOpening(d, t)
            if o > acc: acc = o
    return acc
def run(ds, maxsteps=2000):
    t = INV_N
    for k in range(maxsteps):
        t2 = move(ds, t)
        if t2 == t: return t, k, Lonely(ds, t)
        t = t2                                    # <- the line v1 was missing
    return t, maxsteps, None

NSAMP = int(sys.argv[1]) if len(sys.argv) > 1 else 4000
DMAX  = int(sys.argv[2]) if len(sys.argv) > 2 else 200
random.seed(20260917)

print(f"order {n}: {NDIFF} differences, threshold 1/{n}")
print(f"cap in laps: u < {CAP_U} = {float(CAP_U):.4f}   (equivalently R < {n-1})")
print(f"{NSAMP} shuffled integer difference sets per ratio bound, entries <= {DMAX}\n")

print("  ceiling check: at u = 1/n, lonely  <=>  every d_j <= (n-1)*d_min  (for ratio <= n)")
random.seed(3); ok = True
for _ in range(500):
    while True:
        ds = random.sample(range(1, DMAX + 1), NDIFF); m = min(ds)
        if max(ds) <= n * m: break
    if (max(ds) <= (n - 1) * m) != Lonely(sorted(F(d, m) for d in ds), INV_N): ok = False
print(f"    holds on 500 shuffled sets: {ok}\n")

print(f"  {'ratio bound':>12} {'samples':>8} {'inside':>8} {'beyond':>8} {'no fixpt':>9} "
      f"{'max u':>9} {'max R':>8} {'max steps':>10}")
for S in [8, 10, 14, 20, 30, 60, 120]:
    random.seed(20260917 + S)
    inside = beyond = nonterm = 0; worst = F(0); worst_ds = None; msteps = 0
    for _ in range(NSAMP):
        while True:
            ds = random.sample(range(1, DMAX + 1), NDIFF); m = min(ds)
            if max(ds) <= S * m: break
        rd = sorted(F(d, m) for d in ds)
        t, k, lonely = run(rd)
        if lonely is None: nonterm += 1; continue
        msteps = max(msteps, k)
        if t > CAP_U:
            beyond += 1
            if t > worst: worst, worst_ds = t, rd
        else: inside += 1
    tot = inside + beyond
    print(f"  {S:>12} {tot:>8} {inside:>8} {beyond:>8} {nonterm:>9} "
          f"{float(worst) if worst else float(CAP_U):>9.4f} {float(n*worst) if worst else 0:>8.4f} {msteps:>10}")
    if worst_ds:
        print(f"               beyond-window witness: {[str(r) for r in worst_ds]}")
print()
print("  'beyond' = the first lonely instant lies outside the first window, so the certificate's")
print("  target `sup R < n-1` is false for that arrangement while the framework still produces an")
print("  instant. 'no fixpt' = no lonely instant within the step budget (not a claim of none).")
