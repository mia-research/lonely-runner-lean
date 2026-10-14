"""Is R bounded at order 8? Directed search SEEDED from the framework's named cases.

Section 6.7's line needs `R` finite, not `R < n-1`: `exists_fixed_of_capped` gives that a cascade whose
instants are capped stops, and section 6.2 gives `R = d_min/D_final = prod_j lambda_j` with step factors
`lambda_j = (8N_j + 1)/s_{x_j}`, `s_{x_j}` in `(8N_j - 1, 8N_j + 1)`, so `lambda_j <= (8N_j+1)/(8N_j-1) <= 9/7`.
Bounding R is therefore bounding that product, and the question "how large can R get" is the first thing
a bound has to survive.

`r_directed_search_v1.py` hill-climbed from RANDOM starts and reached only 4.92, below two cases the
manuscript already names at ~10.3. That is the same under-powered-search error as the 28,000 sweep, so
this one seeds from the named cases and reports the step-factor structure of whatever it finds.
"""
import sys, random
from fractions import Fraction as F

n = 8; INV_N = F(1, n)
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

def analyse(dsi, maxsteps=4000):
    """Returns R = n*u and the step factors lambda_j with their N_j, in scale coordinates."""
    ds = sorted(F(d) for d in dsi); m = min(ds)
    D = m; factors = []
    for _ in range(maxsteps):
        best = None; bestN = None
        for d in ds:
            s = d / D; N = round(s / 8)
            if abs(s - 8 * N) < 1:
                c = s / (8 * N + 1)
                if best is None or c < best: best, bestN = c, N
        if best is None:
            R = m / D
            return R, factors
        D = D * best; factors.append((F(1) / best, bestN))     # lambda = 1/best
    return None, factors

SEEDS = [
    [49, 205, 234, 256, 286, 323, 366],      # section 6.7 climb, subject 393
    [30, 74, 96, 127, 159, 175, 224],        # section 6.9 row, subject 1
]
VMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 3000
ROUNDS = int(sys.argv[2]) if len(sys.argv) > 2 else 60
random.seed(20260917)

print(f"order {n}: how large does R get?  (Existence needs R finite, not R < {n-1})")
print(f"seeded from the named cases; hill climb on integer differences, entries <= {VMAX}\n")
for s in SEEDS:
    R, f = analyse(s)
    print(f"  seed {s}:  R = {R} = {float(R):.4f}, {len(f)} steps")

best = (F(0), None)
for si, seed in enumerate(SEEDS):
    for rd in range(ROUNDS):
        cur = list(seed)
        if rd:                                              # perturbed restarts
            cur = [max(1, c + random.randint(-c // 4, c // 4)) for c in cur]
            if len(set(cur)) < 7: continue
        Rc, _ = analyse(cur)
        if Rc is None: continue
        improved = True
        while improved:
            improved = False
            for i in range(7):
                for delta in (-8, -3, -1, 1, 3, 8):
                    cand = list(cur); cand[i] += delta
                    if cand[i] < 1 or cand[i] > VMAX or len(set(cand)) < 7: continue
                    cand = sorted(cand)
                    Rn, _ = analyse(cand)
                    if Rn is not None and Rn > Rc:
                        cur, Rc = cand, Rn; improved = True
        if Rc > best[0]: best = (Rc, list(cur))

R, ds = best
fs = analyse(ds)[1]
m = min(ds); S = F(max(ds), m)
print(f"\n  largest R found: {R} = {float(R):.4f}")
print(f"    differences {ds}   d_min {m}   ratio S = {float(S):.4f}")
print(f"    steps {len(fs)};  step factors (lambda, N):")
from collections import Counter
cnt = Counter(N for _, N in fs)
print(f"      N histogram: {dict(sorted(cnt.items()))}")
print(f"      product of lambdas = {float(F(1).__class__(1)) if not fs else float(eval('*'.join(str(float(l)) for l,_ in fs)))
        if False else float(R):.4f}  (= R, by section 6.2)")
print(f"      largest single lambda = {max((float(l) for l,_ in fs), default=0):.4f}   (bound 9/7 = {9/7:.4f})")
print(f"\n  manuscript section 6.7 records the largest found as ~11.96 at S ~ 7.44")
print(f"  this run: {float(R):.4f} at S = {float(S):.4f}")
