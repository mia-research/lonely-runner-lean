"""
Test the creator's 'consecutive deterministic' claim on the REAL data.
If puzzle key N = a PRNG stream output mapped into [2^(N-1),2^N), then the
normalized positions u_N are consecutive PRNG draws in [0,1). Hunt for that:
autocorrelation, lag-plot lattice (LCG spectral signature), and a modular
linear recurrence u_{N+1} = a*u_N + c (mod 1). Only the CONTIGUOUS run 1..70
gives true consecutive samples.
"""
import csv, math
import numpy as np

rows=[]
with open('/Users/trentpalelei/Desktop/Math Ex/btc_puzzle_investigation/puzzles_verified.csv') as f:
    for r in csv.DictReader(f):
        rows.append((int(r['puzzle']), int(r['bits']), int(r['private_key'],16)))
rows.sort()
d={p:(b,k) for p,b,k in rows}

# consecutive run 1..70 (true adjacency); u in [0,1)
seq=[p for p in range(1,71) if p in d]
u=np.array([ (d[p][1]-2**(d[p][0]-1))/2**(d[p][0]-1) for p in seq ])
print(f"contiguous consecutive keys: {seq[0]}..{seq[-1]}  (n={len(u)})")

# ---- autocorrelation of u at lags 1..8 ----
uc=u-u.mean(); denom=(uc*uc).sum()
print("\n[A] autocorrelation of u-sequence:")
for lag in range(1,9):
    ac=(uc[:-lag]*uc[lag:]).sum()/denom
    # ~95% band for white noise ~ +/-2/sqrt(n)
    print(f"  lag{lag}: r={ac:+.3f}   (white-noise 95% band = +/-{2/math.sqrt(len(u)):.3f})")

# ---- lag-1 plot lattice test: do (u_N,u_{N+1}) lie on few parallel lines? ----
# LCG signature: for some integer a, (a*u_N - u_{N+1}) mod 1 clusters near 0/few values.
print("\n[B] LCG lag-1 lattice scan: min spread of (a*u_N - u_{N+1}) mod 1 over integer a")
best=[]
for a in range(2,200):
    resid=((a*u[:-1]-u[1:])%1.0)
    # circular spread: concentrate? measure resultant length R (1=perfectly concentrated)
    ang=2*math.pi*resid
    R=math.hypot(np.cos(ang).mean(), np.sin(ang).mean())
    best.append((R,a))
best.sort(reverse=True)
print("  top concentrations (R near 1 => lattice structure; random ~ {:.2f}):".format(1/math.sqrt(len(u)-1)))
for R,a in best[:5]:
    print(f"    a={a:3d}  R={R:.3f}")

# ---- permutation baseline for the best R (is it real or just n=69 noise?) ----
rng=np.random.default_rng(0)
nullR=[]
for _ in range(2000):
    up=rng.permutation(u)
    m=0
    for a in range(2,200):
        resid=((a*up[:-1]-up[1:])%1.0); ang=2*math.pi*resid
        R=math.hypot(np.cos(ang).mean(), np.sin(ang).mean())
        if R>m: m=R
    nullR.append(m)
nullR=np.array(nullR)
realbest=best[0][0]
print(f"\n[C] best real R={realbest:.3f}  vs shuffled-null max-R: mean={nullR.mean():.3f} p95={np.quantile(nullR,0.95):.3f}")
print(f"    real percentile = {100*np.mean(nullR<realbest):.1f}%  "
      f"({'SIGNAL' if realbest>np.quantile(nullR,0.95) else 'within noise for n=69'})")

# ---- direct test: are consecutive u independent? (runs / rank correlation) ----
from math import isclose
ranks=np.argsort(np.argsort(u))
# Spearman lag-1
rc=np.corrcoef(ranks[:-1],ranks[1:])[0,1]
print(f"\n[D] Spearman lag-1 rank corr = {rc:+.3f}  (band +/-{2/math.sqrt(len(u)):.3f})")
