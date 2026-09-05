"""ADVERSARIAL kill of the k=3 spectral 'hit'. Proper null max distribution
(300 trials) + multiple varied LCG positive controls. If (a) real sits inside
the 300-null max distribution and (b) real LCGs don't reliably exceed real,
then it's a multiple-testing fluctuation and the tool is underpowered at n=63."""
import csv, math, itertools
import numpy as np

rows=[]
with open('/Users/trentpalelei/Desktop/Math Ex/btc_puzzle_investigation/puzzles_verified.csv') as f:
    for r in csv.DictReader(f):
        rows.append((int(r['puzzle']),int(r['bits']),int(r['private_key'],16),r['funding_block']))
rows.sort(); d={p:(b,k) for p,b,k,fb in rows}
fb={p:f for p,_,_,f in rows}
SAME=[p for p in range(3,66) if p in d and fb[p]=='339085']
u_real=np.array([(d[p][1]-2**(d[p][0]-1))/2**(d[p][0]-1) for p in SAME])
n=len(u_real); k=3; cbox=20
CVECS=[c for c in itertools.product(range(-cbox,cbox+1),repeat=k)
       if not all(x==0 for x in c) and next(x for x in c if x!=0)>0]
CMAT=np.array(CVECS)   # (Ncv, k)

def wmax(u):
    P=np.array([u[i:i+k] for i in range(len(u)-k+1)])   # (m,k)
    ang=2*math.pi*(P@CMAT.T)                              # (m, Ncv)
    s=np.abs(np.exp(1j*ang).mean(axis=0))
    return s.max()

def lcg_pos(a,c,m,seed):
    z=seed; out=[]
    for _ in SAME: z=(a*z+c)%m; out.append(z/m)
    return np.array(out)

real=wmax(u_real)
rng=np.random.default_rng(1)
nulls=np.array([wmax(rng.random(n)) for _ in range(300)])
# varied real LCG controls
lcgs=[(6364136223846793005,1442695040888963407,2**64,7),
      (1103515245,12345,2**31,42),(48271,0,2**31-1,99),
      (25214903917,11,2**48,5),(6364136223846793005,1,2**64,2024)]
ctrls=np.array([wmax(lcg_pos(*p)) for p in lcgs])

print(f"n={n}, k={k}, freq-vectors scanned={len(CVECS)}")
print(f"REAL same-block Weyl max = {real:.3f}")
print(f"NULL (300 random) max-dist: mean={nulls.mean():.3f} p95={np.quantile(nulls,0.95):.3f} "
      f"p99={np.quantile(nulls,0.99):.3f} max={nulls.max():.3f}")
print(f"REAL percentile vs 300 nulls = {100*np.mean(nulls<real):.1f}%   "
      f"p-value = {np.mean(nulls>=real):.3f}")
print(f"LCG controls: {np.round(ctrls,3).tolist()}  (mean {ctrls.mean():.3f})")
print(f"  fraction of real LCGs that EXCEED real data = {np.mean(ctrls>=real):.2f}")
killed = np.mean(nulls>=real)>0.05 or np.mean(ctrls>=real)<0.5
print("VERDICT:", "KILLED -- fluctuation / tool underpowered at n=63" if killed
      else "SURVIVES -- real exceeds nulls AND LCGs clear the bar")
