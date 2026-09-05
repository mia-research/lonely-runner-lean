"""
Spectral test (Weyl sums) on the same-block contiguous run (puzzles 3-65).
Detects a hidden LCG/PRNG lattice via peaks in |mean exp(2pi i <c, P>)| over
k-dim consecutive-position vectors P -- WITHOUT brute-forcing the multiplier.
Positive control: a real LCG's positions MUST peak. Then read the real data.
"""
import csv, cmath, math
import numpy as np

rows=[]
with open('/Users/trentpalelei/Desktop/Math Ex/btc_puzzle_investigation/puzzles_verified.csv') as f:
    for r in csv.DictReader(f):
        rows.append((int(r['puzzle']),int(r['bits']),int(r['private_key'],16),r['funding_block']))
rows.sort()
d={p:(b,k) for p,b,k,fb in rows}
SAME=[p for p in range(3,66) if p in d and dict((pp,fb) for pp,_,_,fb in rows)[p]=='339085']
u_real=np.array([ (d[p][1]-2**(d[p][0]-1))/2**(d[p][0]-1) for p in SAME ])
print(f"same-block contiguous run: puzzles {SAME[0]}..{SAME[-1]} (n={len(u_real)})")

def spectral_max(u,k,cbox=20):
    """max |Weyl sum| over integer freq vectors c (|c_j|<=cbox, not all 0), dim k."""
    P=np.array([u[i:i+k] for i in range(len(u)-k+1)])   # consecutive k-tuples
    best=0.0; bestc=None
    rng=range(-cbox,cbox+1)
    # iterate c; skip all-zero; use symmetry (fix first nonzero >0)
    import itertools
    for c in itertools.product(rng,repeat=k):
        if all(x==0 for x in c): continue
        # symmetry: require first nonzero positive
        fnz=next(x for x in c if x!=0)
        if fnz<0: continue
        ang=2*math.pi*(P@np.array(c))
        s=abs(np.mean(np.exp(1j*ang)))
        if s>best: best=s; bestc=c
    return best,bestc

def lcg_positions(a,c,m,seed,puzzles):
    z=seed; out=[]
    for p in puzzles:
        z=(a*z+c)%m; frac=z/m
        out.append(frac)   # position = unit LCG output scaled into range
    return np.array(out)

for k in (2,3):
    real,rc=spectral_max(u_real,k)
    # positive control: real LCG (Knuth MMIX) positions, same length
    ctrl=lcg_positions(6364136223846793005,1442695040888963407,2**64,12345,SAME)
    pc,pcc=spectral_max(ctrl,k)
    # random baseline: max Weyl over random uniform sequences
    rng=np.random.default_rng(0)
    nb=[spectral_max(rng.random(len(u_real)),k)[0] for _ in range(30)]
    nb=np.array(nb)
    print(f"\n[dim k={k}]  Weyl-sum max (1.0 = perfect lattice):")
    print(f"   REAL same-block : {real:.3f}   at c={rc}")
    print(f"   LCG control     : {pc:.3f}   at c={pcc}   <- tool has power if this is high")
    print(f"   random baseline : mean={nb.mean():.3f}  p95={np.quantile(nb,0.95):.3f}  max={nb.max():.3f}")
    verdict = "ABOVE random -> lattice structure!" if real>nb.max() else "within random noise"
    print(f"   REAL vs random  : {verdict}  (real pctile {100*np.mean(nb<real):.0f}%)")
