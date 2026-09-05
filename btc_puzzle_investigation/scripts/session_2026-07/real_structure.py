"""
Investigate the REAL 82 puzzle keys for the generation engine's fingerprint.
Keys parsed strictly as hex. We look for deterministic structure the creator's
'consecutive keys from one wallet' method would leave -- in the data we HAVE.
"""
import csv, math
rows=[]
with open('/Users/trentpalelei/Desktop/Math Ex/btc_puzzle_investigation/puzzles_verified.csv') as f:
    for r in csv.DictReader(f):
        rows.append((int(r['puzzle']), int(r['bits']), int(r['private_key'],16)))
rows.sort()
d={p:(b,k) for p,b,k in rows}

# sanity: keys must lie in [2^(b-1), 2^b)
bad=[(p,b,k) for p,b,k in rows if not (2**(b-1)<=k<2**b)]
print("out-of-interval keys:", bad if bad else "none (all in [2^(N-1),2^N))")

print("\npuzzle  key(hex)        u=(d-2^(N-1))/2^(N-1)   frac=d/2^N")
for p,b,k in rows:
    R=2**(b-1); u=(k-R)/R; frac=k/2**b
    print(f"{p:3d}   {k:>16x}   u={u:.6f}   frac={frac:.6f}")

# ---- TEST 1: master-prefix hypothesis  d_{N+1} in {2 d_N, 2 d_N +1} ----
print("\n[T1] master-prefix: is d_{N+1} == 2*d_N + bit?  (consecutive solved pairs)")
hits=0; tot=0
for p in range(1,70):
    if p in d and p+1 in d:
        tot+=1; a=d[p][1]; b=d[p+1][1]; delta=b-2*a
        flag="<== prefix!" if delta in (0,1) else ""
        if delta in (0,1): hits+=1
        if abs(delta)<4 or flag: print(f"  {p}->{p+1}: d_+1 - 2*d = {delta} {flag}")
print(f"  prefix hits: {hits}/{tot}")

# ---- TEST 2: high-bit continuity: do top bits of d_N persist into d_{N+1}? ----
print("\n[T2] shared top bits between consecutive keys (align to same bit-length)")
for p in range(60,70):
    if p in d and p+1 in d:
        a=d[p][1]; b=d[p+1][1]
        # compare top 8 bits
        ta=a>>(d[p][0]-8); tb=b>>(d[p+1][0]-8)
        print(f"  {p}: top8={ta:08b}   {p+1}: top8={tb:08b}")

# ---- TEST 3: position uniformity (is u ~ Uniform[0,1)?) ----
us=sorted((d[p][1]-2**(d[p][0]-1))/2**(d[p][0]-1) for p in d)
# Kolmogorov-Smirnov vs uniform
n=len(us); Dstat=max(max((i+1)/n-u, u-i/n) for i,u in enumerate(us))
print(f"\n[T3] position u: n={n}  KS D={Dstat:.4f}  (uniform crit ~1.36/sqrt(n)={1.36/math.sqrt(n):.4f})")
print(f"     mean={sum(us)/n:.4f} (unif=0.5)  min={us[0]:.4f} max={us[-1]:.4f}")

# ---- TEST 4: shared LOW bits across all keys (fixed suffix / even bias) ----
print("\n[T4] low-bit structure across all 82 keys:")
for bitpos in range(6):
    ones=sum((k>>bitpos)&1 for _,_,k in rows)
    print(f"  bit{bitpos}: ones={ones}/82  ({100*ones/82:.0f}%)")

# ---- TEST 5: gcd / common factor structure ----
from math import gcd
g=0
for _,_,k in rows: g=gcd(g,k)
print(f"\n[T5] gcd of all keys = {g}")
