"""
Test for INDIRECT / SHADOW hints of n (not d) in the coordinates: n-dependent
ALGEBRAIC predicates coupling (X,Y) to a candidate modulus m (gcd, order, QR,
mod-n vs k). For each predicate, permutation test: is the statistic at each
puzzle's OWN true n different from n shuffled across puzzles?  A real coupling
=> observed outside the shuffle null.  Built-in positive control (k coprime to n)
proves the test can see a genuine n-coupling.
"""
import csv, math
from math import gcd
import numpy as np

rows=[]
with open('/Users/trentpalelei/Desktop/Math Ex/btc_puzzle_investigation/puzzles_verified.csv') as f:
    for r in csv.DictReader(f):
        rows.append((int(r['puzzle']),int(r['bits']),int(r['X'],16),int(r['Y'],16),
                     int(r['n']),int(r['k'])))
rows=[r for r in rows if r[4]<256 and r[4]>=3]   # drop degenerate n=256 rows
Xs=np.array([r[2] for r in rows]); Ys=np.array([r[3] for r in rows])
Ns=np.array([r[4] for r in rows]); Ks=np.array([r[5] for r in rows])
Bs=np.array([r[1] for r in rows])
Npz=len(rows); print(f"puzzles used: {Npz}")

def order_mod(a,m):
    a%=m
    if gcd(a,m)!=1: return 0
    o=1; x=a%m
    while x!=1 and o<=m: x=x*a%m; o+=1
    return o if x==1 else 0

# predicates pred(i, m) -> a real number (statistic); we test mean over i at true n vs shuffled n
def make_preds():
    return {
      "gcd(X,m)>1":        lambda i,m: 1.0 if gcd(int(Xs[i]),m)>1 else 0.0,
      "gcd(Y,m)>1":        lambda i,m: 1.0 if gcd(int(Ys[i]),m)>1 else 0.0,
      "gcd(X+Y,m)>1":      lambda i,m: 1.0 if gcd(int(Xs[i]+Ys[i]),m)>1 else 0.0,
      "gcd(X-Y,m)>1":      lambda i,m: 1.0 if gcd(int(abs(Xs[i]-Ys[i])),m)>1 else 0.0,
      "gcd(XY,m)>1":       lambda i,m: 1.0 if gcd(int(Xs[i]*Ys[i]%(1<<64)),m)>1 else 0.0,
      "X QR mod m":        lambda i,m: 1.0 if pow(int(Xs[i])%m, (m-1)//2, m)==1 else 0.0,
      "smallOrd(X,m)":     lambda i,m: 1.0 if 0<order_mod(int(Xs[i]),m)<m//4 else 0.0,
      "Xmodm < m/2":       lambda i,m: 1.0 if int(Xs[i])%m < m/2 else 0.0,
      "(Xmodm)==k":        lambda i,m: 1.0 if int(Xs[i])%m == Ks[i]%m else 0.0,
      "m|(X+Y)":           lambda i,m: 1.0 if (int(Xs[i]+Ys[i])%m)==0 else 0.0,
      "gcd(Xmodm2,m)":     lambda i,m: 1.0 if gcd(int(Xs[i])%(m*m), m)>1 else 0.0,
      # POSITIVE CONTROL: k coprime to n is TRUE by construction -> must resonate hard
      "CTRL gcd(k,m)==1":  lambda i,m: 1.0 if gcd(int(Ks[i]),m)==1 else 0.0,
    }

preds=make_preds()
rng=np.random.default_rng(0)
print(f"\n{'predicate':>18} {'obs(trueN)':>11} {'null_mean':>10} {'null_sd':>8} {'z':>7} {'p':>7}")
for name,pr in preds.items():
    obs=np.mean([pr(i,int(Ns[i])) for i in range(Npz)])
    null=[]
    for _ in range(1000):
        perm=rng.permutation(Ns)
        null.append(np.mean([pr(i,int(perm[i])) for i in range(Npz)]))
    null=np.array(null); z=(obs-null.mean())/(null.std()+1e-12)
    p=np.mean(np.abs(null-null.mean())>=abs(obs-null.mean()))
    star=" <==" if p<0.003 else ""
    print(f"{name:>18} {obs:>11.4f} {null.mean():>10.4f} {null.std():>8.4f} {z:>7.2f} {p:>7.3f}{star}")
print("\n(Bonferroni ~12 tests -> need p<0.003. CTRL row must light up or the test has no power.)")
