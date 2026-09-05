"""
PART B: power-up the gcd(Y,n) thread (single-predicate p, jackknife, variants).
PART A: wide battery coupling (X,Y) to n, to k, and to the (n,k) PAIR jointly
        (Kronecker/Jacobi symbols mod n, k-gcds, X mod n vs k, X*k mod n, phi(n)).
Permutation null shuffles the (n,k) pair together across puzzles. Control =
gcd(k,n)==1 (true by construction) must fire.
"""
import csv, math
from math import gcd
import numpy as np

rows=[]
with open('/Users/trentpalelei/Desktop/Math Ex/btc_puzzle_investigation/puzzles_verified.csv') as f:
    for r in csv.DictReader(f):
        n=int(r['n'])
        if 3<=n<256:
            rows.append((int(r['X'],16),int(r['Y'],16),n,int(r['k'])))
X=[r[0] for r in rows]; Y=[r[1] for r in rows]; N=[r[2] for r in rows]; K=[r[3] for r in rows]
m=len(rows); print(f"puzzles: {m}")

def phi(n):
    r=n; p=2; nn=n
    while p*p<=nn:
        if nn%p==0:
            while nn%p==0: nn//=p
            r-=r//p
        p+=1
    if nn>1: r-=r//nn
    return r
def kron(a,n):            # Kronecker symbol (a|n), all integers n>0
    if n==0: return 1 if abs(a)==1 else 0
    if n<0: n=-n
    if n%2==0:
        if a%2==0: return 0
        e=0
        while n%2==0: n//=2; e+=1
        t=1 if (a%8 in (1,7)) else -1
        s=(t**e)
    else: s=1
    a%=n; res=s
    while a:
        while a%2==0:
            a//=2
            if n%8 in (3,5): res=-res
        a,n=n,a
        if a%4==3 and n%4==3: res=-res
        a%=n
    return res if n==1 else 0

rng=np.random.default_rng(0)
def permtest(pred, pairs, trials=5000):
    """pred(i, n, k) -> float; null shuffles (n,k) pairs across puzzles."""
    obs=np.mean([pred(i,N[i],K[i]) for i in range(m)])
    null=np.empty(trials)
    idx=np.arange(m)
    for t in range(trials):
        rng.shuffle(idx)
        null[t]=np.mean([pred(i,N[idx[i]],K[idx[i]]) for i in range(m)])
    z=(obs-null.mean())/(null.std()+1e-12)
    p=np.mean(np.abs(null-null.mean())>=abs(obs-null.mean()))
    return obs,null.mean(),z,p

print("\n=== PART B: gcd(Y,n) powered up ===")
for name,pr in [("gcd(Y,n)>1",   lambda i,n,k: 1.0 if gcd(Y[i],n)>1 else 0.0),
                ("gcd(Y,n-1)>1", lambda i,n,k: 1.0 if gcd(Y[i],n-1)>1 else 0.0),
                ("gcd(Y,n+1)>1", lambda i,n,k: 1.0 if gcd(Y[i],n+1)>1 else 0.0),
                ("gcd(Y,phi(n))>1",lambda i,n,k:1.0 if gcd(Y[i],phi(n))>1 else 0.0)]:
    o,nm,z,p=permtest(pr,None)
    print(f"  {name:>16}: obs={o:.3f} null={nm:.3f} z={z:+.2f} p={p:.4f}")
# jackknife gcd(Y,n): drop each puzzle, recompute z -> is it one-puzzle-driven?
base=[1.0 if gcd(Y[i],N[i])>1 else 0.0 for i in range(m)]
zs=[]
for j in range(m):
    keep=[i for i in range(m) if i!=j]
    obs=np.mean([base[i] for i in keep])
    null=[]
    idx=np.array(keep)
    for _ in range(1500):
        rng.shuffle(idx)
        null.append(np.mean([1.0 if gcd(Y[keep[t]],N[idx[t]])>1 else 0.0 for t in range(len(keep))]))
    null=np.array(null); zs.append((obs-null.mean())/(null.std()+1e-12))
print(f"  jackknife z (drop-one): min={min(zs):+.2f} max={max(zs):+.2f} "
      f"-> {'STABLE' if max(zs)<-1.0 else 'fragile/one-puzzle-driven'}")

print("\n=== PART A: wide battery — (X,Y) x n, k, and (n,k) jointly ===")
battery={
 "Jacobi(X|n)=+1":  lambda i,n,k: 1.0 if kron(X[i],n)==1 else 0.0,
 "Jacobi(Y|n)=+1":  lambda i,n,k: 1.0 if kron(Y[i],n)==1 else 0.0,
 "Jacobi(XY|n)=+1": lambda i,n,k: 1.0 if kron(X[i]*Y[i],n)==1 else 0.0,
 "gcd(X,k)>1":      lambda i,n,k: 1.0 if gcd(X[i],k)>1 else 0.0,
 "gcd(Y,k)>1":      lambda i,n,k: 1.0 if gcd(Y[i],k)>1 else 0.0,
 "gcd(X,n*k)>1":    lambda i,n,k: 1.0 if gcd(X[i],n*k)>1 else 0.0,
 "(X mod n)<k":     lambda i,n,k: 1.0 if (X[i]%n)<k else 0.0,
 "(Y mod n)<k":     lambda i,n,k: 1.0 if (Y[i]%n)<k else 0.0,
 "(X*k mod n)==0":  lambda i,n,k: 1.0 if (X[i]*k%n)==0 else 0.0,
 "|Xmodn - k|<n/8": lambda i,n,k: 1.0 if abs((X[i]%n)-k)<n/8 else 0.0,
 "(X+Y) mod n < k": lambda i,n,k: 1.0 if ((X[i]+Y[i])%n)<k else 0.0,
 "kron(X|n)==kron(k|n)": lambda i,n,k: 1.0 if kron(X[i],n)==kron(k,n) else 0.0,
 # valid controls for the PAIR-shuffle: fire only when (n,k) is paired to its own puzzle
 "CTRL k==trueK":   lambda i,n,k: 1.0 if k==K[i] else 0.0,
 "CTRL n==trueN":   lambda i,n,k: 1.0 if n==N[i] else 0.0,
 "CTRL synth(X~k)": lambda i,n,k: 1.0 if ((X[i]+K[i])%997)==((X[i]+k)%997) else 0.0,
}
print(f"  {'predicate':>22} {'obs':>7} {'null':>7} {'z':>7} {'p':>7}")
for name,pr in battery.items():
    o,nm,z,p=permtest(pr,None,trials=4000)
    star=" <==" if p<0.004 else ""
    print(f"  {name:>22} {o:>7.3f} {nm:>7.3f} {z:>+7.2f} {p:>7.4f}{star}")
print("\n(Bonferroni ~12 -> need p<0.004. CTRL must fire or no power.)")
