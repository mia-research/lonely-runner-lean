"""
TRY GECT's idea #1 for real: the "structural invariant" is X,Y reduced by the
key's OWN n (and n^2), not by fixed small primes. With true (n,k,X,Y) known for
all 82 solved keys, ask: is k related to the public key mod n?  If yes -- even
weakly -- that is the second stage of a real pipeline (n -> k from X mod n).

Part 1  EXACT algebraic relations k == f(X,Y) mod n  (count hits / 82; chance <1).
Part 2  STATISTICAL: normalized r=(X mod n)/n vs s=k/n, Spearman + permutation null.
Part 3  gcd(X,n), gcd(Y,n) 'Type A/B' rate vs matched reference (GECT's other invariant).
Every statistical test carries a shuffle control.
"""
import csv, random
from math import gcd
import numpy as np

rows=[]
with open('/Users/trentpalelei/Desktop/Math Ex/btc_puzzle_investigation/puzzles_verified.csv') as f:
    for r in csv.DictReader(f):
        rows.append((int(r['bits']),int(r['X'],16),int(r['Y'],16),int(r['n']),int(r['k'])))
Bs=[b for b,_,_,_,_ in rows]; X=[x for _,x,_,_,_ in rows]; Y=[y for _,_,y,_,_ in rows]
Nn=[n for _,_,_,n,_ in rows]; Kk=[k for _,_,_,_,k in rows]; M=len(rows)
print(f"{M} solved keys with true (n,k,X,Y).")

def inv(a,m):
    try: return pow(a,-1,m)
    except ValueError: return None

# ---------- Part 1: exact relations ----------
relations={
    "k == X mod n":         lambda x,y,n: x%n,
    "k == Y mod n":         lambda x,y,n: y%n,
    "k == (X+Y) mod n":     lambda x,y,n: (x+y)%n,
    "k == (X*Y) mod n":     lambda x,y,n: (x*y)%n,
    "k == (X-Y) mod n":     lambda x,y,n: (x-y)%n,
    "k == -X mod n":        lambda x,y,n: (-x)%n,
    "k == X^-1 mod n":      lambda x,y,n: inv(x%n,n),
    "n-k == X mod n":       lambda x,y,n: x%n,           # compared to n-k
    "k == X^2 mod n":       lambda x,y,n: (x*x)%n,
    "k == (X*Y) mod n^2":   lambda x,y,n: (x*y)%(n*n),   # compared to k
}
print("\nPart 1  exact relations (hits/82; >~4 is notable, ~82 = deterministic):")
for name,f in relations.items():
    hits=0
    for i in range(M):
        v=f(X[i],Y[i],Nn[i])
        if v is None: continue
        tgt = (Nn[i]-Kk[i]) if name.startswith("n-k") else Kk[i]
        if v==tgt: hits+=1
    print(f"    {name:22s}: {hits}")

# ---------- Part 2: normalized correlation ----------
def spearman(a,b):
    ra=np.argsort(np.argsort(a)); rb=np.argsort(np.argsort(b))
    ra=ra-ra.mean(); rb=rb-rb.mean()
    return (ra@rb)/(np.sqrt((ra@ra)*(rb@rb))+1e-30)
s=np.array([Kk[i]/Nn[i] for i in range(M)])
rng=np.random.default_rng(1)
print("\nPart 2  Spearman(normalized public-mod-n , k/n) + shuffle-p:")
for name,f in (("Xmodn/n",lambda i:(X[i]%Nn[i])/Nn[i]),
               ("Ymodn/n",lambda i:(Y[i]%Nn[i])/Nn[i]),
               ("XYmodn/n",lambda i:((X[i]*Y[i])%Nn[i])/Nn[i]),
               ("XYmodn2/n2",lambda i:((X[i]*Y[i])%(Nn[i]**2))/(Nn[i]**2))):
    r=np.array([f(i) for i in range(M)])
    obs=abs(spearman(r,s))
    null=[abs(spearman(r,rng.permutation(s))) for _ in range(5000)]
    p=(1+sum(x>=obs for x in null))/(1+len(null))
    print(f"    {name:11s}: |rho|={obs:.3f}  p={p:.3f}{'  << signal' if p<0.05 else ''}")

# ---------- Part 3: gcd 'Type B' rate vs matched reference ----------
_r=random.Random(5)
def synth_gcd():
    tb_x=tb_y=0
    for b,n in zip(Bs,Nn):
        lo=2**(b-1); d=lo+_r.randrange(lo)
        # a random pubkey coordinate ~ uniform mod n; emulate by random residue
        rx=_r.randrange(n); ry=_r.randrange(n)
        tb_x+= gcd(rx,n)>1; tb_y+= gcd(ry,n)>1
    return tb_x,tb_y
obsx=sum(gcd(X[i],Nn[i])>1 for i in range(M)); obsy=sum(gcd(Y[i],Nn[i])>1 for i in range(M))
nx=[];ny=[]
for _ in range(2000):
    a,b=synth_gcd(); nx.append(a); ny.append(b)
nx=np.array(nx);ny=np.array(ny)
px=(1+((nx>=obsx).sum() if obsx>=np.median(nx) else (nx<=obsx).sum()))/(1+len(nx))
py=(1+((ny>=obsy).sum() if obsy>=np.median(ny) else (ny<=obsy).sum()))/(1+len(ny))
print("\nPart 3  gcd(.,n)>1 'Type B' count vs matched reference (two-sided-ish):")
print(f"    gcd(X,n)>1: chosen={obsx}  ref-med={np.median(nx):.0f}  p={px:.3f}")
print(f"    gcd(Y,n)>1: chosen={obsy}  ref-med={np.median(ny):.0f}  p={py:.3f}")
print("\nAny '<< signal' or exact-hit spike = the pipeline stage-2 (n->k) exists. Pull it.")
