import numpy as np, pandas as pd, zlib, random
from fractions import Fraction
from sklearn.metrics import mutual_info_score
from sympy import n_order
random.seed(0)
P=0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F
df=pd.read_csv("constructed_keys_1to160_100k.csv", dtype={"D":str})
df["Xi"]=df.X.apply(lambda s:int(s,16)); df["Yi"]=df.Y.apply(lambda s:int(s,16))
df["Dabs"]=[abs(int(v)) for v in df.D]; df["Dsign"]=[np.sign(int(v)) for v in df.D]
s=df.sample(6000,random_state=0).reset_index(drop=True)
rng=np.random.default_rng(0)
def mi_adj(x,y):
    x=np.asarray(x); y=np.asarray(y)
    r=mutual_info_score(x,y); nu=np.mean([mutual_info_score(x,rng.permutation(y)) for _ in range(5)])
    return r-nu
def binq(a,nb=16):
    a=np.asarray(a,float); return np.clip((a-a.min())/(np.ptp(a)+1e-9)*nb,0,nb-1).astype(int)

# ---------- PUBLIC quantities vs n (all from X,Y only) ----------
X=s.Xi.values; Y=s.Yi.values; n=s.n.values
def cf_maxpq(x,d,terms=10):
    a=[]; f=Fraction(int(x),int(d))
    for _ in range(terms):
        w=f.__floor__(); a.append(w); f=f-w
        if f==0: break
        f=1/f
    return max(a[1:]) if len(a)>1 else 0
feats={
 "hamming(X)":      [bin(int(v)).count("1") for v in X],
 "hamming(Y)":      [bin(int(v)).count("1") for v in Y],
 "chi3(X)cls":      [pow(int(v),(P-1)//3,P)%3 for v in X],
 "chi2(X)":         [pow(int(v),(P-1)//2,P) for v in X],
 "X mod 9":         [int(v)%9 for v in X],
 "X mod 25":        [int(v)%25 for v in X],
 "X mod 27":        [int(v)%27 for v in X],
 "zlib(X||Y) ratio":binq([len(zlib.compress(int(v).to_bytes(32,'big')+int(w).to_bytes(32,'big')))/64 for v,w in zip(X,Y)]),
 "maxPQ cf(X/p)":   binq([cf_maxpq(v,P) for v in X]),
 "(X^2+Y^3) mod 7": [(int(v)*int(v)+int(w)**3)%7 for v,w in zip(X,Y)],
 "X mod 7 (q^1)":   [int(v)%7 for v in X],
 "X mod 49 (q^2)":  [int(v)%49 for v in X],
 "X mod 343 (q^3)": [int(v)%343 for v in X],
}
print("=== PUBLIC quantity vs n : MI - null (nat), ranked (candidate hints) ===")
rows=[(k, mi_adj(v,n)) for k,v in feats.items()]
for k,adv in sorted(rows,key=lambda r:-r[1]):
    print(f"  {k:18s} adjMI={adv:+.5f}")

# ---------- formal-group intent: does X mod q^k correlate MORE with D as k grows? ----------
print("\n=== X mod q^k vs |D| bits (does higher p-adic digit track D?) [public X, known D] ===")
Dbl=np.array([int(v).bit_length() for v in s.Dabs])
for q in (7,):
    for kk in (1,2,3):
        adv=mi_adj([int(v)%(q**kk) for v in X], binq(Dbl))
        print(f"  X mod {q}^{kk} vs bitlen|D|: adjMI={adv:+.5f}")

# ---------- necessary-condition (known d): bit-autocorr of d at lag ord_n(2) ----------
print("\n=== d-bit autocorrelation at lag ord_n(2) vs random lags [known d, necessary cond] ===")
sub=s[(s.n%2==1)&(s.n>2)].sample(min(800,len(s[(s.n%2==1)&(s.n>2)])),random_state=0)
diffs=[]
for _,r in sub.iterrows():
    nn=int(r.n)
    try: L=int(n_order(2,nn))
    except Exception: continue
    d=int(r.d); bl=d.bit_length()
    if L<2 or L>=bl-4: continue
    bits=np.array([(d>>i)&1 for i in range(bl)])
    def ac(lag): 
        a=bits[:-lag]-0.5; b=bits[lag:]-0.5; return float(np.mean(a*b))
    rl=[ac(random.randint(2,bl-4)) for _ in range(6)]
    diffs.append(ac(L)-np.mean(rl))
diffs=np.array(diffs)
print(f"  keys used={len(diffs)} ; mean[ac(ord_n(2)) - ac(random)]={diffs.mean():+.5f} ; t={diffs.mean()/(diffs.std()/np.sqrt(len(diffs))+1e-12):+.2f}")

# ---------- Y-parity vs sign(D) conditioned on CF-convergent parity of k/n ----------
print("\n=== Y-parity vs sign(D), conditioned on convergent parity of k/n [known n,k,D] ===")
def cfparity(k,n):
    a=[]; f=Fraction(int(k),int(n)) if n>0 else Fraction(0)
    for _ in range(20):
        w=f.__floor__(); a.append(w); f=f-w
        if f==0: break
        f=1/f
    return len(a)%2
s2=s[s.n>=2].copy(); s2["cfpar"]=[cfparity(int(k),int(nn)) for k,nn in zip(s2.k,s2.n)]
for par in (0,1):
    g=s2[s2.cfpar==par]
    if len(g)<50: continue
    c=np.corrcoef((g.Yi.values&1), g.Dsign.values)[0,1]
    print(f"  CF-parity={par} (n={len(g)}): corr(Y&1, sign(D)) = {c:+.4f}")
print("\nDONE")
