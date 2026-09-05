#!/usr/bin/env python3
"""
n/k leak harness v1  (2026-07-06)
=================================
Honest, controlled test of whether PUBLIC data (X, Y, bits) leaks the Farey
denominator n (or k) of the puzzle construction  d = 2^(N-1) + floor(2^(N-1)*k/n) + D.

Design principles (the "method" the user asked to keep):
  * Every distinguisher gets a PERMUTATION NULL -> a number means nothing without it.
  * A PLANTED-LEAK POSITIVE CONTROL must fire, or the harness is untrustworthy.
  * Bounded phrasing: we report "advantage <= X at N" ; never "no leak".
  * Features use ONLY public quantities (X, Y, bits). Never n, k, d, D.

What is smart here (not a grab-bag):
  On this CONSTRUCTED set, (n,k,D) is a deterministic function of d, so the
  marginals of n / D_terms / Y-parity are fixed by how d was sampled -- they can
  only leak via a biased sampler (tested in Part C against a matched null).
  Any genuine PER-KEY advantage must live in the (X,Y)->n map -> Part B is the
  high-power ML ceiling on exactly that map.

Usage:
    python3 nk_leak_harness_v1.py --csv constructed_keys_1to160_100k.csv --sample 40000
"""
import argparse, math, random
from fractions import Fraction
import numpy as np
import pandas as pd
from sympy import isprime, totient

# ---------- secp256k1 ----------
P  = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F
Nord = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141
Gx = 0x79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798
Gy = 0x483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8

def ec_add(A, B):
    if A is None: return B
    if B is None: return A
    x1,y1=A; x2,y2=B
    if x1==x2 and (y1+y2)%P==0: return None
    if A==B: l=(3*x1*x1)*pow(2*y1,-1,P)%P
    else:    l=(y2-y1)*pow(x2-x1,-1,P)%P
    x3=(l*l-x1-x2)%P; y3=(l*(x1-x3)-y1)%P
    return (x3,y3)

def ec_mul(k, Pt=(Gx,Gy)):
    R=None
    while k:
        if k&1: R=ec_add(R,Pt)
        Pt=ec_add(Pt,Pt); k>>=1
    return R

# ---------- construction (matches memory: u=(d-A)/A, best rational n<=256) ----------
def decompose(d, bits, max_den=256):
    A = 1 << (bits-1)
    u = Fraction(d - A, A)                 # exact position in band, in [0,1)
    f = u.limit_denominator(max_den)       # best rational approx, denom <= 256
    n, k = f.denominator, f.numerator
    base = A + (A*k)//n
    D = d - base
    return n, k, D

# ---------- public feature battery (X, Y, bits ONLY) ----------
SMALL_Q = [3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97]
SWEEP_M = list(range(2, 65))               # Bucket-B candidate sweep: X mod m, Y mod m

def features(X, Y, bits):
    f = {"bits": bits, "Yparity": Y & 1,
         "popX": bin(X).count("1"), "popY": bin(Y).count("1"),
         "Xlow16": X & 0xFFFF, "Xhi16": X >> (X.bit_length()-16) if X.bit_length()>=16 else X,
         "Ylow16": Y & 0xFFFF, "Yhi16": Y >> (Y.bit_length()-16) if Y.bit_length()>=16 else Y}
    for q in SMALL_Q:
        f[f"Xm{q}"]=X%q; f[f"Ym{q}"]=Y%q; f[f"XYm{q}"]=(X*Y)%q; f[f"Xm{q}2"]=X%(q*q)
    for m in SWEEP_M:                       # the "Bucket B" sweep, folded in as features
        f[f"Xmod{m}"]=X%m; f[f"Ymod{m}"]=Y%m
    return f

# ---------- controlled evaluation ----------
def eval_target(Xmat, y, kind, planted=None, reps=15, seed=0):
    """Return (real_metric, null_mean, null_std, z). kind in {clf, top5, reg}."""
    from sklearn.ensemble import HistGradientBoostingClassifier as HGBC
    from sklearn.ensemble import HistGradientBoostingRegressor as HGBR
    from sklearn.model_selection import train_test_split
    rng = np.random.default_rng(seed)
    Xin = Xmat if planted is None else np.column_stack([Xmat, planted])

    def one(yv):
        Xtr,Xte,ytr,yte = train_test_split(Xin, yv, test_size=0.3, random_state=1)
        if kind=="reg":
            m=HGBR(max_iter=200,random_state=1).fit(Xtr,ytr)
            p=m.predict(Xte); ss=((yte-p)**2).sum(); tot=((yte-yte.mean())**2).sum()
            return 1-ss/tot                                   # R^2
        m=HGBC(max_iter=200,random_state=1).fit(Xtr,ytr)
        if kind=="top5":
            proba=m.predict_proba(Xte); cls=m.classes_
            top5=cls[np.argsort(proba,axis=1)[:,-5:]]
            return np.mean([yt in row for yt,row in zip(yte,top5)])
        return m.score(Xte,yte)                               # accuracy

    real = one(y)
    null=[]
    for r in range(reps):
        yp = y.copy(); rng.shuffle(yp); null.append(one(yp))
    null=np.array(null); mu,sd=null.mean(),null.std()+1e-12
    return real, mu, sd, (real-mu)/sd

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument("--csv", default="constructed_keys_1to160_100k.csv")
    ap.add_argument("--sample", type=int, default=40000)
    ap.add_argument("--seed", type=int, default=0)
    a=ap.parse_args()
    random.seed(a.seed); np.random.seed(a.seed)

    df = pd.read_csv(a.csv)
    df["Xi"]=df["X"].apply(lambda s:int(s,16)); df["Yi"]=df["Y"].apply(lambda s:int(s,16))
    print(f"loaded {len(df)} keys; bits {df.bits.min()}..{df.bits.max()}")

    # ---------- Part A: EC + decomposition validation gate ----------
    print("\n=== Part A: validation gate (must pass) ===")
    ok_ec=ok_dec=0; chk=df.sample(min(200,len(df)), random_state=a.seed)
    for _,r in chk.iterrows():
        Pt=ec_mul(int(r.d)); ok_ec += (Pt==(int(r.Xi),int(r.Yi)))
        n,k,D=decompose(int(r.d),int(r.bits)); ok_dec += (n==r.n and k==r.k and D==r.D)
    print(f"  EC reproduces (X,Y) from d:      {ok_ec}/{len(chk)}")
    print(f"  decompose() reproduces (n,k,D):  {ok_dec}/{len(chk)}")
    if ok_ec<len(chk) or ok_dec<len(chk):
        print("  GATE FAILED -- fix before trusting any result below.");
    else:
        print("  GATE PASSED")

    # ---------- build features on a diverse sample ----------
    s=df.sample(min(a.sample,len(df)), random_state=a.seed).reset_index(drop=True)
    feats=[features(int(x),int(y),int(b)) for x,y,b in zip(s.Xi,s.Yi,s.bits)]
    Fdf=pd.DataFrame(feats); Xmat=Fdf.values.astype(float)
    print(f"\nfeature matrix: {Xmat.shape[0]} keys x {Xmat.shape[1]} public features")

    # ---------- Part B: (X,Y)->n MAP  (the load-bearing test) ----------
    print("\n=== Part B: does the public (X,Y) map leak n? (perm-null controlled) ===")
    # positive control: planted noisy copy of (n mod 5); pipeline MUST detect it
    planted=((s.n.values%5)+np.random.randint(0,2,len(s))*5%5).reshape(-1,1).astype(float)
    tgt_ctrl=(s.n.values%5)
    r,mu,sd,z=eval_target(Xmat,tgt_ctrl,"clf",planted=planted,seed=a.seed)
    print(f"  [POSITIVE CONTROL] n mod 5 w/ planted feature: acc={r:.3f} null={mu:.3f}±{sd:.3f}  z={z:+.1f}  (MUST be large)")

    targets=[("n exact (top-1)","clf",s.n.values),
             ("n exact (top-5)","top5",s.n.values),
             ("n is prime","clf",s.n.apply(lambda v:int(isprime(int(v)))).values),
             ("n < 16","clf",(s.n.values<16).astype(int)),
             ("log2(n) [R^2]","reg",np.log2(s.n.values.astype(float)))]
    for name,kind,y in targets:
        r,mu,sd,z=eval_target(Xmat,y,kind,seed=a.seed)
        adv=r-mu
        print(f"  {name:22s}: real={r:.4f}  null={mu:.4f}±{sd:.4f}  advantage={adv:+.4f}  z={z:+.2f}")

    # ---------- Part C: selection / marginal stats vs matched null ----------
    print("\n=== Part C: sampler-selection stats vs matched-uniform null ===")
    # matched null: uniform random d in the SAME per-bit multiset, real decomposition
    counts=df.bits.value_counts().to_dict()
    null_n=[]; null_prime=0; null_tot=0
    for bits,c in counts.items():
        A=1<<(bits-1); hi=1<<bits
        for _ in range(min(c,2000)):                 # cap per band for speed
            d=random.randrange(A,hi); n,_,_=decompose(d,bits)
            null_n.append(n); null_prime+=isprime(n); null_tot+=1
    obs_prime=df.n.apply(lambda v:isprime(int(v))).mean()
    print(f"  P(n prime):  observed={obs_prime:.4f}   matched-null={null_prime/null_tot:.4f}  (watch-item; z needs the null SD)")
    obs_dt=df.D_terms.value_counts(normalize=True).sort_index()
    print(f"  D_terms dist (observed): {dict(obs_dt.round(3))}")
    print(f"  Y-parity rate observed:  {(df.Yi.values&1).mean():.4f}  (0.5 = unbiased)")

    print("\n--- bounded conclusion ---")
    print("  Report each Part-B advantage as 'distinguishing advantage <= (real-null) at N=%d'." % len(s))
    print("  A target is a lead ONLY if z is large AND it survives a fresh seed + bigger sample.")

if __name__=="__main__":
    main()
