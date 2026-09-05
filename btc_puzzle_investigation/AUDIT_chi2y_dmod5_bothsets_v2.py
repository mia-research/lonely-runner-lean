#!/usr/bin/env python3
"""v2: permutation for the small 82; G-test (closed-form even-dof chi2 SF) for
the high-power constructed set. Tests whether chi2(y)->d mod 5 (the buried
secp-82 positive) reproduces on the matched known-generator pipeline."""
import csv, math, random, sys
from collections import Counter

P = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F
pr = lambda *a: print(*a, flush=True)

def chi2y(y): return 0 if pow(y, (P - 1) // 2, P) == 1 else 1
def H(c, N): return -sum((v/N)*math.log2(v/N) for v in c.values() if v)
def mi(xs, ts):
    N=len(xs); return H(Counter(xs),N)+H(Counter(ts),N)-H(Counter(zip(xs,ts)),N)

def perm_p(xs, ts, R, seed):
    obs=mi(xs,ts); rng=random.Random(seed); t=list(ts); ge=0; vs=[]
    for _ in range(R):
        rng.shuffle(t); v=mi(xs,t); vs.append(v)
        if v>=obs-1e-15: ge+=1
    mu=sum(vs)/R; sd=(sum((v-mu)**2 for v in vs)/R)**0.5
    return obs,(ge+1)/(R+1),((obs-mu)/sd if sd else 0.0)

def chi2_sf_even(x, dof):
    """P(X>x) for even dof: e^{-x/2} sum_{i=0}^{dof/2 -1} (x/2)^i / i!."""
    k=dof//2; h=x/2.0; s=0.0; term=1.0
    for i in range(k):
        if i>0: term*=h/i
        s+=term
    return math.exp(-h)*s

def gtest(xs, ts):
    N=len(xs); rows=sorted(set(xs)); cols=sorted(set(ts))
    obs={}; rt=Counter(xs); ct=Counter(ts)
    for a,b in zip(xs,ts): obs[(a,b)]=obs.get((a,b),0)+1
    G=0.0
    for a in rows:
        for b in cols:
            O=obs.get((a,b),0); E=rt[a]*ct[b]/N
            if O>0 and E>0: G+=2*O*math.log(O/E)
    dof=(len(rows)-1)*(len(cols)-1)
    p=chi2_sf_even(G,dof) if dof%2==0 else float('nan')
    return G,dof,p,mi(xs,ts)

def load(path,dcol,ycol,limit=None):
    ds,ys=[],[]
    with open(path,newline="") as f:
        for i,r in enumerate(csv.DictReader(f)):
            if limit and i>=limit: break
            d=(r.get(dcol) or r.get("private_key") or "").strip()
            y=(r.get(ycol) or "").strip()
            if not d or not y: continue
            if d.lower().startswith("0x"): d=int(d,16)
            elif len(d)>12 and any(c in "abcdefABCDEF" for c in d): d=int(d,16)
            else: d=int(d)
            ds.append(d); ys.append(int(y,16))
    return ds,ys

if __name__=="__main__":
    ds,ys=load("solved_puzzles_xy.csv","private_key","Y")
    fs=[chi2y(y) for y in ys]; N=len(ds)
    pr(f"\n### REAL secp-82  N={N}  Pr[chi2y=1]={sum(fs)/N:.4f}  (permutation R=50000)")
    for m in (3,5,7):
        obs,p,z=perm_p(fs,[d%m for d in ds],50000,999+m)
        pr(f"  chi2y -> d mod {m}:  MI={obs:.5f}  perm_p={p:.4f}  z={z:+.2f}{'  <--' if p<0.01 else ''}")
    for lim in (20000,100000):
        dc,yc=load("constructed_keys_1to160_100k_exact.csv","d","Y",limit=lim)
        fc=[chi2y(y) for y in yc]; Nc=len(dc)
        pr(f"\n### CONSTRUCTED known-generator (matched pipeline) first {lim}  N={Nc}  Pr[chi2y=1]={sum(fc)/Nc:.4f}  (G-test)")
        for m in (3,5,7):
            G,dof,p,I=gtest(fc,[d%m for d in dc])
            pr(f"  chi2y -> d mod {m}:  MI={I:.6f}  G={G:.3f} dof={dof}  p={p:.4g}{'  <--' if p<0.01 else ''}")
        # contingency for d mod 5
        ts5=[d%5 for d in dc]; tab={(f,t):0 for f in(0,1) for t in range(5)}
        for f,t in zip(fc,ts5): tab[(f,t)]+=1
        pr("  d mod 5 contingency (col=residue 0..4):")
        for f in (0,1):
            row=[tab[(f,t)] for t in range(5)]; tot=sum(row) or 1
            pr(f"    chi2y={f}: {row}  props={[round(c/tot,4) for c in row]}")
