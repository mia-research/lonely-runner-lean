"""
REALLY LOOK at F1 under the correct success criterion: a HINT that narrows the
RANGE of k/n, not a significant 1-to-1 relationship. Report observations; declare
nothing.

Questions about the MEASUREMENT and PARAMETERS (not asked before):
  Q1 the feature (XY mod n^2)/n^2 has resolution n^2 -- COARSE for small n, FINE
     for large n. Pooling all 72 keys may DILUTE a real effect with coarse small-n
     keys. Does the correlation change if stratified by n?
  Q2 RANGE NARROWING: split keys by the feature; within each bin, what range does
     k/n occupy? How much of [0,1) does that cover vs the full marginal? (the hint)
  Q3 does it track k/n or the position u or the residual? (measurement target)
  Q4 dump the raw pairs for visual inspection.
"""
import csv
import numpy as np

rows=[]
with open('/Users/trentpalelei/Desktop/Math Ex/btc_puzzle_investigation/puzzles_verified.csv') as f:
    for r in csv.DictReader(f):
        if int(r['bits'])>=11 and int(r['n'])>=5:
            rows.append((int(r['bits']),int(r['X'],16),int(r['Y'],16),int(r['n']),int(r['k'])))
B=np.array([b for b,_,_,_,_ in rows]); X=[x for _,x,_,_,_ in rows]; Y=[y for _,_,y,_,_ in rows]
N=np.array([n for _,_,_,n,_ in rows]); K=np.array([k for _,_,_,_,k in rows]); M=len(rows)
feat=np.array([((X[i]*Y[i])%(int(N[i])**2))/(int(N[i])**2) for i in range(M)])
s=K/N
def spear(a,b):
    ra=np.argsort(np.argsort(a)).astype(float); rb=np.argsort(np.argsort(b)).astype(float)
    ra-=ra.mean(); rb-=rb.mean(); return (ra@rb)/(np.sqrt((ra@ra)*(rb@rb))+1e-30)

print(f"{M} keys. overall Spearman(feat, k/n) = {spear(feat,s):+.3f}")

print("\nQ1  stratify by n (feature resolution = n^2):")
for lab,mask in (("n< 64",N<64),("64<=n<160",(N>=64)&(N<160)),("n>=160",N>=160)):
    m=mask.sum()
    if m>3: print(f"    {lab:10s} (n_keys={m:2d}): Spearman={spear(feat[mask],s[mask]):+.3f}")

print("\nQ2  RANGE NARROWING -- does the feature restrict where k/n lives?")
order=np.argsort(feat)
print(f"    marginal k/n:  min={s.min():.3f} max={s.max():.3f} IQR=[{np.quantile(s,.25):.3f},{np.quantile(s,.75):.3f}]")
for lab,idx in (("low  feat tercile",order[:M//3]),
                ("mid  feat tercile",order[M//3:2*M//3]),
                ("high feat tercile",order[2*M//3:])):
    sk=s[idx]
    print(f"    {lab}: k/n median={np.median(sk):.3f}  IQR=[{np.quantile(sk,.25):.3f},{np.quantile(sk,.75):.3f}]  "
          f"range=[{sk.min():.3f},{sk.max():.3f}]")

print("\nQ2b hint value: predict k/n from feat (linear), measure conditional band width vs marginal")
# leave-one-out linear prediction + residual band
def loo_band():
    preds=[];
    for i in range(M):
        tr=[j for j in range(M) if j!=i]
        A=np.vstack([feat[tr],np.ones(len(tr))]).T
        b,_,_,_=np.linalg.lstsq(A,s[tr],rcond=None)
        preds.append(b[0]*feat[i]+b[1])
    preds=np.array(preds); resid=s-preds
    return preds, resid
preds,resid=loo_band()
band=2*resid.std()  # ~ conditional 95%-ish half-width
marg=2*s.std()
cover=np.mean(np.abs(resid)<=band)
print(f"    marginal 2-sigma half-width : {marg/2*2:.3f}  (covers all of ~[{s.mean()-marg:.2f},{s.mean()+marg:.2f}])")
print(f"    conditional (feat) half-width: {band:.3f}  LOO coverage={cover:.2f}")
print(f"    -> conditioning on feat shrinks the k/n search band by {100*(1-band/marg):.0f}% (LOO).")
# shuffle control for the shrink
rng=np.random.default_rng(0); sh=[]
for _ in range(2000):
    sf=rng.permutation(feat); pr=[]
    for i in range(M):
        tr=[j for j in range(M) if j!=i]
        A=np.vstack([sf[tr],np.ones(len(tr))]).T; b,_,_,_=np.linalg.lstsq(A,s[tr],rcond=None)
        pr.append(b[0]*sf[i]+b[1])
    sh.append(2*(s-np.array(pr)).std())
sh=np.array(sh); pshrink=(1+(sh<=band).sum())/(1+len(sh))
print(f"    shuffle-feat band: median={np.median(sh):.3f}; p(real band this tight)={pshrink:.3f}")

print("\nQ3  measurement target (Spearman of feat vs ...):")
u=s  # k/n ~ u; also raw
print(f"    vs k/n={spear(feat,s):+.3f}  vs raw k={spear(feat,K.astype(float)):+.3f}  "
      f"vs raw n={spear(feat,N.astype(float)):+.3f}")

print("\nQ4  raw pairs (feat, k/n, n) sorted by feat -- for the scatter:")
for i in order:
    print(f"    feat={feat[i]:.3f}  k/n={s[i]:.3f}  n={int(N[i]):3d}  k={int(K[i]):3d}")
