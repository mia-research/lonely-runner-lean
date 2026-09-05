"""
Stress-test the one flicker from real_hint_hunt.py: k%2 <- XY channel
(winning feature X+Y mod 53), perm-p=0.013 uncorrected.

Three questions:
  1. Multiple testing: 18 target x channel combos were scanned. Bonferroni.
  2. Stability: jackknife (drop each of the 82 keys) the single-feature MI and
     its perm-p. A real coupling is stable; a flicker is driven by a few keys.
  3. Reproducibility: does the perm-p hold under independent RNG seeds?
"""
import csv
import numpy as np

rows=[]
with open('/Users/trentpalelei/Desktop/Math Ex/btc_puzzle_investigation/puzzles_verified.csv') as f:
    for r in csv.DictReader(f):
        rows.append((int(r['X'],16),int(r['Y'],16),int(r['k'])))
X=np.array([x for x,_,_ in rows],dtype=object)
Y=np.array([y for _,y,_ in rows],dtype=object)
k=np.array([kk for _,_,kk in rows])
M=len(rows)

feat=np.array([(int(x)+int(y))%53 for x,y in zip(X,Y)])   # X+Y mod 53
tgt =(k%2)

def mi(f,t):
    A=int(f.max())+1;B=int(t.max())+1;j=np.zeros((A,B))
    for a,b in zip(f,t): j[a,b]+=1
    j/=j.sum();pa=j.sum(1,keepdims=True);pb=j.sum(0,keepdims=True)
    with np.errstate(divide='ignore',invalid='ignore'):
        term=j*np.log2((j+1e-30)/(pa*pb+1e-30))
    return float(term[j>0].sum())

def single_perm_p(f,t,iters,seed):
    rng=np.random.default_rng(seed)
    obs=mi(f,t);c=1
    for _ in range(iters):
        if mi(f,rng.permutation(t))>=obs: c+=1
    return obs,c/(iters+1)

obs,p=single_perm_p(feat,tgt,20000,1)
print("=== the flicker: k%2 <- (X+Y mod 53) ===")
print(f"single-feature MI={obs:.4f} bits   perm-p(20k)={p:.4f}")
print(f"[1] multiple testing: 18 combos scanned -> Bonferroni p = {min(1.0,p*18):.3f}")

print("\n[3] reproducibility across seeds:")
for s in (2,3,4,5):
    _,ps=single_perm_p(feat,tgt,20000,s); print(f"    seed {s}: perm-p={ps:.4f}")

print("\n[2] jackknife (drop one key): single-feature MI + perm-p")
mis=[];ps=[]
for i in range(M):
    m=np.ones(M,bool);m[i]=False
    o,pp=single_perm_p(feat[m],tgt[m],3000,100+i)
    mis.append(o);ps.append(pp)
mis=np.array(mis);ps=np.array(ps)
print(f"    MI     : full={obs:.4f}  jackknife min={mis.min():.4f} max={mis.max():.4f}")
print(f"    perm-p : jackknife min={ps.min():.4f} max={ps.max():.4f}  "
      f"(#drops with p>0.05: {(ps>0.05).sum()}/{M})")
worst=int(np.argmax(ps))
print(f"    dropping puzzle-index {worst} pushes p to {ps[worst]:.4f} "
      f"-> {'fragile (few-key artifact)' if ps.max()>0.05 else 'stable'}")
