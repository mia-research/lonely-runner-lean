"""
PUBLIC -> (n,k,d) HINT HUNT, on the 82 REAL keys only. No synthetic keys.

Crux (v1 sec.2): can X, Y, or the joint XY channel give ANY hint about n, k, or
the key's position (top bits of d)? n is the lever: a hint about n collapses k to
phi(n) residues, fixes base, and drops the search ~8-9 bits.

Design:
  - 3 SEPARATE feature channels, exactly as framed: X-only, Y-only, XY-joint.
  - targets that are the actual hints worth having:
        n%2, n%3, n<128, position-quartile (top 2 bits of u),  <- n / d hints
        k%2, k%3                                               <- k hints
  - detector: best-feature mutual information within a channel + a permutation
    null (shuffle the target across the 82 keys). The perm null takes max over the
    SAME feature set, so it corrects the alphabet-size / small-sample MI bias.
  - CONTROL (mandatory): sweep a planted coupling of known strength on the
    position-quartile target; report the weakest coupling 82 samples can catch.
    That converts "no hint" into a sensitivity floor.

Control is real: the null is a permutation of the real targets; the population is
the real keys. Nothing is fabricated.
"""
import csv, math
import numpy as np

rows=[]
with open('/Users/trentpalelei/Desktop/Math Ex/btc_puzzle_investigation/puzzles_verified.csv') as f:
    for r in csv.DictReader(f):
        rows.append((int(r['bits']),int(r['private_key'],16),
                     int(r['X'],16),int(r['Y'],16),int(r['n']),int(r['k'])))
bits=np.array([b for b,_,_,_,_,_ in rows])
D  =[d for _,d,_,_,_,_ in rows]
Xs =[x for _,_,x,_,_,_ in rows]
Ys =[y for _,_,_,y,_,_ in rows]
ns =np.array([n for _,_,_,_,n,_ in rows])
ks =np.array([k for _,_,_,_,_,k in rows])
M=len(rows)
u=np.array([(d-2**(int(b)-1))/2**(int(b)-1) for b,d in zip(bits,D)])
print(f"{M} real keys loaded.")

_PR=(2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61)
def chan_features(vals, prefix):
    f={}
    for m in _PR: f[f"{prefix}%{m}"]=np.array([v%m for v in vals])
    for p in (3,5,7,11,13,17,19,23): f[f"{prefix}leg{p}"]=np.array([pow(v%p,(p-1)//2,p) for v in vals])
    for b in range(0,256,16): f[f"{prefix}b{b}"]=np.array([(v>>b)&1 for v in vals])
    f[f"{prefix}hw%4"]=np.array([bin(v).count('1')%4 for v in vals])
    f[f"{prefix}top4"]=np.array([v>>252 for v in vals])
    return f

Xf=chan_features(Xs,"X")
Yf=chan_features(Ys,"Y")
XYf={}
for m in _PR:
    XYf[f"XY%{m}"]=np.array([(x*y)%m for x,y in zip(Xs,Ys)])
    XYf[f"X+Y%{m}"]=np.array([(x+y)%m for x,y in zip(Xs,Ys)])
    XYf[f"Xeq Y%{m}"]=np.array([int((x%m)==(y%m)) for x,y in zip(Xs,Ys)])
for p in (3,5,7,11,13,17,19,23):
    XYf[f"XYleg{p}"]=np.array([pow((x*y)%p,(p-1)//2,p) for x,y in zip(Xs,Ys)])
channels={"X":Xf,"Y":Yf,"XY":XYf}

targets={
    "n%2":(ns%2), "n%3":(ns%3), "n<128":(ns<128).astype(int),
    "pos-quartile":np.floor(u*4).astype(int),
    "k%2":(ks%2), "k%3":(ks%3),
}

def mi(fcol,t):
    A=int(fcol.max())+1; B=int(t.max())+1
    j=np.zeros((A,B))
    for a,b in zip(fcol,t): j[a,b]+=1
    j/=j.sum(); pa=j.sum(1,keepdims=True); pb=j.sum(0,keepdims=True)
    with np.errstate(divide='ignore',invalid='ignore'):
        term=j*np.log2((j+1e-30)/(pa*pb+1e-30))
    return float(term[j>0].sum())

rng=np.random.default_rng(82)
def best_mi(feats,t):
    best=-1; arg=None
    for name,col in feats.items():
        v=mi(col,t)
        if v>best: best=v; arg=name
    return best,arg
def perm_p(feats,t,obs,iters=3000):
    c=1
    for _ in range(iters):
        tp=rng.permutation(t)
        v,_=best_mi(feats,tp)
        if v>=obs: c+=1
    return c/(iters+1)

print(f"\n{'target':>13} | {'channel':>3} | best-MI(bits) | perm-p | feature")
for tname,t in targets.items():
    for cname,feats in channels.items():
        obs,arg=best_mi(feats,t)
        p=perm_p(feats,t,obs,iters=2000)
        flag=" *" if p<0.05 else ""
        print(f"{tname:>13} | {cname:>3} |    {obs:6.4f}    | {p:5.3f}{flag} | {arg}")

print("\n=== CONTROL: detection floor at M=82 (planted coupling on pos-quartile) ===")
base=np.floor(u*4).astype(int)
for frac in [1.0,0.8,0.6,0.4,0.2]:
    # planted feature agrees with target on a fraction `frac` of keys, else random
    keep=rng.random(M)<frac
    planted=np.where(keep, base, rng.integers(0,4,M))
    obs=mi(planted,base)
    p=perm_p({"planted":planted},base,obs,iters=2000)
    print(f"  coupling frac={frac:.1f} : MI={obs:.4f} bits  perm-p={p:.3f}  {'DETECTED' if p<0.05 else 'below floor'}")

print("\nRead: any target/channel row with perm-p<0.05 (*) is a candidate hint;")
print("all others are null AT M=82 down to the coupling strength the control shows.")
