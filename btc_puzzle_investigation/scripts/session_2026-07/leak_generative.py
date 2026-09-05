"""
GENERATIVE HUNT: assume n and/or k IS recoverable from X and/or Y. Find it.

Search is deliberately aggressive (big feature bag, many targets). Honesty is
enforced downstream: every candidate must survive HELD-OUT validation (predict on
keys it never saw) or an EXACT-relation check (deterministic on all 82). The bias
of "look for a leak" is thus paid back by an out-of-sample filter that a wishful
signal cannot pass.

PART A  exact / near-exact algebraic relation scan
        For each feature f and target t, conditional entropy H(t|f). H=0 => f
        determines t exactly (a construction break, needs no statistics). Low-H
        with big alphabet = overfitting -> must clear PART B.
PART B  held-out single-feature validation
        Select best feature on a train split, score its MI on held-out keys.
        Real leak: held-out MI above the label-permuted null. Artifact: collapses.

Channels cover "x and/or y": X, Y, X+Y, X-Y, X*Y, and the GLV image beta*X.
"""
import csv, math
import numpy as np

P  = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F
BETA=0x7ae96a2b657c07106e64479eac3434e99cf0497512f58995c1396c28719501ee  # GLV cube root

rows=[]
with open('/Users/trentpalelei/Desktop/Math Ex/btc_puzzle_investigation/puzzles_verified.csv') as f:
    for r in csv.DictReader(f):
        rows.append((int(r['bits']),int(r['private_key'],16),
                     int(r['X'],16),int(r['Y'],16),int(r['n']),int(r['k'])))
bitsA=[b for b,_,_,_,_,_ in rows]; Dk=[d for _,d,_,_,_,_ in rows]
Xs=[x for _,_,x,_,_,_ in rows]; Ys=[y for _,_,_,y,_,_ in rows]
n=np.array([nn for _,_,_,_,nn,_ in rows]); k=np.array([kk for _,_,_,_,_,kk in rows]); M=len(rows)
bX=[(BETA*x)%P for x in Xs]

# ---------- feature bag ----------
feat={}
def add_mod(name, vals):
    for m in list(range(2,49))+[53,59,61,64,81,97,128,127,251,256]:
        feat[f"{name}%{m}"]=np.array([int(v)%m for v in vals])
add_mod("X",Xs); add_mod("Y",Ys)
add_mod("X+Y",[x+y for x,y in zip(Xs,Ys)])
add_mod("X-Y",[x-y for x,y in zip(Xs,Ys)])
add_mod("XY", [x*y for x,y in zip(Xs,Ys)])
add_mod("bX", bX)                                  # GLV endomorphism image
for p in (3,5,7,11,13,17,19,23,29,31,37,41,43):
    feat[f"Xjac{p}"]=np.array([pow(int(x)%p,(p-1)//2,p) for x in Xs])
    feat[f"Yjac{p}"]=np.array([pow(int(y)%p,(p-1)//2,p) for y in Ys])
for b in range(0,256,8):
    feat[f"Xb{b}"]=np.array([(int(x)>>b)&1 for x in Xs])
    feat[f"Yb{b}"]=np.array([(int(y)>>b)&1 for y in Ys])
fnames=list(feat); print(f"feature bag: {len(fnames)} features from X,Y,X+Y,X-Y,XY,betaX")

u=np.array([(d-2**(b-1))/2**(b-1) for b,d in zip(bitsA,Dk)])
targets={
    "n":n, "k":k,
    "n%6":n%6, "n%8":n%8, "k%6":k%6, "k%8":k%8,
    "pos-3bit":np.clip((u*8).astype(int),0,7),
}

def cond_entropy(f,t):
    """H(t|f) in bits, and the max within-f purity (1.0 => deterministic)."""
    vals={}
    for a,b in zip(f,t): vals.setdefault(a,[]).append(b)
    H=0.0; Ntot=len(t); purity_min=1.0
    for a,bl in vals.items():
        bl=np.array(bl); w=len(bl)/Ntot
        _,cnts=np.unique(bl,return_counts=True); pr=cnts/cnts.sum()
        H+= w*(-(pr*np.log2(pr)).sum())
        purity_min=min(purity_min, cnts.max()/cnts.sum())
    return H, purity_min

print("\n=== PART A: exact / near-exact relation scan (min H(t|f) per target) ===")
for tn,t in targets.items():
    best=(9e9,None,None)
    for fn in fnames:
        H,pur=cond_entropy(feat[fn],t)
        # penalize trivial determinism from huge alphabets: require alphabet<=M/2
        if len(np.unique(feat[fn]))<=M/2 and H<best[0]:
            best=(H,fn,pur)
    print(f"  {tn:>9}: min H(t|f)={best[0]:.3f} bits via {best[1]}  (worst-cell purity {best[2]:.2f})"
          f"{'   << EXACT' if best[0]<1e-9 else ''}")

# ---------- PART B: held-out single-feature validation ----------
def mi(f,t):
    if len(f)==0: return 0.0
    A=int(f.max())+1;B=int(t.max())+1;j=np.zeros((A,B))
    for a,b in zip(f,t): j[a,b]+=1
    s=j.sum()
    if s==0: return 0.0
    j/=s;pa=j.sum(1,keepdims=True);pb=j.sum(0,keepdims=True)
    with np.errstate(divide='ignore',invalid='ignore'):
        term=j*np.log2((j+1e-30)/(pa*pb+1e-30))
    return float(term[j>0].sum())
def oos(t,rng,nsplit=250):
    sc=[]
    for _ in range(nsplit):
        perm=rng.permutation(M); a=perm[:55]; b=perm[55:]
        best=-1;arg=None
        for fn in fnames:
            v=mi(feat[fn][a],t[a])
            if v>best: best=v;arg=fn
        sc.append(mi(feat[arg][b],t[b]))
    return float(np.mean(sc)),arg
rng=np.random.default_rng(99)
print("\n=== PART B: held-out validation (real leak survives, artifact collapses) ===")
for tn,t in targets.items():
    obs,arg=oos(t,rng)
    null=np.array([oos(rng.permutation(t),rng,80)[0] for _ in range(30)])
    p=(1+(null>=obs).sum())/(1+len(null))
    print(f"  {tn:>9}: held-out MI={obs:.4f}  null={null.mean():.4f} (95pct {np.quantile(null,.95):.4f})"
          f"  p={p:.3f}{'  << SURVIVES' if p<0.05 else ''}")

print("\nAny EXACT in A, or any SURVIVES in B, is a real candidate -> escalate.")
print("Otherwise the live leak (if present) is below single-feature+82-sample power")
print("-> next moves: learned multivariate model, and the selection-sequence PRNG.")
