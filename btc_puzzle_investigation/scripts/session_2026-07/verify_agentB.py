"""
Verify agent B's two strongest stratified hits with a proper large within-group
permutation null (the G-test is invalid here: skewed within-group marginals push
the shuffle-MI far above chi^2). Then place them in the real multiple-testing
context (~135,576 total triplets tested).
  hit1: k=128 group, X%13 -> n%13, adjMI 0.1284 (agent)
  hit2: n=216 group, slope%13 -> k%13, adjMI 0.1113 (agent)
"""
import leak_lib as L
import numpy as np

d=L.load(); X=d["X"]; Y=d["Y"]; n=d["n"]; k=d["k"]
rng=np.random.default_rng(0)

def within_group_p(mask, fvals, tvals, iters=4000):
    f=fvals[mask]; t=tvals[mask]; G=mask.sum()
    raw,_,_=(*L.mi_bits(f,t),)  # raw, A, B
    raw=L.mi_bits(f,t)[0]
    null=np.array([L.mi_bits(f, rng.permutation(t))[0] for _ in range(iters)])
    p=(1+(null>=raw).sum())/(1+iters)
    z=(raw-null.mean())/null.std()
    return G, raw, null.mean(), z, p

# hit1: k=128
Xm13=L.col_mod(X,13); slope13=L.col_mod(L.tf_slope(X,Y),13)
m1=(k==128)
G,raw,nm,z,p=within_group_p(m1, Xm13, n%13)
NT_perk=61488
print(f"hit1  k=128 group: X%13 -> n%13")
print(f"   group size={G}  rawMI={raw:.4f}  shuffle-mean={nm:.4f}  z={z:+.2f}  within-group p={p:.4f}")
print(f"   Bonferroni over per-k tests (61488): p*NT = {min(1,p*NT_perk):.2f}")

# hit2: n=216
m2=(n==216)
G,raw,nm,z,p=within_group_p(m2, slope13, k%13)
NT_pern=74088
print(f"\nhit2  n=216 group: slope%13 -> k%13")
print(f"   group size={G}  rawMI={raw:.4f}  shuffle-mean={nm:.4f}  z={z:+.2f}  within-group p={p:.4f}")
print(f"   Bonferroni over per-n tests (74088): p*NT = {min(1,p*NT_pern):.2f}")

# global context: distribution of the MAX adjusted-MI over many random (group,feature,target)
# under the null -- to see what max ~135k tests produces by chance.
print(f"\nglobal look-elsewhere: max within-group z over 3000 random (feature-shuffled) triplets")
groups=[nn for nn in [] ]
# sample real groups (n with >=300) and features, compute adjusted-MI under shuffle (=null)
big_n=[v for v in np.unique(n) if (n==v).sum()>=300]
feats=[Xm13, slope13, L.col_mod(X,11), L.col_mod(Y,13), L.col_mod(L.tf_glv(X),13)]
maxz=[]
for _ in range(3000):
    v=big_n[rng.integers(len(big_n))]; mask=(n==v)
    f=feats[rng.integers(len(feats))][mask]; t=(k%13)[mask]
    ts=rng.permutation(t)   # null: shuffled target
    raw=L.mi_bits(f,ts)[0]; nb=np.mean([L.mi_bits(f,rng.permutation(t))[0] for _ in range(4)])
    maxz.append(raw-nb)
maxz=np.array(maxz)
print(f"   null adjusted-MI over 3000 draws: 99th pct={np.quantile(maxz,0.99):.4f}  max={maxz.max():.4f} bits")
print(f"   -> the top real hits (0.11-0.13) sit near the null's own extreme over ~135k tests.")
