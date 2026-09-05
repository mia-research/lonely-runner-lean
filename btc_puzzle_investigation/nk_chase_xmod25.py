import numpy as np, pandas as pd
from sklearn.metrics import mutual_info_score
P=0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F
df=pd.read_csv("constructed_keys_1to160_100k.csv", dtype={"D":str})
df["Xi"]=df.X.apply(lambda s:int(s,16)); df["Yi"]=df.Y.apply(lambda s:int(s,16))
df["Dbl"]=[abs(int(v)).bit_length() for v in df.D]; df["Dsign"]=[int(np.sign(int(v))) for v in df.D]

def mi_z(x,y,reps=40,seed=0):
    rng=np.random.default_rng(seed); x=np.asarray(x); y=np.asarray(y)
    r=mutual_info_score(x,y); nu=np.array([mutual_info_score(x,rng.permutation(y)) for _ in range(reps)])
    return r-nu.mean(), (r-nu.mean())/(nu.std()+1e-12)

print("=== CHASE X mod 25 -> n : proper null (40 shuffles), 2 seeds, pooled + within-band ===")
for seed in (0,1):
    s=df.sample(8000,random_state=seed)
    adv,z=mi_z([int(v)%25 for v in s.Xi],s.n.values,seed=seed)
    print(f"  seed{seed} pooled (8000): adjMI={adv:+.5f} z={z:+.2f}")
for bb in (130,150):
    sub=df[df.bits==bb]
    adv,z=mi_z([int(v)%25 for v in sub.Xi],sub.n.values)
    print(f"  within band bits={bb} (n={len(sub)}): adjMI={adv:+.5f} z={z:+.2f}")
# same for X mod 9 and chi3
for lab,q in [("X mod 9",9)]:
    s=df.sample(8000,random_state=0); adv,z=mi_z([int(v)%q for v in s.Xi],s.n.values)
    print(f"  {lab} pooled: adjMI={adv:+.5f} z={z:+.2f}")

print("\n=== CHASE X mod 7^2 -> bitlen|D| : proper z, 2 seeds, within-band ===")
def binq(a,nb=16):
    a=np.asarray(a,float); return np.clip((a-a.min())/(np.ptp(a)+1e-9)*nb,0,nb-1).astype(int)
for seed in (0,1):
    s=df.sample(8000,random_state=seed)
    adv,z=mi_z([int(v)%49 for v in s.Xi], binq(s.Dbl.values),seed=seed)
    print(f"  seed{seed} X mod49 vs |D|bits pooled: adjMI={adv:+.5f} z={z:+.2f}")
for bb in (130,150):   # within band, |D| bitlen nearly constant -> tests residual
    sub=df[df.bits==bb]
    adv,z=mi_z([int(v)%49 for v in sub.Xi], binq(sub.Dbl.values))
    print(f"  within band bits={bb}: adjMI={adv:+.5f} z={z:+.2f}")

print("\n=== FIX Y-parity vs sign(D) by CF convergent parity (drop D==0) ===")
from fractions import Fraction
def cfpar(k,n):
    a=[];f=Fraction(int(k),int(n))
    for _ in range(20):
        w=f.__floor__();a.append(w);f=f-w
        if f==0:break
        f=1/f
    return len(a)%2
s2=df[(df.n>=2)&(df.Dsign!=0)].sample(20000,random_state=0)
s2=s2.assign(cfpar=[cfpar(int(k),int(nn)) for k,nn in zip(s2.k,s2.n)])
for par in (0,1):
    g=s2[s2.cfpar==par]
    yp=(g.Yi.values&1).astype(float); ds=g.Dsign.values.astype(float)
    c=np.corrcoef(yp,ds)[0,1]
    print(f"  CF-parity={par} (n={len(g)}): corr(Y&1, sign(D))={c:+.4f}")
print("\nDONE")
