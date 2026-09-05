import math, random
from fractions import Fraction
from collections import Counter
import numpy as np, pandas as pd
from sympy import isprime
P=0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F
Nord=0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141
BETA=0x7AE96A2B657C07106E64479EAC3434E99CF0497512F58995C1396C28719501EE
LAMBDA=0x5363AD4CC05C30E0A5261C028812645A122E22EA20816678DF02967C1B23BD72
a1=0x3086D221A7D46BCDE86C90E49284EB15; b1=-0xE4437ED6010E88286F547FA90ABFE4C3
a2=0x114CA50F7A8E2F3F657C1108D9D44CFD8; b2=0x3086D221A7D46BCDE86C90E49284EB15
def decompose(d,bits,md=256):
    A=1<<(bits-1); f=Fraction(d-A,A).limit_denominator(md); n,k=f.denominator,f.numerator
    return n,k,d-(A+(A*k)//n)
def glv(d):
    c1=round(Fraction(b2*d,Nord)); c2=round(Fraction(-b1*d,Nord))
    d1=(d-c1*a1-c2*a2)%Nord; d2=(-c1*b1-c2*b2)%Nord
    if d1>Nord//2: d1-=Nord
    if d2>Nord//2: d2-=Nord
    return d1,d2
def clustering(pairs_by_n):
    er=[]
    for nn,pairs in pairs_by_n.items():
        if nn<2 or len(pairs)<30: continue
        c=Counter(pairs); pr=np.array(list(c.values()))/len(pairs)
        H=-(pr*np.log2(pr)).sum(); Hmax=2*math.log2(nn); er.append(H/Hmax)
    return np.mean(er),len(er)
df=pd.read_csv("constructed_keys_1to160_100k.csv")
df["Xi"]=df.X.apply(lambda s:int(s,16)); df["Yi"]=df.Y.apply(lambda s:int(s,16))
random.seed(0); np.random.seed(0)

print("=== Control 1: GLV clustering  constructed vs uniform-random d ===")
sg=df.sample(20000,random_state=0)
con={}
for _,r in sg.iterrows():
    d1,d2=glv(int(r.d)); nn=int(r.n); con.setdefault(nn,[]).append((d1%nn,d2%nn))
c_con,g_con=clustering(con)
ran={}
bands=df.bits.value_counts().to_dict(); made=0
while made<20000:
    bits=random.choices(list(bands),weights=list(bands.values()))[0]
    if bits<2: continue
    dd=random.randrange(1<<(bits-1),1<<bits); nn,kk,DD=decompose(dd,bits)
    d1,d2=glv(dd); ran.setdefault(nn,[]).append((d1%nn,d2%nn)); made+=1
c_ran,g_ran=clustering(ran)
print(f"  constructed d: H/Hmax={c_con:.4f} [{g_con} groups]")
print(f"  uniform-rand d: H/Hmax={c_ran:.4f} [{g_ran} groups]")
print(f"  => delta = {c_con-c_ran:+.4f}  (near 0 => generic GLV-mod-n line, NOT construction-specific)")

print("\n=== Control 2: n-prime deficit with PROPER null SE ===")
null_n=[]
for bits,cnt in df.bits.value_counts().items():
    A=1<<(bits-1); hi=1<<bits
    for _ in range(min(cnt,1500)):
        null_n.append(decompose(random.randrange(A,hi),bits)[0])
null_n=np.array(null_n); n=df.n.values
p0=np.mean([isprime(int(v)) for v in null_n]); pobs=np.mean([isprime(int(v)) for v in n])
se_obs=math.sqrt(pobs*(1-pobs)/len(n)); se_null=math.sqrt(p0*(1-p0)/len(null_n))
z=(pobs-p0)/math.sqrt(se_obs**2+se_null**2)
print(f"  observed={pobs:.4f} (SE {se_obs:.4f})  null={p0:.4f} (SE {se_null:.4f}, from {len(null_n)} draws)")
print(f"  z (both SEs) = {z:+.2f}")

print("\n=== Control 3: can PUBLIC (X,Y) predict sign(D) or D_terms? (seals the stage-1 pass) ===")
from sklearn.ensemble import HistGradientBoostingClassifier as C
from sklearn.model_selection import train_test_split
Q=[3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71]
s=df.sample(15000,random_state=0).reset_index(drop=True)
def kf(X,Y,b):
    f={"bits":b,"Yp":Y&1,"pX":bin(X).count("1")}
    for q in Q: f[f"X{q}"]=X%q; f[f"Y{q}"]=Y%q
    for m in range(2,48): f[f"Xs{m}"]=X%m
    return f
F=pd.DataFrame([kf(int(x),int(y),int(b)) for x,y,b in zip(s.Xi,s.Yi,s.bits)]).values.astype(float)
rng=np.random.default_rng(0)
def ceil(y,reps=6):
    def one(yv):
        a,b,c,d=train_test_split(F,yv,test_size=0.3,random_state=1)
        return C(max_iter=80,early_stopping=False,random_state=1).fit(a,c).score(b,d)
    r=one(y); nu=np.array([one(rng.permutation(y)) for _ in range(reps)])
    return r,nu.mean(),(r-nu.mean())/(nu.std()+1e-12)
for nm,y in [("sign(D)>0",(s.D.values>0).astype(int)),("D_terms",s.D_terms.values)]:
    r,mu,z=ceil(y); print(f"  public->{nm:9s}: acc={r:.4f} null={mu:.4f} adv={r-mu:+.4f} z={z:+.2f}")
print("\nDONE")
