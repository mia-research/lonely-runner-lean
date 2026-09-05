import numpy as np, math, random
p = 2**256 - 2**32 - 977
n = 115792089237316195423570985008687907852837564279074904382605163141518161494337
Gx = 0x79be667ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f2815b16f81798
Gy = 0x483ada7726a3c4655da4fbfc0e1108a8fd17b448a68554199c47d08ffb10d4b8
beta= 0x7ae96a2b657c07106e64479eac3434e99cf0497512f58995c1396c28719501ee
def inv(a,m):return pow(a,-1,m)
def add(P,Q):
    if P is None:return Q
    if Q is None:return P
    x1,y1=P;x2,y2=Q
    if x1==x2 and (y1+y2)%p==0:return None
    m=((3*x1*x1)*inv(2*y1,p) if P==Q else (y2-y1)*inv((x2-x1)%p,p))%p
    x3=(m*m-x1-x2)%p;return (x3,(m*(x1-x3)-y1)%p)
def mul(k,P):
    R=None;Q=P
    while k>0:
        if k&1:R=add(R,Q)
        Q=add(Q,Q);k>>=1
    return R
G=(Gx,Gy)
def chi3(x):
    v=pow(x%p,(p-1)//3,p)
    for j in range(3):
        if pow(beta,j,p)==v:return j
def MI(feat,truth):
    from collections import Counter
    N=len(feat);cf=Counter(feat);ct=Counter(truth);cft=Counter(zip(feat,truth));mi=0.0
    for (f,t),c in cft.items():
        pft=c/N;mi+=pft*math.log2(pft/((cf[f]/N)*(ct[t]/N)))
    return mi
def run(lo,hi,N,seed,label):
    r=random.Random(seed)
    d3=[];d2=[];d6=[];j3=[];yp=[]
    for _ in range(N):
        d=r.randrange(lo,hi);P=mul(d,G);x,y=P
        d3.append(d%3);d2.append(d%2);d6.append(d%6);j3.append(chi3(x));yp.append(y&1)
    feat6=list(zip(j3,yp))
    # real MI vs permutation-null MI (mean+std over 20 shuffles)
    def nullMI(feat,truth,reps=20):
        vals=[]
        for k in range(reps):
            t2=truth[:];r.shuffle(t2);vals.append(MI(feat,t2))
        return np.mean(vals),np.std(vals)
    print(f"\n{label} (N={N}):  [real MI vs shuffle-null MI floor]")
    for fname,feat,truth,ch in [("chi3->d%3",j3,d3,3),("ypar->d%2",yp,d2,2),("(chi3,ypar)->d%6",feat6,d6,6)]:
        rmi=MI(feat,truth); nm,ns=nullMI(feat,truth)
        z=(rmi-nm)/ns if ns>0 else 0
        print(f"  {fname:20s}: real={rmi:.5f}  null={nm:.5f}±{ns:.5f}  z={z:+.2f}  {'<-- signal' if z>4 else 'no signal'}")
run(1,n,6000,1,"FULL-RANGE d in [1,n)")
run(2**134,2**135,6000,2,"PUZZLE-135 range d in [2^134,2^135)")
print("\nNote: a real 'd mod 6' extraction (the claimed 2.585-bit reduction) needs MI ~ 2.585 bits.")
