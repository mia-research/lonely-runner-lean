# Does d leak from PUBLIC orbit-coordinate + carry features of P=[d]G?
# Exact arithmetic. Firing control = shuffle. Target: low bits of d (and GLV half d1).
import random

p = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F
n = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141
Gx = 0x79be667ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f2815b16f81798
Gy = 0x483ada7726a3c4655da4fbfc0e1108a8fd17b448a68554199c47d08ffb10d4b8
G=(Gx,Gy)
def inv(a,m): return pow(a,-1,m)
def padd(P,Q):
    if P is None: return Q
    if Q is None: return P
    x1,y1=P;x2,y2=Q
    if x1==x2 and (y1+y2)%p==0: return None
    if P==Q: lam=(3*x1*x1)*inv(2*y1,p)%p
    else: lam=(y2-y1)*inv((x2-x1)%p,p)%p
    x3=(lam*lam-x1-x2)%p; y3=(lam*(x1-x3)-y1)%p
    return (x3,y3)
def mul(k,P):
    R=None;Q=P;k%=n
    while k>0:
        if k&1: R=padd(R,Q)
        Q=padd(Q,Q);k>>=1
    return R
beta=pow(3,(p-1)//3,p); b2=(beta*beta)%p
def chi3_idx(x):
    t=pow(x%p,(p-1)//3,p)
    return {1:0,beta:1,b2:2}[t]
def legendre(a):
    a%=p
    return 0 if a==0 else (1 if pow(a,(p-1)//2,p)==1 else -1)

# GLV lattice decomposition d = d1 + d2*lam (mod n), d1,d2 ~ sqrt(n). Public constants a1,b1,a2,b2g.
lam=pow(2,(n-1)//3,n)
if mul(lam,G)!=((beta*Gx)%p,Gy): lam=(lam*lam)%n
# standard secp GLV basis (Babai rounding uses these public constants)
a1=0x3086d221a7d46bcde86c90e49284eb15
b1=-0xe4437ed6010e88286f547fa90abfe4c3
a2=0x114ca50f7a8e2f3f657c1108d9d44cfd8
b2g=0x3086d221a7d46bcde86c90e49284eb15
def glv_decompose(k):
    # returns (d1,d2) with k = d1 + d2*lam mod n, via Babai rounding
    c1=(b2g*k)//n
    c2=(-b1*k)//n
    d1=(k - (c1*a1 + c2*a2))%n
    d2=(-(c1*b1 + c2*b2g))%n
    # center
    if d1> n//2: d1-=n
    if d2> n//2: d2-=n
    return d1,d2

def features(P):
    x,y=P
    Px=((beta*x)%p,y)      # phi P
    Px2=((b2*x)%p,y)
    f=[]
    f.append(chi3_idx(x))            # orbit coord (mu3 class of x)  -- the "orbit coordinate"
    f.append(legendre(y))            # chi2(y)
    f.append(x & 1)                  # low bit x  ("carry"-like)
    f.append(y & 1)                  # low bit y
    f.append((x>>1)&1); f.append((y>>1)&1)
    f.append(chi3_idx(Px[0]))        # redundant (=f0+1 mod3) but include
    f.append(int(bin(x).count('1')&1))  # parity of x popcount (a carry proxy)
    return f

random.seed(7)
N=4000
BITS=40  # moderate range so we can also brute-verify if needed
rows=[]
for _ in range(N):
    d=random.randrange(1,1<<BITS)
    P=mul(d,G)
    d1,d2=glv_decompose(d)
    rows.append((d,d1,d2,features(P)))

def predict_bit(target_fn, name):
    # simple: for each feature, best single-feature predictor of target bit; report max accuracy vs shuffle
    import statistics
    Y=[target_fn(r)&1 for r in rows]
    base=max(sum(1 for y in Y if y==0), sum(1 for y in Y if y==1))/len(Y)
    nf=len(rows[0][3])
    best=0; best_f=-1
    for fi in range(nf):
        # map feature value -> majority bit, measure accuracy
        from collections import defaultdict
        cnt=defaultdict(lambda:[0,0])
        for r,y in zip(rows,Y):
            cnt[r[3][fi]][y]+=1
        correct=sum(max(c) for c in cnt.values())
        acc=correct/len(Y)
        if acc>best: best=acc; best_f=fi
    # shuffle control: shuffle Y, redo
    Ys=Y[:]; random.shuffle(Ys)
    bests=0
    for fi in range(nf):
        from collections import defaultdict
        cnt=defaultdict(lambda:[0,0])
        for r,y in zip(rows,Ys):
            cnt[r[3][fi]][y]+=1
        correct=sum(max(c) for c in cnt.values())
        bests=max(bests, correct/len(Ys))
    print(f"  {name:20s}: base-rate {base:.3f} | best public-feature acc {best:.3f} (f#{best_f}) | shuffle-null best {bests:.3f}")

print(f"secp256k1, N={N} random d in [1,2^{BITS}). Predict target bit from PUBLIC orbit+carry features.")
print("(If a real feature beats the shuffle-null by a margin, that's a leak.)\n")
predict_bit(lambda r: r[0], "low bit of d")
predict_bit(lambda r: r[0]>>1, "bit 1 of d")
predict_bit(lambda r: r[1], "low bit of d1 (GLV)")
predict_bit(lambda r: r[2], "low bit of d2 (GLV)")
predict_bit(lambda r: r[1]>>1, "bit1 of d1 (GLV)")

# sanity: the mu3-orbit reduction IS free -- show chi3(x) is a deterministic public fn (not a d-leak)
print("\nControl: is any feature a deterministic function of d's low bits? (should be NO for a real leak)")
print("  If 'best public-feature acc' ~ shuffle-null ~ base-rate => NO leakage beyond chance.")

# ---- JOINT predictor: orbit coord AND carry features TOGETHER, held-out test vs shuffle ----
print("\n=== JOINT predictor (all features together), train/test split, shuffle null ===")
def joint_test(target_fn, name):
    data=[(tuple(r[3]), target_fn(r)&1) for r in rows]
    half=len(data)//2
    train,test=data[:half],data[half:]
    from collections import defaultdict
    def build(tr):
        tbl=defaultdict(lambda:[0,0])
        for feat,y in tr: tbl[feat][y]+=1
        return {k:(0 if c[0]>=c[1] else 1) for k,c in tbl.items()}
    def acc(model,te):
        maj=1 if sum(y for _,y in te)>=len(te)/2 else 0
        good=sum(1 for feat,y in te if model.get(feat,maj)==y)
        return good/len(te)
    m=build(train); real=acc(m,test)
    # shuffle labels within train, keep test labels; also shuffle test independently
    import random as R
    trs=[(f,y) for (f,_),y in zip(train,[y for _,y in train])]
    lab=[y for _,y in train]; R.shuffle(lab)
    trs=[(f,lab[i]) for i,(f,_) in enumerate(train)]
    ms=build(trs)
    # test on shuffled test labels too
    tl=[y for _,y in test]; R.shuffle(tl)
    tes=[(f,tl[i]) for i,(f,_) in enumerate(test)]
    sh=acc(ms,tes)
    print(f"  {name:20s}: joint held-out acc {real:.3f} | shuffle-null {sh:.3f}  -> {'LEAK?' if real-sh>0.03 else 'no signal'}")

joint_test(lambda r: r[0], "low bit of d")
joint_test(lambda r: r[0]>>1, "bit 1 of d")
joint_test(lambda r: r[0]>>2, "bit 2 of d")
joint_test(lambda r: r[1], "low bit of d1 (GLV)")
joint_test(lambda r: r[1]>>1, "bit1 of d1 (GLV)")
