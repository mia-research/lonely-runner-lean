#!/usr/bin/env python3
"""
Z[omega] / GLV-lattice probe of the solved puzzle keys (user ideas 2 & 4).
EXACT integers only; every test carries a firing control + matched null.

Objects:
  n  = order of G (prime); lambda = image of omega in Z/nZ (lambda^2+lambda+1=0).
  The point group <G> ~= Z[omega]/(pi_n).  A scalar d "in Z[omega]" is its
  balanced GLV pair (a,b) with a + b*lambda == d (mod n), found by Babai rounding
  against the GLV lattice L = <(n,0), (-lambda,1)>.

Tests:
  T1  GLV-short:  are the solved keys anomalously short in the (a,b) rep vs a
      matched null of random d in the same bit range (generator emits GLV-short
      / lattice-aligned scalars)?   [idea 2]
  T2  LCG-mod-n:  do consecutive-index keys satisfy d_{i+2}-d_{i+1} == a*(d_{i+1}-d_i)
      (mod n) with a CONSISTENT multiplier a (LCG whose modulus aligns with n)?  [idea 2]
  T3  GLV-conjugacy:  any d_j == lambda^e * d_i (mod n), e in 1..5 (key set closed
      under the CM automorphism)?  [idea 4]
  T4  sextic leak:  does the sextic residue class of X([d]G) carry info about d mod 6
      (x-coord multiplicative relation to d via beta)?  [idea 4]
Rank/permutation p-values only -- no float threshold decides a verdict.
"""
import csv, math, random

# --- secp256k1 constants (exact) ---
P  = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F
N  = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141
LAM= 0x5363AD4CC05C30E0A5261C028812645A122E22EA20816678DF02967C1B23BD72  # lambda mod n
BET= 0x7AE96A2B657C07106E64479EAC3434E99CF0497512F58995C1396C28719501EE  # beta mod p
Gx = 0x79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798
Gy = 0x483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8
assert (LAM*LAM+LAM+1) % N == 0
assert pow(BET,3,P) == 1 and BET != 1

# --- EC point ops (affine, exact) ---
def inv(a,m): return pow(a,m-2,m)
def padd(Pt,Q):
    if Pt is None: return Q
    if Q is None: return Pt
    x1,y1=Pt; x2,y2=Q
    if x1==x2 and (y1+y2)%P==0: return None
    if Pt==Q:
        s=(3*x1*x1)*inv(2*y1,P)%P
    else:
        s=(y2-y1)*inv((x2-x1)%P,P)%P
    x3=(s*s-x1-x2)%P; y3=(s*(x1-x3)-y1)%P
    return (x3,y3)
def pmul(k,Pt):
    R=None
    while k:
        if k&1: R=padd(R,Pt)
        Pt=padd(Pt,Pt); k>>=1
    return R
G=(Gx,Gy)

# --- 2D exact Gauss lattice reduction of L = <(n,0),(-lambda,1)> ---
def dot(u,v): return u[0]*v[0]+u[1]*v[1]
def gauss_reduce(b1,b2):
    while True:
        if dot(b2,b2) < dot(b1,b1): b1,b2=b2,b1
        # mu = round(<b1,b2>/<b1,b1>)  -- exact nearest integer
        num=dot(b1,b2); den=dot(b1,b1)
        mu=(2*num+den)//(2*den) if den>0 else 0   # round half up on positive den
        # correct rounding for possibly-negative num:
        mu=round_div(num,den)
        b2=(b2[0]-mu*b1[0], b2[1]-mu*b1[1])
        if dot(b2,b2) >= dot(b1,b1):
            break
    return b1,b2
def round_div(num,den):
    # nearest integer to num/den for ANY sign of den, exact
    if den<0: num,den=-num,-den
    q,r=divmod(num,den)   # den>0 => 0<=r<den
    if 2*r>=den: q+=1
    return q
b1,b2=gauss_reduce((N,0),((-LAM)%N - N,1))  # ensure (-lambda,1) small-ish start
# rebuild cleanly: basis vectors of L
b1,b2=gauss_reduce((N,0),(-LAM,1))

def glv_decompose(d):
    # balanced (a,b): (a,b) = (d,0) - nearest lattice vector
    # solve (d,0) ~ c1*b1 + c2*b2 over rationals, round c1,c2, subtract
    det=b1[0]*b2[1]-b1[1]*b2[0]
    # c1 = det^{-1} * ( d*b2[1] - 0*b2[0] ), c2 = det^{-1} * ( -d*b1[1] + 0*b1[0] )
    c1n=d*b2[1]; c2n=-d*b1[1]
    c1=round_div(c1n,det); c2=round_div(c2n,det)
    lat=(c1*b1[0]+c2*b2[0], c1*b1[1]+c2*b2[1])
    a,bb=(d-lat[0], 0-lat[1])
    assert (a+bb*LAM - d) % N == 0
    return a,bb

def maxbits(a,b):
    m=max(abs(a),abs(b))
    return m.bit_length()

# --- load solved keys in index order ---
keys=[]
with open('puzzles_verified.csv') as f:
    for row in csv.DictReader(f):
        keys.append((int(row['puzzle']), int(row['private_key'],16),
                     int(row['X'],16), int(row['Y'],16)))
keys.sort()
idx=[k[0] for k in keys]; D=[k[1] for k in keys]; XS=[k[2] for k in keys]

print(f"loaded {len(keys)} solved keys, indices {idx[0]}..{idx[-1]}")
print(f"GLV lattice reduced basis: b1={b1}, b2={b2}  (|b1|~2^{maxbits(*b1)-1})")

# ================= T1: GLV-short =================
print("\n=== T1  GLV-short (max|a,b| bits) vs matched null ===")
def glv_maxbits(d): return maxbits(*glv_decompose(d))
obs=[glv_maxbits(d) for d in D]
nontrivial=[i for i,d in zip(idx,D) if d>=(1<<128)]
print(f"  keys with d>=2^128 (rep genuinely 2-D): {nontrivial}")
# aggregate statistic: sum of maxbits (smaller => shorter/aligned). rank vs null.
S_obs=sum(obs)
rng=random.Random(12345)
NULL=2000
worse=0
for _ in range(NULL):
    s=0
    for d in D:
        nb=d.bit_length()
        dr=rng.randrange(1<<(nb-1),1<<nb) if nb>1 else 1
        s+=glv_maxbits(dr)
    if s<=S_obs: worse+=1
print(f"  observed sum(maxbits)={S_obs}; null P(sum<=obs)={worse/NULL:.3f}")
# CONTROL: keys chosen AS short GLV vectors should fire (tiny p)
ctrl=[]
for d in D:
    a,b=glv_decompose(d)
    # plant: force a small vector of same rough scale-ish -> use (a mod 2^40, b mod 2^40) rebuilt
    ca=rng.randrange(1<<40); cb=rng.randrange(1<<40)
    ctrl.append((ca + cb*LAM) % N)
S_ctrl=sum(glv_maxbits(d) for d in ctrl)
worse=sum(1 for _ in range(NULL) if sum(glv_maxbits(rng.randrange(1<<(d.bit_length()-1),1<<d.bit_length()) if d.bit_length()>1 else 1) for d in ctrl)<=S_ctrl)
print(f"  [CONTROL planted GLV-short] sum={S_ctrl}, null P<=obs={worse/NULL:.3f}  (want ~0)")

# ================= T2: LCG mod n =================
print("\n=== T2  LCG-mod-n consistency across consecutive-index keys ===")
def lcg_multipliers(seq_idx, seq_d, mod):
    mus={}
    runs=0
    # only consecutive indices (i,i+1,i+2)
    for j in range(len(seq_idx)-2):
        if seq_idx[j+1]==seq_idx[j]+1 and seq_idx[j+2]==seq_idx[j]+2:
            runs+=1
            d0,d1,d2=seq_d[j],seq_d[j+1],seq_d[j+2]
            den=(d1-d0)%mod
            if math.gcd(den,mod)!=1: continue
            a=((d2-d1)*inv(den,mod))%mod
            mus[a]=mus.get(a,0)+1
    return mus,runs
mus,runs=lcg_multipliers(idx,D,N)
print(f"  consecutive triples: {runs}; distinct multipliers a (mod n): {len(mus)}")
if runs and len(mus): print(f"  max multiplicity of any single a: {max(mus.values())}  (all-equal => LCG mod n)")
# CONTROL: plant an LCG mod n over indices 1..30
aa=rng.randrange(2,N); cc=rng.randrange(N); s=rng.randrange(N)
lidx=list(range(1,31)); ld=[]
for _ in lidx:
    ld.append(s); s=(aa*s+cc)%N
mus_c,_=lcg_multipliers(lidx,ld,N)
print(f"  [CONTROL LCG mod n] distinct multipliers: {len(mus_c)} (want 1), matches planted a={aa==next(iter(mus_c))}")

# ================= T3: GLV-conjugacy among keys =================
print("\n=== T3  GLV-conjugacy: d_j == lambda^e * d_i (mod n) ===")
powL=[pow(LAM,e,N) for e in range(6)]
Dset={d:i for i,d in zip(idx,D)}
hits=[]
for i,di in zip(idx,D):
    for e in range(1,6):
        v=(di*powL[e])%N
        if v in Dset and Dset[v]!=i:
            hits.append((i,Dset[v],e))
print(f"  hits: {hits if hits else 'none'}")
# CONTROL: inject d and lambda*d
tv=D[10]; inj={tv:1,(tv*LAM)%N:2}
print(f"  [CONTROL] lambda*d recognized: {((tv*LAM)%N in inj)} (want True)")

# ================= T4: sextic class of X vs d mod 6 =================
print("\n=== T4  sextic residue class of X([d]G) vs d mod 6 ===")
exp6=(P-1)//6
# fixed primitive 6th root zeta = g^((p-1)/6), g=3 is a generator-ish; find zeta of order 6
def find_zeta():
    for g in range(2,50):
        z=pow(g,exp6,P)
        if pow(z,6,P)==1 and all(pow(z,k,P)!=1 for k in (1,2,3)):
            return z
    raise RuntimeError
zeta=find_zeta()
zpow={pow(zeta,j,P):j for j in range(6)}
def sextic_class(x):
    return zpow.get(pow(x%P,exp6,P))
cls=[sextic_class(x) for x in XS]
dm6=[d%6 for d in D]
# contingency independence via permutation on a chi-like count, rank p-value
def stat(cl,dm):
    from collections import Counter
    c=Counter(zip(cl,dm));
    return sum(v*v for v in c.values())   # sum of squared cell counts (monotone assoc)
s_obs=stat(cls,dm6)
worse=0
for _ in range(5000):
    p=dm6[:]; rng.shuffle(p)
    if stat(cls,p)>=s_obs: worse+=1
print(f"  distinct sextic classes present: {sorted(set(c for c in cls if c is not None))}")
print(f"  observed assoc stat={s_obs}; permutation P(>=obs)={worse/5000:.3f}")
# CONTROL: plant cls := dm6 (perfect dependence) -> tiny p
s_ctrl=stat(dm6,dm6); worse=0
for _ in range(5000):
    pp=dm6[:]; rng.shuffle(pp)
    if stat(dm6,pp)>=s_ctrl: worse+=1
print(f"  [CONTROL cls=d mod6] stat={s_ctrl}; permutation P(>=obs)={worse/5000:.4f} (want ~0)")
