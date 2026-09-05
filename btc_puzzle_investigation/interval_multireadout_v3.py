#!/usr/bin/env python3
"""interval_multireadout_v3.py -- v2 with the null/plant cost removed.

v2 recomputed every pairwise character on every null draw: ~60M modular exponentiations at a
MEASURED 84.7 us each = 85 minutes for the field pass alone.  v3 precomputes ONE pool-wide
difference-class table (C(Npool,2) exponentiations), after which every null draw and the entire
greedy plant are table lookups and cost nothing.

Axes (unchanged from v2): (1) larger M, (2) readouts chi_2/chi_3/chi_6 from one exponentiation
per pair, (3) FIELD difference x_i-x_j vs GROUP-LAW difference x(P_i-P_j).

CONSTRUCTED scalars only. No puzzle keys. No generator pool. Exact integers in the signal path.
"""
import random, hashlib, sys, time
from itertools import combinations

P  = 2**256 - 2**32 - 977
N  = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141
GX = 0x79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798
GY = 0x483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8
E6 = (P - 1) // 6

def _z6():
    g = 3
    while pow(g, (P-1)//2, P) == 1 or pow(g, (P-1)//3, P) == 1: g += 1
    z = pow(g, E6, P); tab = {}; v = 1
    for j in range(6): tab[v] = j; v = v*z % P
    assert len(tab) == 6 and v == 1
    return tab
Z6TAB = _z6()
BETA = pow(2, (P-1)//3, P)
assert pow(BETA,3,P) == 1 and BETA != 1

def mu6(d):
    d %= P
    return None if d == 0 else Z6TAB[pow(d, E6, P)]

# ---- Jacobian ----
def jdbl(A):
    X,Y,Z = A
    if Y == 0 or Z == 0: return (0,0,0)
    a=X*X%P; b=Y*Y%P; c=b*b%P
    d=2*((X+b)*(X+b)-a-c)%P; e=3*a%P; f=e*e%P
    X3=(f-2*d)%P
    return (X3,(e*(d-X3)-8*c)%P,2*Y*Z%P)
def jadd(A,B):
    X1,Y1,Z1=A
    if Z1==0: return B
    X2,Y2,Z2=B
    if Z2==0: return A
    z1z1=Z1*Z1%P; z2z2=Z2*Z2%P
    u1=X1*z2z2%P; u2=X2*z1z1%P
    s1=Y1*Z2%P*z2z2%P; s2=Y2*Z1%P*z1z1%P
    h=(u2-u1)%P; r=2*(s2-s1)%P
    if h==0: return jdbl(A) if r==0 else (0,0,0)
    i=2*h%P; i=i*i%P; j=h*i%P; v=u1*i%P
    X3=(r*r-j-2*v)%P
    return (X3,(r*(v-X3)-2*s1*j)%P,((Z1+Z2)*(Z1+Z2)-z1z1-z2z2)*h%P)
def jneg(A): return (A[0],(-A[1])%P,A[2])
def jmul(k,Pt=(GX,GY,1)):
    R=(0,0,0); Q=Pt
    while k:
        if k&1: R=jadd(R,Q)
        Q=jdbl(Q); k>>=1
    return R
def batch_x(pts):
    zs=[p[2] for p in pts]; pre=[1]*(len(zs)+1)
    for i,z in enumerate(zs): pre[i+1]=pre[i]*z%P
    inv=pow(pre[-1],P-2,P); out=[]
    for i in range(len(zs)-1,-1,-1):
        zi=inv*pre[i]%P; inv=inv*zs[i]%P
        out.append(pts[i][0]*zi%P*zi%P)
    return out[::-1]

# ---- statistics (exact integers) ----
def stats(counts):
    c=counts
    E2=(sum(c[j] for j in (0,2,4))-sum(c[j] for j in (1,3,5)))**2
    t=[c[0]+c[3],c[1]+c[4],c[2]+c[5]]
    E3=((2*t[0]-t[1]-t[2])**2+3*(t[1]-t[2])**2)//4
    re=2*c[0]+c[1]-c[2]-2*c[3]-c[4]+c[5]; im=c[1]+c[2]-c[4]-c[5]
    E6=(re*re+3*im*im)//4
    return E2,E3,E6
def counts_of(classes):
    c=[0]*6
    for j in classes: c[j]+=1
    return c

# ---- difference classes ----
def field_classes(pts):
    xs=[p[0] if p[2]==1 else None for p in pts]
    if any(x is None for x in xs): xs=batch_x(pts)
    return [v for v in (mu6(xs[i]-xs[j]) for i,j in combinations(range(len(xs)),2)) if v is not None]
def group_classes(pts):
    d=[jadd(pts[i],jneg(pts[j])) for i,j in combinations(range(len(pts)),2)]
    d=[q for q in d if q[2]!=0]
    return [v for v in (mu6(x) for x in batch_x(d)) if v is not None]

# ---- pool + table ----
def pool_pts(n,rng):
    out=[]
    while len(out)<n:
        x=rng.randrange(0,P); r=(x*x%P*x+7)%P
        if pow(r,(P-1)//2,P)!=1: continue
        out.append((x,pow(r,(P+1)//4,P),1))
    return out
def pool_table(pool,mode):
    """class of the difference for every pool pair. ONE exponentiation per pair, once."""
    n=len(pool); T=[[None]*n for _ in range(n)]
    if mode=="field":
        xs=[p[0] for p in pool]
        for i in range(n):
            xi=xs[i]
            for j in range(i+1,n):
                v=mu6(xi-xs[j]); T[i][j]=T[j][i]=v
    else:
        for i in range(n):
            di=[]; idx=[]
            for j in range(i+1,n):
                q=jadd(pool[i],jneg(pool[j]))
                if q[2]!=0: di.append(q); idx.append(j)
            if di:
                for j,x in zip(idx,batch_x(di)):
                    v=mu6(x); T[i][j]=T[j][i]=v
    return T
def counts_from_table(T,sel):
    c=[0]*6
    for a in range(len(sel)):
        ia=sel[a]; row=T[ia]
        for b in range(a+1,len(sel)):
            v=row[sel[b]]
            if v is not None: c[v]+=1
    return c

# ---- controls ----
def glv_set(M,pool):
    out=[]
    for (x,y,_) in pool:
        if len(out)+3>M: break
        out+=[(x,y,1),(BETA*x%P,y,1),(BETA*BETA%P*x%P,y,1)]
    return out
def plant_indices(T,M,n,rng,target=0,scan=250):
    """greedy bias of the DIFFERENCE set -- pure table lookups, no exponentiation."""
    cand=list(range(n)); rng.shuffle(cand)
    out=[cand.pop()]
    while len(out)<M and cand:
        bi,bh=0,-1
        for i,q in enumerate(cand[:scan]):
            row=T[q]; h=sum(1 for z in out if row[z]==target)
            if h>bh: bi,bh=i,h
        out.append(cand.pop(bi))
    return out

def run(mode,M,R,NP,rng,label):
    t0=time.time()
    print(f"\n{'='*76}\n{label}\n  mode={mode}  M={M}  R={R}  pool={NP}\n{'='*76}",flush=True)
    pool=pool_pts(NP,rng)
    print(f"  building pool difference table ({NP*(NP-1)//2} pairs) ...",flush=True)
    T=pool_table(pool,mode)
    print(f"  table done [{time.time()-t0:.0f}s]; null draws are now table lookups",flush=True)
    idx=list(range(NP)); nl=[]
    for _ in range(R):
        nl.append(stats(counts_from_table(T,rng.sample(idx,M))))
    cols=list(zip(*nl)); q={}
    for i,nm in enumerate(("E2","E3","E6")):
        s=sorted(cols[i]); q[nm]=(s,s[int(.95*R)],s[int(.99*R)])
        print(f"  null {nm}: median={s[R//2]}  95th={s[int(.95*R)]}  99th={s[int(.99*R)]}")
    def pc(nm,v):
        s=q[nm][0]; return 100.0*sum(1 for z in s if z<v)/len(s)
    def ro(pts):
        return stats(counts_of(field_classes(pts) if mode=="field" else group_classes(pts)))

    print("  -- controls --",flush=True)
    e=stats(counts_from_table(T,plant_indices(T,M,NP,rng)))
    pl=e[1]>=q["E3"][2]
    print(f"   C-PLANT E2={e[0]} ({pc('E2',e[0]):.1f})  E3={e[1]} ({pc('E3',e[1]):.1f})  "
          f"E6={e[2]} ({pc('E6',e[2]):.1f})  -> {'FIRES' if pl else '*** NO FIRE ***'}")
    e=ro(glv_set(min(M,90),pool))
    glv=(e[1]==0)
    print(f"   C-GLV   E2={e[0]} [parity-void]  E3={e[1]}  E6={e[2]} [parity-void]  -> "
          f"{'E3=0 EXACT (forced)' if glv else '*** E3 NOT FORCED -- readout wrong ***'}")
    e=ro([jmul(rng.randrange(1,N)) for _ in range(M)])
    ng=(e[1]<q["E3"][1])
    print(f"   C-NEG   E2={e[0]} ({pc('E2',e[0]):.1f})  E3={e[1]} ({pc('E3',e[1]):.1f})  "
          f"E6={e[2]} ({pc('E6',e[2]):.1f})  -> {'quiet' if ng else '*** FIRES -- VOID ***'}")
    if not (pl and glv and ng):
        print("   F-VOID: no arm number is read.",flush=True); return
    print(f"  -- arms --",flush=True)
    print(f"   {'k':>5} | {'E3 (DECIDES)':>13} {'pct':>6} | {'E2*':>11} {'E6*':>11}   (* parity-void)")
    for k in (40,64,96,128,135,160,200):
        lo,hi=(2**(k-1),2**k)
        e=ro([jmul(rng.randrange(lo,hi)) for _ in range(M)])
        fl=" FIRE" if e[1]>=q["E3"][2] else ""
        print(f"   {k:>5} | {e[1]:>13} {pc('E3',e[1]):>5.1f}% | {e[0]:>11} {e[2]:>11}{fl}",flush=True)
    print(f"  [{time.time()-t0:.0f}s total]",flush=True)

if __name__=="__main__":
    with open("PREREG_interval_cubic_structure_v1.md","rb") as f:
        print("v1 PREREG SHA-256:",hashlib.sha256(f.read()).hexdigest(),flush=True)
    print("measured pow(256-bit) cost drives all sizing; null+plant are table lookups.",flush=True)
    rng=random.Random(20260731)
    run("field",400,3000,1100,rng,"AXIS 1+2 -- FIELD difference, readouts chi_2 / chi_3 / chi_6")
    run("group",160,3000, 600,rng,"AXIS 3 -- GROUP-LAW difference x(P_i - P_j)  [CM-native]")
