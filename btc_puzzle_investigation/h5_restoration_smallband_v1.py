# h5_restoration_smallband_v1.py -- run: sage h5_restoration_smallband_v1.py
# PREREG secondary comparability band: generic cyclic curves at p in [523,823] (j0's own scale),
# confinement T1 at matched index, to close the p-confound in the matched-index j0-vs-generic gap.
from sage.all import *
import json, sys, time, random, math
from collections import defaultdict
BASE="/Users/trentpalelei/Desktop/Math Ex/btc_puzzle_investigation"
H=BASE+"/semaev_elimination_v1.py"; _g={'__name__':'hm'}; exec(open(H).read(),_g)
decomposition_system=_g['decomposition_system']
m=3; V=6; K=25; QFLOOR=80; NEED=15; PBAND=(523,823)
def lm(qs): return math.log(sum(qs)/len(qs))  # noqa: float — (stat) monotone stat on exact-int quo
def quo_vsd(F,A,B,tval,Vr):
    Rx,gl,xs=decomposition_system(F,A,B,m,tval,Vr); I=Rx.ideal(gl)
    if int(I.dimension())!=0: return None
    return int(I.vector_space_dimension())
def confined(E,G,c,q,extra,rng):
    Hh=c*G; q=int(q)
    for _ in range(300):
        pts=[int(rng.randrange(1,q))*Hh for _ in range(m)]; xs=[P[0] for P in pts]
        if any(P==E(0) for P in pts) or len(set(xs))<m: continue
        S=E(0)
        for P in pts: S=S+P
        T=-S
        if T==E(0): continue
        Vr=list(xs)
        for _ in range(extra): Vr.append((int(rng.randrange(1,q))*Hh)[0])
        return T[0],[E.base_field()(x) for x in Vr]
    return None
def full(E,extra,seed):
    set_random_seed(int(seed))
    for _ in range(300):
        pts=[E.random_point() for _ in range(m)]
        if any(P==E(0) for P in pts): continue
        xs=[P[0] for P in pts]
        if len(set(xs))<m: continue
        S=E(0)
        for P in pts: S=S+P
        T=-S
        if T==E(0): continue
        Vr=list(xs)
        for _ in range(extra):
            Q=E.random_point()
            if Q!=E(0): Vr.append(Q[0])
        return T[0],[E.base_field()(x) for x in Vr]
    return None
random.seed(555); out=defaultdict(list); found=0; p=PBAND[0]-1
t0=time.time()
while found<NEED and p<PBAND[1]:
    p=int(next_prime(p))
    F=GF(p)
    for _ in range(8):
        A=F(random.randrange(1,p)); B=F(random.randrange(1,p))
        if (4*A**3+27*B**2)==0: continue
        E=EllipticCurve(F,[A,B]); j=E.j_invariant()
        if j==F(0) or j==F(1728): continue
        inv=E.abelian_group().invariants()
        if len(inv)>1: continue
        N=int(E.order()); G=E.gens()[0]
        cs=[int(c) for c in divisors(N) if c>=2 and N//c>=QFLOOR]
        if len(cs)<2: continue
        fq=[]
        for k in range(K):
            ft=full(E,V-m,7000+k)
            if ft:
                r=quo_vsd(F,int(A),int(B),ft[0],ft[1])
                if r is not None: fq.append(r)
        if not fq: continue
        lmf=lm(fq)
        rng=random.Random(int(9000+p))
        for c in cs:
            q=N//c; cq=[]
            for k in range(K):
                ct=confined(E,G,c,q,V-m,rng)
                if ct:
                    r=quo_vsd(F,int(A),int(B),ct[0],ct[1])
                    if r is not None: cq.append(r)
            if cq: out[c].append(lm(cq)-lmf)
        found+=1
        print("  p=%d curve %d/%d cs=%s [%.0fs]"%(p,found,NEED,cs,time.time()-t0))
        break
print("SMALL-BAND generic cyclic confinement T1 (p in [523,823], |V|=6):")
for c in sorted(out):
    xs=out[c]; print("  index c=%-2d  T1=%.3f  (n=%d)"%(c,sum(xs)/len(xs),len(xs)))
json.dump({str(c):out[c] for c in out}, open(BASE+"/h5_restoration_smallband_v1.json","w"))
