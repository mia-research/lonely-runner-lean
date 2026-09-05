# h2_order3_control_run_v1.py -- run: sage h2_order3_control_run_v1.py [--smoke]
# Executes PREREG_h2_order3_structure_control_v1.md: does the M26 x-closure boost come from beta/CM
# specifically, or from GENERIC order-3-orbit closure? Compares Vinv (beta-orbits) vs V3(phi)
# (generic split order-3 Mobius orbits) on the SAME curve/target.
#
# DISCLOSED DEVIATION (D-impl-1): pre-reg k in {2,3} -> |V| in {6,9}. With m=3 the three decomposition
# x-coords each seed a size-3 orbit => |V| >= 9 generically; |V|=6 is infeasible. Use n_orb in {3,4}
# (|V| in {9,12}); larger |V| is POWER-FAVORABLE (more quo resolution, fewer ties), does not change
# the beta-vs-phi contrast. All other spec elements unchanged.
#
# Exact ints for field elements, quo, orbit members, counts; float only in R3_med (log, descriptor).

from sage.all import *
import json, sys, time, random

BASE="/Users/trentpalelei/Desktop/Math Ex/btc_puzzle_investigation"
H=BASE+"/semaev_elimination_v1.py"; _g={'__name__':'hm'}; exec(open(H).read(),_g)
decomposition_system=_g['decomposition_system']; mu3_lever_test=_g['mu3_lever_test']

SMOKE=('--smoke' in sys.argv)
PRIMES=[211,307] if SMOKE else [211,307,421,631,907,1093]
NORBS=[3] if SMOKE else [3,4]          # |V| = 9, 12
J_SEEDS=2 if SMOKE else 3              # target seeds per prime
K_MAPS=6 if SMOKE else 30             # generic order-3 Mobius maps per instance
B_PERM=199 if SMOKE else 999
m=3
OUT=BASE+("/h2_order3_smoke_v1.jsonl" if SMOKE else "/h2_order3_results_v1.jsonl")

def cube_root(F):
    for u in range(2,int(F.characteristic())):
        if F(u)**3==1: return F(u)
    return None

def quo_vsd(F, tval, V, m):
    Dmax=2**(m-1)+m*len(V)+5
    Rx,gens_list,xs=decomposition_system(F,0,7,m,tval,V)
    I=Rx.ideal(gens_list)
    if int(I.dimension())!=0: return None
    return int(I.vector_space_dimension())

def decomp(F, seed):
    """decomposable target from m gens-multiples (as mu3_lever_test). returns (E,tval,xs)."""
    E=EllipticCurve(F,[0,7]); G=E.gens()[0]; N=int(E.order()); pyr=random.Random(seed)
    for _ in range(300):
        pts=[int(pyr.randrange(1,N))*G for _ in range(m)]
        xs=[P[0] for P in pts]
        if any(P==E(0) for P in pts) or len(set(xs))<m: continue
        S=E(0)
        for P in pts: S=S+P
        T=-S
        if T!=E(0): return E,T[0],[F(x) for x in xs]
    return None

def orbit(mapfn, x):
    return (x, mapfn(x), mapfn(mapfn(x)))

def beta_map(beta):
    return lambda x: beta*x

def rand_mobius_order3(F, beta, forbid_fixed, rng):
    """phi = Mobius(g . diag(beta,1) . g^-1), split order-3, phi not in {beta,beta^2},
    fixed points not in forbid_fixed. returns (phi_fn, (a,b,c,d))."""
    p=int(F.characteristic())
    for _ in range(500):
        g=matrix(F,2,2,[rng.randrange(p) for _ in range(4)])
        if g.determinant()==0: continue
        M=g*matrix(F,2,2,[beta,0,0,1])*g.inverse()
        a,b,c,d=M[0,0],M[0,1],M[1,0],M[1,1]
        if c==0 and b==0: continue                      # diagonal => multiplicative => beta family
        # fixed points of Mobius: solve c x^2 +(d-a)x - b =0
        fps=[]
        if c!=0:
            disc=(d-a)**2+4*c*b
            if disc.is_square():
                s=disc.sqrt()
                fps=[(a-d+s)/(2*c),(a-d-s)/(2*c)]
        if any(fp in forbid_fixed for fp in fps): continue
        def phi(x, a=a,b=b,c=c,d=d):
            if x is None: return None
            den=c*x+d
            if den==0: return None
            return (a*x+b)/den
        # verify order 3 on a probe and no None on relevant points later
        return phi,(int(a),int(b),int(c),int(d))
    return None,None

def build_base(seeds, mapfn):
    """union of size-3 orbits over seeds; return (list, orbits) or None if any orbit degenerate/overlap."""
    orbs=[]; seen=set()
    for s in seeds:
        o=orbit(mapfn,s)
        if any(v is None for v in o): return None
        if len(set(o))<3: return None
        if any(v in seen for v in o): return None
        seen|=set(o); orbs.append(tuple(o))
    return list(seen), orbs

def is_relation_triple(E, orb):
    """do the 3 x-coords admit y-signs with P0+P1+P2=O ?"""
    F=E.base_field()
    lifts=[]
    for x in orb:
        try: P=E.lift_x(F(x))
        except Exception: return False
        lifts.append([P,-P])
    for s0 in lifts[0]:
        for s1 in lifts[1]:
            for s2 in lifts[2]:
                if s0+s1+s2==E(0): return True
    return False

def signwin(qi, qj_list):
    w=0; nt=0
    for qj in qj_list:
        if qi>qj: w+=1
        elif qi<qj: w-=1
        else: nt+=1
    return w,nt

def run_arm(F, E, tval, xs, n_orb, beta, rng):
    """returns dict for one instance: quo_inv, [quo_phi..], n_rel_inv, [n_rel_phi..], plus planted."""
    p=int(F.characteristic())
    # seeds = xs (m of them) + (n_orb - m) padding seeds; SAME seeds for beta and every phi
    pad=[]
    while len(pad) < n_orb-m:
        r=F(rng.randrange(1,p))
        if r not in xs and r not in pad and r!=0: pad.append(r)
    seeds=list(xs)+pad
    forbid=set(xs)|set(pad)|{F(0)}
    bmap=beta_map(beta)
    binv=build_base(seeds,bmap)
    if binv is None: return None
    Vinv,orbs_inv=binv
    q_inv=quo_vsd(F,tval,Vinv,m)
    if q_inv is None: return None
    nrel_inv=sum(is_relation_triple(E,o) for o in orbs_inv)
    q_phis=[]; nrel_phis=[]; phimaps=[]
    tries=0
    while len(q_phis)<K_MAPS and tries<K_MAPS*8:
        tries+=1
        phi,coef=rand_mobius_order3(F,beta,forbid,rng)
        if phi is None: continue
        bb=build_base(seeds,phi)
        if bb is None: continue
        V3,orbs3=bb
        q=quo_vsd(F,tval,V3,m)
        if q is None: continue
        q_phis.append(q); nrel_phis.append(sum(is_relation_triple(E,o) for o in orbs3)); phimaps.append(coef)
    # planted P-a: phi=beta and beta^2 must reproduce quo(Vinv) EXACTLY
    b2map=lambda x: beta*beta*x
    pa=[]
    for mp in (bmap,b2map):
        bb=build_base(seeds,mp)
        pa.append(quo_vsd(F,tval,bb[0],m) if bb else None)
    return dict(q_inv=q_inv,q_phis=q_phis,nrel_inv=nrel_inv,nrel_phis=nrel_phis,
                pa=pa,n_orb=n_orb,sizeV=len(Vinv))

def relation_triple(E, rng):
    """three x-coords {x(R),x(S),x(T)} with R+S+T=O (R,S random, T=-(R+S))."""
    F=E.base_field(); N=int(E.order()); G=E.gens()[0]
    for _ in range(200):
        R=int(rng.randrange(1,N))*G; S=int(rng.randrange(1,N))*G; T=-(R+S)
        if R==E(0) or S==E(0) or T==E(0): continue
        xs={R[0],S[0],T[0]}
        if len(xs)==3: return list(xs)
    return None

def generic_triple(F, rng):
    while True:
        t={F(rng.randrange(1,int(F.characteristic()))) for _ in range(3)}
        if len(t)==3: return list(t)

def plant_pb(F, E, tval, xs, rng, n_pad=3):
    """P-b dose-response: V = xs U (j relation-triples) U ((n_pad-j) generic triples), |V| fixed.
    quo(j) must be non-decreasing / detectably rising in j (# relation-triples)."""
    rel=[relation_triple(E,rng) for _ in range(n_pad)]
    gen=[generic_triple(F,rng) for _ in range(n_pad)]
    if any(r is None for r in rel): return None
    out=[]
    for j in range(n_pad+1):
        V=set(xs)
        for t in rel[:j]: V|=set(t)
        for t in gen[:n_pad-j]: V|=set(t)
        out.append(quo_vsd(F,tval,list(V),m))
    return out

def main():
    t0=time.time(); print("H2 order-3 control  SMOKE=%s primes=%s norbs=%s K=%d J=%d B=%d"%(SMOKE,PRIMES,NORBS,K_MAPS,J_SEEDS,B_PERM))
    open(OUT,"w").close()
    # R2 reproduction floor (anchor 211/307, k=2) + P-b plant, once per prime
    for p in PRIMES:
        F=GF(p); Dm=2**(m-1)+m*(3*2)+5
        try:
            r2=mu3_lever_test(p,m,2,Dm)
            qb=r2.get('secp_betaInvV',{}).get('quo'); qr=r2.get('secp_randomV',{}).get('quo')
        except Exception as ex:
            qb=qr=None
        d=decomp(F,seed=7000)
        pb=plant_pb(F, d[0], d[1], d[2], random.Random(80000+p)) if d else None
        with open(OUT,"a") as fh: fh.write(json.dumps(dict(kind="anchor",p=p,qb=qb,qr=qr,pb=pb))+"\n")
        print("  ANCHOR p=%-5d R2 quo(betaInv)=%s quo(rnd)=%s  P-b(quo vs #rel-triples)=%s"%(p,qb,qr,pb))
    for n_orb in NORBS:
        for p in PRIMES:
            F=GF(p); beta=cube_root(F)
            if beta is None: print("  skip p=%d (no cube root)"%p); continue
            for j in range(J_SEEDS):
                rng=random.Random(90000+p*10+j)
                d=decomp(F, seed=7000+j)
                if d is None: print("  p=%d j=%d decomp fail"%(p,j)); continue
                E,tval,xs=d
                res=run_arm(F,E,tval,xs,n_orb,beta,rng)
                if res is None: print("  p=%d j=%d arm fail"%(p,j)); continue
                res.update(p=p,j=j)
                with open(OUT,"a") as fh: fh.write(json.dumps(res)+"\n")
                print("  p=%-5d n_orb=%d j=%d |V|=%d q_inv=%d q_phis(med)=%s PA=%s nrel_inv=%d [%.0fs]"%(
                    p,n_orb,j,res['sizeV'],res['q_inv'],
                    sorted(res['q_phis'])[len(res['q_phis'])//2] if res['q_phis'] else None,res['pa'],res['nrel_inv'],time.time()-t0))
    print("DONE [%.0fs]"%(time.time()-t0))

if __name__=='__main__':
    sys.stdout.reconfigure(line_buffering=True); main()
