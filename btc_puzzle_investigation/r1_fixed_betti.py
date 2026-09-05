import sys; sys.path.insert(0,"/Users/trentpalelei/Desktop/Math Ex/btc_puzzle_investigation")
from sage.all import *
from semaev_elimination_v1 import summation_poly, decomposition_system
from delta_r_corrected_v2 import cube_root, cell
from semaev_cm_relation_yield_v4 import build_curves, match_nearest
import random as pyr
p=523; m=2; F=GF(p); beta=cube_root(F)
Rh=PolynomialRing(F,['x1','x2','h'],order='degrevlex'); xh=Rh.gens(); h=xh[2]
def qb(gens,R):
    I=R.ideal(gens)
    if int(I.dimension())!=0: return None,None
    quo=int(I.vector_space_dimension())
    Ih=Rh.ideal([R.hom(list(xh[:2]),Rh)(gg).homogenize(h) for gg in gens])
    Is=Ih._singular_(); Is.parent().lib('homolog.lib')
    return quo, str(Is.mres(0).betti()).strip()
cur=build_curves(p,5,seed=1234+p); j0=[c for c in cur if c['lab']=='j0'][0]
ncm=[c for c in cur if c['lab']=='nonCM']; nc=ncm[match_nearest(j0['order'],ncm,set())]
def cm_fixed(seed):   # CM fixed-target (single fiber), mu3-inv V
    r=cell(F,m,beta,seed)
    if r is None: return None
    t,V=r; Rx,gens,xs=decomposition_system(F,0,7,m,t,V); return gens,Rx
def ncm_fixed(seed):
    pyr.seed(seed+700); En=EllipticCurve(F,[nc['A'],nc['B']]); Gn=En.gens()[0]; Nn=int(En.order())
    pts=[int(pyr.randrange(1,Nn))*Gn for _ in range(m)]; xc=[P[0] for P in pts]
    if len(set(xc))<m: return None
    Sn=En(0)
    for P in pts: Sn=Sn+P
    if -Sn==En(0): return None
    tn=(-Sn)[0]; Vn=sorted(set(xc)|{F(pyr.randrange(0,p)) for _ in range(4)})
    Rx,gens,xs=decomposition_system(F,nc['A'],nc['B'],m,tn,Vn); return gens,Rx
cmB={}; ncB={}
for s in range(1,20):
    r=cm_fixed(s)
    if r:
        q,b=qb(r[0],r[1])
        if q: cmB.setdefault(q,(s,b))
    r=ncm_fixed(s)
    if r:
        q,b=qb(r[0],r[1])
        if q: ncB.setdefault(q,(s,b))
shared=sorted(set(cmB)&set(ncB))
print(f"CM-fixed quos={sorted(cmB)}  nonCM-fixed quos={sorted(ncB)}  shared={shared}",flush=True)
for q in shared:
    ident=cmB[q][1]==ncB[q][1]
    print(f"  quo={q}: CM betti == nonCM betti ? {ident}",flush=True)
    if not ident:
        print(f"    CM : {cmB[q][1]}",flush=True); print(f"    nCM: {ncB[q][1]}",flush=True)
print("[done]",flush=True)
