import sys; sys.path.insert(0,"/Users/trentpalelei/Desktop/Math Ex/btc_puzzle_investigation")
from sage.all import *
from semaev_elimination_v1 import summation_poly, decomposition_system, _exps_le
from delta_r_corrected_v2 import cube_root, cell
import random as pyr

def fall_profile(F,gens,xs,Dmax):
    n=len(xs); Rr=xs[0].parent(); prev={0:0,1:0,2:0}; prof={0:[],1:[],2:[]}
    for D in range(1,Dmax+1):
        cols=list(_exps_le(n,D)); colidx={e:i for i,e in enumerate(cols)}
        ciso=[sum(e)%3 for e in cols]; pos={}; nb={0:0,1:0,2:0}
        for i in range(len(cols)):
            r=ciso[i]; pos[i]=nb[r]; nb[r]+=1
        rows={0:[],1:[],2:[]}
        for f in gens:
            df=f.degree()
            if df>D: continue
            for ue in _exps_le(n,D-df):
                poly=Rr.monomial(*ue)*f
                if not poly: continue
                r=sum(next(iter(poly.dict())))%3
                rows[r].append({pos[colidx[tuple(e)]]:c for e,c in poly.dict().items()})
        for r in (0,1,2):
            if not rows[r]: continue
            top={pos[i] for i in range(len(cols)) if ciso[i]==r and sum(cols[i])==D}
            M=matrix(F,len(rows[r]),nb[r],sparse=True)
            for ri,row in enumerate(rows[r]):
                for cj,c in row.items(): M[ri,cj]=c
            rk=M.rank(); rt=M.matrix_from_columns(sorted(top)).rank() if top else 0
            fall=(rk-rt)-prev[r]
            if fall>0: prof[r].append((D,int(fall)))
            prev[r]=rk
    return prof

def betti(gens,R):
    try: return R.ideal(gens).free_resolution().betti_numbers()
    except Exception as e: return f"err:{repr(e)[:50]}"

p=523; m=2; F=GF(p); beta=cube_root(F)
t,V=cell(F,m,beta,seed=1)
S,zs,tt=summation_poly(F,0,7,m); R=PolynomialRing(F,['x1','x2','xT'],order='degrevlex'); g=R.gens()
S3=zs[0].parent().hom(list(g[:2])+[g[2]],R)(S)
gens_cm=[S3]+[prod([xi-F(v) for v in V]) for xi in g[:2]]+[g[2]**3-F(t)**3]
Dmax=2**(m-1)+m*len(V)+8
prof=fall_profile(F,gens_cm,list(g),Dmax)
print("CM(orbit) m=2 -- FULL per-isotype fall profile (which syzygies resolve when):",flush=True)
for r in (0,1,2): print(f"  isotype {r}: {prof[r]}",flush=True)
print(f"CM(orbit) Betti: {betti(gens_cm,R)}",flush=True)
# matched nonCM
from semaev_cm_relation_yield_v4 import build_curves, match_nearest
cur=build_curves(p,5,seed=1234+p); j0=[c for c in cur if c['lab']=='j0'][0]
ncm=[c for c in cur if c['lab']=='nonCM']; nc=ncm[match_nearest(j0['order'],ncm,set())]
pyr.seed(2); En=EllipticCurve(F,[nc['A'],nc['B']]); Gn=En.gens()[0]; Nn=int(En.order())
pts=[int(pyr.randrange(1,Nn))*Gn for _ in range(m)]; xcn=[P[0] for P in pts]
Sn=En(0)
for P in pts: Sn=Sn+P
tn=(-Sn)[0]; Vn=sorted(set(xcn)|{F(pyr.randrange(0,p)) for _ in range(4)})
SN,zsn,ttn=summation_poly(F,nc['A'],nc['B'],m); S3n=zsn[0].parent().hom(list(g[:2])+[g[2]],R)(SN)
c0,c1=F(pyr.randrange(1,p)),F(pyr.randrange(1,p))
gens_n=[S3n]+[prod([xi-F(v) for v in Vn]) for xi in g[:2]]+[(g[2]-c0)*(g[2]-c1)*(g[2]-F(tn))]
print(f"nonCM(match) Betti: {betti(gens_n,R)}  (#E gap={abs(nc['order']-j0['order'])})",flush=True)
print("[done]",flush=True)
