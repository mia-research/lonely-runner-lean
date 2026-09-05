import sys; sys.path.insert(0,"/Users/trentpalelei/Desktop/Math Ex/btc_puzzle_investigation")
from delta_r_corrected_v2 import cube_root, d_LF_plain, blockLF, cell
from sage.all import *
from semaev_elimination_v1 import summation_poly, decomposition_system
def one(p,m,seed):
    F=GF(p); beta=cube_root(F); c=cell(F,m,beta,seed)
    if c is None: return None
    t,V=c
    Rxf,gf,xsf=decomposition_system(F,0,7,m,t,V); Dmax=2**(m-1)+m*len(V)+8
    df=d_LF_plain(F,gf,xsf,Dmax)
    S,zs,tt=summation_poly(F,0,7,m); vn=['x%d'%i for i in range(1,m+1)]+['xT']
    R=PolynomialRing(F,vn,order='degrevlex'); g=R.gens()
    S4=zs[0].parent().hom(list(g[:m])+[g[m]],R)(S)
    gens=[S4]+[prod([xi-F(v) for v in V]) for xi in g[:m]]+[g[m]**3-F(t)**3]
    lf=blockLF(F,gens,list(g),Dmax+4)
    return df,lf,{r:(df-lf[r] if (df and lf[r]) else None) for r in (0,1,2)}
print("m=2 delta_r sweep -- is {-2,0,-1} forced/universal, or does it vary?")
for p in (523,541,547,571,577,601):
    for seed in (1,2):
        r=one(p,2,seed)
        if r: print(f"  p={p} seed{seed}: d_LF_fixed={r[0]:2} blocks={r[1]} delta_r={r[2]}",flush=True)
print("[done]")
