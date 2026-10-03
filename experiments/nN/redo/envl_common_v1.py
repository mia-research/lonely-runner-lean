import pickle, sys
from fractions import Fraction as F
exec(open('cascade_path_map_v1.py').read().split('\nif __name__ ==')[0])
exec(open('outcome_classes_v2.py').read().split('\nif __name__ ==')[0])
def load(J):
    T=pickle.load(open(f'terminals5_J{J}.pkl','rb')); M=pickle.load(open(f'cell_members_J{J}.pkl','rb'))
    return T,M
def signature(rhos):
    """combinatorial type of the cascade from rhos (sorted, rhos[0]==1): returns (sig, nmoves)."""
    steps,Rf=path(rhos)
    states=[]
    R=F(1); s=0; j=0
    seq=[(0,0)]+[(None,None)]*0
    # states: R0=1 (setter rank 0, j=0), then each step R2 with setter/lap
    for st in steps: seq.append((st['setter'],st['lap']))
    out=[]
    Rk=[F(1)]+[st['R2'] for st in steps]
    for k,(s,j) in enumerate(seq):
        R=Rk[k]; per=[]
        for y,r in enumerate(rhos):
            if y==s: per.append(None); continue
            u=R*r; p=u%8
            if min(p,8-p)<1:
                per.append(('B',int(round(u/8))))
            else:
                per.append(('G',int(u//8)))
        out.append((s,j,tuple(per)))
    return tuple(out), len(steps)
def rows(sig,W):
    """constraints A x <= b over x=(rho1..rho7); returns list (coef list, b), plus equality rho1=1"""
    n=7; A=[]
    def row(d,b): 
        c=[0]*n
        for i,v in d.items(): c[i]+=v
        A.append((c,b))
    for i in range(6): row({i:1,i+1:-1},0)   # rho_i <= rho_{i+1}
    row({6:1},W)
    for k,(s,j,per) in enumerate(sig):
        for y,e in enumerate(per):
            if e is None: continue
            t,l=e
            # u = (8j+1) rho_y / rho_s ; compare to bounds, multiply by rho_s
            if t=='B': lo,hi=8*l-1,8*l+1
            else: lo,hi=8*l+1,8*l+7
            # u>=lo : lo*rho_s - (8j+1)rho_y <=0 ; u<=hi: (8j+1)rho_y - hi*rho_s <=0
            row({s:lo,y:-(8*j+1)},0) if s!=y else None
            row({y:(8*j+1),s:-hi},0)
        # max-exit constraint at step k>=1: previous state's blockers (laps) exit <= this exit
        if k>=1:
            ps,pj,pper=sig[k-1]
            for y,e in enumerate(pper):
                if e is None:
                    pass
                if y==ps: continue
                if y!=s and e is not None and e[0]=='B':
                    l=e[1]
                    row({s:(8*l+1),y:-(8*j+1)},0)
            # the previous setter was also a blocker (its own state: R=(8pj+1)/rho_ps, in zone j'): its exit is (8*lap+1)/rho; setter == itself if s==ps
        pass
    return A
