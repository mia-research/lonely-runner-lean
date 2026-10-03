# retry the interior-nudge certificate for the upper-side extremes with smaller eps and an exact interior point
import sys,glob; sys.path.insert(0,'.')
from envl_lp_v1 import *
J=int(sys.argv[1]); W={1:9,2:17}[J]
SP='/private/tmp/claude-501/-Users-trentpalelei-Desktop-Math-Ex/ed62988a-aa4c-4682-b812-d4182b31b4a6/scratchpad/'
if J==1: o=pickle.load(open(SP+'envl_lpfull_J1.pkl','rb')); o={k:(v[0],v[1],v[2],v[3]) for k,v in o.items()}
else:
    o={}
    for f in glob.glob(SP+'envl_chunk_J2_*.pkl'): o.update(pickle.load(open(f,'rb')))
def interior(A):
    Aub=np.array([c+[np.linalg.norm(c)] for c,b in A],float); bub=np.array([b for c,b in A],float)
    Aeq=np.zeros((1,8)); Aeq[0,0]=1; c=np.zeros(8); c[7]=-1
    r=linprog(c,A_ub=Aub,b_ub=bub,A_eq=Aeq,b_eq=[1],bounds=[(0,None)]*7+[(0,1)],method='highs'); return r.x[:7],r.x[7]
for r in range(6):
    cand=sorted(((hi[r],sg,n) for sg,(n,idx,lo,hi) in o.items() if n>=10 and hi[r] is not None),key=lambda z:-z[0])
    rej=0
    for v,sg,n in cand:
        A=rows(sg,W); xi,t=interior(A)
        if t>1e-7: break
        rej+=1
    a=lp(A,r+1,-1); xv=exact_vertex(A,a.x)
    xi=[F(float(z)).limit_denominator(10**12) for z in xi]; xi[0]=F(1)
    inter_ok=all(sum(F(ci)*xx for ci,xx in zip(c,xi))<=b for c,b in A)
    res=None
    for e in (6,8,10,12,14):
        eps=F(1,10**e); xe=[xv[i]+eps*(xi[i]-xv[i]) for i in range(7)]
        sg2,n2=signature(xe)
        if sg2==sg: res=(e,float(xe[r+1])); break
    print(f'J{J} rejected-degenerate-candidates-above={rej} rank {r+2} sup {xv[r+1]} interior-slack t={t:.3e} interior exact-feasible={inter_ok} nudge same sig at eps=1e-{res[0] if res else None}; rank value there {res[1] if res else None}')
