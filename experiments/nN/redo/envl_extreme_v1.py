# exact extremal vertices per (rank, threshold, side); certificate: vertex exact-feasible, and vertex + eps*(interior-vertex) has the SAME exact signature
import sys,glob; sys.path.insert(0,'.')
from envl_lp_v1 import *
J=int(sys.argv[1]); W={1:9,2:17}[J]
SP='/private/tmp/claude-501/-Users-trentpalelei-Desktop-Math-Ex/ed62988a-aa4c-4682-b812-d4182b31b4a6/scratchpad/'
if J==1:
    o=pickle.load(open(SP+'envl_lpfull_J1.pkl','rb')); o={k:(v[0],v[1],v[2],v[3]) for k,v in o.items()}
else:
    o={}
    for f in glob.glob(SP+'envl_chunk_J2_*.pkl'): o.update(pickle.load(open(f,'rb')))
print('J',J,'sigs',len(o))
def interior(A):
    Aub=np.array([c+[np.linalg.norm(c)] for c,b in A],float); bub=np.array([b for c,b in A],float)
    Aeq=np.zeros((1,8)); Aeq[0,0]=1
    c=np.zeros(8); c[7]=-1
    r=linprog(c,A_ub=Aub,b_ub=bub,A_eq=Aeq,b_eq=[1],bounds=[(0,None)]*7+[(0,1)],method='highs')
    return r.x[:7]
res={}
for th in (2,10):
  for side in ('min','max'):
    if side=='max' and th==2: continue
    for r in range(6):
        best=None
        for sg,(n,idx,lo,hi) in o.items():
            if n<th: continue
            v=lo[r] if side=='min' else hi[r]
            if v is None: continue
            if best is None or (v<best[0] if side=='min' else v>best[0]): best=(v,sg,n)
        v,sg,n=best
        A=rows(sg,W); a=lp(A,r+1,1 if side=='min' else -1)
        xv=exact_vertex(A,a.x)
        if xv is None: print('rank',r+2,th,side,'float',v,'NO exact vertex'); continue
        ok=feasible(A,xv); val=xv[r+1]
        xi=interior(A); eps=F(1,10**6)
        xe=[xv[i]+eps*(F(float(xi[i])).limit_denominator(10**9)-xv[i]) for i in range(7)]
        sg2,n2=signature(xe)
        print(f'rank {r+2} thr>={th} {side}: float {v:.9f} exact {val} = {float(val):.9f} feasible={ok} same_sig_after_nudge={sg2==sg} nmoves={n}')
        print('   vertex',[str(x) for x in xv]); print('   path (setter rank,lap):',[(s+1,j) for s,j,_ in sg[1:]])
