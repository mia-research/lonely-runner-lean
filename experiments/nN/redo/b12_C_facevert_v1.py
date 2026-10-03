# (C2b) cross the facets at every extreme vertex of the optimal face of the extremal cell (not only the one LP vertex); then continue best-first.
import sys, time, pickle, heapq, math; sys.path.insert(0,'.')
from b12_cell_lib_v1 import *
from collections import Counter
from scipy.optimize import linprog
import numpy as np
T0=time.time(); LIM=float(sys.argv[1]) if len(sys.argv)>1 else 500
BEST=F(26433,2209)
(x0,)=pickle.load(open('b12_A_x0_v1.pkl','rb'))
base=cell_info(x0); rows=base['rows']
face=rows+[[2209,0,0,0,0,0,-297]]
verts={}
for k in range(2,7):
    for sg in (1,-1):
        c=[0]*6; c[k-2]=sg
        r=min_rho_s_exact(face,0,cvec=c)
        if r: verts[tuple(r[0])]=1
print('distinct exact face vertices',len(verts),flush=True)
def dedupe(rows,idx):
    out={}
    for i in idx:
        a=rows[i]; g=math.gcd(*[abs(t) for t in a]); out.setdefault(tuple(t//g for t in a),i)
    return list(out.values())
def cross(rows,X,S,T):
    A_eq=[[float(t) for t in rows[i][1:]] for i in S]; b_eq=[-1.0]*len(S)
    A_ub=[[-float(t) for t in rows[j][1:]] for j in T if j not in S]; b_ub=[-1.0]*len(A_ub)
    r=linprog(np.zeros(6),A_ub=A_ub or None,b_ub=b_ub or None,A_eq=A_eq,b_eq=b_eq,bounds=[(None,None)]*6,method='highs')
    if r.status!=0: return None
    dv=[F(float(t)).limit_denominator(10**6) for t in r.x]
    for k in range(4,14):
        e=F(1,10**k); y=[F(1)]+[X[i+1]+e*dv[i] for i in range(6)]
        if all(row_val(rows[i],y)<0 for i in S) and all(row_val(rows[j],y)>=0 for j in T if j not in S): return y
    return None
seen={base['sig']:base['sup']}; res=Counter(); above=[]; nbr=[]; heap=[]; cnt=0
def push(y):
    global cnt
    info=cell_info(y)
    if info['n']==0 or info['sig'] in seen: return 'dup'
    if not gate_ok(info['steps']): return 'lost'
    seen[info['sig']]=info['sup']
    if info['sup'] is None: return 'nosup'
    cnt+=1; heapq.heappush(heap,(-info['sup'],cnt,info))
    if info['sup']>BEST: above.append((info['sup'],info['x']))
    return 'new'
for X in verts:
    T=dedupe(rows,[i for i,a in enumerate(rows) if row_val(a,list(X))==0])
    subs=[(i,) for i in T]+[(i,j) for ii,i in enumerate(T) for j in T[ii+1:]]
    for S in subs:
        y=cross(rows,list(X),S,T)
        if y is None: res['nodir']+=1; continue
        res[push(y)]+=1
print('level-1 results',dict(res),'distinct new cells',cnt,flush=True)
while heap and time.time()-T0<LIM:
    ns,_,info=heapq.heappop(heap); rows2=info['rows']; X=info['X']
    T=dedupe(rows2,[i for i,a in enumerate(rows2) if row_val(a,X)==0])
    subs=[(i,) for i in T]+[(i,j) for ii,i in enumerate(T) for j in T[ii+1:]]
    for S in subs:
        y=cross(rows2,X,S,T)
        if y is None: res['nodir']+=1; continue
        res[push(y)]+=1
vals=sorted([v for v in seen.values() if v is not None],reverse=True)
print('fine cells with exact sup',len(vals),' top',[(str(v),float(v)) for v in vals[:6]])
print('cells above 26433/2209:',len(above)); [print(a) for a in above[:5]]
print('level-1+ results',dict(res),' frontier left',len(heap),'time',time.time()-T0)
print('distinct exact sups > 11.5:',sorted(set(str(v) for v in vals if v>F(23,2))))
