# (C2) pivot walk across the cells adjacent to the optimal vertex of each cell (constraint-structure driven; exact path()/sup at every cell).
# Starting points: the near-vertex cell and the exact members of the tree cells with Rhi>11 and the gate.
import sys, time, pickle, heapq, math; sys.path.insert(0,'.')
from b12_cell_lib_v1 import *
from collections import Counter
T0=time.time(); LIM=float(sys.argv[1]) if len(sys.argv)>1 else 520
BEST=F(26433,2209)
d=pickle.load(open('terminals5_J2.pkl','rb')); m=pickle.load(open('cell_members_J2.pkl','rb'))
memb={}
for ci,x in m: memb.setdefault(ci,x)
(x0,)=pickle.load(open('b12_A_x0_v1.pkl','rb'))
starts=[('vertex-cell',x0)]
for i,c in enumerate(d):
    if c[2]>11 and any(s[0]==1 for s in c[0]):
        if i in memb: starts.append(('member%d'%i,memb[i]))
        else:
            x=[F(1)]+[F(w).limit_denominator(10**12) for w in c[4]]
            starts.append(('wit%d'%i,x))
print('start points',len(starts),flush=True)
seen={}; heap=[]; stalls=Counter(); above=[]; cnt=0; expanded=0; bad=0
def push(x,label):
    global cnt,bad
    info=cell_info(x)
    if info['n']==0: return None
    if info['sig'] in seen: return None
    if not gate_ok(info['steps']): return 'gatelost'
    if info['sup'] is None: bad+=1; seen[info['sig']]=None; return None
    seen[info['sig']]=info['sup']; cnt+=1
    if info['sup']>BEST: above.append((label,info['sup'],info['x']))
    heapq.heappush(heap,(-info['sup'],cnt,label,info))
    return 'new'
for lab,x in starts:
    st,R=path(norm(x))
    if len(st)==0: continue
    push(x,lab)
print('initial distinct fine cells',len(seen),'max sup',max(v for v in seen.values() if v is not None),flush=True)
from scipy.optimize import linprog
import numpy as np
def dedupe(rows,idx):
    out={}
    for i in idx:
        a=rows[i]; g=math.gcd(*[abs(t) for t in a]); out.setdefault(tuple(t//g for t in a),i)
    return list(out.values())
def cross(info,S,T):
    """direction with n_i d = -1 (i in S), n_j d >= 1 (j in T\\S); returns exact nbr arrangement or reason"""
    rows=info['rows']; X=info['X']
    A_eq=[[float(t) for t in rows[i][1:]] for i in S]; b_eq=[-1.0]*len(S)
    A_ub=[[-float(t) for t in rows[j][1:]] for j in T if j not in S]; b_ub=[-1.0]*len(A_ub)
    r=linprog(np.zeros(6),A_ub=A_ub or None,b_ub=b_ub or None,A_eq=A_eq,b_eq=b_eq,bounds=[(None,None)]*6,method='highs')
    if r.status!=0: return None,'no pure crossing direction (infeasible)'
    dv=[F(float(t)).limit_denominator(10**6) for t in r.x]
    for k in range(4,14):
        e=F(1,10**k); y=[F(1)]+[X[i+1]+e*dv[i] for i in range(6)]
        # exact check: rows in S violated, rows in T\S satisfied at y
        if all(row_val(rows[i],y)<0 for i in S) and all(row_val(rows[j],y)>=0 for j in T if j not in S):
            return y,None
    return None,'exact direction check failed'
while heap and time.time()-T0<LIM:
    negs,_,lab,info=heapq.heappop(heap); expanded+=1
    rows=info['rows']; X=info['X']
    T=[i for i,a in enumerate(rows) if row_val(a,X)==0]; T=dedupe(rows,T)
    subs=[(i,) for i in T]+[(i,j) for ii,i in enumerate(T) for j in T[ii+1:]]
    for S in subs:
        y,why=cross(info,S,T)
        if y is None: stalls[('nodir',len(S))]+=1; continue
        r=push(y,lab+'>x')
        if r=='gatelost': stalls[('gate/len lost across', tuple(row_meaning(info['tags'][i]).split(':')[1].strip()[:40] for i in S))]+=1
print('expanded cells',expanded,'distinct fine cells with exact sup',len([v for v in seen.values() if v is not None]),'sup-failed',bad)
vals=sorted([v for v in seen.values() if v is not None],reverse=True)
print('top exact cell sups:',[(str(v),float(v)) for v in vals[:8]])
print('cells with sup > 26433/2209:',len(above))
for a in above[:10]: print(a[0],a[1],[str(t) for t in a[2]])
print('frontier left',len(heap),' time',time.time()-T0)
print('no-crossing / loss counts:')
for k,v in stalls.most_common(25): print('  ',v,k)
