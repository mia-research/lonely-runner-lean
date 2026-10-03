# (B) exact identities / inequalities checked on the exact near-supremum arrangements of the gate-crossing cells with tree Rhi > 11.
import sys, pickle; sys.path.insert(0,'.')
from b12_cell_lib_v1 import *
from collections import Counter
d=pickle.load(open('terminals5_J2.pkl','rb')); m=pickle.load(open('cell_members_J2.pkl','rb'))
memb={}
for ci,x in m: memb.setdefault(ci,x)
pts=[]
for i,c in enumerate(d):
    if c[2]>11 and any(s[0]==1 for s in c[0]):
        pts.append(memb[i] if i in memb else [F(1)]+[F(w).limit_denominator(10**12) for w in c[4]])
ok_id=0; tot=0; lapb=[]; viol=0; seen=set()
for x in pts:
    x=norm(x); steps,R=path(x)
    key=tuple((s['setter'],s['lap']) for s in steps)
    if key in seen: continue
    seen.add(key); tot+=1
    kg=next(k for k,s in enumerate(steps) if s['setter']==0)   # move index of (1,1); state after = steps[kg]['R2'] = 9
    assert steps[kg]['R2']==9
    # identity: R* - 9 = sum over later moves of (2/rho - slack), slack = R_k - entry(setter,lap)
    tail=steps[kg+1:]; tot_id=F(0)
    for s in tail:
        rho=x[s['setter']]; entry=F(8*s['lap']-1)/rho
        tot_id+=F(2)/rho-(s['R']-entry)
    if R-9==tot_id: ok_id+=1
    # lap-ratio inequality: opener o = last setter, lap jo; for every earlier state a where o is blocked at lap ja: R* <= R_a (8jo+1)/(8ja-1)
    o=steps[-1]['setter']; jo=steps[-1]['lap']
    best=None
    states=[(0,F(1))]+[(k+1,s['R2']) for k,s in enumerate(steps)]
    for k,Rk in states[:-1]:
        if blocks(Rk,x[o]):
            ja=round(Rk*x[o]/8); b=Rk*F(8*jo+1)/(8*ja-1)
            if R>b: viol+=1
            if best is None or b<best[0]: best=(b,k,ja)
    lapb.append((best,o+1,jo,R))
print('cells (distinct paths) examined',tot,' identity R*-9 = sum(2/rho-slack) exact in',ok_id)
print('lap-ratio inequality violations:',viol)
lapb.sort(key=lambda t:-t[3])
print('tightest lap-ratio bound per cell (top 8 by R*): (bound, state k, lap at k), opener rank, opener lap, R*')
for b,o,jo,R in lapb[:8]: print('  ',b[0] if b else None, float(b[0]) if b else None, b[1:] if b else None,o,jo,float(R))
print('cells whose tightest lap-ratio bound exceeds 12:',sum(1 for b,o,jo,R in lapb if b and b[0]>12),' of ',len(lapb))
print('cells with no earlier state at which the opener is blocked:',sum(1 for b,o,jo,R in lapb if b is None),' of ',len(lapb))
print('cells whose tightest lap-ratio bound is <= 12:',sum(1 for b,o,jo,R in lapb if b and b[0]<=12))
print('max over cells of the tightest bound:',max(b[0] for b,o,jo,R in lapb if b),float(max(b[0] for b,o,jo,R in lapb if b)))
