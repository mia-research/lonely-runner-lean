# (C1) exact line scans from the near-vertex arrangement and (C3) exact cell suprema for the gate-crossing cells with tree Rhi > 11.
import sys, time, pickle; sys.path.insert(0,'.')
from b12_cell_lib_v1 import *
from collections import Counter
T0=time.time(); LIM=float(sys.argv[1]) if len(sys.argv)>1 else 520
BEST=F(26433,2209)
(x0,)=pickle.load(open('b12_A_x0_v1.pkl','rb'))
# near-vertex interior arrangement: vertex pulled toward x0 by exact 1e-9 and re-verified
v=[F(1),F(16715503,7123545),F(47,15),F(726761,173745),F(47,9),F(15463,2673),F(2209,297)]
xn=None
for k in range(4,16):
    e=F(1,10**k); y=[a+e*(b-a) for a,b in zip(v,x0)]
    st,R=path(y)
    if tuple((s['setter']+1,s['lap']) for s in st)==tuple((s['setter']+1,s['lap']) for s in path(x0)[0]): xn=y;break
print('near-vertex arrangement at eps=1e-%d: R*=%.9f len=%d'%(k,float(R),len(st)))
base=cell_info(xn)
print('its fine cell sup',base['sup'],float(base['sup']))
res=Counter(); stall=Counter(); maxseen=F(0); above=[]
def scan(x,d,label,maxcells=400):
    """walk along x+t d, exact rational intervals; step across each boundary by an exact eps"""
    global maxseen
    cur=norm(x); t=F(0); cells=0; direction=1
    pos=cur
    while cells<maxcells and time.time()-T0<LIM:
        info=cell_info(pos)
        cells+=1
        if info['sup'] is not None:
            maxseen=max(maxseen,info['sup'])
            if info['sup']>BEST: above.append((label,info['sup'],pos))
        # exact interval along direction d from pos: rows a.(pos+s d)>=0
        hi=None; hirow=None
        for r,tg in zip(info['rows'],info['tags']):
            ad=sum(F(a)*b for a,b in zip(r,d)); av=row_val(r,pos)
            if ad<0:
                s=av/(-ad)
                if hi is None or s<hi: hi=s; hirow=tg
        if hi is None: stall[(label[0],'unbounded')]+=1; return cells,'unbounded'
        eps=F(1,10**9)*max(hi,F(1,10**3)) if hi>0 else F(1,10**12)
        new=[p+(hi+eps)*q for p,q in zip(pos,d)]
        # ensure we stepped into a cell different from this one
        ni=cell_info(new,with_sup=False)
        if ni['n']==0 or not gate_ok(ni['steps']):
            stall[(label[0],row_meaning(hirow))]+=1
            return cells,'stall at '+row_meaning(hirow)+(' gate/len lost: len %d gate %s'%(ni['n'],any(s['setter']==0 for s in ni['steps'])))
        if any(new[i]>=new[i+1] for i in range(6)) or new[0]!=1:
            stall[(label[0],'order')]+=1; return cells,'stall at order'
        pos=new
    return cells,'budget'
tot=0
for i in range(1,7):
    for sg in (1,-1):
        d=[0]*7; d[i]=sg
        c,why=scan(xn,d,('single',i+1,sg)); tot+=c
        print('single rho%d %+d: %d cells visited, end: %s'%(i+1,sg,c,why),flush=True)
for i in range(1,7):
    for j in range(i+1,7):
        for si,sj in ((1,1),(1,-1),(-1,1),(-1,-1)):
            d=[0]*7; d[i]=si; d[j]=sj
            c,why=scan(xn,d,('pair',i+1,j+1,si,sj),maxcells=150); tot+=c
            print('pair rho%d%+d rho%d%+d: %d cells, end: %s'%(i+1,si,j+1,sj,c,why),flush=True)
print('cells visited in line scans:',tot,' max exact cell sup seen:',maxseen,float(maxseen),' cells with sup > 26433/2209:',len(above))
print('stall causes:'); 
for k,v in stall.most_common(): print('  ',v,k)
