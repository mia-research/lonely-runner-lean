import sys, random, math; sys.path.insert(0,'.')
from envl_common_v1 import *
random.seed(3); W=40.0
def blocks_f(R,r):
    p=(R*r)%8; return min(p,8-p)<1-1e-9
def pathf(rh):
    R=1/rh[0]; st=[]
    while True:
        bl=[i for i,r in enumerate(rh) if blocks_f(R,r)]
        if not bl: return st
        R2,s=max(((8*round(R*rh[i]/8)+1)/rh[i],i) for i in bl); st.append(s); R=R2
        if len(st)>200: return st
found=0
for _ in range(400000):
    top=7+(W-7)*random.random(); mode=random.random()
    if mode<0.4: mid=[random.uniform(1,top) for _ in range(5)]
    elif mode<0.8: mid=[math.exp(random.uniform(0,math.log(top))) for _ in range(5)]
    else: mid=[random.uniform(top*0.5,top) for _ in range(5)]
    rh=sorted([1.0]+mid+[top]); st=pathf(rh)
    if len(st)>=3 and len(set(st[:3]))<3 and rh[4]<343/81-1e-9:
        r=[F(x).limit_denominator(10**6) for x in rh]; r[0]=F(1)
        steps,R=path(r); sett=[s['setter']+1 for s in steps]
        if len(steps)>=3 and len(set(sett[:3]))<3 and sorted(r)[4]<F(343,81):
            print('exact arrangement',[str(x) for x in r]); print('setters(rank)',sett[:6],'moves',len(steps),'rho_5',float(r[4]),'< 343/81 =',float(F(343,81)))
            print('laps',[s['lap'] for s in steps][:6]); found+=1
            if found>=2: break
print('found',found)
