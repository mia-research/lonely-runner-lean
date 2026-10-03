# Exact check of the proof steps of k2s1_decision_v1.md on random exact arrangements (incl. rho_7 up to 1000).
import random, pickle, sys
from fractions import Fraction as F
exec(open('outcome_classes_v2.py').read().split('\nif __name__ ==')[0])
random.seed(20261003)
def entries(rho, lo, hi):  # entries (8j-1)/rho, j>=1, in [lo,hi)
    out=[]; j=1
    while (8*j-1)/rho < hi:
        e=F(8*j-1)/rho
        if e>=lo: out.append((e,j))
        j+=1
    return out
def rnd(a,b): return F(random.randint(int(a*10**6),int(b*10**6)),10**6)
cells=pickle.load(open('terminals5_J2.pkl','rb'))
sel=[c for c in cells if c[0][-1] in ((2,1),(1,1))]
print("cells with last move (2,1)/(1,1):",len(sel))
def gen(mode):
    if mode==0:   # from a (2,1)/(1,1) cell box, ranks 6,7 pushed up
        c=random.choice(sel); rg=c[3]; r=[F(1)]
        for k in range(1,5): r.append(rnd(float(rg[k][0]),float(rg[k][1])))
        top=random.choice([17,100,1000]); r.append(rnd(float(rg[5][0]),top)); r.append(rnd(float(rg[6][0]),top))
        return r
    if mode==1:   # chain-shaped: setter chain of lap-1 zones, readings in (7,12)
        r=[F(1)]+[rnd(1.0001,12) if random.random()<.3 else rnd(5,12) for _ in range(6)]
        return r
    if mode==2:
        return [F(1)]+[rnd(1.0001,random.choice([20,100,1000])) for _ in range(6)]
    # mode 3: all readings in a narrow band (4/3 rule region)
    b=rnd(5,10); return [F(1)]+[b*rnd(1,1.33) for _ in range(6)]
N=int(sys.argv[1]) if len(sys.argv)>1 else 40000
stat=dict(total=0,distinct=0,moves2=0,open_lap1=0,open_lap1_m2=0,k2s1=0,caseA=0,caseB=0,viol=0)
for n in range(N):
    r=gen(n%4); stat['total']+=1
    if len(set(r))<7: continue
    stat['distinct']+=1
    r=sorted(r); o=outcome(r)
    if o['nmoves']>=2: stat['moves2']+=1
    if o['opener'] and o['opener'][1]==1:
        stat['open_lap1']+=1
        if o['nmoves']>=2:
            stat['open_lap1_m2']+=1
            s=o['opener'][0]-1; p=o['path'][-2][0]-1; rs=r[s]; rp=r[p]; Rst=o['R']
            assert Rst==9/rs
            # the proof: previous setter p
            if rp>=F(4,3)*rs:
                stat['caseA']+=1
                e=entries(rp,9/rs,15/rs)
                if not e: stat['viol']+=1; print("caseA viol",r)
            else:
                stat['caseB']+=1
                ok = o['path'][-2][1]==1 and rp>rs and 9/rs<=15/rp<15/rs
                if not ok: stat['viol']+=1; print("caseB viol",r)
            if o['closer']==(s+1,2): stat['k2s1']+=1; print("K2s1 HIT",r)
print(stat)
