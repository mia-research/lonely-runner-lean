# K6 = clear set of readings 1..6 on [1,7] (closed windows, one-point windows included).  Test  L_max >= 2/(7 rho_6)  and look at how close it comes.
import sys, random, math
from fractions import Fraction as F
def comps(rho, lo=F(1), hi=F(7)):
    Z=[]
    for r in rho:
        j=1
        while F(8*j-1)/r < hi+1: Z.append((F(8*j-1)/r,F(8*j+1)/r)); j+=1
    Z.sort(); out=[]; cur=lo
    for a,b in Z:
        if b<=cur: continue
        if a>=cur and cur<=min(a,hi): out.append((cur,min(a,hi)))
        cur=max(cur,b)
        if cur>hi: break
    if cur<=hi: out.append((cur,hi))
    return out
rnd=random.Random(int(sys.argv[1])); N=int(sys.argv[2])
def q(x): return F(round(x*10**6),10**6)
def fam(kind):
    if kind==0: xs=sorted(q(math.exp(rnd.uniform(0,math.log(rnd.choice((9,20,60,200)))))) for _ in range(5))
    elif kind==1: xs=sorted(q(rnd.uniform(1.05,rnd.choice((8,12,20,40)))) for _ in range(5))
    elif kind==2: c=q(rnd.uniform(1.02,1.6)); xs=sorted(c*k+q(rnd.uniform(-.06,.06)) for k in range(2,7))        # AP-like with deviation
    elif kind==3: xs=sorted(F(k)+q(rnd.uniform(-.3,.3)) for k in rnd.sample(range(2,16),5))
    else: xs=sorted(F(k,rnd.choice((2,3,5,7)))+q(rnd.uniform(-.01,.01)) for k in rnd.sample(range(3,90),5))
    return [F(1)]+xs
worst=None; tot=0; viol=0; ratios=[]
for t in range(N):
    rho=fam(t%5)
    if len(set(rho))<6 or sorted(rho)!=rho or rho[1]<=1: continue
    W=comps(rho); tot+=1
    L=max((b-a for a,b in W), default=F(-1)); bound=F(2)/(7*rho[5])
    ratios.append(L/bound)
    if L<bound:
        viol+=1
        if worst is None or L/bound<worst[0]: worst=(L/bound,rho,L)
mn=min(ratios)
print(f"six-reading arrangements {tot} | longest component L < 2/(7 rho_6): {viol} | smallest L / (2/(7 rho_6)) = {float(mn):.4f}")
if worst: print("  smallest ratio arrangement:",[str(x) for x in worst[1]],"L",float(worst[2]))
