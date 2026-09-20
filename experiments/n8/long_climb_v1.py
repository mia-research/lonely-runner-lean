import sys; sys.path.insert(0,'.')
from fractions import Fraction as F
import random
from lapvector_decide_v1 import diffs
def moment_u(ds):
    m=min(ds); lo=F(1,8*m); hi=F(7,8*m); B={lo,hi}
    for d in ds:
        k=0
        while F(8*k+1,8)/d<=hi:
            for num in (8*k+1,8*k+7):
                t=F(num,8)/d
                if lo<=t<=hi: B.add(t)
            k+=1
    B=sorted(B)
    def clear(t): return all(min((d*t)%1,1-(d*t)%1)>=F(1,8) for d in ds)
    for i,t in enumerate(B):
        if clear(t): return m*t
        if i+1<len(B) and clear((t+B[i+1])/2): return m*(t+B[i+1])/2
    return None
random.seed(int(sys.argv[1])); LIM=int(sys.argv[2]); best=(F(0),None)
for restart in range(4000):
    V=sorted(random.sample(range(1,LIM),8))
    cur=max((moment_u(sorted(diffs(V,i))) or F(0)) for i in range(8))
    for it in range(1500):
        W=list(V); j=random.randrange(8)
        W[j]+=random.choice((-5,-3,-2,-1,1,2,3,5))
        if W[j]<1 or W[j]>LIM*3 or len(set(W))<8: continue
        W=sorted(W)
        try: s=max((moment_u(sorted(diffs(W,i))) or F(0)) for i in range(8))
        except Exception: continue
        if s>=cur: V,cur=W,s
        if cur>best[0]:
            best=(cur,tuple(V))
            print('u = %-14s = %.6f   at %s   (7/8 = 0.875)'%(str(best[0]),float(best[0]),str(best[1])), flush=True)
            if best[0]>F(7,8): print('*** EXCEEDS 7/8 ***', flush=True); sys.exit(0)
print('done. best u =',str(best[0]),float(best[0]),'at',best[1])
