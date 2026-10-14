from fractions import Fraction as F
import math
def casc(speeds,k,n=8):
    ds=[abs(v-speeds[k]) for i,v in enumerate(speeds) if i!=k]
    t=F(1,n*min(ds)); steps=[t]
    def dist(x): x=x-math.floor(x); return min(x,1-x)
    while True:
        ways=[d for d in ds if dist(d*t)<F(1,n)]
        if not ways: return t,steps
        t=max(F(math.floor(d*t-F(1,n))+1,1)/d+F(1,n)/d if False else (math.floor(d*t-F(1,n))+1+F(1,n))/d for d in ways)
        steps.append(t)
for S in ([1,2,3,4,5,6,7,8],[1,2,3,4,5,6,7,16],[1,2,3,4,5,6,7,15]):
    print(S)
    for k in range(8):
        t,st=casc(S,k); print(' runner',k+1,'speed',S[k],'first lonely t=',t,'moves',len(st)-1)
