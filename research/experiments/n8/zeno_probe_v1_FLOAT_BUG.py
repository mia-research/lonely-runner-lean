from fractions import Fraction as F
from math import floor
def blocked(d,t):
    f=d*t-floor(d*t); return f<F(1,8) or f>F(7,8)
def nxt(d,t):
    j=floor(d*t+F(1,8)); return (8*j+1)/(8*d)
def trace(ds,k):
    m=min(ds); t=F(1,8*m); out=[]
    for n in range(k):
        bl=[d for d in ds if blocked(d,t)]
        if not bl: return out,t,True
        d=max(bl,key=lambda d:nxt(d,t)); t2=nxt(d,t); out.append((d,t2)); t=t2
    return out,t,False
for ds in [(1,19,20,21,22,23,24),(1,5,6,8,15,21,22)]:
    out,t,fin=trace(ds,400)
    ts=F(49,176)
    print(ds,"finished",fin,"t* clear?",all(not blocked(d,ts) for d in ds))
    for d,t2 in out[-6:]: print("  setter",d,"gap to t*=",float(ts-t2), "denominator digits",len(str(t2.denominator)))
    # gap ratio
    gaps=[ts-t2 for d,t2 in out[-40:]]
    print("  last setters",[d for d,_ in out[-12:]])
    print("  gap ratios",[float(gaps[i+1]/gaps[i]) for i in range(len(gaps)-6,len(gaps)-1)])
