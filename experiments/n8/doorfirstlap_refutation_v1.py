from fractions import Fraction as F
import math

N = 8
THR = F(1,N)

def frac(x):  # exact fractional part of a positive Fraction
    return x - (x.numerator // x.denominator)

def circdist(x):
    f = frac(x)
    return min(f, 1-f)

def inway(d,t):  return circdist(d*t) < THR
def nextopening(d,t):
    Q = math.ceil(d*t - THR)          # exact: Fraction -> int
    return (F(Q)+THR)/d, Q

def move(ds,t):
    best=None
    for d in ds:
        if inway(d,t):
            op,Q = nextopening(d,t)
            if best is None or op>best[0]: best=(op,d,Q)
    return best

def cascade(ds):
    m=min(ds); t=F(1)/(N*m); words=[]
    while True:
        b=move(ds,t)
        if b is None: return t,m,words
        words.append((b[1],b[2],b[0])); t=b[0]

def lonely(ds,t): return all(circdist(d*t)>=THR for d in ds)

v=[27,70,107,137,159,188,344,393]; k=393
ds=sorted(F(abs(x-k)) for x in v if x!=k)
t,m,w=cascade(ds)
print("ds            =",[str(x) for x in ds])
print("d_min m       =",m)
print("fixed point t =",t, " (manuscript records t = 49/1872)")
print("t == 49/1872  :", t==F(49,1872))
print("lonely at t   :", lonely(ds,t))
print("circDist(d*t) :",[str(circdist(d*t)) for d in ds], " all >= 1/8:", lonely(ds,t))
print("tau = m*t     =",m*t,"=",float(m*t))
print()
print("DoorFirstLap asserts  t <= 1/leastDisp  i.e.  m*t <= 1")
print("   here  m*t =",m*t,">",1, "->", "REFUTED" if m*t>1 else "holds")
print()
# is it the FIRST lonely instant? scan openings below t to be sure nothing earlier is lonely
cands=set()
for d in ds:
    j=0
    while True:
        op=(F(j)+THR)/d
        if op>t: break
        if op>0: cands.add(op)
        j+=1
print("openings at or before t:",len(cands),
      " any earlier lonely:",sorted(x for x in cands if x<t and lonely(ds,x))[:3])
print()
# second named case
v2=[1,31,75,97,128,160,176,225]; k2=1
ds2=sorted(F(abs(x-k2)) for x in v2 if x!=k2)
t2,m2,w2=cascade(ds2)
print("case 2 ds     =",[str(x) for x in ds2])
print("  t =",t2," m*t =",m2*t2,"=",float(m2*t2),
      " (manuscript: 'first lonely at u = 165/128, in its second lap')")
print("  u == 165/128:", m2*t2==F(165,128), " lonely:",lonely(ds2,t2), " -> m*t > 1:", m2*t2>1)
