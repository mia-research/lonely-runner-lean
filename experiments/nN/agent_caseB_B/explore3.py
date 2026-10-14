import random, time, sys
from fractions import Fraction as F
from core import *
random.seed(int(sys.argv[1]) if len(sys.argv)>1 else 2)
D=2520
def valid(x): return all(x[i]<x[i+1] for i in range(6)) and x[0]==D and 9*D<x[6]<=24*D
def val(x):
    rd=[F(v,D) for v in x]; R,s=first_lonely(rd); return R
best=None;bestx=None
t=time.time()
for rs in range(60):
    top=random.randint(9*D+1,24*D)
    x=[D]+sorted(random.sample(range(D+1,top),5))+[top]
    v=val(x)
    for it in range(1500):
        y=x[:]
        k=random.randint(1,6); y[k]+=random.randint(-D//(1+random.randint(0,40)),D//(1+random.randint(0,40)))
        y[1:]=sorted(y[1:])
        if not valid(y): continue
        w=val(y)
        if w>=v: x,v=y,w
    if best is None or v>best: best,bestx=v,x
print(float(best),best,[str(F(a,D)) for a in bestx],time.time()-t)
