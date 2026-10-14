from fractions import Fraction as F
from math import floor
import sys
def blocked(d,t):
    f=d*t-floor(d*t); return f<F(1,8) or f>F(7,8)
def nxt(d,t):
    j=floor(d*t+F(1,8)); return (8*j+1)/(8*d)
def run(ds,limit):
    m=min(ds); t=F(1,8*m); n=0
    while n<limit:
        bl=[d for d in ds if blocked(d,t)]
        if not bl: return n,t,8*m*t
        d=max(bl,key=lambda d:nxt(d,t)); t=nxt(d,t); n+=1
    return None,t,8*m*t
for ds in [(1,5,6,8,15,21,22),(1,5,6,8,19,21,22),(1,5,6,16,19,21,22),(1,19,20,21,22,23,24)]:
    n,t,R=run(ds,50000)
    print(ds,"moves",n,"t=",t if n is not None else "unfinished","R~",float(R),flush=True)
