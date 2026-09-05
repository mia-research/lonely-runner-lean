from math import gcd
from fractions import Fraction as F
def fract(num,den): return F(num%den,den)
def in_R(X,Y): return F(1,6)<=X<=F(1,2) and F(1,6)<=Y<=F(1,3)
# (5,2): relation 5p≡2r mod q -> 2r-5p=cq. r in (q,3q/2). check c-range and R-witness
print("=== (5,2): 5p≡2r, 2r=5p+cq ===")
from collections import Counter
ccount=Counter(); norwit=0; tot=0
for q in range(30,80):
    for p in range(1,q):
        if 3*p>=q or gcd(p,q)!=1: continue
        for r in range(q+1,(3*q-1)//2+1):
            if 2*r>=3*q: continue
            if (2*r-5*p)%q!=0: continue   # relation 2r≡5p mod q
            c=(2*r-5*p)//q
            ccount[c]+=1; tot+=1
            den=2*q
            if not any(in_R(fract(r*(2*l+1),den),fract(p*(2*l+1),den)) for l in range(2*q)):
                norwit+=1
print("c distribution:",dict(ccount)," total configs:",tot," NO R-witness:",norwit)
print("\n=== (5,-2): 5p≡-2r, 2r+5p=cq ===")
ccount=Counter(); norwit=0; tot=0
for q in range(30,80):
    for p in range(1,q):
        if 3*p>=q or gcd(p,q)!=1: continue
        for r in range(q+1,(3*q-1)//2+1):
            if 2*r>=3*q: continue
            if (2*r+5*p)%q!=0: continue
            c=(2*r+5*p)//q
            ccount[c]+=1; tot+=1
            den=2*q
            if not any(in_R(fract(r*(2*l+1),den),fract(p*(2*l+1),den)) for l in range(2*q)):
                norwit+=1
print("c distribution:",dict(ccount)," total configs:",tot," NO R-witness:",norwit)
