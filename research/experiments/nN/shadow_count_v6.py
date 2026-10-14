"""WHY the counting bounds decay: the best achievable bound/e tends to a constant above 1,
while the truth stays below 1.  Randomly sampled, middle of the trichotomy, order 8."""
import random, statistics
from math import gcd
N=8
def bset(d,e,n=N): return frozenset(j for j in range(e) if not (e<=(d*(n*j+1))%(n*e)<=(n-1)*e))
def ratios(L,n=N):
    out=[]
    for e in L:
        B=[bset(d,e,n) for d in L if d!=e]
        if not B: continue
        u=len(set().union(*B)); b0=sum(map(len,B))
        b1=min(len(B[i])+sum(len(B[k])-len(B[k]&B[i]) for k in range(len(B)) if k!=i) for i in range(len(B)))
        b2=b1
        for i in range(len(B)):
            for j in range(i+1,len(B)):
                base=len(B[i])+len(B[j])-len(B[i]&B[j])
                rest=sum(len(B[k])-max(len(B[k]&B[i]),len(B[k]&B[j])) for k in range(len(B)) if k not in (i,j))
                b2=min(b2,base+rest)
        out.append((b0/e,b1/e,b2/e,u/e))
    return min(out,key=lambda t:t[0]),min(out,key=lambda t:t[1]),min(out,key=lambda t:t[2]),min(out,key=lambda t:t[3])
random.seed(7)
print("  range  |  mean of the BEST ratio over flanks (needs < 1 to close)")
print("         |   union     1-pivot    2-pivot     TRUTH")
for H in (21,40,80,160,320):
    A=[[],[],[],[]]; got=0; tries=0
    while got<400 and tries<100000:
        tries+=1
        L=sorted(random.sample(range(1,H+1),7))
        if L[0]!=1: L[0]=1; L=sorted(set(L))
        if len(L)!=7: continue
        M=sum(1 for d in L if d%N==0)
        if not (1<=M<=5): continue
        got+=1
        r=ratios(L)
        for k in range(4): A[k].append(r[k][k])
    print(f"  [1,{H:3d}] |  {statistics.mean(A[0]):.4f}    {statistics.mean(A[1]):.4f}    {statistics.mean(A[2]):.4f}     {statistics.mean(A[3]):.4f}")
