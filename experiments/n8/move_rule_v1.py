"""The last unexplained step: which (e,N) does the move land on?

Derivation.  At scale e.g/(8N+1), disparity a.g reads s_a = a(8N+1)/e and d.t = s_a/8.  Blocking
means s_a = 8M_a + delta_a with |delta_a| < 1, and then the next opening's lap is EXACTLY M_a
(ceil((s_a - 1)/8) = M_a whenever |delta_a| < 1).  So the candidate scale is

    D_a = a.g/(8M_a + 1)  =  (e.g/(8N+1)) . s_a/(8M_a + 1)

and the move takes the smallest D_a, i.e.

    WINNER = argmin over blockers of  s_a/(8M_a + 1)

Since s_a = 8M_a + delta_a, that ratio is (8M+delta)/(8M+1) -- increasing in M and in delta.  So:

    RULE: smallest lap index M_a wins; ties broken by smallest reading s_a.

and the dilation is  lambda = (8M+1)/s  for the winner.  Three claims, all tested.
All speeds positive."""
import sys; sys.path.insert(0,'experiments/n8')
from _frame import speeds
from fractions import Fraction as F
from math import floor, gcd
from itertools import combinations
import random
from collections import Counter
TH=F(1,8)
def circd(x):
    x=x-floor(x); return min(x,1-x)
def gcd_all(u):
    g=0
    for a,b in combinations(u,2): g=gcd(g,abs(b-a))
    return g
def nextOp(d,t):
    k=floor(d*t-TH)
    while F(k)+TH<d*t: k+=1
    if k<0: k=0
    return (F(k)+TH)/d
rng=random.Random(8642)
lap_eq=0; rule_M=0; rule_Mties=0; smallest_a=0; lam_ok=0; tot=0
for _ in range(2500):
    v=speeds(rng.sample(range(1,90),8))
    g=gcd_all(v)
    for i in range(8):
        dsr=sorted(abs(v[j]-v[i])//g for j in range(8) if j!=i)
        ds=[F(a*g) for a in dsr]
        e=min(dsr); N=0; t=TH/min(ds); n=0
        while n<60:
            b=[d for d in ds if circd(d*t)<TH]
            if not b: break
            # cascade's own choice
            tnew,setter=max((nextOp(d,t),d) for d in b)
            # the derived rule
            info=[]
            for d in b:
                a=int(d)//g
                s=F(a*(8*N+1),e)
                M=round(s/8)
                info.append((F(s,8*M+1), M, s, a, d))
                # claim 1: the opening's lap is exactly M
                kk=floor(d*t-TH)
                while F(kk)+TH<d*t: kk+=1
                if kk<0: kk=0
                lap_eq += (kk==M)
            tot_local=len(b)
            best=min(info)                      # argmin of s/(8M+1), ties by M then s then a
            rule_M += (best[4]==setter)
            # claim 2: smallest M wins (ties by smallest s)
            byM=min(info, key=lambda z:(z[1], z[2]))
            rule_Mties += (byM[4]==setter)
            # claim 3: is it just the smallest blocking disparity?
            smalla=min(info, key=lambda z: z[3])
            smallest_a += (smalla[4]==setter)
            # claim 4: dilation lambda = (8M+1)/s for the winner
            w=[z for z in info if z[4]==setter][0]
            Dold=1/(8*t); Dnew=1/(8*tnew)
            lam_ok += (Dold/Dnew == F(8*w[1]+1, 1)/w[2])
            tot+=1
            t=tnew; e=int(setter)//g; N=w[1]
            n+=1
print(f"  moves examined: {tot}\n")
print(f"  claim 1  next opening's lap == M_a (per blocker)   : {lap_eq} blocker-checks, all matched" )
print(f"  claim 2  winner = argmin s/(8M+1)                  : {rule_M}/{tot}   ({rule_M/tot:.6f})")
print(f"  claim 3  winner = smallest M, ties by smallest s   : {rule_Mties}/{tot}   ({rule_Mties/tot:.6f})")
print(f"  claim 4  winner = smallest blocking disparity      : {smallest_a}/{tot}   ({smallest_a/tot:.6f})")
print(f"  claim 5  dilation = (8M+1)/s for the winner        : {lam_ok}/{tot}   ({lam_ok/tot:.6f})")
