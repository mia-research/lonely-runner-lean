"""How much did 28 -> 10 actually buy, measured in PROFILES rather than in values of b?
And do the 'open' profiles in fact clear (they should -- the category is verified exhaustively)?"""
from math import lcm
from functools import reduce
import random
def L(b): return -((-(b-1))//8)
def U(b): return (7*b-1)//8
def clears(bs,q): return all(L(b) <= q % b <= U(b) for b in bs)
def has_witness(bs):
    M=reduce(lcm,bs)
    if M>3_000_000: return None
    return any(clears(bs,q) for q in range(M))
random.seed(9)
n=0; ge28=0; ge10=0; le9=0
for _ in range(60000):
    m=random.choice([24,36,48,60,72,96,120,144,180,240,360,504,720,840])
    divs=[d for d in range(2,m+1) if m%d==0]
    if len(divs)<5: continue
    bs=sorted(random.sample(divs,5)); n+=1
    if min(bs)>=28: ge28+=1
    if min(bs)>=10: ge10+=1
    if max(bs)<=9: le9+=1
print(f"profiles: {n}")
print(f"   every quotient >= 28 (the OLD proved threshold): {ge28:6d}  {100*ge28/n:5.2f}%")
print(f"   every quotient >= 10 (the NEW proved threshold): {ge10:6d}  {100*ge10/n:5.2f}%")
print(f"   gain from 28 -> 10, in profiles:                {ge10-ge28:6d}  {100*(ge10-ge28)/n:5.2f} points")
print(f"   every quotient <= 9  (q = 1):                   {le9:6d}  {100*le9/n:5.2f}%")
print("\ndo the OPEN (mixed) profiles clear anyway?")
ex=[[4,8,9,24,36],[2,15,28,35,70],[3,4,20,30,240],[3,8,12,36,42],[2,4,6,9,18]]
for bs in ex:
    M=reduce(lcm,bs)
    w=next((q for q in range(min(M,3_000_000)) if clears(bs,q)), None)
    print(f"   {bs}  lcm={M:7d}  witness q = {w}")
