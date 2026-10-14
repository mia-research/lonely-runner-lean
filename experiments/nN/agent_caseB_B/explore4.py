import random, math
from fractions import Fraction as F
from core import *
from collections import Counter
random.seed(5)
D=2520
def sample(mode):
    top=random.randint(9*D+1,24*D)
    if mode=='u': xs=random.sample(range(D+1,top),5)
    else:
        xs=set()
        while len(xs)<5:
            v=int(round(D*math.exp(random.uniform(0,math.log(top/D)))))
            if D<v<top: xs.add(v)
        xs=list(xs)
    return [F(1)]+sorted(F(x,D) for x in xs)+[F(top,D)]

def clear_pieces(f, a, b):
    """closed clear pieces of reading f inside [a,b]"""
    out=[]
    k=(f*a).numerator//(8*(f*a).denominator)-1
    while True:
        lo=F(8*k+1)/f; hi=F(8*k+7)/f
        if lo>b: break
        L=max(lo,a); H=min(hi,b)
        if L<=H: out.append((L,H))
        k+=1
    return out

def nested_longest(fast, a, b, order):
    I=(a,b)
    for f in order(fast):
        ps=clear_pieces(f,*I)
        if not ps: return None
        I=max(ps,key=lambda p:p[1]-p[0])
    return I[0]

def nested_all(fast,a,b):
    # full branching (exact search within block)
    Is=[(a,b)]
    for f in sorted(fast):
        new=[]
        for I in Is: new+=clear_pieces(f,*I)
        Is=new
        if not Is: return None
    return min(I[0] for I in Is)

def phi(L):
    if L<2: return None
    return min(F(6),(L-2)/2)
def worst(fast, a, b):
    Lam=None; ell=b-a
    fs=sorted(fast)
    for i,f in enumerate(fs):
        Lam=f*ell
        if Lam<2: return False
        if i==len(fs)-1: return True
        ell=phi(Lam)/f
    return True

for mode in ('u','log'):
    c=Counter()
    for _ in range(5000):
        rd=sample(mode)
        R,s=first_lonely(rd)
        i,g=largest_gap(rd); stop=rd[i]
        if stop>7: c['stop>7']+=1; continue
        slow=rd[:i+1]; fast=rd[i+1:]
        blk = R<=7/stop
        c['blk' if blk else 'noblk']+=1
        if not blk: continue
        a,b=F(1),F(7)/stop
        c['one_step' if s<=1 else 'multi']+=1
        if nested_longest(fast,a,b,sorted) is not None: c['nl_inc']+=1
        if nested_longest(fast,a,b,lambda x:sorted(x,reverse=True)) is not None: c['nl_dec']+=1
        if worst(fast,a,b): c['worst']+=1
        # best split: any i with s_i<=7
    print(mode,c)
