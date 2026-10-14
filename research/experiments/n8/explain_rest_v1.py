"""The two unexplained classes.  Not 'failures' -- explain them.

 (A) 8|m, some 8|b_i, constructions FAIL  -- 11.16%
 (B) 8|m, no  8|b_i, constructions FAIL   --  6.11%

For each, find an actual witness q and ask what form it takes:  q = m*x/8 with x = 8q/m.
Is x extremal (leftmost)?  Is it of the form (8k+1)/s for SOME speed?  Which one?
"""
from fractions import Fraction as F
from itertools import combinations

def I(b): return (-(-(b-1)//8), (7*b-1)//8)
def ok(q,m,bs): return all(I(b)[0] <= q%b <= I(b)[1] for b in bs+[m])
def spine_q(m,bs):
    if m % 8: return None
    for u in (1,3,5,7):
        if ok(u*m//8, m, bs): return u*m//8
    return None
def endpoint_q(m,bs):
    for b in bs:
        if b % 8: continue
        k=0
        while b*(8*k+1)//8 < m:
            q=b*(8*k+1)//8
            if ok(q,m,bs): return q
            k+=1
    return None
def all_sols(m,bs): return [q for q in range(m) if ok(q,m,bs)]

A=[];B=[]
for m in range(24, 240):
    if m % 8: continue
    mid=[d for d in range(2,m) if m%d==0]
    for c in combinations(mid,5):
        bs=sorted(m//s for s in c)
        if spine_q(m,bs) is not None or endpoint_q(m,bs) is not None: continue
        (A if any(b%8==0 for b in bs) else B).append((m,bs))
print(f"class A (8|m, some 8|b, uncovered): {len(A):,}")
print(f"class B (8|m, no 8|b,  uncovered): {len(B):,}\n")

def analyse(pop, lab):
    forms = {"x=(8k+1)/s for some speed s":0, "x not of that form":0}
    nosol = 0; ex=[]
    for m,bs in pop[:1500]:
        S=all_sols(m,bs)
        if not S: nosol+=1; continue
        hit=False
        for q in S:
            x=F(8*q,m)
            # is x = (8k+1)/s for one of the speeds s = m/b ?
            for b in bs+[m]:
                s=m//b
                num=x*s
                if num.denominator==1 and (int(num)-1)%8==0: hit=True; break
            if hit:
                if len(ex)<3: ex.append((m,bs,q,x))
                break
        forms["x=(8k+1)/s for some speed s" if hit else "x not of that form"] += 1
    print(f"  {lab}: no solution at all = {nosol}")
    for k,v in forms.items(): print(f"     {k:<34} {v:,}")
    for e in ex: print(f"     e.g. m={e[0]} b={e[1]}  q={e[2]}  x={e[3]}")
analyse(A,"class A"); print(); analyse(B,"class B")
