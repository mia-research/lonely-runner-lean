"""The bad interval has TWO endpoints.  reach_mem returns the right ones, (8k+1)/s.
clear_reflect says clearing is symmetric, so the reflected family is the LEFT endpoints (8k-1)/s.
Do the interior witnesses live there?
"""
from fractions import Fraction as F
from itertools import combinations

def I(b): return (-(-(b-1)//8), (7*b-1)//8)
def ok(q,m,bs): return all(I(b)[0] <= q%b <= I(b)[1] for b in bs+[m])
def spine_q(m,bs):
    if m % 8: return None
    for u in (1,3,5,7):
        if ok(u*m//8,m,bs): return u*m//8
    return None
def right_q(m,bs):
    for b in bs:
        if b%8: continue
        k=0
        while b*(8*k+1)//8 < m:
            q=b*(8*k+1)//8
            if ok(q,m,bs): return q
            k+=1
    return None
def left_q(m,bs):
    """x = (8k-1)/s  ->  q = m*x/8 = b(8k-1)/8, integral iff 8 | b."""
    for b in bs:
        if b%8: continue
        k=1
        while b*(8*k-1)//8 < m:
            q=b*(8*k-1)//8
            if ok(q,m,bs): return q
            k+=1
    return None

tot=0; cov=dict(spine=0, right=0, left=0, any=0, none=0)
none_ex=[]
for m in range(24, 320):
    mid=[d for d in range(2,m) if m%d==0]
    if len(mid)<5: continue
    for c in combinations(mid,5):
        bs=sorted(m//s for s in c); tot+=1
        s_,r_,l_ = spine_q(m,bs), right_q(m,bs), left_q(m,bs)
        cov['spine'] += s_ is not None
        cov['right'] += r_ is not None
        cov['left']  += l_ is not None
        if s_ is None and r_ is None and l_ is None:
            cov['none'] += 1
            if len(none_ex)<4: none_ex.append((m,bs))
        else: cov['any'] += 1
print(f"divisor-closed, exhaustive m < 320 : {tot:,}\n")
for k in ('spine','right','left'):
    print(f"  {k:<6} construction alone covers : {cov[k]:>8,}  ({100*cov[k]/tot:6.2f}%)")
print(f"  {'ANY':<6} of the three            : {cov['any']:>8,}  ({100*cov['any']/tot:6.2f}%)")
print(f"  {'NONE':<6}                        : {cov['none']:>8,}  ({100*cov['none']/tot:6.2f}%)")
for e in none_ex: print(f"     e.g. m={e[0]} b={e[1]}")
