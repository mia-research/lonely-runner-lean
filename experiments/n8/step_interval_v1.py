"""The step reduction.
q = L(m) + T.  At a collider the residue of L(m) is 0, so q's residue is T.
At a non-collider it is R_b + T, with R_b = ceil((v_b*b-1)/8), v_b = (m/b) mod 8.
If R_b + T <= U(b) there is no wraparound, so clearing is a plain interval condition:

    T in  [L(b), U(b)]            for every collider b
    T in  [L(b)-R_b, U(b)-R_b]    for every non-collider b

No modular arithmetic at all. Does that interval intersection ever miss?"""
from math import lcm
from functools import reduce
import random
def L(b): return -((-(b-1))//8)
def U(b): return (7*b-1)//8
def R(m,b): 
    v=(m//b)%8
    return -((-(v*b-1))//8)
def clears(bs,q): return all(L(b) <= q % b <= U(b) for b in bs)
def T_interval(m,bs):
    lo,hi=0,10**18
    for b in bs:
        if (m//b)%8==0: lo,hi=max(lo,L(b)),min(hi,U(b))
        else:           lo,hi=max(lo,L(b)-R(m,b)),min(hi,U(b)-R(m,b))
    return lo,hi
random.seed(17)
tot=0; nonempty=0; verified=0; miss=[]
for _ in range(200000):
    m=random.choice([48,72,96,120,144,192,240,288,360,480,720,840,960,1440,2520,5040])
    divs=[d for d in range(2,m+1) if m%d==0]
    if len(divs)<5: continue
    bs=sorted(random.sample(divs,5))
    if not any((m//b)%8==0 for b in bs): continue
    tot+=1
    lo,hi=T_interval(m,bs)
    if lo<=hi:
        nonempty+=1
        if clears(bs, L(m)+lo): verified+=1
    elif len(miss)<8: miss.append((m,bs,lo,hi))
    if tot>=25000: break
print(f"Branch B divisor-closed profiles: {tot}")
print(f"   step interval non-empty:              {100*nonempty/tot:6.2f}%")
print(f"   and q = L(m)+T really clears (check): {verified}/{nonempty} "
      f"{'ALL' if verified==nonempty else 'MISMATCH'}")
print(f"   compare: the single choice T = L(b*) reached 59.84%")
print(f"\n   profiles where the interval is EMPTY (the owed case):")
for x in miss[:8]:
    m,bs,lo,hi=x
    cols=[b for b in bs if (m//b)%8==0]
    print(f"      m={m} bs={bs} colliders={cols}  T-range [{lo},{hi}] empty")
