import math, random
from math import gcd
from collections import Counter

# t is held as an exact pair (P,Q) meaning P/Q.  All tests are integer tests.
def inway(d, P, Q):          # circDist(d*P/Q) < 1/8
    r = (d*P) % Q
    return 8*min(r, Q-r) < Q
def lonely(ds, P, Q):
    for d in ds:
        r = (d*P) % Q
        if 8*min(r, Q-r) < Q: return False
    return True
def nextop(d, P, Q):         # ((ceil(d*P/Q - 1/8)) + 1/8)/d  -> (8k+1, 8d)
    num = 8*d*P - Q; den = 8*Q
    k = -((-num)//den)
    g = gcd(8*k+1, 8*d)
    return ((8*k+1)//g, (8*d)//g)
def move(ds, P, Q):
    bP,bQ = P,Q
    for d in ds:
        if inway(d,P,Q):
            nP,nQ = nextop(d,P,Q)
            if nP*bQ > bP*nQ: bP,bQ = nP,nQ
    return bP,bQ
def cascade(ds, cap=2000):
    m = min(ds); P,Q = 1, 8*m; g=gcd(P,Q); P,Q = P//g, Q//g
    mv = 0
    while mv < cap:
        P2,Q2 = move(ds,P,Q)
        if (P2,Q2)==(P,Q): return mv
        P,Q = P2,Q2; mv += 1
    return None

def primitive(s):
    g = 0
    for x in s: g = gcd(g,x)
    return g == 1

print("=== DOOR 2: does the move count grow with the speed range? ===")
random.seed(17)
for hi in (25, 40, 60, 90, 140, 200):
    mx, arg, n = 0, None, 0
    seen = set()
    # random 7-subsets
    for _ in range(40000):
        s = tuple(sorted(random.sample(range(1,hi+1), 7)))
        if s in seen or not primitive(s): continue
        seen.add(s); n += 1
        mv = cascade(list(s))
        if mv is None: print("   NO ARRIVAL:", s); continue
        if mv > mx: mx, arg = mv, s
    # TARGETED: the earlier run's worst cases all had a tiny min with everything else large.
    for _ in range(40000):
        lo = random.choice([1,2,3,4])
        rest = sorted(random.sample(range(max(2,hi//3), hi+1), 6))
        s = tuple([lo]+rest)
        if len(set(s)) < 7 or s in seen or not primitive(s): continue
        seen.add(s); n += 1
        mv = cascade(list(s))
        if mv is None: print("   NO ARRIVAL:", s); continue
        if mv > mx: mx, arg = mv, s
    print(f"  range [1,{hi}]  sets={n}  MAX MOVES={mx}   at {arg}")
