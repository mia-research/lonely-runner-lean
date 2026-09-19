"""A divisor TOWER always has a witness, by greedy nesting.
Blocked at b is the cyclic ball around 0 of radius ~b/8, so the clear set is ONE interval
[L(b),U(b)] of length w(b) = U-L+1 ~ 3b/4.
If b' | b properly then b' <= b/2 < w(b), so the b-window contains a FULL PERIOD of b'.
Hence after fixing the b-window we can always additionally satisfy the b'-window, retaining an
interval of length w(b'). Induction down the tower."""
from math import gcd
import random, itertools
def L(b): return -((-(b-1))//8)
def U(b): return (7*b-1)//8
def w(b): return U(b)-L(b)+1
print("(1) w(b) >= b/2 for every b >= 2  (so a window covers a full period of any proper divisor)")
bad=[b for b in range(2,20001) if 2*w(b) < b]
print(f"    checked b = 2..20000: {'HOLDS' if not bad else f'FAILS at {bad[:5]}'}")
print(f"    tightest: {min(((2*w(b)-b), b) for b in range(2,20001))} (slack 2w-b, at that b)")
print("\n(2) greedy down a tower: keep an interval, intersect with the next window")
def greedy(tower):
    """tower: b1 > b2 > ... each dividing the previous. Returns a witness q or None."""
    lo,hi = L(tower[0]), U(tower[0])          # interval [lo,hi]
    for b in tower[1:]:
        # find a sub-interval of [lo,hi] whose residues mod b lie in [L(b),U(b)]
        start = lo + ((L(b) - lo) % b)
        if start + w(b) - 1 > hi: return None
        lo, hi = start, start + w(b) - 1
    return lo
def ok(tower,q): return all(L(b) <= q % b <= U(b) for b in tower)
random.seed(23)
fail=0; n=0
for _ in range(200000):
    k=random.randint(2,6)
    t=[1]
    for _ in range(k): t.append(t[-1]*random.choice([2,2,3,3,4,5,6,7,8]))
    tower=sorted(set(t[1:]), reverse=True)
    if len(tower)<2: continue
    n+=1
    q=greedy(tower)
    if q is None or not ok(tower,q): fail+=1
print(f"    random towers (up to 6 levels): {n-fail}/{n} "
      f"{'ALL SUCCEED' if fail==0 else f'{fail} FAIL'}")
print("\n(3) exhaustive towers from divisors of highly composite m")
fail2=0; n2=0
for m in (48,72,96,120,144,240,360,480,720,840,1440,2520,5040):
    divs=[d for d in range(2,m+1) if m%d==0]
    for k in (2,3,4,5):
        for c in itertools.combinations(divs,k):
            t=sorted(c, reverse=True)
            if any(t[i] % t[i+1] for i in range(len(t)-1)): continue   # tower only
            n2+=1
            q=greedy(t)
            if q is None or not ok(t,q): fail2+=1
print(f"    {n2-fail2}/{n2} {'ALL SUCCEED' if fail2==0 else f'{fail2} FAIL'}")
