"""S03: exhaustive-ish search for unit-complete E with E_div nonempty.
Checks (a) is some b in B_div safe?  (b) is some b in the two 4L/35 windows safe?
Exact integers throughout."""
import sys
from itertools import combinations
from math import gcd
from n8_fibre_core import L_of, split, blocked_non, safe, div_ok, witness_from_fibre

UNITS = {1,3,5,7}

def unit_complete(E_non):
    R = set(e % 8 for e in E_non)
    return UNITS <= R and len(R) == 5   # 4 units + exactly one of {2,4,6}

def scan(E, Lcap=2_000_000):
    L = L_of(E)
    if L > Lcap: return None
    Ed, En = split(E)
    lo, hi = -(-L//8), (7*L)//8          # ceil(L/8) .. floor(7L/8)
    w1 = (-(-2*L//7), (2*L)//5)          # [2L/7, 2L/5)
    w2 = (-(-3*L//5), (5*L)//7)          # [3L/5, 5L/7)
    n_safe_div = 0; n_safe_w = 0; first_div=None; first_w=None
    n_bdiv = 0
    for b in range(lo, hi+1):
        if not div_ok(Ed, b, L):   # honest B: every divisible runner unblocked
            continue
        n_bdiv += 1
        if safe(En, b, L):
            n_safe_div += 1
            if first_div is None: first_div = b
            if (w1[0] <= b < w1[1]) or (w2[0] <= b < w2[1]):
                n_safe_w += 1
                if first_w is None: first_w = b
    return dict(L=L, Ed=Ed, En=En, n_bdiv=n_bdiv, n_safe_div=n_safe_div,
                n_safe_w=n_safe_w, first_div=first_div, first_w=first_w)

def divisors(n):
    d=[]
    i=1
    while i*i<=n:
        if n%i==0:
            d.append(i)
            if i!=n//i: d.append(n//i)
        i+=1
    return sorted(d)

if __name__ == "__main__":
    Ls = [int(x) for x in sys.argv[1:]] or [8,16,24,32,40,48,56,72,80,88,96,120,144,168,
                                            192,216,240,264,280,288,312,336,360,408,420*8//8*8,
                                            432,440,456,480,504,528,552,576,600,624,648,672,
                                            696,720,840,1008,1080,1200,1260*8//4,1440,1680,2520*8//8*8]
    Ls = sorted(set(l for l in Ls if l%8==0))
    tot=0; bad_div=[]; bad_win=[]
    for L in Ls:
        divs = divisors(L)
        if len(divs) > 26: continue
        for E in combinations(divs, 7):
            if L_of(E) != L: continue
            if gcd(*E) if False else 0: pass
            g=0
            for e in E: g=gcd(g,e)
            if g != 1: continue
            Ed, En = split(E)
            if not Ed: continue
            if not unit_complete(En): continue
            r = scan(E)
            if r is None: continue
            tot += 1
            if r["n_safe_div"] == 0: bad_div.append((E, r))
            if r["n_safe_w"] == 0:   bad_win.append((E, r))
    print(f"configurations tested: {tot}")
    print(f"NO safe fibre anywhere in B  : {len(bad_div)}")
    print(f"NO safe fibre in the 2 windows: {len(bad_win)}")
    for E,r in bad_win[:20]:
        print("  window-fail:", E, "L=",r["L"], "|B|=",r["n_bdiv"], "safe in B=",r["n_safe_div"])
    for E,r in bad_div[:20]:
        print("  B-FAIL     :", E, "L=",r["L"], "|B|=",r["n_bdiv"])
