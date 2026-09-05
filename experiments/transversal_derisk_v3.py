"""
v3: for the ZERO-survivor transversal pairs (R-witness always exists, no pentagon),
find the cleanest witness construction to choose the formalization route:
 (A) explicit formula via fract_odd_mul: aim Y=(2k+p)/(2q) in [1/6,1/3], X follows;
     is there a SIMPLE k (e.g. nearest to центру) that always lands X in [1/6,1/2]?
 (B) else need general-slope grid (generalize antidiag_circle_witness).

Also: confirm which transversal pairs are truly 0-survivor (R-closable) vs have
small-q P\R survivors, via box-minimality, q up to 160.
"""
from math import gcd
from fractions import Fraction as F
from collections import defaultdict

def frac(x): return x - (x.numerator // x.denominator)
def S(l, p, q, r):
    u = 2*l + 1
    return frac(F(r*u, 2*q)), frac(F(p*u, 2*q))
XLO, XHI, YLO, YHI = F(1,6), F(1,2), F(1,6), F(1,3)
def inR(X, Y): return XLO <= X <= XHI and YLO <= Y <= YHI
def cap_R_empty(p, q, r): return all(not inR(*S(l,p,q,r)) for l in range(q))

def in_G(i, j, p, q, r):
    ii, jj = i % q, j % q
    return any((m*r) % q == ii and (m*p) % q == jj for m in range(q))

def minimal_box_pair(p, q, r):
    cands = []
    for m in range(q):
        i = (m*r) % q
        if i >= 6: continue
        j = (m*p) % q
        if j > q//2: j -= q
        if -6 - i < 2*j < 6 + i and not (i == 0 and j == 0):
            cands.append((i, j))
    def is_min(i, j):
        for k in range(-abs(i), abs(i)+1):
            for l in range(-abs(j), abs(j)+1):
                if (k,l)==(0,0) or (abs(k)==abs(i) and abs(l)==abs(j)): continue
                if in_G(k, l, p, q, r): return False
        return True
    mins = [(i,j) for (i,j) in cands if is_min(i,j)]
    return min(mins, key=lambda ij:(ij[0],abs(ij[1]),ij[1])) if mins else None

QMAX = 160
tot = defaultdict(int); empty = defaultdict(int)
tuples_by_pair = defaultdict(list)
for q in range(18, QMAX+1):
    for p in range(1, q):
        if 3*p >= q or gcd(p,q)!=1: continue
        for r in range(q+1,(3*q)//2+1):
            if 2*r >= 3*q: continue
            mp = minimal_box_pair(p,q,r)
            if mp is None: continue
            i,j = mp
            if abs(j)<2 or i==0: continue
            tot[(i,j)]+=1
            if cap_R_empty(p,q,r): empty[(i,j)]+=1
            else: tuples_by_pair[(i,j)].append((p,q,r))

zero = sorted(ij for ij in tot if empty[ij]==0)
nonzero = sorted(ij for ij in tot if empty[ij]>0)
print("ZERO-survivor (R-closable) pairs:", zero)
print("survivor-bearing pairs:", [(ij, empty[ij]) for ij in nonzero])

# (A) witness-formula hunt on zero-survivor pairs: for each tuple, among l with Y in window,
# does the one with Y closest to 1/4 land X in window? what fraction need a non-nearest l?
print("\n=== witness structure on zero-survivor pairs (q>=26) ===")
for ij in zero:
    i,j = ij
    near_ok = 0; tot_t = 0; multi = []
    for (p,q,r) in tuples_by_pair[ij]:
        if q < 26: continue
        tot_t += 1
        ws = [(l, *S(l,p,q,r)) for l in range(q) if inR(*S(l,p,q,r))]
        # candidate: among ALL l with Y in [1/6,1/3], the one with Y nearest 1/4
        ywin = [(l, *S(l,p,q,r)) for l in range(q) if YLO <= S(l,p,q,r)[1] <= YHI]
        best = min(ywin, key=lambda t: abs(t[2]-F(1,4)))
        if XLO <= best[1] <= XHI: near_ok += 1
        multi.append(len(ws))
    if tot_t:
        print(f"  {ij}: tuples={tot_t}  nearest-Y-to-1/4 lands X: {near_ok}/{tot_t}"
              f"  #witness/tuple min={min(multi)} max={max(multi)} mean={sum(multi)/len(multi):.1f}")
