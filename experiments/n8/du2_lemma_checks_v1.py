r"""
du2_lemma_checks_v1 -- the structural facts the DROPPED-UNIT proof leans on.

L1  PAIR RULE.  rho odd  =>  bad(e,t) = {-t*rho, -(t+1)*rho}, two elements differing
    by rho (odd), hence one odd and one even.  Depends only on rho and t mod 8.
L2  NON-UNITS.  gcd(e,8) = 2  => bad is a single coset of H_2 = {0,4};
    gcd(e,8) = 4  => bad is a single coset of H_4 = {0,2,4,6} or empty.
    In both cases bad lies inside ONE parity class.
L3  DIVISIBLE.  e = 8m  =>  bad(e,t) = Z/8 if t mod 8 in {0,7}, else empty; and
    {x : floor(8mx) mod 8 in {0,7}} = B_m, of measure exactly 1/4.
L4  B-LEMMA.  |B_m1 u B_m2| <= 1/2 - gcd(m1,m2)/(4 max(m1,m2)) for m1 != m2.
L5  DIRECTION OF THE INCLUSION.  The floor-built bad set is a SUPERSET of the true
    one: when (t_e + e r) = 7 mod 8 AND s_e = 0 the runner is in fact satisfied.
    Checked by counting genuine witnesses vs floor-criterion witnesses.
L6  gcd(E) for the 18 representative dropped-unit sets.
"""
from fractions import Fraction as F
from itertools import combinations
from math import gcd
from functools import reduce

def bad(e, t):
    return frozenset(r for r in range(8) if (e * r + t) % 8 in (0, 7))

print("L1  pair rule, all odd rho and all t mod 8, and speed-independence")
v = 0
for rho in (1, 3, 5, 7):
    for t in range(8):
        pred = frozenset({(-t * rho) % 8, (-(t + 1) * rho) % 8})
        if bad(rho, t) != pred or len(pred) != 2:
            v += 1
        if (pred - {x for x in pred if x % 2 == 0}) == pred or \
           all(x % 2 == 0 for x in pred):
            v += 1                                   # must be one odd one even
        for q in range(0, 12):                       # speed-independence
            e = 8 * q + rho
            for s in range(0, 40, 8):
                if bad(e, t + s) != bad(rho, t):
                    v += 1
print(f"    violations = {v}")

print("L2  non-units")
H2, H4 = {0, 4}, {0, 2, 4, 6}
v = 0
for rho in (2, 4, 6):
    g = gcd(rho, 8)
    H = H2 if g == 2 else H4
    for t in range(8):
        B = bad(rho, t)
        if B:
            c = min(B)
            if B != frozenset((c + h) % 8 for h in H):
                v += 1
            if len({x % 2 for x in B}) != 1:
                v += 1
        for q in range(0, 12):
            if bad(8 * q + rho, t) != B:
                v += 1
    print(f"    rho={rho} gcd={g}: bad sizes {sorted({len(bad(rho,t)) for t in range(8)})}"
          f"  empty at t in {sorted(t for t in range(8) if not bad(rho,t))}")
print(f"    violations = {v}")

print("L3  divisible runners")
v = 0
for m in range(1, 25):
    e = 8 * m
    for t in range(8):
        want = frozenset(range(8)) if t in (0, 7) else frozenset()
        if bad(e, t) != want:
            v += 1
    # B_m from the floor condition, measure
    tot = F(0)
    for j in range(8 * m):
        if j % 8 in (0, 7):
            tot += F(1, 8 * m)
    if tot != F(1, 4):
        v += 1
print(f"    violations = {v}")

print("L4  B-lemma (independent recomputation of the union measure)")
def Bset(m):
    return [(F(j, 8*m), F(j+1, 8*m)) for j in range(8*m) if j % 8 in (0, 7)]
def um(a, b):
    iv = sorted(a + b); out = []
    for x, y in iv:
        if out and x <= out[-1][1]: out[-1] = (out[-1][0], max(out[-1][1], y))
        else: out.append((x, y))
    return sum((y - x for x, y in out), F(0))
v = 0; tight = []
for m1 in range(1, 31):
    for m2 in range(m1 + 1, 31):
        u = um(Bset(m1), Bset(m2))
        bd = F(1, 2) - F(gcd(m1, m2), 4 * max(m1, m2))
        if u > bd: v += 1
        if u == bd: tight.append((m1, m2))
print(f"    violations = {v}   bound attained with equality at {len(tight)} pairs, "
      f"e.g. {tight[:6]}")
print(f"    max union over 1<=m1<m2<=30 = "
      f"{max(um(Bset(a),Bset(b)) for a in range(1,31) for b in range(a+1,31))}")

print("L5  direction of the inclusion (floor bad set is a superset of the true one)")
UNITS = {1, 3, 5, 7}
tot_floor = tot_true = 0; bad_dir = 0
for A in combinations(range(1, 8), 2):
    if not set(A) & UNITS: continue
    Enon = sorted(set(range(1, 8)) - set(A))
    for m1, m2 in [(1, 2), (2, 3), (3, 5)]:
        E = Enon + [8*m1, 8*m2]
        L = reduce(lambda a, b: a*b//gcd(a, b), E)
        N = 8*L
        nf = nt = 0
        for b in range(L):
            for r in range(8):
                k = b + r*L
                fl = all((e*r + (e*b)//L) % 8 in range(1, 7) for e in E)
                tr = all(L <= (e*k) % N <= 7*L for e in E)
                nf += fl; nt += tr
                if fl and not tr: bad_dir += 1
        tot_floor += nf; tot_true += nt
print(f"    floor-criterion witnesses = {tot_floor}, true witnesses = {tot_true}, "
      f"floor-but-not-true = {bad_dir}")
print(f"    every floor witness is a true witness: {bad_dir == 0};  "
      f"true >= floor: {tot_true >= tot_floor}")

print("L6  gcd of the 18 representative E_non")
for A in combinations(range(1, 8), 2):
    if not set(A) & UNITS: continue
    Enon = sorted(set(range(1, 8)) - set(A))
    print(f"    absent {A}  E_non = {Enon}  gcd = {reduce(gcd, Enon)}")
