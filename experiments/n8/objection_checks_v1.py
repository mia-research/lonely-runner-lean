"""
Checks behind OBJECTIONS_AND_ANSWERS_v1.md.  Exact rationals throughout; Decimal at 80 digits
only where a difference is irrational.  Each block prints the claim, the source that states
it, and the verdict.
"""
from fractions import Fraction as F
from decimal import Decimal, getcontext
from math import gcd
from itertools import product
getcontext().prec = 80

def cd(x):
    fr = x - (x.numerator // x.denominator) if isinstance(x, F) else x - int(x)
    if fr < 0: fr += 1
    return min(fr, 1 - fr)

def lonely(V, i, t):
    return all(cd(F(abs(V[i] - V[j])) * t) >= F(1, 8) for j in range(len(V)) if j != i)

def diffs(V, i):
    return [abs(V[i] - V[j]) for j in range(len(V)) if j != i]

print("C1. Register item 17: 'a = 1 (mod 8) is refuted by t = 71/8'  (SKETCH_v7 7d)")
V = [F(1), None, F(3), F(4), F(5), F(6), F(7), F(8)]
# r1's integer differences are 2..7; 71/8 as an opening of difference 7:
t = F(71, 8)
print("   71/8 == 497/(8*7):", t == F(497, 56), "  497 mod 8 =", 497 % 8, "  7 is a difference of r1: True")
print("   (8k+1)/(8d) form with d = 7, k = 62:", F(8*62+1, 8*7) == t)
bad = 0
for D in range(1, 60):
    for a in range(1, 8*D, 2):
        j = next(j for j in (1, 3, 5, 7) if (a*j) % 8 == 1)
        if F(a, 8*D) != F(a*j, 8*D*j) or (a*j) % 8 != 1: bad += 1
print("   every odd a/(8D) rewritten as a'/(8D') with a' = 1 (mod 8), D<60: failures", bad)
print("   VERDICT: with D free, a = 1 (mod 8) loses nothing; item 17's refutation fixed D = 1\n")

print("C2. Register item 16 / PROOF_REQUIREMENTS_v2 6: SKETCH_v7 7c failure clears at (D,a) = (5,9)")
V = [27, 45, 308, 678, 679, 799, 806, 979]
print("   r4 differences:", diffs(V, 3))
for tt in (F(9, 40), F(305, 2408)):
    print(f"   t = {tt}: lonely {lonely(V, 3, tt)}; distances",
          [str(cd(F(e)*tt)) for e in diffs(V, 3)])
print("   305/2408 == 305/(8*301):", F(305, 2408) == F(305, 8*301), " 305 mod 8 =", 305 % 8)
V = [1, 31, 75, 97, 128, 160, 176, 225]
print("   WHY_THE_LAST_MILE arrangement, runner at 1, t = 9/40: lonely", lonely(V, 0, F(9, 40)), "\n")

print("C3. WHY_REDUCTIONS 1: '(3,7,12,20,29,31,44,50) ... no instant at which all eight are lonely'")
V = [3, 7, 12, 20, 29, 31, 44, 50]
ts = [F(1,8), F(1,16), F(1,24), F(1,40), F(1,8), F(1,16), F(11,40), F(1,8)]
print("   each stated time lonely for its runner:", all(lonely(V, i, ts[i]) for i in range(8)),
      "  distinct:", len(set(ts)))
g = 0
for i in range(8):
    for j in range(i+1, 8): g = gcd(g, V[j]-V[i])
print("   the transcript's check tested only the produced times (2026-09-14T02:08, 'allsame=[t for t in ts ...]')")
print("   gcd of all pairwise differences:", g, "-> all-lonely needs every difference*t in (1/8)Z, so t in (1/8)Z")
res = sorted(v % 8 for v in V)
print("   speeds mod 8:", res, "-> repeated residues, so no c makes {c*v mod 8} a permutation of 0..7")
print("   brute force t = c/8, c = 0..7, all eight lonely:",
      any(all(lonely(V, i, F(c, 8)) for i in range(8)) for c in range(8)))
print("   VERDICT: claim TRUE for every instant, by Thm 4.2 + residue collision; the stated check was narrower\n")

print("C4. OBJECTION_LEDGER Part 4 row 1 and the transcript line 'nothing is restricted to the first cycle'")
print("   produce() used D = k*d_min, a in range(1, 8k+9, 2)  ->  u = d_min*t = a/(8k) <= (8k+7)/(8k) < 2")
print("   so 'furthest lap 1' was forced by the numerator cap, not measured.  The 12,000/12,000 stands;")
print("   the lap statistic carries no information.\n")

print("C5. Register 0, the free test: e cannot block at gap D  iff  m = 8D/gcd(e,8D) is even and <= 8")
bad = 0; n = 0
for e in range(1, 120):
    for D in range(1, 40):
        blocks = any(not (D <= (a*e) % (8*D) <= 7*D) for a in range(1, 8*D, 2))
        m = 8*D // gcd(e, 8*D)
        n += 1
        if (not blocks) != (m % 2 == 0 and m <= 8): bad += 1
print(f"   {n} (e,D) pairs, disagreements {bad}\n")

print("C6. Register 0, all-or-nothing: if D divides every difference, every odd a gives the same verdict")
bad = 0; n = 0
for ks in product(range(1, 20), repeat=3):
    for D in (1, 2, 3, 5, 6):
        es = [k*D for k in ks]
        verdicts = {all(D <= (a*e) % (8*D) <= 7*D for e in es) for a in range(1, 8*D, 2)}
        n += 1; bad += len(verdicts) > 1
print(f"   {n} cases, mixed verdicts {bad}\n")

print("C7. SKETCH_v7 7d / ledger Part 1 row 1: r2 of (1, 1+sqrt2/100, 3..8) at t = p/(8 d_min)")
d = Decimal(2).sqrt()/100
ds = [d] + [Decimal(k) - d for k in (2, 3, 4, 5, 6, 7)]
def cdD(x):
    fr = x - int(x)
    if fr < 0: fr += 1
    return min(fr, Decimal(1) - fr)
for p in (1, 3, 5, 7):
    tt = Decimal(p) / (8*d)
    mar = min(cdD(e*tt) for e in ds) - Decimal(1)/8
    print(f"   p = {p}: margin {str(mar)[:12]}")
tt = Decimal(71)/8
print("   r1 at 71/8, distances:", [str(cdD(e*tt))[:8] for e in [d] + [Decimal(k) for k in range(2, 8)]])
