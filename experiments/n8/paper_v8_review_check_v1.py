"""Checks of the external review of PAPER_v8 (2026-09-24).

Each check names the paper claim it tests and prints counts with the misses listed.
Exact arithmetic throughout (integers and fractions.Fraction).
"""
from fractions import Fraction as F
from itertools import combinations
from math import gcd, floor


def flank_works(n, ds, e):
    """Theorem 10: some j < e with d(nj+1) mod ne in [e, (n-1)e] for every d."""
    for j in range(e):
        a = n * j + 1
        if all(e <= (d * a) % (n * e) <= (n - 1) * e for d in ds):
            return j
    return None


def any_flank(n, ds):
    for e in ds:
        j = flank_works(n, ds, e)
        if j is not None:
            return e, j
    return None


def circ(x):
    x = x - floor(x)
    return min(x, 1 - x)


def lonely(n, ds, t):
    return all(circ(d * t) >= F(1, n) for d in ds)


def cascade(n, ds):
    """The move of Section 7, from the bound; returns the list of steps."""
    t = F(1, n * min(ds))
    steps = [t]
    while True:
        inway = [d for d in ds if circ(d * t) < F(1, n)]
        if not inway:
            return steps
        nxt = []
        for d in inway:
            N = floor(d * t - F(1, n)) + 1  # least N with (N+1/n)/d >= t
            while (N + F(1, n)) / d < t:
                N += 1
            nxt.append((N + F(1, n)) / d)
        t = max(nxt)
        steps.append(t)


def phi(n):
    return sum(1 for k in range(1, n + 1) if gcd(k, n) == 1)


print("=" * 72)
print("CHECK 1  Section 11: 'M >= c-1 closed -- R5, flank the lone non-multiple'")
print("population: all (n-1)-subsets of [1,H] with exactly one disparity not divisible by n")
for n, H in [(4, 40), (5, 50), (6, 48), (7, 56), (8, 64)]:
    tot = fail_lone = fail_all = 0
    ex = None
    mults = [m for m in range(n, H + 1, n)]
    for x in range(1, H + 1):
        if x % n == 0:
            continue
        for ms in combinations(mults, n - 2):
            c = tuple(sorted((x,) + ms))
            tot += 1
            if flank_works(n, c, x) is None:
                fail_lone += 1
                ex = ex or c
                if any_flank(n, c) is None:
                    fail_all += 1
    print(f"  n={n} H={H}: sets={tot}  lone-non-multiple flank fails={fail_lone}"
          f"  no flank at all={fail_all}  first failure={ex}")
print("  worked: n=4, {1,4,8}: flank 1 ->", flank_works(4, [1, 4, 8], 1),
      "; any flank ->", any_flank(4, [1, 4, 8]))

print("=" * 72)
print("CHECK 2  R4 at composite n: flank e largest, n|e, no other d divisible by n,")
print("         #(non-flank d coprime to n) < phi(n)  ==>  flank e works at a = k e + 1, k a unit")
for n, H in [(4, 40), (6, 36), (8, 32), (9, 27), (10, 30)]:
    tested = fails = 0
    control_tested = control_fail = 0
    for e in range(n, H + 1, n):
        pool = [d for d in range(1, e) if d % n]
        for L in combinations(pool, n - 2):
            c = L + (e,)
            cop = sum(1 for d in L if gcd(d, n) == 1)
            ks = [k for k in range(1, n) if gcd(k, n) == 1
                  and all((d * k) % n not in (0, n - 1) for d in L)]
            works = flank_works(n, c, e) is not None
            if cop < phi(n):
                tested += 1
                if not ks or not works:
                    fails += 1
            else:
                control_tested += 1
                if not works:
                    control_fail += 1
    print(f"  n={n} phi={phi(n)} H={H}: hypothesis holds on {tested}, failures {fails};"
          f"  control (#coprime >= phi): {control_tested}, flank e fails on {control_fail}")

print("=" * 72)
print("CHECK 3  Theorem 11(c) converse: 'a run of such zones ending at a lonely instant ... is this run'")
n, ds = 8, [1, 8, 16]
st = cascade(n, ds)
print("  cascade steps:", st)
z16 = ((2 - F(1, 8)) / 16, (2 + F(1, 8)) / 16)
z8 = ((1 - F(1, 8)) / 8, (1 + F(1, 8)) / 8)
b = F(1, 64 // 8)
print("  bound", b, " in zone(16)?", z16[0] < b < z16[1], " in zone(8)?", z8[0] < b < z8[1])
print("  end of zone(16) =", z16[1], " inside zone(8)?", z8[0] < z16[1] < z8[1])
print("  run A = [zone(8)] ends", z8[1], "; run B = [zone(16), zone(8)] ends", z8[1],
      "; lonely there?", lonely(n, ds, z8[1]))

print("=" * 72)
print("CHECK 4  Section 2.1 'every candidate instant this paper constructs is an endpoint'")
n, ds = 8, [1, 2, 3, 4, 5, 7, 8]
t = F(1, 6)
opening = [(e, t * e - F(1, n)) for e in ds if (t * e - F(1, n)).denominator == 1]
print("  R6 instant t=1/6 lonely?", lonely(n, ds, t), "; is it an opening of any flank?", opening or "no")
print("  cascade halts at", cascade(n, ds)[-1], "; certificate (7,1) works?",
      all(e <= (d * (8 * 1 + 1)) % (8 * 7) <= 7 * 7 for d in ds for e in [7]))

print("=" * 72)
print("CHECK 5  Section 12 {1,2,3,5} at n=5: flank 5 is not coprime to 5")
n, ds = 5, [1, 2, 3, 5]
for e, j in [(5, 1), (3, 2)]:
    a = n * j + 1
    print(f"  flank {e}, j={j}: readings {[(d * a) % (n * e) for d in ds]} band [{e},{(n - 1) * e}]"
          f"  ok={all(e <= (d * a) % (n * e) <= (n - 1) * e for d in ds)}  gcd(e,n)={gcd(e, n)}")

print("=" * 72)
print("CHECK 6  Section 4 scale: reading s*u with u = d_min t; Theorem 8 at u = 1/n")
n, s = 8, 7
u = F(1, n)
print(f"  s={s}, u=1/n: s*u = {s * u}; its distance from Z = {circ(s * u)} (>= 1/n: {circ(s * u) >= F(1, n)});"
      f" distance of s*u from nZ = {min(abs(s * u - n * k) for k in range(0, 3))} (>= 1: False)")
