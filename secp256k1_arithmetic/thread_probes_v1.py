#!/usr/bin/env python3
"""
Thread-grounding probes for the secp256k1 pure-arithmetic study (2026-07-11).

P1  Single-symbol hypothesis: is the Hecke unit u(ell) (defined by
    a_ell = Tr(u * pi_primary)) equal to  u0 * (c/pi)_6^e  for fixed
    rational c, exponent e, constant unit u0?  Exhaustive search over
    c in {2,4,7,12,14,21,28,63}, e in 1..5, u0 in mu_6, both conjugates,
    validated on all split ell < 2000, re-validated on 2000..5000.
    If found: evaluate at the 256-bit p (expect unit 1 = capstone) and at
    n on the ideal (1 - pi_p) (expect the amicable alignment unit).

P2  ASD / Honda upgrades:
    (a) three-term  b_{ell^2} - a_ell b_ell + ell  mod ell^2 and ell^3,
        split ell in {13,19,31,37,43,61,67,73,79,97};
    (b) all-m congruence b_m = a_m mod m for every m = 1 mod 6, m <= 500
        (composites included; bad prime 7 tracked separately).
    b_m := 7^((m-1)/6) * C((m-1)/2, (m-1)/6).

P3  Amicable closure rate: among split ell < 200000 with q = #E7(F_ell)
    prime, how often does #E7(F_q) = ell?  Heuristic prediction 1/6.
    Uses the P1 formula if validated (Cornacchia-fast), else brute counts
    to a reduced bound. Includes the (67,79) worked example.

P4  Formal-log radius: verify T_c^6 = 4/(27*7) equals the T-chart critical
    point x^3 = 2b exactly (symbolic identity), and compute the boundary
    value L(T_c) as an elliptic integral; compare against Omega multiples.

Exact arithmetic decides P1-P3; P4's boundary value is numerical (reported,
not asserted).
"""

import math, random
from fractions import Fraction

random.seed(11)

p  = 2**256 - 2**32 - 977
n  = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141
A_ = 367917413016453100223835821029139468249
B_ = 303414439467246543595250775667605759171
UNITS = [(1,0), (-1,0), (0,1), (0,-1), (-1,-1), (1,1)]  # 1,-1,w,-w,w^2,-w^2

def mulw(a, b):  # (a0+a1 w)(b0+b1 w), w^2 = -1-w
    return (a[0]*b[0] - a[1]*b[1], a[0]*b[1] + a[1]*b[0] - a[1]*b[1])
def Nrm(v): return v[0]*v[0] - v[0]*v[1] + v[1]*v[1]
def Tr(v):  return 2*v[0] - v[1]
def conj(v): return (v[0]-v[1], -v[1])

def primary(v):
    """unique associate with x=2 mod 3, y=0 mod 3 (norm coprime to 3)."""
    out = [mulw(u, v) for u in UNITS]
    hits = [w for w in out if w[0] % 3 == 2 and w[1] % 3 == 0]
    assert len(hits) == 1, (v, hits)
    return hits[0]

def cornacchia(ell):
    """some (x,y) with x^2-xy+y^2 = ell, ell = 1 mod 3 prime."""
    for y in range(1, math.isqrt(4*ell//3) + 2):
        d = 4*ell - 3*y*y
        if d < 0: break
        s = math.isqrt(d)
        if s*s == d and (s + y) % 2 == 0:
            return ((s + y)//2, y)
    raise ValueError(ell)

def sieve(limit):
    bs = bytearray([1])*(limit+1); bs[0:2] = b'\x00\x00'
    for i in range(2, math.isqrt(limit)+1):
        if bs[i]: bs[i*i::i] = bytearray(len(bs[i*i::i]))
    return [i for i in range(limit+1) if bs[i]]

def a_count(ell):
    """a_ell for y^2 = x^3 + 7 by table-based count."""
    qr = bytearray(ell)
    for x in range((ell//2)+1): qr[x*x % ell] = 1
    cnt = 1
    for x in range(ell):
        v = (x*x*x + 7) % ell
        if v == 0: cnt += 1
        elif qr[v]: cnt += 2
    return ell + 1 - cnt

# ---------------------------------------------------------------------------
# P1: single sextic symbol search
# ---------------------------------------------------------------------------
print("=== P1: single-symbol search for the Hecke unit ===")
primes = sieve(5000)
def frob_unit(ell):
    """(u_index, pi_primary, w) with a_ell = Tr(u * pi_prim); w = omega mod pi.
       Convention: pi = cornacchia rep (fixes the prime above ell)."""
    a = a_count(ell)
    pi0 = cornacchia(ell)
    pip = primary(pi0)
    matches = [i for i, u in enumerate(UNITS) if Tr(mulw(u, pip)) == a]
    if len(matches) != 1: return None  # trace tie; skip
    w = (-pip[0] * pow(pip[1], -1, ell)) % ell   # omega mod (pi)
    return matches[0], pip, w, a

def unit_table(w, ell):
    """reduction of the six units mod (pi) -> index."""
    return { (u[0] + u[1]*w) % ell : i for i, u in enumerate(UNITS) }

# mu_6 is cyclic: generator g = -w^2 = (1,1) = zeta_6.  index->power table:
# order: 1,-1,w,-w,w^2,-w^2 = zeta^0, zeta^3, zeta^2, zeta^5, zeta^4, zeta^1
IDX2POW = {0:0, 1:3, 2:2, 3:5, 4:4, 5:1}
POW2IDX = {v:k for k,v in IDX2POW.items()}

train, test = [], []
for ell in primes:
    if ell < 11 or ell % 3 != 1 or ell in (7,): continue
    fu = frob_unit(ell)
    if fu is None: continue
    (train if ell < 2000 else test).append((ell, fu))

cands = []
for c in (2, 4, 7, 12, 14, 21, 28, 63):
    for e in range(1, 6):
        for u0 in range(6):
            for cj in (False, True):
                cands.append((c, e, u0, cj))

def formula_unit(c, e, u0, cj, ell, pip, w):
    if cj:
        pipc = conj(pip)
        w = (-pipc[0] * pow(pipc[1], -1, ell)) % ell
    tab = unit_table(w, ell)
    s = pow(c % ell, (ell - 1)//6, ell)
    if s not in tab: return None
    powc = (IDX2POW[tab[s]] * e + IDX2POW[u0]) % 6
    return POW2IDX[powc]

survivors = []
for cand in cands:
    ok = True
    for ell, (ui, pip, w, a) in train:
        if math.gcd(cand[0], ell) != 1: continue
        if formula_unit(*cand, ell, pip, w) != ui: ok = False; break
    if ok: survivors.append(cand)
print(f"  survivors on split ell < 2000 ({len(train)} primes): {survivors}")
final = []
for cand in survivors:
    if all(formula_unit(*cand, ell, pip, w) == ui
           for ell, (ui, pip, w, a) in test if math.gcd(cand[0], ell) == 1):
        final.append(cand)
print(f"  re-validated on 2000..5000 ({len(test)} primes): {final}")

FORMULA = final[0] if final else None
if FORMULA:
    c, e, u0, cj = FORMULA
    print(f"  ==> u(ell) = zeta6^{IDX2POW[u0]} * (({c}/pi)_6{'~conj' if cj else ''})^{e}")
    # capstone at p: pi_p primary?  and expected unit 1 (index 0)
    pip_p = primary((A_, B_))
    print(f"  pi_p primary rep = {'(A,B) itself' if pip_p == (A_, B_) else pip_p}")
    w_p = (-pip_p[0] * pow(pip_p[1], -1, p)) % p
    up = formula_unit(c, e, u0, cj, p, pip_p, w_p)
    print(f"  formula at 256-bit p: unit index {up} "
          f"({'PASS: = 1, trace = t' if UNITS[up] == (1,0) else 'value ' + str(UNITS[up])})")
    # amicability at n: Frobenius over F_n must be 1 - pi_p
    target = (1 - A_, -B_)                      # 1 - pi_p, norm n
    pin = primary(target)
    # v = unit with  v * pin = target
    v = [u for u in UNITS if mulw(u, pin) == target]
    w_n = (-pin[0] * pow(pin[1], -1, n)) % n
    un = formula_unit(c, e, u0, cj, n, pin, w_n)
    print(f"  needed alignment unit at n: {v[0] if v else '??'}; formula gives {UNITS[un]}"
          f"  ({'PASS: amicability = one symbol evaluation' if v and UNITS[un] == v[0] else 'MISMATCH'})")

# ---------------------------------------------------------------------------
# P2: ASD / Honda upgrades
# ---------------------------------------------------------------------------
print("\n=== P2: ASD three-term + all-m congruences ===")
def b_(m): return 7**((m-1)//6) * math.comb((m-1)//2, (m-1)//6)

print("  (a) b_{l^2} - a_l b_l + l  mod l^2 / l^3 :")
for ell in (13, 19, 31, 37, 43, 61, 67, 73, 79, 97):
    a = a_count(ell)
    val = b_(ell*ell) - a*b_(ell) + ell
    print(f"    l={ell:3d}: mod l^2 {'0 PASS' if val % ell**2 == 0 else val % ell**2}"
          f" | mod l^3 {'0 (supercongruence!)' if val % ell**3 == 0 else 'nonzero'}")

# a_m multiplicative table
amem = {}
def a_m(m):
    if m in amem: return amem[m]
    if m == 1: return 1
    f, mm = {}, m
    d = 2
    while d*d <= mm:
        while mm % d == 0: f[d] = f.get(d,0)+1; mm //= d
        d += 1
    if mm > 1: f[mm] = f.get(mm,0)+1
    r = 1
    for ell, k in f.items():
        if ell in (2,3,7): loc = 0 if k >= 1 else 1
        else:
            a1 = a_count(ell); seq = [1, a1]
            for i in range(2, k+1): seq.append(a1*seq[-1] - ell*seq[-2])
            loc = seq[k]
        r *= loc
    amem[m] = r
    return r

bad = []
for m in range(7, 501, 6):
    if b_(m) % m != a_m(m) % m: bad.append(m)
def classify(m):
    f, mm, d = {}, m, 2
    while d*d <= mm:
        while mm % d == 0: f[d] = f.get(d,0)+1; mm //= d
        d += 1
    if mm > 1: f[mm] = f.get(mm,0)+1
    splitmult = sum(k for ell,k in f.items() if ell % 3 == 1 and ell != 7)
    return splitmult, 7 in f
viol = [m for m in bad if classify(m)[0] < 2 and not classify(m)[1]]
clean = [m for m in range(7, 501, 6) if m not in bad
         and (classify(m)[0] >= 2 or classify(m)[1])]
print(f"  (b) b_m = a_m mod m, m = 1 mod 6 <= 500: fails at {bad}")
print(f"      pattern [fails <=> >=2 split factors (w/ mult) or 7|m]: "
      f"{'EXACT' if not viol and not clean else f'exceptions {viol} {clean}'}")

# (c) mod-l^2 shape of b_l - a_l: fit delta*a^-1 = c2 q_2 + c3 q_3 + c7 q_7 + c0
#     (q_x = Fermat quotient (x^(l-1)-1)/l mod l) on 4 primes, validate on rest
print("  (c) delta_l := (b_l - a_l)/l * a_l^{-1} mod l vs Fermat quotients:")
splits = [ell for ell in primes if ell % 3 == 1 and 7 < ell < 300]
rows = []
for ell in splits:
    a = a_count(ell)
    delta = ((b_(ell) - a)//ell) % ell
    d = delta * pow(a, -1, ell) % ell
    qs = [ (pow(x, ell-1, ell*ell) - 1)//ell % ell for x in (2,3,7) ]
    rows.append((ell, d, qs))
import itertools
sol_found = None
for quad in itertools.combinations(range(len(rows)), 4):
    # solve d = c2 q2 + c3 q3 + c7 q7 + c0 mod ell for integer c's in [-6,6]
    pass  # (direct small search below instead)
for c2 in range(-6,7):
  for c3 in range(-6,7):
    for c7 in range(-6,7):
      for c0h in range(-6,7):   # c0 = c0h/2 allowed: test 2d = ... form
        ok = all((2*d - (2*c2*q[0] + 2*c3*q[1] + 2*c7*q[2] + c0h)) % ell == 0
                 for ell, d, q in rows)
        if ok: sol_found = (c2, c3, c7, c0h)
if sol_found:
    c2, c3, c7, c0h = sol_found
    print(f"      FIT: delta/a = {c2} q_l(2) + {c3} q_l(3) + {c7} q_l(7) + {c0h}/2  (all split l<300)")
else:
    print(f"      no small integer/half-integer Fermat-quotient fit on l<300; "
          f"sample (l, delta/a, q2, q3, q7): {rows[:5]}")

# ---------------------------------------------------------------------------
# P3: amicable closure rate
# ---------------------------------------------------------------------------
print("\n=== P3: amicable closure rate for E7 ===")
# worked example (67,79)
a67 = a_count(67); q67 = 67 + 1 - a67
a79 = a_count(79)
print(f"  (67): a=({a67}), #E={q67}; closure needs a_79 = {2-a67}; actual a_79 = {a79}"
      f"  -> {'2-cycle CLOSES' if a79 == 2 - a67 and 79 + 1 - a79 == 67 else 'open'}")

if FORMULA:
    c, e, u0, cj = FORMULA
    def a_fast(ell):
        if ell <= 7 or math.gcd(ell, 84) != 1: return None  # bad/uncovered
        fu_pi = primary(cornacchia(ell))
        w = (-fu_pi[0] * pow(fu_pi[1], -1, ell)) % ell
        ui = formula_unit(c, e, u0, cj, ell, fu_pi, w)
        if ui is None: return None
        return Tr(mulw(UNITS[ui], fu_pi))
    # sanity: formula vs count on 30 random split primes < 5000
    smp = [ell for ell in primes if ell % 3 == 1 and ell > 7]
    assert all(a_fast(ell) == a_count(ell) for ell in random.sample(smp, 30))
    LIM = 200_000
    ps = sieve(LIM)
    pset = set(ps)
    def isprime_big(x):
        if x <= LIM: return x in pset
        for q in ps[:60]:
            if x % q == 0: return False
        d, s = x-1, 0
        while d % 2 == 0: d //= 2; s += 1
        for _ in range(20):
            a0 = random.randrange(2, x-1); y = pow(a0, d, x)
            if y in (1, x-1): continue
            for _ in range(s-1):
                y = y*y % x
                if y == x-1: break
            else: return False
        return True
    tot = closed = 0
    for ell in ps:
        if ell % 3 != 1 or ell <= 7: continue
        aL = a_fast(ell)
        if aL is None: continue
        q = ell + 1 - aL
        if q <= 7 or not isprime_big(q): continue   # q=2,3,7 bad: not aliquot
        if q % 3 != 1: continue
        aQ = a_fast(q)
        if aQ is None: continue
        tot += 1
        if aQ == 2 - aL: closed += 1
    import statistics
    se = math.sqrt((1/6)*(5/6)/tot)
    print(f"  split ell < {LIM}: {tot} with #E7(F_ell) prime (good); "
          f"2-cycle closes for {closed} ({closed/tot:.4f}); "
          f"1/6 = {1/6:.4f} +- {se:.4f} (1 SE)")
else:
    print("  (no validated formula; skipped large scan)")

# ---------------------------------------------------------------------------
# P4: radius = critical point; boundary value
# ---------------------------------------------------------------------------
print("\n=== P4: formal-log radius and boundary value ===")
# symbolic: T^2 = x^2/(x^3+b); d/dx = 0 => x(2b - x^3) ... => x^3 = 2b,
# T_c^6 = (x^2/(x^3+b))^3 at x^3=2b: ((2b)^(2/3)/(3b))^3 = 4b^2/27b^3 = 4/(27b)
b = 7
Tc6 = Fraction(4, 27*b)
print(f"  T_c^6 = 4/(27b) = {Tc6}  (= 4/189; critical point x^3 = 2b = 14) [exact]")
x_star = (2*b) ** (1/3)
def om_int(x_lo, N_=1_000_000, S=200.0):
    def f(s):
        if s == 0.0:
            d = 3*x_lo*x_lo
            return 2.0/math.sqrt(d) if d > 0 else 0.0
        x = x_lo + s*s
        return 2*s/math.sqrt(x**3 + b)
    h = S/N_; tot = 0.0
    for i in range(N_+1):
        wgt = 1 if i in (0, N_) else (4 if i % 2 else 2)
        tot += wgt*f(i*h)
    return tot*h/3 + 2/math.sqrt(x_lo + S*S)
Om = math.gamma(1/3)*math.gamma(1/6)/(2*math.sqrt(math.pi)*7**(1/6))
Lc = om_int(x_star) / 2.0          # elliptic log = int_{x*}^inf dx/(2y)
print(f"  L(T_c) = {Lc:.9f};  Omega = {Om:.9f};  ratio = {Lc/Om:.9f}")
for lab, v in (("1/6", 1/6), ("1/5", .2), ("1/4", .25), ("2/9", 2/9),
               ("1/3", 1/3), ("1/(2pi)", 1/(2*math.pi)), ("3/14", 3/14)):
    if abs(Lc/Om - v) < 2e-4: print(f"    ~ matches {lab}")
print(f"  series check: T_c*3F2(...;1) partial sums -> ", end="")
Tcf = (4/(27*b)) ** (1/6)
sser, term = 0.0, 0.0
sK = 0.0
kk = 0
val = 1.0
# ratio method: t_0 = 1; t_{k+1}/t_k = ((k+1/6)(k+1/3)(k+2/3))/((k+1/2)(k+7/6)(k+1))
tk, ssum = 1.0, 1.0
for k in range(0, 400000):
    tk *= ((k+1/6)*(k+1/3)*(k+2/3))/((k+1/2)*(k+7/6)*(k+1))
    ssum += tk
print(f"{Tcf*ssum:.6f} (slow tail; integral value above is the precise one)")
