#!/usr/bin/env python3
"""Attack the single open gap of RESULT_jacobi_closed_form_m_law_v4 sec2: the SIGN of J(chi3,chi4)
over F_{p^2}, p = 3 mod 4.

Candidate classical input (SEMIPRIMITIVE / subfield-trivial Gauss sum): a character chi of order d on
F_{p^2}* is trivial on F_p* iff d | p+1, and then
        g(chi) = (-1)^((p+1)/d) * p                                    (S)
This script VERIFIES (S) exactly, then checks the two consequences:
  (C1) it reproduces the record's BARRED 3-point G(chi4) rule  (+p at p=7 mod 8, -p at p=3 mod 8)
  (C2) at p = 11 mod 12 (12 | p+1) all of chi3,chi4,chi12 are semiprimitive, so with k=(p+1)/12
       J = g(chi3)g(chi4)/g(chi12) has sign exponent 4k+3k-k = 6k = EVEN  =>  J = +p.
  (B)  at p = 7 mod 12, chi3 is a NORM-LIFT (3 | p-1) and chi12 is neither lift nor semiprimitive --
       record what g(chi12) actually is, to see what the remaining case needs.

EXACT ARITHMETIC ONLY. Z[zeta_12] = Z[x]/(x^4-x^2+1); zeta_12=z, zeta_6=z^2, zeta_4=z^3, zeta_3=z^4,
zeta_2=z^6. Gauss sums are computed as elements of Z[zeta_12][zeta_p] and reduced on the basis
{zeta_p^1..zeta_p^(p-1)}; a value is a rational integer iff the p-1 coefficients agree. No floats."""

PHI12 = [1, 0, -1, 0, 1]          # x^4 - x^2 + 1, low-to-high

def zmul(a, b):
    """multiply in Z[zeta_12] = Z[x]/(x^4-x^2+1); a,b are length-4 coeff lists (low->high)."""
    r = [0]*7
    for i, ai in enumerate(a):
        if ai:
            for j, bj in enumerate(b):
                if bj: r[i+j] += ai*bj
    for k in (6, 5, 4):            # reduce: x^4 = x^2 - 1
        c = r[k]
        if c:
            r[k] = 0; r[k-2] += c; r[k-4] -= c
    return r[:4]

def zadd(a, b): return [x+y for x, y in zip(a, b)]
def zsub(a, b): return [x-y for x, y in zip(a, b)]
ZERO = [0, 0, 0, 0]
def zpow_zeta12(e):
    """zeta_12^e as an element of Z[zeta_12]."""
    e %= 12
    r = [1, 0, 0, 0]
    for _ in range(e): r = zmul(r, [0, 1, 0, 0])
    return r
def is_rat_int(a): return a[1] == 0 and a[2] == 0 and a[3] == 0

# ---------- F_{p^2} as F_p[i], i^2 = -1  (valid since p = 3 mod 4) ----------
def f2_mul(u, v, p): return ((u[0]*v[0] - u[1]*v[1]) % p, (u[0]*v[1] + u[1]*v[0]) % p)

def build_field(p):
    els = [(a, b) for a in range(p) for b in range(p) if (a, b) != (0, 0)]
    # find a generator of F_{p^2}^*
    order = p*p - 1
    fac = []
    m = order; d = 2
    while d*d <= m:
        if m % d == 0:
            fac.append(d)
            while m % d == 0: m //= d
        d += 1
    if m > 1: fac.append(m)
    def powf(u, e):
        r = (1, 0)
        while e:
            if e & 1: r = f2_mul(r, u, p)
            u = f2_mul(u, u, p); e >>= 1
        return r
    gen = None
    for u in els:
        if all(powf(u, order//q) != (1, 0) for q in fac): gen = u; break
    dlog = {}
    cur = (1, 0)
    for k in range(order):
        dlog[cur] = k
        cur = f2_mul(cur, gen, p)
    return els, dlog, order

def gauss_sum(p, d, els, dlog, order):
    """g(chi_d) = sum_{x != 0} chi_d(x) * zeta_p^Tr(x), chi_d(gen)=zeta_d.  Returns int or None."""
    assert order % d == 0
    step = order // d                       # chi_d(g^k) = zeta_d^(k/step)... use exponent k*12/d /? :
    # chi_d(g^k) = zeta_d^k = zeta_12^(k * 12/d)
    e12 = 12 // d
    coeff = [ZERO[:] for _ in range(p)]     # c_t in Z[zeta_12], t = Tr(x) in F_p
    for x in els:
        k = dlog[x]
        t = (2*x[0]) % p                    # Tr(a+bi) = 2a
        coeff[t] = zadd(coeff[t], zpow_zeta12((k*e12) % 12))
    # g = sum_t c_t zeta_p^t ; using 1 = -sum_{t>=1} zeta_p^t  =>  g = sum_{t>=1} (c_t - c_0) zeta_p^t.
    # If every (c_t - c_0) equals a common v, then g = v * sum_{t>=1} zeta_p^t = v*(-1) = -v.
    # (An earlier version returned c_0 - v; that gave |g| = 2p-1, impossible for |g| = p over F_{p^2}.)
    diffs = [zsub(coeff[t], coeff[0]) for t in range(1, p)]
    v = diffs[0]
    if any(dd != v for dd in diffs): return None       # not a rational integer
    m = [-c for c in v]                                 # g = -v
    return m[0] if is_rat_int(m) else None

def jacobi(p, d1, d2, els, dlog, order):
    """J(chi_d1, chi_d2) = sum_x chi_d1(x) chi_d2(1-x), exact in Z[zeta_12]."""
    e1, e2 = 12 // d1, 12 // d2
    tot = ZERO[:]
    for x in els:
        y = ((1 - x[0]) % p, (-x[1]) % p)
        if y == (0, 0): continue
        k1, k2 = dlog[x], dlog[y]
        tot = zadd(tot, zmul(zpow_zeta12((k1*e1) % 12), zpow_zeta12((k2*e2) % 12)))
    return tot

print("=== (S) semiprimitive Gauss sum  g(chi_d) = (-1)^((p+1)/d) * p   for d | p+1, over F_{p^2} ===")
print(f"  {'p':>4} {'p%12':>5} {'d':>3} {'(p+1)/d':>8} {'predicted':>10} {'computed':>10}  ok")
PRIMES = [7, 11, 19, 23, 31, 43, 47, 59, 67, 71, 79, 83]
allok = True
for p in PRIMES:
    els, dlog, order = build_field(p)
    for d in (2, 3, 4, 6, 12):
        if (p+1) % d: continue
        pred = (-1)**((p+1)//d) * p
        got = gauss_sum(p, d, els, dlog, order)
        ok = (got == pred); allok &= ok
        print(f"  {p:>4} {p%12:>5} {d:>3} {(p+1)//d:>8} {pred:>10} {str(got):>10}  {'OK' if ok else 'FAIL'}")
print(f"  --> (S) holds in every tested cell: {allok}")

print("\n=== (C1) does (S) reproduce the record's BARRED 3-point G(chi4) rule? ===")
print(f"  {'p':>4} {'p%8':>4} {'record rule':>12} {'(S) says':>9} {'computed':>9}  agree")
for p in PRIMES:
    if (p+1) % 4: continue
    els, dlog, order = build_field(p)
    rec = p if p % 8 == 7 else -p          # record: +p at p=7 mod 8, -p at p=3 mod 8
    s = (-1)**((p+1)//4) * p
    got = gauss_sum(p, 4, els, dlog, order)
    print(f"  {p:>4} {p%8:>4} {rec:>12} {s:>9} {str(got):>9}  {'YES' if rec == s == got else 'NO'}")

print("\n=== (C2) p = 11 mod 12: J(chi3,chi4) from (S).  sign exponent 4k+3k-k = 6k, k=(p+1)/12 ===")
print(f"  {'p':>4} {'k':>3} {'6k even?':>9} {'predicted J':>12} {'computed J':>12}  ok")
for p in PRIMES:
    if p % 12 != 11: continue
    els, dlog, order = build_field(p)
    k = (p+1)//12
    pred = p                                # (-1)^(6k) = +1
    J = jacobi(p, 3, 4, els, dlog, order)
    got = J[0] if is_rat_int(J) else J
    print(f"  {p:>4} {k:>3} {str((6*k) % 2 == 0):>9} {pred:>12} {str(got):>12}  {'OK' if got == pred else 'FAIL'}")

print("\n=== (B) p = 7 mod 12: chi3 is a NORM-LIFT, chi12 is neither. What is g(chi12)? ===")
print(f"  {'p':>4} {'g(chi4)':>9} {'g(chi12)':>28} {'J(chi3,chi4)':>14}")
for p in PRIMES:
    if p % 12 != 7: continue
    els, dlog, order = build_field(p)
    g4 = gauss_sum(p, 4, els, dlog, order)
    g12 = gauss_sum(p, 12, els, dlog, order)
    J = jacobi(p, 3, 4, els, dlog, order)
    got = J[0] if is_rat_int(J) else J
    print(f"  {p:>4} {str(g4):>9} {str(g12):>28} {str(got):>14}")

# ===================== FROBENIUS: what is FORCED, and what is not =====================
# Frobenius x -> x^p permutes F_{p^2}, so J(chi^p, psi^p) = J(chi, psi)  (substitution in the sum).
#   p = 11 mod 12: chi3^p = chi3^2 = chi3^-1 and chi4^p = chi4^3 = chi4^-1  =>  conj(J) = J
#                  => J REAL, and |J| = p  =>  J = +-p.  Sign then from (S).  [both halves forced]
#   p =  7 mod 12: chi3^p = chi3 (norm-lift) and chi4^p = chi4^-1  =>  only sigma_7-invariance,
#                  whose fixed field in Q(zeta_12) is Q(zeta_3)  =>  J in Z[zeta_3], |J| = p.
#                  That does NOT force J = -p: elements of norm p^2 in Z[zeta_3] include +-p, +-p*w,
#                  +-p*w^2 AND pi^2 for the Eisenstein prime pi | p (p = 1 mod 3 SPLITS).
print("\n=== FROBENIUS invariance: J(chi^p, psi^p) == J(chi,psi)?  (forced identity) ===")
print(f"  {'p':>4} {'p%12':>5} {'chi3^p':>8} {'chi4^p':>8} {'J==J(frob)':>11} {'J real?':>8}")
for p in PRIMES:
    els, dlog, order = build_field(p)
    J  = jacobi(p, 3, 4, els, dlog, order)
    e3 = 4 if p % 3 == 1 else 8      # chi3^p: exponent of zeta_12 (chi3=z^4); p%3==1 -> chi3, else chi3^-1=z^8
    e4 = 9 if p % 4 == 3 else 3      # chi4^p: chi4=z^3; p%4==3 -> chi4^-1=z^9
    tot = ZERO[:]
    for x in els:
        y = ((1 - x[0]) % p, (-x[1]) % p)
        if y == (0, 0): continue
        tot = zadd(tot, zmul(zpow_zeta12((dlog[x]*e3) % 12), zpow_zeta12((dlog[y]*e4) % 12)))
    print(f"  {p:>4} {p%12:>5} {'chi3' if p%3==1 else 'chi3^-1':>8} {'chi4^-1':>8} "
          f"{str(tot == J):>11} {str(is_rat_int(J)):>8}")

print("\n=== p = 7 mod 12: is J = -p FORCED by 'J in Z[zeta_3] and |J| = p'?  (competing elements) ===")
print(f"  {'p':>4} {'J':>6} {'other norm-p^2 elts of Z[w] (pi^2, pi*conj(pi)=p, ...)':>56}")
for p in PRIMES:
    if p % 12 != 7: continue
    # Eisenstein prime above p: p = a^2 - a*b + b^2  (p = 1 mod 3 splits in Z[w])
    rep = None
    for a in range(1, 2*p):
        for b in range(1, 2*p):
            if a*a - a*b + b*b == p: rep = (a, b); break
        if rep: break
    a, b = rep
    # pi = a + b*w ; pi^2 = (a^2 - b^2) + (2ab - b^2) w   [using w^2 = -1-w]
    s1, s2 = a*a - b*b, 2*a*b - b*b
    nrm = s1*s1 - s1*s2 + s2*s2
    els, dlog, order = build_field(p)
    J = jacobi(p, 3, 4, els, dlog, order)
    print(f"  {p:>4} {str(J[0] if is_rat_int(J) else J):>6}   pi={a}+{b}w, pi^2=({s1})+({s2})w, N(pi^2)={nrm}=p^2={p*p}")
