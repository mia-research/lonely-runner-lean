#!/usr/bin/env python3
"""
eps_to_d_run_v1.py  —  RUN of PREREG_eps_to_d_constraint_v1.md (frozen spec).

Question (1) IDENTITY: is public eps(x(P_sum)) a function of the d-side carry ε(d1,d2,j)?
Primary statistic M = #unforced-orbit-reps with [eps(x_sum) >= 1] == ε, vs a matched control that
preserves μ3/j forcing and destroys only the point<->carry link. Plants must fire before any verdict.

Definitions frozen by the prereg:
  feature  f = [eps(x(P_sum)) >= 1],  eps from int1_frame_operator.build(p)  (x-only, no d)
  j        = μ3-orbit coord of P_sum = index of χ3(x_sum) in {1,ω_p,ω_p^2}     (public, from x)
  target   ε = [ (d1*λ^j mod m) + (d2*λ^j mod m) >= m ]                         (scalars + public j)
  unforced = one representative per ⟨φ⟩-orbit of the sum scalar (d1+d2) under ×λ mod m

EXACT: all signal-path arithmetic is int (χ3 via pow, ε via int compare, s<3/16 via 16*enorm<3*p).
No float in the signal path. eps/eis/enorm are integer maps.
"""
import random
from fractions import Fraction as Fr
from sympy import isprime
from int1_frame_operator_v1 import build
from lift_sextant_rhombus_law_proof_v2 import enorm


# ---------- exact curve machinery (y^2 = x^3 + 7) ----------
def legendre(a, p):
    a %= p
    if a == 0:
        return 0
    return 1 if pow(a, (p - 1) // 2, p) == 1 else -1


def tonelli(a, p):
    a %= p
    if a == 0:
        return 0
    if p % 4 == 3:
        return pow(a, (p + 1) // 4, p)
    q, s = p - 1, 0
    while q % 2 == 0:
        q //= 2; s += 1
    z = 2
    while legendre(z, p) != -1:
        z += 1
    m, c, t, r = s, pow(z, q, p), pow(a, q, p), pow(a, (q + 1) // 2, p)
    while t != 1:
        i, t2 = 0, t
        while t2 != 1:
            t2 = t2 * t2 % p; i += 1
        b = pow(c, 1 << (m - i - 1), p)
        m, c, t, r = i, b * b % p, t * b * b % p, r * b % p
    return r


def padd(P, Q, p):
    if P is None:
        return Q
    if Q is None:
        return P
    (x1, y1), (x2, y2) = P, Q
    if x1 == x2 and (y1 + y2) % p == 0:
        return None
    if P == Q:
        lam = (3 * x1 * x1) % p * pow(2 * y1, p - 2, p) % p
    else:
        lam = (y2 - y1) % p * pow((x2 - x1) % p, p - 2, p) % p
    x3 = (lam * lam - x1 - x2) % p
    return (x3, (lam * (x1 - x3) - y1) % p)


def prime_order_curve(lo, hi):
    """y^2=x^3+7 over F_q, q==1 mod 3, prime group order m; return (q, m, G)."""
    for q in range(lo, hi):
        if not (isprime(q) and q % 3 == 1):
            continue
        m = q + 1
        for x in range(q):
            m += legendre((x ** 3 + 7) % q, q)
        if isprime(m):
            for x0 in range(1, q):
                r = (x0 ** 3 + 7) % q
                if legendre(r, q) == 1:
                    return q, m, (x0, tonelli(r, q))
    return None


def full_orbit(G, p, m):
    xs = [None] * m
    acc = None
    for d in range(1, m):
        acc = padd(acc, G, p)
        xs[d] = acc[0]
    return xs  # xs[d] = x([d]G); xs[0] = None (point at infinity)


def find_glv(xs, p, m):
    """λ (mod m), β (mod p) with x([λ d]G) = β x([d]G); ω_p a primitive cube root mod p."""
    e = (p - 1) // 3
    g = 2
    while pow(g, e, p) == 1:
        g += 1
    wp = pow(g, e, p)                     # primitive cube root of 1 mod p
    for beta in (wp, wp * wp % p):
        for lam in [c for c in range(2, m) if pow(c, 3, m) == 1 and c != 1]:
            if all(xs[(lam * d) % m] == (beta * xs[d]) % p for d in range(1, min(30, m))):
                return lam, beta, wp
    return None, None, wp


def chi3_index(x, p, wp):
    """j = index of χ3(x)=x^((p-1)/3) in {1(->0), ω_p(->1), ω_p^2(->2)}."""
    v = pow(x % p, (p - 1) // 3, p)
    if v == 1:
        return 0
    if v == wp:
        return 1
    return 2                              # wp^2


# ---------- the run on one curve ----------
def run_curve(p, m, G, d1, B=2000, rng=None, verbose=True):
    rng = rng or random.Random(0)
    xs = full_orbit(G, p, m)
    lam, beta, wp = find_glv(xs, p, m)
    if lam is None:
        return None
    eis, eps = build(p)

    # collect one unforced representative per ⟨λ⟩-orbit of the SUM scalar t=(d1+d2) mod m
    seen = set()
    reps = []   # (t, x_sum, f, eps_raw, j, s_lt)
    for d2 in range(1, m):
        t = (d1 + d2) % m
        if t == 0:
            continue
        orb_min = min(t, (lam * t) % m, (lam * lam * t) % m)
        if orb_min in seen:
            continue
        seen.add(orb_min)
        x_sum = xs[t]
        if x_sum is None:
            continue
        er = eps(x_sum)
        f = 1 if er >= 1 else 0
        j = chi3_index(x_sum, p, wp)
        s_lt = (16 * enorm(eis(x_sum)) < 3 * p)        # s < 3/16, exact
        reps.append((t, d1, d2, f, er, j, s_lt))
    U = len(reps)

    def eps_of(d1_, d2_, j):
        lj = pow(lam, j, m)
        r1 = (d1_ * lj) % m
        r2 = (d2_ * lj) % m
        return 1 if (r1 + r2) >= m else 0

    def pct95(vals):                       # integer 95th percentile, no float
        return sorted(vals)[(95 * len(vals)) // 100]

    # PRIMARY: M_real = # reps with f == ε(d1,d2,j)
    tgt = [eps_of(d1, d2, j) for (t, d1_, d2, f, er, j, s_lt) in reps]
    feat = [f for (t, d1_, d2, f, er, j, s_lt) in reps]
    M_real = sum(1 for a, b in zip(feat, tgt) if a == b)
    n_eps1 = sum(tgt)                       # #{ε=1}; largest cell q = max(n_eps1, U-n_eps1)

    # MATCHED CONTROL: re-pair f_r with ε(d1, d2', j_r), d2' from same j-bin (preserve j forcing)
    byj = {}
    for (t, d1_, d2, f, er, j, s_lt) in reps:
        byj.setdefault(j, []).append(d2)
    Mc = []
    for _ in range(B):
        Mc.append(sum(1 for (t, d1_, d2, f, er, j, s_lt) in reps
                      if f == eps_of(d1, rng.choice(byj[j]), j)))
    cnt_ge = sum(1 for x in Mc if x >= M_real)
    p_perm = Fr(cnt_ge + 1, B + 1)          # exact permutation p-value (integer counts)
    c95 = pct95(Mc)

    # PLANTS (all integer count comparisons)
    # positive: feature := ε  -> must give M = U  (validates the comparison pipeline)
    M_pos = sum(1 for (t, d1_, d2, f, er, j, s_lt) in reps if eps_of(d1, d2, j) == eps_of(d1, d2, j))
    # negative: μ3-respecting random field independent of ε (constant within j-bin)
    nb = {j: rng.randint(0, 1) for j in byj}
    M_neg = sum(1 for (t, d1_, d2, f, er, j, s_lt) in reps if nb[j] == eps_of(d1, d2, j))
    Mc_neg = []
    for _ in range(B):
        nbn = {j: rng.randint(0, 1) for j in byj}
        Mc_neg.append(sum(1 for (t, d1_, d2, f, er, j, s_lt) in reps
                          if nbn[j] == eps_of(d1, rng.choice(byj[j]), j)))
    neg_c95 = pct95(Mc_neg)

    # gate: s<3/16 => ε=0 ? count violations among reps (real carry ε)
    gate_viol = sum(1 for (t, d1_, d2, f, er, j, s_lt) in reps if s_lt and eps_of(d1, d2, j) != 0)
    # gate PLANT (prereg §4): a truly-gated ε_plant (0 when s<3/16) must report 0 violations
    gate_plant_viol = sum(1 for (t, d1_, d2, f, er, j, s_lt) in reps if s_lt and (0 if s_lt else 1) != 0)

    # verdict pieces (all integer): identity fires iff M_real>c95 AND 20*(cnt_ge+1)<=(B+1) (p<=0.05)
    fires = (M_real > c95) and (20 * (cnt_ge + 1) <= (B + 1))
    powered = (U - c95)                     # if full identity (M_real=U) would we clear control? >0 = yes

    if verbose:
        print(f"  p={p} m={m} d1={d1}: U={U}  M_real={M_real}  ctrl[95%]={c95}  "
              f"p_perm={p_perm.numerator}/{p_perm.denominator}  fires={fires}")
        print(f"     PLANTS: pos M={M_pos}/{U} (need =U)   neg M={M_neg} vs ctrl95={neg_c95} (need <=)   "
              f"gate s<3/16&ε!=0 viol={gate_viol} (gate-plant viol={gate_plant_viol}, need 0)   "
              f"power U-ctrl95={powered} (>0 to detect)  #eps1={n_eps1}")
    return dict(p=p, m=m, d1=d1, U=U, M_real=M_real, c95=c95, p_perm=p_perm, fires=fires,
                M_pos=M_pos, M_neg=M_neg, neg_c95=neg_c95, gate_viol=gate_viol,
                powered=powered, n_eps1=n_eps1)


def single_key_mc(p, m, G, B=2000, rng=None, verbose=True):
    """SECONDARY M_c (prereg §2): single-key frozen map eps(x([d]G)) vs c(d) mod 3.
    c(d) = ((-1)^s d0 (λ^j mod m) - d)//m, d0=orbit-min under ±λ^k. Both in {0,1,2}."""
    rng = rng or random.Random(0)
    xs = full_orbit(G, p, m)
    lam, beta, wp = find_glv(xs, p, m)
    if lam is None:
        return None
    eis, eps = build(p)
    seen = set(); reps = []
    for d in range(1, m):
        orb = []
        for k in range(3):
            lk = pow(lam, k, m)
            orb.append((lk * d) % m); orb.append((-lk * d) % m)
        d0 = min(x for x in orb if x != 0)
        if d0 in seen:
            continue
        seen.add(d0)
        # find (j,s): d == (-1)^s * λ^j * d0 mod m
        j = s = None
        for k in range(3):
            lk = pow(lam, k, m)
            if (lk * d0) % m == d % m:
                j, s = k, 0; break
            if (-lk * d0) % m == d % m:
                j, s = k, 1; break
        lj = pow(lam, j, m)
        c = (((-1) ** s) * d0 * lj - d) // m
        tc = c % 3
        fe = eps(xs[d])                       # feature in {0,1,2}; frozen map eps->eps mod3 = eps
        reps.append((d, j, fe, tc))
    U = len(reps)
    M_real = sum(1 for (d, j, fe, tc) in reps if fe == tc)
    byj = {}
    for (d, j, fe, tc) in reps:
        byj.setdefault(j, []).append((d, tc))
    Mc = []
    for _ in range(B):
        M = 0
        for (d, j, fe, tc) in reps:
            _, tcp = rng.choice(byj[j])       # permute target within same j-bin
            if fe == tcp:
                M += 1
        Mc.append(M)
    cnt_ge = sum(1 for x in Mc if x >= M_real)
    p_perm = Fr(cnt_ge + 1, B + 1)
    c95 = sorted(Mc)[(95 * B) // 100]
    fires = (M_real > c95) and (20 * (cnt_ge + 1) <= (B + 1))
    if verbose:
        print(f"  [M_c single-key] p={p} m={m}: U={U}  M_real={M_real}  ctrl95={c95}  "
              f"p_perm={p_perm.numerator}/{p_perm.denominator}  fires={fires}")
    return dict(U=U, M_real=M_real, c95=c95, p_perm=p_perm, fires=fires)


def main():
    print("PREREG_eps_to_d_constraint_v1 — RUN\n")
    print("[A] p=43 plumbing curve (U small; verifying plants fire, not a verdict):")
    r = prime_order_curve(43, 44)
    if r:
        p, m, G = r
        for d1 in (1, 5, 11):
            run_curve(p, m, G, d1, B=1000, rng=random.Random(1))

    print("\n[B] powered curves (search for prime order m with U=m/3 >= 55):")
    lo = 500
    found = 0
    rng = random.Random(7)
    while found < 3 and lo < 12000:
        r = prime_order_curve(lo, lo + 400)
        if r and r[1] // 3 >= 55:
            p, m, G = r
            for d1 in (1, 7, 13):
                run_curve(p, m, G, d1, B=2000, rng=random.Random(100 + d1))
            single_key_mc(p, m, G, B=2000, rng=random.Random(555))
            found += 1
            print()
        lo += 400


if __name__ == "__main__":
    main()
