#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
audit_d2_bridge_reduction_v1.py
================================
Exact-precision audit of the externally produced "D2 Lang-torsor twist bridge"
mod-6 keyspace-reduction claim for Bitcoin Puzzles 135 / 140.

Audited artifacts (~/Downloads):
  * eisenstein-core-gate-real-keys.py
  * farey-coprimality-filament-sieve-p135.py / farey-coprimality-filament-sieve-p140.py
  * farey-coprimality-filament-p135.md / farey-coprimality-filament-p140.md
  * d2-bridge-exact-residues.md
  * d2-bridge-search-space-reduction.md

Layered verdicts:
  [A] Raw arithmetic of every claimed constant / lift / norm / character.
  [B] Distributional content of the public "Core Gate" (s < 3/16).
  [C] The claimed INFORMATION reduction:
        C1  d mod 3 from the GLV orbit label ("bridge congruence")
        C2  d mod 2 from the public y LSB
        C3  their sandbox "verification" (checked for tautology)
  [D] Orbit-label facts that ARE real, and what they are worth.

Deterministic: seeded RNG. Pure stdlib. Usage: python3 audit_d2_bridge_reduction_v1.py [N_MAIN]
"""

import math
import random
import sys
from fractions import Fraction

random.seed(20260816)

# ----------------------------------------------------------------------------
# Section 0: constants
# ----------------------------------------------------------------------------
p = 2**256 - 2**32 - 977
n = 115792089237316195423570985008687907852837564279074904382605163141518161494337

A_SP = 367917413016453100223835821029139468249   # split p = a^2 - ab + b^2
B_SP = 64502973549206556628585045361533709078
BETA2 = 0x7ae96a2b657c07106e64479eac3434e99cf0497512f58995c1396c28719501ee
BETA1 = 0x851695d49a83f8ef919bb86153cbcb16630fb68aed0a766a3ec693d68e6afa40
LAM = 0x5363ad4cc05c30e0a5261c028812645a122e22ea20816678df02967c1b23bd72
LAM_INV = pow(LAM, -1, n)
GX = 0x79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798
GY = 0x483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8

X135 = 0x145d2611c823a396ef6712ce0f712f09b9b4f3135e3e0aa3230fb9b6d08d1e16
Y135 = 0x667a05e9a1bdd6f70142b66558bd12ce2c0f9cbc7001b20c8a6a109c80dc5330
X140 = 0x1f6a332d3c5c4f2de2378c012f429cd109ba07d69690c6c701b6bb87860d6640
Y140 = 0xf96923e4c4e959430c81a73a62a05609b2bbea22620cefc54a58182b9f2a2ae9

# Claimed values transcribed from the Downloads reports
CLAIM_S135 = 0.0589329970
CLAIM_S140 = 0.019792401440
CLAIM_Z135_F1 = (95212580547138244972706614431937799998, 52596102493765775842825011415457038458)  # with BETA1
CLAIM_Z135_F2 = (42616478053372469129881603016480761540, -52596102493765775842825011415457038458)  # with BETA2
CLAIM_Z140 = (52421632692394001710516608127457318831, 41402354554157814533999488250816709361)
CLAIM_MOCK_D = 39934069904927644054324625818796611221260
CLAIM_CF135_U = [0, 3, 1, 1, 2, 2, 1, 1, 1, 92, 5, 1, 1, 6, 3]
CLAIM_CF140_U = [0, 6, 4, 3, 1, 1, 14, 1, 3, 1, 1, 1, 1, 4, 4, 2, 2, 1, 6, 2]

EXP3 = (p - 1) // 3

PASS, FAIL = "PASS", "FAIL"


def check(name, ok, detail=""):
    print(f"  [{PASS if ok else FAIL}] {name}" + (f"  ({detail})" if detail else ""))
    return ok


# ----------------------------------------------------------------------------
# Jacobian EC arithmetic on secp256k1 (y^2 = x^3 + 7, a=0)
# ----------------------------------------------------------------------------
def _jac_double(X, Y, Z):
    if Y == 0:
        return (1, 1, 0)
    S = 4 * X * Y * Y % p
    M = 3 * X * X % p
    Xp = (M * M - 2 * S) % p
    Yp = (M * (S - Xp) - 8 * Y**4) % p
    Zp = 2 * Y * Z % p
    return (Xp, Yp, Zp)


def _jac_add(X1, Y1, Z1, X2, Y2, Z2):
    if Z1 == 0:
        return (X2, Y2, Z2)
    if Z2 == 0:
        return (X1, Y1, Z1)
    Z1Z1 = Z1 * Z1 % p
    Z2Z2 = Z2 * Z2 % p
    U1 = X1 * Z2Z2 % p
    U2 = X2 * Z1Z1 % p
    S1 = Y1 * Z2 % p * Z2Z2 % p
    S2 = Y2 * Z1 % p * Z1Z1 % p
    if U1 == U2:
        if S1 != S2:
            return (1, 1, 0)
        return _jac_double(X1, Y1, Z1)
    H = (U2 - U1) % p
    r = 2 * (S2 - S1) % p
    I = 4 * H * H % p
    J = H * I % p
    V = U1 * I % p
    Xp = (r * r - J - 2 * V) % p
    Yp = (r * (V - Xp) - 2 * S1 * J) % p
    Zp = ((Z1 + Z2) * (Z1 + Z2) - Z1Z1 - Z2Z2) % p * H % p
    return (Xp, Yp, Zp)


def scalar_mult(k, P):
    """Affine output of [k]P for k >= 1; None for infinity."""
    X, Y = P
    RX, RY, RZ = X, Y, 1
    Q = (1, 1, 0)
    while k:
        if k & 1:
            Q = _jac_add(Q[0], Q[1], Q[2], RX, RY, RZ)
        RX, RY, RZ = _jac_double(RX, RY, RZ)
        k >>= 1
    if Q[2] == 0:
        return None
    zinv = pow(Q[2], p - 2, p)
    zinv2 = zinv * zinv % p
    return (Q[0] * zinv2 % p, Q[1] * zinv2 % p * zinv % p)


def on_curve(x, y):
    return (y * y - x * x * x - 7) % p == 0


# ----------------------------------------------------------------------------
# Cubic character / orbit label
# ----------------------------------------------------------------------------
def cubic_exponent(x):
    """e in {0,1,2} with x^((p-1)/3) == BETA2^e (mod p)."""
    h = pow(x, EXP3, p)
    if h == 1:
        return 0
    if h == BETA2:
        return 1
    if h == BETA1:
        return 2
    raise AssertionError("x^((p-1)/3) not in <beta> -- impossible for x != 0")


def orbit_label(P):
    """Public label (e, j, s): GLV orbit index j = 2e mod 3, sign s = [y > p/2]."""
    x, y = P
    e = cubic_exponent(x)
    j = (2 * e) % 3
    s = 1 if 2 * y > p else 0
    return e, j, s


def canonical_d0(d, j, s):
    """d = (-1)^s * LAM^j * d0 (mod n)  =>  d0 = (-1)^s * LAM^{-j} * d (mod n)."""
    d0 = d * pow(LAM_INV, j, n) % n
    if s:
        d0 = (n - d0) % n
    return d0


# ----------------------------------------------------------------------------
# Eisenstein lift machinery (square Babai domain, u_frac, v_frac in [-1/2, 1/2])
# ----------------------------------------------------------------------------
def lift_uv(X, aa, bb):
    """Exact integer numerators with u_frac = u_num/p, v_frac = v_num/p for the
    lattice basis {(aa,bb), (-bb, aa-bb)} (requires aa^2-aa*bb+bb^2 == p)."""
    ku = (2 * X * (aa - bb) + p) // (2 * p)
    kv = (-2 * X * bb + p) // (2 * p)
    u_num = X * (aa - bb) - ku * p
    v_num = -X * bb - kv * p
    return u_num, v_num


def s_norm(X, aa=A_SP, bb=B_SP):
    u_num, v_num = lift_uv(X, aa, bb)
    return Fraction(u_num * u_num - u_num * v_num + v_num * v_num, p * p)


def s_norm_int(X, aa=A_SP, bb=B_SP):
    u_num, v_num = lift_uv(X, aa, bb)
    return u_num * u_num - u_num * v_num + v_num * v_num  # s * p^2, exact


def z_lift(X, aa, bb, beta):
    u_num, v_num = lift_uv(X, aa, bb)
    ku = (X * (aa - bb) - u_num) // p
    kv = (-X * bb - v_num) // p
    z0 = X - ku * aa + kv * bb
    z1 = -ku * bb - kv * (aa - bb)
    assert (z0 + z1 * beta - X) % p == 0, "lift congruence failed"
    return z0, z1


def s_from_claimed_z(z0, z1, aa=A_SP, bb=B_SP):
    """s computed from a claimed (z0, z1) by the Downloads inverse-map formula."""
    u_tot = Fraction(z0 * (aa - bb) + z1 * bb, p)
    v_tot = Fraction(aa * z1 - z0 * bb, p)
    u = u_tot - round(u_tot)
    v = v_tot - round(v_tot)
    return u, v, u * u - u * v + v * v


# ----------------------------------------------------------------------------
# chi^2 machinery (regularized incomplete gamma, NR-style)
# ----------------------------------------------------------------------------
def _gser(a, x):
    ap, s, d = a, 1.0 / a, 1.0 / a
    for _ in range(1000):
        ap += 1
        d *= x / ap
        s += d
        if abs(d) < abs(s) * 1e-15:  # noqa: float — (stat) Numerical-Recipes series-convergence criterion for the regularized incomplete gamma function (chi2 p-value machinery); inherently transcendental, not a discrete/algebraic decision
            break
    return s * math.exp(-x + a * math.log(x) - math.lgamma(a))


def _gcf(a, x):
    tiny = 1e-300
    b, c, d, h = x + 1 - a, 1 / tiny, 1 / (x + 1 - a), 1 / (x + 1 - a)
    for i in range(1, 1000):
        an = -i * (i - a)
        b += 2
        d = an * d + b
        if abs(d) < tiny:
            d = tiny
        c = b + an / c
        if abs(c) < tiny:
            c = tiny
        d = 1 / d
        de = d * c
        h *= de
        if abs(de - 1.0) < 1e-15:  # noqa: float — (stat) Numerical-Recipes continued-fraction convergence criterion for the regularized incomplete gamma function (chi2 p-value machinery); inherently transcendental, not a discrete/algebraic decision
            break
    t = -x + a * math.log(x) - math.lgamma(a)
    return math.exp(t) * h if t > -700 else 0.0


def chi2_p(stat, dof):
    a, x = dof / 2.0, stat / 2.0
    if x < 0 or a <= 0:
        return 1.0
    if x == 0:
        return 1.0
    return _gser(a, x) if x < a + 1 else _gcf(a, x)


def chi2_indep(rows):
    N = sum(sum(r) for r in rows)
    colt = [sum(r[i] for r in rows) for i in range(len(rows[0]))]
    stat = 0.0
    for r in rows:
        rt = sum(r)
        for i, o in enumerate(r):
            e = rt * colt[i] / N
            stat += (o - e) ** 2 / e
    dof = (len(rows) - 1) * (len(rows[0]) - 1)
    return stat, dof, chi2_p(stat, dof)


def print_table(rows, rowlab, collab, title):
    print(f"\n  {title}")
    width = max(6, max(len(str(l)) for l in collab) + 1)
    print("    " + " " * len(str(rowlab[0])) + "".join(f"{c:>{width}}" for c in collab) + "   | tot")
    for lab, r in zip(rowlab, rows):
        print(f"    {lab:<{len(str(rowlab[0]))}}" + "".join(f"{v:>{width}}" for v in r) + f"   | {sum(r)}")


# ----------------------------------------------------------------------------
def cont_frac(fr, k=15):
    out = []
    fr = abs(fr)
    while len(out) < k:
        w = fr.numerator // fr.denominator
        out.append(w)
        fr -= w
        if fr == 0:
            break
        fr = 1 / fr
    return out


def egyptian(fr):
    out = []
    while fr > 0:
        k = -((-fr.denominator) // fr.numerator)
        out.append(k)
        fr -= Fraction(1, k)
    return out


# ============================================================================
print("=" * 88)
print(" EXACT-PRECISION AUDIT OF THE 'D2 BRIDGE' MOD-6 REDUCTION CLAIM (P135/P140)")
print("=" * 88)

# ----------------------------------------------------------------------------
print("\n[A] RAW ARITHMETIC OF THE CLAIMED CONSTANTS AND LIFTS")
print("-" * 88)
A_fail = 0
A_fail += not check("p % 9 == 7 (so (p-1)/3 = 2 mod 3)", p % 9 == 7, f"p%9={p % 9}, EXP3%3={EXP3 % 3}")
A_fail += not check("beta2^3 = 1, beta1 = beta2^2 (mod p)",
                    pow(BETA2, 3, p) == 1 and BETA1 == pow(BETA2, 2, p) and BETA2 == pow(BETA1, 2, p))
A_fail += not check("lambda^3 = 1 (mod n), lambda != 1", pow(LAM, 3, n) == 1 and LAM % n != 1)
A_fail += not check("a^2 - ab + b^2 == p", A_SP * A_SP - A_SP * B_SP + B_SP * B_SP == p)
A_fail += not check("a + b*beta2 == 0 (mod p)", (A_SP + B_SP * BETA2) % p == 0)
A_fail += not check("(a-b) - b*beta1 == 0 (mod p)  [conjugate ideal]", ((A_SP - B_SP) - B_SP * BETA1) % p == 0)
check("GROUND TRUTH: n % 3 = 1, lambda % 3 = 2  -- the reports' bridge algebra assumed "
      "lambda^j = 1 and n = 2 (mod 3); both are false", True,
      f"n%3={n % 3}, lambda%3={LAM % 3}")
A_fail += not check("chi3(beta2) = beta1  (step of the orbit index under [lambda])",
                    pow(BETA2, EXP3, p) == BETA1)

# GLV pairing
Pl = scalar_mult(LAM, (GX, GY))
pairing = "beta2" if Pl == (BETA2 * GX % p, GY) else ("beta1" if Pl == (BETA1 * GX % p, GY) else "NEITHER")
A_fail += not check("[lambda]G == (beta*x_G, y_G) with beta = " + pairing, pairing != "NEITHER")

A_fail += not check("P135 on curve", on_curve(X135, Y135))
A_fail += not check("P140 on curve", on_curve(X140, Y140))

e135 = cubic_exponent(X135)
e140 = cubic_exponent(X140)
A_fail += not check("claimed cubic exponents: e(x135)=1, e(x140)=0", (e135, e140) == (1, 0),
                    f"computed e135={e135}, e140={e140}")
A_fail += not check("claimed y-side labels: y135<p/2 (s=0), y140>p/2 (s=1)",
                    2 * Y135 < p and 2 * Y140 > p)
A_fail += not check("claimed y LSBs: y135 even, y140 odd", (Y135 & 1, Y140 & 1) == (0, 1))

# Lifts: mine vs claimed
z135_b2 = z_lift(X135, A_SP, B_SP, BETA2)
z135_b1 = z_lift(X135, A_SP - B_SP, -B_SP, BETA1)
z140_b2 = z_lift(X140, A_SP, B_SP, BETA2)
z140_b1 = z_lift(X140, A_SP - B_SP, -B_SP, BETA1)
s135_b2, s135_b1 = s_norm(X135), s_norm(X135, A_SP - B_SP, -B_SP)
s140_b2, s140_b1 = s_norm(X140), s_norm(X140, A_SP - B_SP, -B_SP)

print("\n  Lift cross-check (my square-reduced lifts vs Downloads-claimed z, s):")
for tag, mine, claim, beta, s_mine, s_claim in [
    ("P135 beta2", z135_b2, CLAIM_Z135_F2, BETA2, s135_b2, CLAIM_S135),
    ("P135 beta1", z135_b1, CLAIM_Z135_F1, BETA1, s135_b1, CLAIM_S135),
    ("P140 (their z is a beta1-lift)", z140_b1, CLAIM_Z140, BETA1, s140_b1, CLAIM_S140),
]:
    cong_ok = (claim[0] + claim[1] * beta - (X135 if "135" in tag else X140)) % p == 0
    z_match = mine == claim
    s_claimed_from_z = s_from_claimed_z(claim[0], claim[1])
    s_close = abs(float(s_mine) - s_claim) < 5e-10
    A_fail += not check(f"{tag}: claimed z congruent / z==mine / s matches",
                        cong_ok and s_close, f"z==mine:{z_match}, s={float(s_mine):.12f} "
                        f"(claimed {s_claim:.10f}, from claimed z {float(s_claimed_from_z[2]):.12f})")
check("P140 claimed z also congruent under beta1 (they never say which beta)",
      (CLAIM_Z140[0] + CLAIM_Z140[1] * BETA1 - X140) % p == 0,
      f"under beta1: {(CLAIM_Z140[0] + CLAIM_Z140[1] * BETA1 - X140) % p == 0}, "
      f"under beta2: {(CLAIM_Z140[0] + CLAIM_Z140[1] * BETA2 - X140) % p == 0}")

print(f"\n  s(P135) = {float(s135_b2):.12f} (both roots: {float(s135_b1):.12f} -- conjugate symmetry)")
print(f"  s(P140) = {float(s140_b2):.12f} (both roots: {float(s140_b1):.12f})")
A_fail += not check("conjugate symmetry s_pi = s_pibar holds for both puzzles",
                    s135_b2 == s135_b1 and s140_b2 == s140_b1)
A_fail += not check("both puzzles satisfy s < 3/16 (the 'core gate' values are correct)",
                    float(s135_b2) < 3 / 16 and float(s140_b2) < 3 / 16)

# Farey/Egyptian spot checks
u135_f1 = s_from_claimed_z(CLAIM_Z135_F1[0], CLAIM_Z135_F1[1])[0]
cf_u135 = cont_frac(u135_f1)
A_fail += not check("claimed CF of |u_frac| (P135, formula 1) first 15 terms",
                    cf_u135[:15] == CLAIM_CF135_U, f"{cf_u135[:15]}")
u140 = s_from_claimed_z(CLAIM_Z140[0], CLAIM_Z140[1])[0]
cf_u140 = cont_frac(u140, 20)
A_fail += not check("claimed CF of |u_frac| (P140) first 20 terms",
                    cf_u140[:20] == CLAIM_CF140_U, f"{cf_u140[:20]}")
eg = egyptian(Fraction(17, 61))
A_fail += not check("claimed Egyptian signature 17/61 = [4, 35, 8540]",
                    eg == [4, 35, 8540] and sum(Fraction(1, k) for k in eg) == Fraction(17, 61))

# 'No unit square has 4 coprime corners' -- provable by parity, sweep confirms
bad_squares = 0
for xc in range(1, 101):
    for yc in range(1, 101):
        if all(__import__("math").gcd(a, b) == 1 for a, b in
               [(xc, yc), (xc + 1, yc), (xc, yc + 1), (xc + 1, yc + 1)]):
            bad_squares += 1
A_fail += not check("'no fully-coprime unit square' sweep Q<=100 (parity theorem)", bad_squares == 0,
                    f"counter-squares: {bad_squares}")

print(f"\n  [A] layer result: {'ALL ARITHMETIC CLAIMS VERIFIED' if A_fail == 0 else str(A_fail) + ' FAILURES'}")

# ----------------------------------------------------------------------------
print("\n[B] DISTRIBUTIONAL CONTENT OF THE 'CORE GATE' (s < 3/16)")
print("-" * 88)
M = 50000
cnt_gate = cnt_s135 = cnt_s140 = 0
mx = 0
for _ in range(M):
    X = random.randrange(1, p)
    sv = s_norm_int(X)
    if 16 * sv < 3 * p * p:
        cnt_gate += 1
    if sv < s135_b2.numerator * (p * p) // s135_b2.denominator + 1:
        cnt_s135 += 1
    if sv < s140_b2.numerator * (p * p) // s140_b2.denominator + 1:
        cnt_s140 += 1
    mx = max(mx, sv)
frac_gate = Fraction(3 * p * p, 16)
cdf = lambda s: 2 * math.pi * float(s) / math.sqrt(3)   # exact for s <= 3/16 (inscribed ellipse)
print(f"  Ellipse {{u^2-uv+v^2 <= 3/16}} is tangent to all four sides of the square domain:")
print(f"  s(1/2, 1/4) = 1/4 - 1/8 + 1/16 = 3/16  ==> 'core' = inscribed ellipse.")
print(f"  Exact area fraction  Pr[s < 3/16] = pi*sqrt(3)/8 = {math.pi * math.sqrt(3) / 8:.6f}")
print(f"  Empirical (M={M}): Pr[s < 3/16] = {cnt_gate / M:.6f}")
print(f"  Exact CDF for s <= 3/16: F(s) = 2*pi*s/sqrt(3).")
print(f"  So a UNIFORM RANDOM key passes the 'core gate' {100 * math.pi * math.sqrt(3) / 8:.2f}% of the time.")
print(f"  Percentile of P135's s: F(s135) = {cdf(s135_b2) * 100:.2f}%  (empirical {100 * cnt_s135 / M:.2f}%)")
print(f"  Percentile of P140's s: F(s140) = {cdf(s140_b2) * 100:.2f}%  (empirical {100 * cnt_s140 / M:.2f}%)")
print(f"  Max observed s = {mx / (p * p):.6f}  (sup over square domain = 3/4 = 0.75)")
print("  ==> The 'core gate' is a coarse property of a ~uniform field element, not of the key.")

# ----------------------------------------------------------------------------
print("\n[D] ORBIT LABELS: WHAT IS ACTUALLY REAL (and what it is worth)")
print("-" * 88)
N_ORBIT = 240
label_d3 = [[0] * 3 for _ in range(6)]   # rows: 2*j + s
ok_label = ok_id = 0
their_form_failures = 0
demo_rows = []
for _ in range(N_ORBIT):
    d = random.randrange(2**134, 2**135)
    P = scalar_mult(d, (GX, GY))
    e, j, s = orbit_label(P)
    d0 = canonical_d0(d, j, s)
    P0 = scalar_mult(d0, (GX, GY))
    if cubic_exponent(P0[0]) == 0 and 2 * P0[1] < p:
        ok_label += 1
    # exact integer identity t = (-1)^s * d0 * lambda^j = d + c*n  (t, c may be negative)
    t = (-d0 if s else d0) * LAM**j
    c = (t - d) // n
    # corrected mod-3 identity (folding the true lambda = 2, n = 1 mod 3):
    corrected_ok = t == d + c * n and (d - ((-1) ** s * (2 ** j) * d0 - c * n)) % 3 == 0
    if corrected_ok:
        ok_id += 1
    # THEIR stated form (implicitly lambda^j = 1 mod 3):
    if (d - ((-1) ** s * d0 - c * n)) % 3 != 0:
        their_form_failures += 1
        assert j == 1 and d0 % 3 != 0, "their-form failure outside the predicted j=1, d0%3!=0 class"
    label_d3[2 * j + s][d % 3] += 1
    demo_rows.append((d, j, s, d % 3, d0 % 3, c % 3))
check("orbit label (j, s) extraction from public data only: consistent on all mocks",
      ok_label == N_ORBIT, f"{ok_label}/{N_ORBIT}")
check("bridge congruence holds as an IDENTITY (with the corrected lambda=2 folding) "
      "when d0, c are computed FROM d", ok_id == N_ORBIT, f"{ok_id}/{N_ORBIT}")
print(f"  THEIR stated form 'd = (-1)^s d0 - c*n (mod 3)' (lambda^j treated as 1): "
      f"fails {their_form_failures}/{N_ORBIT} = {100 * their_form_failures / N_ORBIT:.1f}% of keys "
      f"(exactly the j=1, d0 mod 3 != 0 class); it is not even a valid identity.")
print("\n  Contingency: orbit label (j,s) x d mod 3  (does the public label pin d mod 3?):")
print_table(label_d3, [f"j={r // 2},s={r % 2}" for r in range(6)], ["d%3=0", "d%3=1", "d%3=2"],
            f"(mock keys, N={N_ORBIT})")
st, dof, pv = chi2_indep(label_d3)
print(f"  chi^2 = {st:.2f} on {dof} dof, p-value = {pv:.4f}  (consistent with independence)")
print("  Only d itself satisfies [d]G = P (prime order n); the five other orbit scalars")
print("  generate the DISTINCT conjugate pubkeys (beta^k x, +/-y). Each of the six")
print("  determines the others by public multiplication by lambda^(+-k) mod n, so any")
print("  one is equivalent knowledge -- but the label (j,s) is a function of P alone,")
print("  statistically independent of d mod 3/6 (tables above), with no exact public")
print("  anchor (every congruence factors through the unknown d0). ZERO bits.")

# ----------------------------------------------------------------------------
print("\n[C3] THEIR SANDBOX 'VERIFICATION': TAUTOLOGY CHECK")
print("-" * 88)
dm = CLAIM_MOCK_D
Pm = scalar_mult(dm, (GX, GY))
em, jm, sm = orbit_label(Pm)
d0m = canonical_d0(dm, jm, sm)
cm = ((-1) ** sm * d0m * LAM**jm - dm) // n
print(f"  Their mock d = {dm}")
print(f"  Recomputed: x = 0x{Pm[0]:064x}")
print(f"  exponent={em} (they claim 0), j={jm}, s={sm}; d0={d0m}, c={cm}")
check("their mock is the degenerate case d0 == d, c == 0 (so the check is d%d == d%d)",
      d0m == dm and cm == 0)
print("  Non-degenerate example (c != 0, d0 != d): the law still 'passes' -- because d0, c")
print("  were computed FROM d. Public data gives neither d0 mod 3 nor c mod 3:")
for d, j, s, d3, d03, c3 in [r for r in demo_rows if r[5] != 0][:4]:
    print(f"    d=...{str(d)[-12:]}: label(j={j},s={s}), d%3={d3}, d0%3={d03}, c%3={c3}"
          f"  -> RHS = ((-1)^s d0 - c n)%3 needs d0")

# P140's celebrated collapse, made explicit:
print("\n  P140 case (j=0, s=1): the 'bridge' says d = -d0 + n exactly, i.e. d + d0 = n.")
print(f"  Ground truth: n mod 3 = {n % 3}, so d = -d0 + 1 (mod 3). Their headline line")
print("  'd_140 = -d0 + 2 (mod 3)' is an arithmetic error (they took n = 2 mod 3).")
print("  Even corrected, it determines d mod 3 exactly as well as knowing d0 mod 3,")
print("  i.e. not at all without the DLP.")

# ----------------------------------------------------------------------------
print("\n[C1/C2] THE INFORMATION CLAIMS: EMPIRICAL INDEPENDENCE TESTS")
print("-" * 88)
N_MAIN = int(sys.argv[1]) if len(sys.argv) > 1 else 8000
tab_e_d3 = [[0] * 3 for _ in range(3)]        # e(x) x d%3
tab_ylsb_d2 = [[0] * 2 for _ in range(2)]     # y LSB x d%2      <-- their mod-2 law
tab_yhalf_d2 = [[0] * 2 for _ in range(2)]    # y>p/2 x d%2
tab_gate_d3 = [[0] * 3 for _ in range(2)]     # core-gate x d%3  <-- their epsilon bridge
tab_lab6_d6 = [[0] * 6 for _ in range(12)]    # (j,s,ylsb) x d%6 <-- their composite mod-6
counterex = []
for _ in range(N_MAIN):
    d = random.randrange(2**134, 2**135)
    xP, yP = scalar_mult(d, (GX, GY))
    e = cubic_exponent(xP)
    j = (2 * e) % 3
    s = 1 if 2 * yP > p else 0
    ylsb = yP & 1
    core = 16 * s_norm_int(xP) < 3 * p * p
    tab_e_d3[e][d % 3] += 1
    tab_ylsb_d2[ylsb][d % 2] += 1
    tab_yhalf_d2[s][d % 2] += 1
    tab_gate_d3[1 if core else 0][d % 3] += 1
    tab_lab6_d6[4 * j + 2 * s + ylsb][d % 6] += 1
    if ylsb != d % 2 and len(counterex) < 5:
        counterex.append((d, d % 2, ylsb))

print(f"  Samples: {N_MAIN} uniform d in [2^134, 2^135)  (puzzle keyspace), seeded.\n")
print_table(tab_e_d3, ["e=0", "e=1", "e=2"], ["d%3=0", "d%3=1", "d%3=2"], "T1: cubic character e(x) x d mod 3")
st, dof, pv = chi2_indep(tab_e_d3)
print(f"  chi^2 = {st:.2f} on {dof} dof, p = {pv:.4f}")

print_table(tab_ylsb_d2, ["y even", "y odd"], ["d even", "d odd"], "T2: y LSB x d mod 2  (their claimed law)")
agree = tab_ylsb_d2[0][0] + tab_ylsb_d2[1][1]
st, dof, pv = chi2_indep(tab_ylsb_d2)
print(f"  chi^2 = {st:.2f} on {dof} dof, p = {pv:.3g}")
print(f"  Their law 'y LSB = d mod 2' predicts {N_MAIN} agreements; observed {agree} "
      f"({100 * agree / N_MAIN:.2f}% -- a coin flip).")

print_table(tab_yhalf_d2, ["y<p/2", "y>p/2"], ["d even", "d odd"], "T3: y vs p/2 x d mod 2")
st, dof, pv = chi2_indep(tab_yhalf_d2)
print(f"  chi^2 = {st:.2f} on {dof} dof, p = {pv:.4f}")

print_table(tab_gate_d3, ["core", "outer"], ["d%3=0", "d%3=1", "d%3=2"],
            "T4: 'core gate' epsilon-bridge x d mod 3")
st, dof, pv = chi2_indep(tab_gate_d3)
print(f"  chi^2 = {st:.2f} on {dof} dof, p = {pv:.4f}")

st, dof, pv = chi2_indep(tab_lab6_d6)
print(f"\n  T5: full composite label (j, s, y LSB) [12 classes] x d mod 6:")
print(f"  chi^2 = {st:.2f} on {dof} dof, p = {pv:.4f}  (no dependence)")

print("\n  Explicit counterexamples to 'y LSB = d mod 2' (d, d%2, y%2):")
for d, d2, y2 in counterex:
    print(f"    d = {d}   d%2 = {d2}, y%2 = {y2}")

# negation consistency (why one mock cannot refute their mod-2 law)
d = counterex[0][0]
P = scalar_mult(d, (GX, GY))
Pneg = scalar_mult(n - d, (GX, GY))
print("\n  Negation consistency (why their single-sample 'verification' was meaningless):")
print(f"    p odd  => y and p-y have opposite LSB; n odd => d and n-d have opposite parity.")
print(f"    Check: y LSB {P[1] & 1} vs {Pneg[1] & 1}; d%2 {d % 2} vs {(n - d) % 2}. "
      f"Law is negation-closed, so a consistent pair proves nothing; T2 kills it.")

# ----------------------------------------------------------------------------
print("\n" + "=" * 88)
print(" VERDICT SUMMARY")
print("=" * 88)
print("""  [A] Arithmetic layer: constants, splits, lifts, norms, characters, CF and
      Egyptian values all check out EXCEPT two bridge-algebra errors:
      n = 1 (not 2) mod 3, lambda = 2 (not 1) mod 3 -- so their P140 residue
      '-d0 + 2' is wrong (correct: '-d0 + 1') and their stated congruence form
      fails on all j=1 keys (~22% of the keyspace) even as an identity.
  [B] The 'core gate' s < 3/16 is a true PUBLIC statement about x; it holds for
      pi*sqrt(3)/8 ~= 68.02% of uniform random keys. It says nothing about d.
  [C1] The mod-3 'bridge' (corrected) is an identity in the UNKNOWN d0 (for P140
      literally d = n - d0). It extracts nothing: d0 mod 3 is as hard as d itself.
  [C2] 'y LSB = d mod 2' is FALSE (agreement = coin flip; counterexamples above).
  [C3] Their sandbox verification is the degenerate case d0 = d, c = 0, i.e. it
      verifies d % 3 == d % 3 -- and its c*n = 0 term hid the n mod 3 error.
  Net key information extracted: 0 bits. Net keyspace/work reduction: none.""")
