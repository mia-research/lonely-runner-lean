#!/usr/bin/env python3
"""
First-hand re-verification of three ideation-agent claims (2026-08-21 session).

Grounding docs:
  - CLAIM 8 (Silverman-Stange amicable pair)  <- RESULT_secp_amicable_pair_v1.md [P24]
  - CLAIM 9 (Core Gate s<3/16 kills the carry) <- CONFIRMED_core_gate_carry_epsilon_zero_v3.md,
                                                  RESULT_eps_to_d_constraint_v1.md [N16]
  - CLAIM 2 (k=3 phase channel, p mod 4 split) <- CONFIRMED_k3_phase_channel_weierstrass_v1.md [M24/M4]

Exact integer arithmetic everywhere it touches field/curve data (project rule). Floats appear
only in Part D's Fourier phases, where the statistic itself is complex-analytic (same
instrument class as the repo's own k3 sweeps).
"""
import cmath, math, random, sys
from fractions import Fraction

random.seed(20260821)

# ---------------- shared: Jacobian EC over F_p, y^2 = x^3 + b (a = 0) ----------------

def jac_double(P, p, b):
    if P is None:
        return None
    X, Y, Z = P
    if Y == 0:
        return None
    YY = (Y * Y) % p
    S = (4 * X * YY) % p
    M = (3 * X * X) % p
    X3 = (M * M - 2 * S) % p
    Y3 = (M * (S - X3) - 8 * YY * YY) % p
    Z3 = (2 * Y * Z) % p
    return (X3, Y3, Z3)

def jac_add(P, Q, p, b):
    if P is None: return Q
    if Q is None: return P
    X1, Y1, Z1 = P; X2, Y2, Z2 = Q
    Z1Z1 = (Z1 * Z1) % p; Z2Z2 = (Z2 * Z2) % p
    U1 = (X1 * Z2Z2) % p; U2 = (X2 * Z1Z1) % p
    S1 = (Y1 * Z2 % p) * Z2Z2 % p; S2 = (Y2 * Z1 % p) * Z1Z1 % p
    H = (U2 - U1) % p
    r = (S2 - S1) % p
    if H == 0:
        if r == 0:
            return jac_double(P, p, b)
        return None
    HH = (H * H) % p; HHH = (H * HH) % p
    V = (U1 * HH) % p
    X3 = (r * r - HHH - 2 * V) % p
    Y3 = (r * (V - X3) - S1 * HHH) % p
    Z3 = Z1 * Z2 % p * H % p
    return (X3, Y3, Z3)

def jac_mul(k, P, p, b):
    R = None
    while k:
        if k & 1:
            R = jac_add(R, P, p, b)
        P = jac_double(P, p, b)
        k >>= 1
    return R

def to_affine(P, p):
    if P is None:
        return None
    X, Y, Z = P
    zi = pow(Z, p - 2, p)
    zi2 = zi * zi % p
    return (X * zi2 % p, Y * zi2 % zi % p)

def tonelli(a, p):
    # sqrt of a mod p (p odd prime), or None if non-residue
    a %= p
    if a == 0: return 0
    if pow(a, (p - 1) // 2, p) == p - 1:
        return None
    if p % 4 == 3:
        x = pow(a, (p + 1) // 4, p)
        return x if x * x % p == a else None
    q, s = p - 1, 0
    while q % 2 == 0:
        q //= 2; s += 1
    z = 2
    while pow(z, (p - 1) // 2, p) != p - 1:
        z += 1
    m, c, t, r = s, pow(z, q, p), pow(a, q, p), pow(a, (q + 1) // 2, p)
    while t != 1:
        i, t2 = 0, t
        while t2 != 1:
            t2 = t2 * t2 % p; i += 1
        b = pow(c, 1 << (m - i - 1), p)
        m, c = i, b * b % p
        t = t * c % p; r = r * b % p
    return r if r * r % p == a else None

def count_points(b, p):
    cnt = 1  # infinity
    for x in range(p):
        if tonelli((x * x * x + b) % p, p) is not None:
            y = tonelli((x * x * x + b) % p, p)
            cnt += 1 if y == 0 else 2
    return cnt

def is_probable_prime(m, rounds=40):
    if m < 2: return False
    for sp in (2,3,5,7,11,13,17,19,23,29,31,37):
        if m % sp == 0: return m == sp
    d, s = m - 1, 0
    while d % 2 == 0: d //= 2; s += 1
    for _ in range(rounds):
        a = random.randrange(2, m - 1)
        x = pow(a, d, m)
        if x in (1, m - 1): continue
        for _ in range(s - 1):
            x = x * x % m
            if x == m - 1: break
        else:
            return False
    return True

# ---------------- shared: square-centered Eisenstein lift (exact integers) ----------------
# Coset rep (U,V) in Z^2 with U + w0*V = x (mod p), chosen square-centered.
# s = (U^2-UV+V^2)/p as an exact Fraction; flap eps = 0 iff 4(U-V)^2 <= p.

def qform(U, V): return U * U - U * V + V * V
def ip2(u, v): return 2*u[0]*v[0] - u[0]*v[1] - u[1]*v[0] + 2*u[1]*v[1]

def gauss_reduce_q(b1, b2):
    while True:
        if qform(*b2) < qform(*b1):
            b1, b2 = b2, b1
        num, den = ip2(b1, b2), 2 * qform(*b1)
        mu = (2 * num + den) // (2 * den)
        if mu == 0:
            return b1, b2
        b2 = (b2[0] - mu * b1[0], b2[1] - mu * b1[1])

def cube_root_of_unity_mod(p):
    for c in range(2, 1000):
        w = pow(c, (p - 1) // 3, p)
        if w != 1:
            assert pow(w, 3, p) == 1
            return w
    raise RuntimeError

class EisensteinLift:
    def __init__(self, p):
        self.p = p
        self.w0 = cube_root_of_unity_mod(p)   # coordinate-side cube root (x -> w0*x)
        v1 = (p, 0)
        v2 = ((-self.w0) % p, 1)
        self.b1, self.b2 = gauss_reduce_q(v1, v2)
        assert (self.b1[0] + self.w0 * self.b1[1]) % p == 0
        assert (self.b2[0] + self.w0 * self.b2[1]) % p == 0

    def lift(self, x):
        p = self.p
        det = self.b1[0] * self.b2[1] - self.b2[0] * self.b1[1]
        c1 = Fraction(x * self.b2[1], det)
        c2 = Fraction(-x * self.b1[1], det)
        r1, r2 = round(c1), round(c2)
        best = None
        for d1 in range(-2, 3):
            for d2 in range(-2, 3):
                a1, a2 = r1 + d1, r2 + d2
                U = x - a1 * self.b1[0] - a2 * self.b2[0]
                V = - a1 * self.b1[1] - a2 * self.b2[1]
                key = (max(abs(U), abs(V)), qform(U, V))
                if best is None or key < best[0]:
                    best = (key, U, V)
        _, U, V = best
        assert (U + self.w0 * V - x) % p == 0
        return U, V

    @staticmethod
    def gate_and_flap(U, V, p):
        s_num = qform(U, V)               # s = s_num / p
        inside_gate = 16 * s_num < 3 * p  # s < 3/16
        eps_zero = 4 * (U - V) ** 2 <= p  # |u-v| <= 1/2
        return inside_gate, eps_zero, Fraction(s_num, p)

# ========================================================================
print("=" * 78)
print("PART A - CLAIM 8: secp256k1 Silverman-Stange amicable pair (exact ints)")
print("=" * 78)

p_secp = 2**256 - 2**32 - 977
n_secp = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141
assert is_probable_prime(p_secp) and is_probable_prime(n_secp)

def hasse_window_excludes_2x(m_prime, order_claim, field):
    # if order_claim | #E and one point of order order_claim exists, then
    # #E = k*order_claim; show only k=1 fits [field+1-2r, field+1+2r]
    import math as _m
    r2 = _m.isqrt(field)            # r2 = floor(sqrt(field)); 2*sqrt >= 2*r2
    lo_other = 2 * order_claim - (field + 1)
    # need 2*order_claim > field+1+2*sqrt(field): check 2*order_claim-(field+1) > 0 and its square > 4*field
    ok = lo_other > 0 and lo_other * lo_other > 4 * field
    claim_in_window = abs(field + 1 - order_claim) ** 2 <= 4 * field
    return ok, claim_in_window

def verify_order_pair(field, b, claimed, n_points=5, label=""):
    pts = []
    trials = 0
    while len(pts) < n_points and trials < 4000:
        trials += 1
        x = random.randrange(field)
        y = tonelli((x * x * x + b) % field, field)
        if y:
            pts.append((x, y))
    results = []
    for (x, y) in pts:
        P = (x, y, 1)
        Q = jac_mul(claimed, P, field, b)
        results.append(Q is None)   # [claimed]P = O
    k2_excluded, claim_in_window = hasse_window_excludes_2x(field, claimed, field)
    print(f"[{label}] field={str(field)[:18]}...  claimed order | #E: "
          f"{sum(results)}/{len(results)} points satisfy [claimed]P = O")
    print(f"[{label}] claimed order inside Hasse window: {claim_in_window}; "
          f"2x claimed order excluded from window: {k2_excluded}")
    return all(results) and k2_excluded and claim_in_window

ok_p = verify_order_pair(p_secp, 7, n_secp, label="E/F_p, #E(F_p) =?= n_secp")
ok_n = verify_order_pair(n_secp, 7, p_secp, label="E/F_n, #E(F_n) =?= p_secp")
t_pn = p_secp + 1 - n_secp
print(f"trace of E/F_n if #E=p: t = n+1-p = {-t_pn}, |t|^2 <= 4n: {t_pn**2 <= 4*n_secp}")
print(f"VERDICT A: amicable pair CONFIRMED first-hand: {ok_p and ok_n}")

# ========================================================================
print()
print("=" * 78)
print("PART B - CLAIM 9 (proved half): on secp, s<3/16 => coordinate-flap eps = 0")
print("=" * 78)

# B1: pure geometry of the unit torus (the v3 doc's "2M random lifts", exact ints)
N = 200_000
SCALE = 1 << 40           # represent u = a / SCALE with a integer in [-SCALE/2, SCALE/2]
half = SCALE // 2
n_eps0 = n_gate = n_viol = 0
max_s_at_eps0 = Fraction(0)
for _ in range(N):
    a = random.randrange(-half, half + 1)
    c = random.randrange(-half, half + 1)
    s_num = a * a - a * c + c * c          # s*SCALE^2
    inside = 16 * s_num < 3 * SCALE * SCALE
    eps0 = 4 * (a - c) ** 2 <= SCALE * SCALE
    n_eps0 += eps0; n_gate += inside; n_viol += (inside and not eps0)
    if eps0:
        max_s_at_eps0 = max(max_s_at_eps0, Fraction(s_num, SCALE * SCALE))
print(f"[B1 random torus, N={N}]  Pr[eps=0] = {n_eps0/N:.5f} (doc: 0.75)   "
      f"Pr[s<3/16] = {n_gate/N:.5f} (doc: 0.6802)")
print(f"[B1] gate violations (s<3/16 and eps>=1): {n_viol} (theorem: 0)")
print(f"[B1] max s on eps=0 locus: {float(max_s_at_eps0):.5f} (doc: 0.2496 <= 1/4)")

# B2: actual secp x-coordinates of random points [d]G
Gx = 0x79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798
Gy = 0x483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8
G = (Gx, Gy, 1)
L = EisensteinLift(p_secp)
N2 = 2000
n_eps0 = n_gate = n_viol = 0
maxab = 0
for i in range(N2):
    d = random.randrange(1, n_secp)
    X = to_affine(jac_mul(d, G, p_secp, 7), p_secp)[0]
    U, V = L.lift(X)
    inside, eps0, _ = EisensteinLift.gate_and_flap(U, V, p_secp)
    n_eps0 += eps0; n_gate += inside; n_viol += (inside and not eps0)
    maxab = max(maxab, abs(U), abs(V))
import math as _m
print(f"[B2 secp x(dG), N={N2}]  Pr[eps=0] = {n_eps0/N2:.4f}   Pr[s<3/16] = {n_gate/N2:.4f}")
print(f"[B2] gate violations on REAL x-coordinates: {n_viol} (must be 0)")
print(f"[B2] lift quality: max|U|,|V| = {maxab} = {maxab/_m.sqrt(p_secp):.3f}*sqrt(p)")

# ========================================================================
print()
print("=" * 78)
print("PART C - CLAIM 9 (refuted half): s<3/16 does NOT gate the scalar carry (p=547)")
print("=" * 78)

pc = 547
bc = 7
cnt = count_points(bc, pc)
print(f"#E(y^2=x^3+7, F_547) = {cnt} (doc: m=547)")
assert cnt == 547
m = cnt
# generator: any non-identity point (prime order)
Gc = None
for x in range(pc):
    y = tonelli((x * x * x + bc) % pc, pc)
    if y:
        Gc = (x, y, 1); break
# GLV eigenvalue: cube root of unity mod m (group order), m prime
lam = None
for h in range(2, 100):
    w = pow(h, (m - 1) // 3, m)
    if w != 1:
        lam = w; break
assert pow(lam, 3, m) == 1 and lam != 1
Lc = EisensteinLift(pc)
print(f"lambda (GLV scalar eigenvalue mod m={m}) = {lam}; w0 (coordinate) = {Lc.w0}")

NC = 5000
viol = []
flap_viol = 0
gated = 0
for i in range(NC):
    d1 = random.randrange(1, m)
    d2 = random.randrange(1, m)
    j = random.randrange(3)
    r1 = d1 % m
    r2 = (d2 * pow(lam, j, m)) % m
    eps_carry = 1 if r1 + r2 >= m else 0        # the d-containing LBE carry
    R = (r1 + r2) % m
    if R == 0:
        continue  # point at infinity: no x-coordinate; ~1/m of draws
    X = to_affine(jac_mul(R, Gc, pc, bc), pc)[0]
    U, V = Lc.lift(X)
    inside, eps0, s = EisensteinLift.gate_and_flap(U, V, pc)
    if inside:
        gated += 1
        if not eps0:
            flap_viol += 1
        if eps_carry == 1:
            viol.append((d1, d2, j, X, float(s)))
print(f"[C] N={NC} draws: gated (s<3/16) = {gated}; flap violations inside gate = {flap_viol} (0)")
print(f"[C] CARRY violations inside gate (s<3/16 and eps_carry=1): {len(viol)} "
      f"(doc RESULT_eps_to_d: 21-93 per cell; ideation claim says 'guaranteed 0')")
for (d1, d2, j, X, s) in viol[:5]:
    print(f"     example: d1={d1} d2={d2} j={j} x={X} s={s:.4f} eps_carry=1")

# ========================================================================
print()
print("=" * 78)
print("PART D - CLAIM 2: k=3 phase channel + the p mod 4 real/imaginary dichotomy")
print("=" * 78)

def phase_channel(p, b, a0=1, tag=""):
    cnt = count_points(b, p)
    if not is_probable_prime(cnt):
        print(f"[{tag}] p={p}: #E={cnt} not prime - skipped"); return None
    n = cnt
    Gp = None
    for x in range(p):
        y = tonelli((x * x * x + b) % p, p)
        if y:
            Gp = (x, y, 1); break
    xs = [None] * n
    for d in range(1, n):
        A = to_affine(jac_mul(d, Gp, p, b), p)
        xs[d] = A[0]
    # T(a0,b) = sum_d exp(2pi i (b x_d)/p) * exp(2pi i (a0 d)/n)
    def E(q_, x_): return cmath.exp(2j * cmath.pi * (x_ % q_) / q_)
    T = [0j] + [sum(E(p, bpar * xs[d]) * E(n, a0 * d) for d in range(1, n))
                for bpar in range(1, p)]
    max_parity_res = max(abs(T[p - bp] - T[bp].conjugate()) for bp in range(1, p))
    chi2 = [0] * p
    for bp in range(1, p):
        chi2[bp] = 1 if pow(bp, (p - 1) // 2, p) == 1 else -1
    ph = [0j] + [cmath.exp(3j * cmath.phase(T[bp])) for bp in range(1, p)]
    R = abs(sum(chi2[bp] * ph[bp] for bp in range(1, p)) / (p - 1))
    meanQR = sum(ph[bp] for bp in range(1, p) if chi2[bp] == 1) / ((p - 1) // 2)
    meanall = sum(ph[bp] for bp in range(1, p)) / (p - 1)
    chan = sum(chi2[bp] * ph[bp] for bp in range(1, p)) / (p - 1)
    print(f"[{tag}] p={p} (p mod 4 = {p%4})  n={n}  a0={a0}")
    print(f"   R = {R:.4f}   (doc CM p=547: 0.289; CM p=43: 0.441)")
    print(f"   parity residual max|T(-b)-conj T(b)| = {max_parity_res:.2e}")
    print(f"   mean_QR = {meanQR.real:+.4f} {meanQR.imag:+.4f}i   "
          f"(lemma: Im=0 forced at p=1 mod 4)")
    print(f"   mean_all = {meanall.real:+.4f} {meanall.imag:+.4f}i   (real at p=3 mod 4)")
    print(f"   chi2-weighted channel = {chan.real:+.4f} {chan.imag:+.4f}i   "
          f"(imag at p=3 mod 4, real at p=1 mod 4)")
    return R

phase_channel(547, 7, 1, "CM x^3+7 p=547")
phase_channel(43, 7, 1, "CM x^3+7 p=43")

# non-CM curve needs a=1: y^2 = x^3 + x + 3 -- our Jac code has a=0 only; do affine for p=43
def affine_points_general(p, A, B):
    pts = [None]
    for x in range(p):
        rhs = (x * x * x + A * x + B) % p
        y = tonelli(rhs, p)
        if y:
            pts.append((x, y))
            if y != 0:
                pts.append((x, p - y))
    return pts

def phase_channel_a1(p, A, B, a0=1, tag=""):
    cnt = 1 + sum(2 if tonelli((x*x*x+A*x+B)%p, p) not in (None,0) else (1 if tonelli((x*x*x+A*x+B)%p,p)==0 else 0) for x in range(p))
    if not is_probable_prime(cnt):
        print(f"[{tag}] p={p}: #E={cnt} not prime - skipped"); return
    n = cnt
    Gp = None
    for x in range(p):
        y = tonelli((x * x * x + A * x + B) % p, p)
        if y: Gp = (x, y); break
    def add(P, Q):
        if P is None: return Q
        if Q is None: return P
        (x1, y1), (x2, y2) = P, Q
        if x1 == x2 and (y1 + y2) % p == 0: return None
        if P == Q:
            mm = (3 * x1 * x1 + A) * pow(2 * y1, p - 2, p) % p
        else:
            mm = (y2 - y1) * pow(x2 - x1, p - 2, p) % p
        x3 = (mm * mm - x1 - x2) % p
        return (x3, (mm * (x1 - x3) - y1) % p)
    def mul(k, P):
        R = None
        while k:
            if k & 1: R = add(R, P)
            P = add(P, P); k >>= 1
        return R
    xs = [None] * n
    for d in range(1, n):
        xs[d] = mul(d, Gp)[0]
    def E(q_, x_): return cmath.exp(2j * cmath.pi * (x_ % q_) / q_)
    T = [0j] + [sum(E(p, bp * xs[d]) * E(n, a0 * d) for d in range(1, n))
                for bp in range(1, p)]
    chi2 = [0] * p
    for bp in range(1, p):
        chi2[bp] = 1 if pow(bp, (p - 1) // 2, p) == 1 else -1
    ph = [0j] + [cmath.exp(3j * cmath.phase(T[bp])) for bp in range(1, p)]
    R = abs(sum(chi2[bp] * ph[bp] for bp in range(1, p)) / (p - 1))
    meanQR = sum(ph[bp] for bp in range(1, p) if chi2[bp] == 1) / ((p - 1) // 2)
    chan = sum(chi2[bp] * ph[bp] for bp in range(1, p)) / (p - 1)
    print(f"[{tag}] p={p} (p mod 4 = {p%4})  n={n}  R = {R:.4f}  mean_QR = "
          f"{meanQR.real:+.4f} {meanQR.imag:+.4f}i  chan = {chan.real:+.4f} {chan.imag:+.4f}i")

phase_channel_a1(43, 1, 3, 1, "non-CM x^3+x+3 p=43 (doc: R=0.336, n=47)")

# a p = 1 mod 4 prime-order CM example, to see the dichotomy flip
found = False
for p1m4 in [13, 37, 61, 73, 97, 109, 157, 181, 193, 229, 241, 277, 313, 337, 349,
             373, 397, 409, 421, 433, 457, 541, 601, 613, 661, 673, 709, 733, 757, 769]:
    if p1m4 % 12 != 1:
        continue
    c = count_points(7, p1m4)
    if is_probable_prime(c) and c > 20:
        phase_channel(p1m4, 7, 1, f"CM x^3+7 p={p1m4} [p=1 mod 4 arm]")
        found = True
        break
if not found:
    print("no small p=1 mod 12 prime-order CM x^3+7 curve found in scan range")

print()
print("DONE.")
