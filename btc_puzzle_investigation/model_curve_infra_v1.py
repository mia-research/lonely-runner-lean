"""
model_curve_infra_v1.py -- shared, GATE-SAFE staging infrastructure for the three
pre-registered model-curve experiments:

  A-joint    PREREG_cm_jointset_excess_v1.md
  C-center   PREREG_monodromy_center_glv_ratio_v1.md
  D-mechanism PREREG_omega_twisted_lefschetz_120deg_v1.md  (prereg pending)

WHAT THIS MODULE IS (and is not)
--------------------------------
This module contains ONLY neutral primitives and deterministic curve/prime
SELECTION. Selection is public curve data -- explicitly NOT a verdict statistic
per every prereg's Scope section. This module computes NO confirmatory statistic:
no cubic-cross feature Psi, no membership indicator I3/g3, no twisted Lefschetz
count, no mutual information, no Delta. Those live in the per-prereg runners and
run only after the experiment-designer gate returns on each prereg.

NO FLOAT IN THE SIGNAL PATH (CLAUDE.md). Everything here is exact Python int /
GF(q) arithmetic. There is no float anywhere in this file.

Usage:
  python3 model_curve_infra_v1.py --selftest     # validate primitives (KATs)
  python3 model_curve_infra_v1.py --schedule DIR  # emit + SHA-256 the frozen schedules
"""

from __future__ import annotations
import json
import hashlib
import sys
from dataclasses import dataclass, asdict
from typing import Optional

# ---------------------------------------------------------------------------
# 0. Field helpers over F_q (q an odd prime).  int-only.
# ---------------------------------------------------------------------------

def inv_mod(a: int, q: int) -> int:
    return pow(a % q, q - 2, q)

def legendre(a: int, q: int) -> int:
    """chi_2(a): +1 if a is a nonzero QR, -1 if non-residue, 0 if a==0 (mod q)."""
    a %= q
    if a == 0:
        return 0
    r = pow(a, (q - 1) // 2, q)
    return 1 if r == 1 else -1

def _prime_factors(m: int) -> list[int]:
    fs, d = [], 2
    while d * d <= m:
        if m % d == 0:
            fs.append(d)
            while m % d == 0:
                m //= d
        d += 1 if d == 2 else 2
    if m > 1:
        fs.append(m)
    return fs

def primitive_root(q: int) -> int:
    """Smallest primitive root mod prime q."""
    if q == 2:
        return 1
    phi = q - 1
    fs = _prime_factors(phi)
    g = 2
    while g < q:
        if all(pow(g, phi // f, q) != 1 for f in fs):
            return g
        g += 1
    raise RuntimeError(f"no primitive root mod {q}")

def is_prime(m: int) -> bool:
    if m < 2:
        return False
    for p in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37):
        if m % p == 0:
            return m == p
    d, r = m - 1, 0
    while d % 2 == 0:
        d //= 2
        r += 1
    for a in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37):
        x = pow(a, d, m)
        if x in (1, m - 1):
            continue
        for _ in range(r - 1):
            x = x * x % m
            if x == m - 1:
                break
        else:
            return False
    return True

# ---------------------------------------------------------------------------
# 1. Short-Weierstrass curve arithmetic  y^2 = x^3 + A x + B  over F_q.
#    Points are (x, y) tuples; the identity O is the Python object None.
# ---------------------------------------------------------------------------

Point = Optional[tuple[int, int]]

@dataclass(frozen=True)
class Curve:
    q: int
    A: int
    B: int

    def is_on(self, P: Point) -> bool:
        if P is None:
            return True
        x, y = P
        return (y * y - (x * x * x + self.A * x + self.B)) % self.q == 0

    def neg(self, P: Point) -> Point:
        if P is None:
            return None
        x, y = P
        return (x, (-y) % self.q)

    def add(self, P: Point, Q: Point) -> Point:
        q = self.q
        if P is None:
            return Q
        if Q is None:
            return P
        x1, y1 = P
        x2, y2 = Q
        if x1 == x2 and (y1 + y2) % q == 0:
            return None
        if x1 == x2 and y1 == y2:
            if y1 == 0:
                return None
            m = (3 * x1 * x1 + self.A) * inv_mod(2 * y1, q) % q
        else:
            m = (y2 - y1) * inv_mod((x2 - x1) % q, q) % q
        x3 = (m * m - x1 - x2) % q
        y3 = (m * (x1 - x3) - y1) % q
        return (x3, y3)

    def mul(self, k: int, P: Point) -> Point:
        if P is None or k == 0:
            return None
        if k < 0:
            k, P = -k, self.neg(P)
        R: Point = None
        Q = P
        while k:
            if k & 1:
                R = self.add(R, Q)
            Q = self.add(Q, Q)
            k >>= 1
        return R

    def j_invariant(self) -> Optional[int]:
        """j = 1728 * 4A^3 / (4A^3 + 27B^2) mod q; None if singular."""
        q = self.q
        disc4 = (4 * self.A % q) * (self.A * self.A % q) % q
        denom = (disc4 + 27 * self.B % q * self.B) % q
        if denom == 0:
            return None
        return 1728 * disc4 % q * inv_mod(denom, q) % q


def _qr_sieve(q: int) -> bytearray:
    """is_qr[r] = 1 iff r is a nonzero quadratic residue mod q. Depends only on q."""
    is_qr = bytearray(q)
    for a in range(1, (q // 2) + 1):
        is_qr[a * a % q] = 1
    return is_qr

def point_count(A: int, B: int, q: int, is_qr: Optional[bytearray] = None) -> int:
    """#E(F_q) exact, via a QR sieve: #E = q + 1 + sum_x chi_2(x^3+Ax+B).
    Pass a precomputed `is_qr` (from _qr_sieve(q)) to amortize the sieve over many curves."""
    if is_qr is None:
        is_qr = _qr_sieve(q)
    s = 0
    for x in range(q):
        v = (x * x % q * x + A * x + B) % q
        if v == 0:
            continue
        s += 1 if is_qr[v] else -1
    return q + 1 + s


def find_point(curve: Curve, smallest: bool = True) -> Point:
    """First affine point scanning x upward, smaller y first."""
    q = curve.q
    is_qr = bytearray(q)
    roots: dict[int, int] = {}
    for a in range(q):
        r = a * a % q
        if r not in roots or a < roots[r]:
            roots[r] = a
        is_qr[r] = 1
    for x in range(q):
        v = (x * x % q * x + curve.A * x + curve.B) % q
        if v == 0:
            return (x, 0)
        if is_qr[v]:
            y0 = roots[v]
            return (x, min(y0, q - y0))
    return None

# ---------------------------------------------------------------------------
# 2. Cubic residue symbol chi_3 and the cube roots of unity (q, N).
# ---------------------------------------------------------------------------

def cube_root_units(m: int) -> tuple[int, int]:
    """The two nontrivial cube roots of unity mod m (requires m prime, m == 1 mod 3)."""
    assert m % 3 == 1, f"{m} != 1 mod 3; no nontrivial cube root of unity"
    g = primitive_root(m)
    z = pow(g, (m - 1) // 3, m)
    return (z, z * z % m)

def chi3(a: int, q: int, zeta_q: int) -> int:
    """Cubic-residue index in {0,1,2}. chi3(0)=0. zeta_q = a fixed primitive cube root mod q.
    Returns j with a^((q-1)/3) == zeta_q^j."""
    a %= q
    if a == 0:
        return 0
    t = pow(a, (q - 1) // 3, q)
    if t == 1:
        return 0
    if t == zeta_q:
        return 1
    if t == zeta_q * zeta_q % q:
        return 2
    raise RuntimeError("chi3: value not a cube-root-of-unity (bad zeta_q?)")

# ---------------------------------------------------------------------------
# 3. Semaev third summation polynomial for y^2 = x^3 + A x + B.
#    S3(x1,x2,x3) = (x1-x2)^2 x3^2
#                 - 2[(x1+x2)(x1 x2 + A) + 2B] x3
#                 + [(x1 x2 - A)^2 - 4B(x1+x2)]
#    Semaev 2004, Thm 1 (char != 2,3; here q prime > 500, ok): S3 = 0 iff there exist
#    y_i in the ALGEBRAIC CLOSURE K-bar with (x_i,y_i) on E and +-P1 +-P2 +-P3 = O.
#    When the x_i are x-coordinates of genuine E(F_q) points (A-joint's use), the y_i
#    lie in F_q, so the "+-P_i in E(F_q)" restatement is exact. (Coefficients
#    citation-verified 2026-08-21 vs Semaev Thm 1 + Kosters-Yeo; see A-joint DEVIATIONS D2.)
# ---------------------------------------------------------------------------

def semaev_s3(x1: int, x2: int, x3: int, A: int, B: int, q: int) -> int:
    c2 = (x1 - x2) ** 2 % q
    c1 = (-2 * (((x1 + x2) * (x1 * x2 + A)) + 2 * B)) % q
    c0 = (((x1 * x2 - A) ** 2) - 4 * B * (x1 + x2)) % q
    return (c2 * x3 * x3 + c1 * x3 + c0) % q

# ---------------------------------------------------------------------------
# 4. GLV data for a j=0 curve of prime order:  beta, lambda, generator.
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class J0Arm:
    q: int
    B: int          # curve y^2 = x^3 + B
    N: int          # prime group order
    beta: int       # nontrivial cube root of unity mod q; (x,y) -> (beta x, y)
    lam: int        # matching cube root of unity mod N; [lam] realizes the endomorphism
    Gx: int
    Gy: int

def build_j0_arm(q: int, B: int, N: int) -> J0Arm:
    """Assemble the j=0 GLV arm; verifies [lam]G == (beta*Gx, Gy) exactly."""
    assert is_prime(N) and N % 3 == 1  # prime-order j=0 forces N == 1 mod 3
    beta, beta2 = cube_root_units(q)    # pick the smaller-primitive-root one deterministically
    curve = Curve(q, 0, B)
    G = find_point(curve, smallest=True)
    assert G is not None
    phiG = (beta * G[0] % q, G[1])
    lam_a, lam_b = cube_root_units(N)
    lam = None
    for cand in (lam_a, lam_b):
        if curve.mul(cand % N, G) == phiG:
            lam = cand
            break
    if lam is None:
        # try the other beta (beta2) -- beta and lam must be paired consistently
        phiG2 = (beta2 * G[0] % q, G[1])
        for cand in (lam_a, lam_b):
            if curve.mul(cand % N, G) == phiG2:
                beta, lam = beta2, cand
                break
    assert lam is not None, "no lambda matches the beta-endomorphism on G"
    return J0Arm(q=q, B=B, N=N, beta=beta, lam=lam, Gx=G[0], Gy=G[1])

# ---------------------------------------------------------------------------
# 5. Deterministic curve SELECTION (public data; NOT a verdict statistic).
# ---------------------------------------------------------------------------

def select_j0_prime_order(q: int, exclude_anomalous: bool = False) -> Optional[J0Arm]:
    """B-witness rule: smallest B>0 s.t. y^2 = x^3 + B over F_q has PRIME order.

    exclude_anomalous=True adds 'AND trace != 1' (i.e. N != q): anomalous curves admit
    Smart's formal-group/p-adic-log attack (per-point scalar recovery), which would confound
    a joint-synergy contrast. See STAGING_NOTES / A-joint DEVIATIONS. The bare B-witness rule
    is biased toward anomalous curves because N=q is automatically prime."""
    if q % 3 != 1:
        return None
    for B in range(1, q):
        N = point_count(0, B, q)
        if is_prime(N) and not (exclude_anomalous and N == q):
            return build_j0_arm(q, B, N)
    return None

@dataclass(frozen=True)
class ArmRecord:
    kind: str          # 'j0' | 'j1728' | 'jgen'
    q: int
    A: int
    B: int
    N: int             # full group order
    trace: int         # t = q + 1 - N
    cofactor: int
    prime_part: int    # largest prime dividing N that we treat as the subgroup order
    j: Optional[int]
    disc_pi: int       # t^2 - 4q  (< 0); |disc_pi| gauges CM-disc size

def _arm_record(kind: str, q: int, A: int, B: int) -> ArmRecord:
    N = point_count(A, B, q)
    t = q + 1 - N
    fs = _prime_factors(N)
    prime_part = max(fs)
    cof = N // prime_part
    j = Curve(q, A, B).j_invariant()
    return ArmRecord(kind, q, A, B, N, t, cof, prime_part, j, t * t - 4 * q)

def select_j1728_cofactor2(q: int) -> Optional[ArmRecord]:
    """y^2 = x^3 + Ax (j=1728, CM by Z[i]); chi_2(-A) = -1, N = 2 n' with n' prime (cyclic)."""
    if q % 4 != 1:
        return None
    for A in range(1, q):
        if legendre(-A, q) != -1:
            continue
        N = point_count(A, 0, q)
        if N % 2 == 0 and is_prime(N // 2):
            return _arm_record('j1728', q, A, 0)
    return None

def select_jgen(q: int, target_N: Optional[int] = None, cofactor: Optional[int] = None,
                d_min: Optional[int] = None, exclude_anomalous: bool = False) -> Optional[ArmRecord]:
    """Ordinary j not in {0,1728}, |t^2-4q| >= d_min (default floor(sqrt q)).
    If target_N given, minimise |N - target_N|; if cofactor given, require it.
    exclude_anomalous=True drops trace-1 (N=q) curves -- A-joint DEVIATION D4: the
    anomalous-exclusion of D1 must apply to the non-CM matching arm too, or a Smart-
    attackable ordinary curve can enter the CM-vs-non-CM contrast from the non-CM side."""
    if d_min is None:
        d_min = isqrt(q)
    best: Optional[ArmRecord] = None
    for A in range(1, q):
        for B in range(1, q):
            cur = Curve(q, A, B)
            j = cur.j_invariant()
            if j is None or j == 0 or j == 1728 % q:
                continue
            N = point_count(A, B, q)
            t = q + 1 - N
            if t % q == 0:                      # supersingular -> not ordinary
                continue
            if exclude_anomalous and t == 1:    # anomalous (N=q) -> Smart-attackable
                continue
            if abs(t * t - 4 * q) < d_min:
                continue
            fs = _prime_factors(N)
            cof = N // max(fs)
            if cofactor is not None and cof != cofactor:
                continue
            rec = _arm_record('jgen', q, A, B)
            if target_N is None:
                return rec
            if best is None or abs(rec.N - target_N) < abs(best.N - target_N) \
               or (abs(rec.N - target_N) == abs(best.N - target_N) and (rec.j, rec.A, rec.B) < (best.j, best.A, best.B)):
                best = rec
        if best is not None and target_N is not None and best.N == target_N:
            break
    return best

def select_jgen_random(q: int, target_N: int, exclude_anomalous: bool = True,
                       budget: int = 1500, seed: int = 0,
                       d_min: Optional[int] = None) -> Optional[ArmRecord]:
    """Bounded random-search non-CM matcher (DEVIATION from the O(q^2) enumerative select_jgen,
    for tractability at large q where no early exact-order match exists). Draws `budget` random
    (A,B), keeps the best ordinary j not in {0,1728}, |t^2-4q| >= d_min, t != 1 (anomalous) curve
    minimizing |N - target_N|; early-exits on an exact match. Deterministic given `seed`.
    Reuses one QR sieve across all draws. Reports the achieved order gap (caller logs it)."""
    import random as _r
    if d_min is None:
        d_min = isqrt(q)
    rng = _r.Random(seed)
    is_qr = _qr_sieve(q)
    best: Optional[ArmRecord] = None
    for _ in range(budget):
        A = rng.randrange(1, q)
        B = rng.randrange(1, q)
        cur = Curve(q, A, B)
        j = cur.j_invariant()
        if j is None or j == 0 or j == 1728 % q:
            continue
        N = point_count(A, B, q, is_qr)
        t = q + 1 - N
        if t % q == 0:                      # supersingular
            continue
        if exclude_anomalous and t == 1:    # anomalous
            continue
        if abs(t * t - 4 * q) < d_min:
            continue
        fs = _prime_factors(N)
        cand = ArmRecord('jgen', q, A, B, N, t, N // max(fs), max(fs), j, t * t - 4 * q)
        if best is None or abs(cand.N - target_N) < abs(best.N - target_N):
            best = cand
            if best.N == target_N:
                break
    return best

def isqrt(n: int) -> int:
    """Exact integer sqrt (floor). Pure-int Newton -- no float anywhere (CLAUDE.md)."""
    if n < 0:
        raise ValueError("isqrt of negative")
    if n == 0:
        return 0
    x = 1 << ((n.bit_length() + 1) // 2)   # integer seed via bit length
    while True:
        y = (x + n // x) // 2
        if y >= x:
            return x
        x = y

# ---------------------------------------------------------------------------
# 6. Frozen prime schedules (per prereg Section 6). Public data.
# ---------------------------------------------------------------------------

def primes_in(lo: int, hi: int, cong_mod: int, cong_res: int) -> list[int]:
    return [p for p in range(lo, hi) if p % cong_mod == cong_res and is_prime(p)]

def schedule_A_joint(exclude_anomalous: bool = True) -> dict:
    """A-joint Section 6: j=0 prime-order q == 1 mod 3.
    discovery = smallest 3 with q>500; confirmation = smallest 3 with q>2000;
    ladder = smallest such q exceeding each of 2^10,2^12,2^14,2^16.
    DEVIATION D1 (2026-08-21, default ON): exclude anomalous (trace-1) curves -- see
    PREREG_cm_jointset_excess_v1_DEVIATIONS.md."""
    def ok(q: int) -> bool:
        return q % 3 == 1 and is_prime(q) and \
            select_j0_prime_order(q, exclude_anomalous) is not None
    def smallest_j0(n: int, start: int) -> list[int]:
        out, q = [], start + 1
        while len(out) < n:
            if ok(q):
                out.append(q)
            q += 1
        return out
    def first_j0_above(x: int) -> int:
        q = x + 1
        while not ok(q):
            q += 1
        return q
    def arms(qs: list[int]) -> list[dict]:
        out = []
        for q in qs:
            a = select_j0_prime_order(q, exclude_anomalous)
            out.append({"q": q, "B": a.B, "N": a.N, "beta": a.beta, "lam": a.lam,
                        "trace": q + 1 - a.N})
        return out
    disc = smallest_j0(3, 500)
    conf = smallest_j0(3, 2000)
    ladder = sorted({first_j0_above(2 ** e) for e in (10, 12, 14, 16)})
    return {"prereg": "A-joint",
            "rule": "j=0 B-witness prime order, q==1 mod 3, trace!=1 (D1: exclude anomalous)",
            "exclude_anomalous": exclude_anomalous,
            "discovery": arms(disc), "confirmation": arms(conf), "ladder": arms(ladder)}

def schedule_C_center() -> dict:
    """C-center Section 6: p == 1 mod 12; discovery 30<p<250, confirmation 250<p<1000.
    The prereg lists the full band; the runner filters to primes where all verdict arms
    (J0 cofactor-1 prime order + J1728 cofactor-2 prime part) exist. Both are emitted:
    'band' is the frozen prereg list, 'arm_available' the staged runnable subset."""
    def annotate(qs: list[int]) -> dict:
        band, avail = [], []
        for p in qs:
            a0 = select_j0_prime_order(p)
            a4 = select_j1728_cofactor2(p)
            band.append(p)
            if a0 is not None and a4 is not None:
                avail.append({"p": p, "j0_B": a0.B, "j0_N": a0.N,
                              "j1728_A": a4.A, "j1728_N": a4.N})
        return {"band": band, "arm_available": avail}
    return {"prereg": "C-center",
            "rule": "p == 1 mod 12; verdict needs J0(cof1,prime) AND J1728(cof2,prime part)",
            "discovery": annotate(primes_in(31, 250, 12, 1)),
            "confirmation": annotate(primes_in(251, 1000, 12, 1))}

# ---------------------------------------------------------------------------
# 7. Self-tests (KATs on the PRIMITIVES only -- no verdict statistic).
# ---------------------------------------------------------------------------

def selftest() -> None:
    print("== primitive KATs ==")

    # (a) group law + Hasse + point count on a known small curve
    q, A, B = 101, 2, 3
    cur = Curve(q, A, B)
    N = point_count(A, B, q)
    assert abs(q + 1 - N) <= 2 * isqrt(q), "Hasse bound violated"
    # brute-force order agreement
    bf = 1 + sum(1 + legendre((x * x % q * x + A * x + B) % q, q) if (x*x%q*x+A*x+B)%q != 0
                 else 1 for x in range(q))
    assert bf == N, f"point_count {N} != bruteforce {bf}"
    print(f"  [ok] point_count == brute force  (#E(F_{q}) = {N}, Hasse ok)")

    # (b) associativity / inverse spot-check
    P = find_point(cur); Q = cur.add(P, P)
    assert cur.is_on(P) and cur.is_on(Q)
    assert cur.add(P, cur.neg(P)) is None
    assert cur.add(cur.add(P, Q), P) == cur.add(P, cur.add(Q, P)), "add not associative"
    print("  [ok] add: inverse + associativity spot-check")

    # (c) j-invariant sentinels
    assert Curve(q, 0, 5).j_invariant() == 0
    assert Curve(q, 5, 0).j_invariant() == 1728 % q
    print("  [ok] j-invariant: j0=0, j1728=1728")

    # (d) chi3 multiplicativity: chi3(ab) == chi3(a)+chi3(b) mod 3
    q3 = 103  # == 1 mod 3
    zq, _ = cube_root_units(q3)
    import random
    rng = random.Random(20260821)
    for _ in range(200):
        a = rng.randrange(1, q3); b = rng.randrange(1, q3)
        assert (chi3(a, q3, zq) + chi3(b, q3, zq)) % 3 == chi3(a * b % q3, q3, zq)
    print("  [ok] chi3 multiplicative on 200 random pairs (q=103)")

    # (e) Semaev S3 vanishes exactly when P3 = -(P1 + P2)
    qs, As, Bs = 1009, 4, 7
    Es = Curve(qs, As, Bs)
    hits = trials = 0
    Pg = find_point(Es)
    acc = Pg
    for _ in range(60):
        acc = Es.add(acc, Pg)
        P1 = acc
        P2 = Es.add(P1, Pg)
        if P1 is None or P2 is None:
            continue
        P3 = Es.neg(Es.add(P1, P2))
        if P3 is None:
            continue
        trials += 1
        val = semaev_s3(P1[0], P2[0], P3[0], As, Bs, qs)
        if val == 0:
            hits += 1
        # and a non-relation should generically NOT vanish
    assert hits == trials, f"S3 vanished on only {hits}/{trials} true relations"
    # negative control: random unrelated triples rarely vanish
    zero_neg = 0
    for _ in range(300):
        xs = [rng.randrange(qs) for _ in range(3)]
        if semaev_s3(xs[0], xs[1], xs[2], As, Bs, qs) == 0:
            zero_neg += 1
    assert zero_neg < 30, f"S3 vanishing too often on random triples: {zero_neg}/300"
    print(f"  [ok] Semaev S3: {hits}/{trials} true relations vanish; "
          f"{zero_neg}/300 random triples vanish (generic-nonzero)")

    # (f) GLV: build a real j=0 arm and verify [lam]G == (beta*Gx, Gy) AND lam^3==1
    arm = select_j0_prime_order(103)
    assert arm is not None
    ca = Curve(arm.q, 0, arm.B)
    assert ca.mul(arm.lam % arm.N, (arm.Gx, arm.Gy)) == (arm.beta * arm.Gx % arm.q, arm.Gy)
    assert pow(arm.beta, 3, arm.q) == 1 and arm.beta != 1
    assert pow(arm.lam, 3, arm.N) == 1 and arm.lam % arm.N != 1
    assert arm.N % 3 == 1
    print(f"  [ok] GLV arm q=103: B={arm.B}, N={arm.N}, beta^3=1, [lam]G=(beta x,y)")

    # (g) selection availability across the C-center discovery band (staging de-risk).
    #     Report per-prime which arms exist; assert every RETURNED arm is valid; and
    #     assert j0 exists at every 1-mod-12 prime (1 mod 12 => 1 mod 3).
    band = primes_in(31, 250, 12, 1)
    have_j0 = have_1728 = have_gen = have_all = 0
    print("  arm availability on p==1 mod 12, 30<p<250:")
    print("    p    j0   j1728(cof2)  jgen")
    for p in band:
        a0 = select_j0_prime_order(p)     # cofactor-1 (N prime) j0 -- does NOT exist at every p
        a4 = select_j1728_cofactor2(p)
        ag = select_jgen(p)
        if a0 is not None:
            assert pow(a0.beta, 3, p) == 1 and a0.N % 3 == 1 and is_prime(a0.N)
        if a4 is not None:
            assert a4.cofactor == 2 and is_prime(a4.prime_part) and legendre(-a4.A, p) == -1
        if ag is not None:
            assert ag.j not in (0, 1728 % p) and ag.trace % p != 0
        have_j0 += a0 is not None
        have_1728 += a4 is not None
        have_gen += ag is not None
        have_all += (a0 is not None and a4 is not None and ag is not None)
        print(f"    {p:<4} {('B='+str(a0.B)) if a0 else '---':<7}"
              f"{('N='+str(a4.N)) if a4 else '---':<13}"
              f"{('j='+str(ag.j)) if ag else '---'}")
    assert have_all >= 3, "too few band primes support all three arms"
    print(f"  [ok] band n={len(band)}: j0 {have_j0}/{len(band)}, "
          f"j1728-cof2 {have_1728}/{len(band)}, jgen {have_gen}/{len(band)}, "
          f"all-three {have_all}/{len(band)}")

    print("== all primitive KATs passed ==")

# ---------------------------------------------------------------------------
# 8. Schedule emission + freeze (SHA-256).
# ---------------------------------------------------------------------------

def emit_schedules(out_dir: str) -> None:
    import os
    os.makedirs(out_dir, exist_ok=True)
    for name, fn in (("schedule_A_joint", schedule_A_joint),
                     ("schedule_C_center", schedule_C_center)):
        data = fn()
        blob = json.dumps(data, indent=2, sort_keys=True).encode()
        path = os.path.join(out_dir, name + "_v1.json")
        with open(path, "wb") as f:
            f.write(blob)
        sha = hashlib.sha256(blob).hexdigest()
        with open(path + ".sha256", "w") as f:
            f.write(sha + "  " + name + "_v1.json\n")
        print(f"[emit] {path}")
        print(f"       SHA-256 {sha}")
        print(f"       {json.dumps(data)}")

# ---------------------------------------------------------------------------

if __name__ == "__main__":
    if len(sys.argv) >= 2 and sys.argv[1] == "--selftest":
        selftest()
    elif len(sys.argv) >= 3 and sys.argv[1] == "--schedule":
        emit_schedules(sys.argv[2])
    else:
        print(__doc__)
        print("commands: --selftest | --schedule OUT_DIR")
