#!/usr/bin/env python3
"""
glv_three_point_lift_v1.py

The 3-point law: how the Eisenstein lift handles the GROUP LAW between INDEPENDENT points.
(First object that involves independently chosen keys, not an algebraically-locked pair.)

Recipe (colleague's plan + our coarse/full-lift split):
  * random P1, P2 in E(F_p); P3 = -(P1+P2)  so  P1+P2+P3 = O  (=> d1+d2+d3 = 0 mod n).
  * X_i = x(P_i);  U_i = eis(X_i);  s_i = sextant(U_i).
  * (a) coarse: does (s1,s2) predict s3?  MI vs matched-shuffle null + population scaling.
  * (b) stability cross-tab: does the group law preserve the CM-stable core (pinned wedges)?
  * (c) full-lift 3-correction c3 = reduce_P(U3 - U1 - U2): a small set (like the 2-point +-R)
        or spread?  We report distinct-count / top-mass, NOT a coarse readout.
  * (d) mu6-equivariance: beta(P1+P2+P3)=O => the (s1,s2,s3) joint should be invariant under a
        simultaneous +2 sextant shift.  We test it.

We DO NOT pre-judge coarse nulls (a single coarse projection can decouple while the full lift
carries structure -- cf. doubling). Exact integer arithmetic in the point/lift path.
"""
import math
import random
from glv_fundamental_domain_law_v1 import make_lift, sextant, cube_roots, P_SECP, AP_SECP, BP_SECP
from lift_sextant_rhombus_law_proof_v2 import gauss_reduce, sector_props
from fractions import Fraction as F


# ---- elliptic curve y^2 = x^3 + 7 over F_p (affine, O = None) ----
def ec_add(P, Q, p):
    if P is None:
        return Q
    if Q is None:
        return P
    x1, y1 = P; x2, y2 = Q
    if x1 == x2 and (y1 + y2) % p == 0:
        return None
    if P == Q:
        m = (3 * x1 * x1) % p * pow(2 * y1, p - 2, p) % p
    else:
        m = (y2 - y1) % p * pow((x2 - x1) % p, p - 2, p) % p
    x3 = (m * m - x1 - x2) % p
    return (x3, (m * (x1 - x3) - y1) % p)


def sqrt_mod(a, p):
    a %= p
    if a == 0:
        return 0
    if pow(a, (p - 1) // 2, p) != 1:
        return None
    if p % 4 == 3:
        return pow(a, (p + 1) // 4, p)
    from sympy.ntheory.residue_ntheory import sqrt_mod as _s
    return _s(a, p)


def rand_point(p, rng):
    while True:
        x = rng.randrange(p)
        y = sqrt_mod((pow(x, 3, p) + 7) % p, p)
        if y is not None:
            return (x, y if rng.getrandbits(1) else (-y) % p)


def mi_bits(J):
    tot = sum(sum(r) for r in J)
    if not tot:
        return 0.0
    rs = [sum(r) for r in J]
    cs = [sum(J[i][j] for i in range(len(J))) for j in range(len(J[0]))]
    return sum((J[i][j] / tot) * math.log2((J[i][j] * tot) / (rs[i] * cs[j]))
               for i in range(len(J)) for j in range(len(J[0])) if J[i][j] and rs[i] and cs[j])


def run(name, p, ntrials, R1=None, R2=None, seed=0):
    R1, R2, DET, reduce_P, eis = make_lift(p, R1, R2)
    props = sector_props(R1, R2)
    pinned = set(t for t in range(6) if props[t] == F(1, 8))
    rng = random.Random(seed)

    trip = []                              # (s1,s2,s3)
    J = [[0] * 6 for _ in range(36)]       # (s1,s2)->s3
    c3_hist = {}                           # 3-correction vector census
    stab = [[0, 0], [0, 0]]                # [s1&s2 both pinned?][s3 pinned?]
    for _ in range(ntrials):
        P1 = rand_point(p, rng); P2 = rand_point(p, rng)
        S = ec_add(P1, P2, p)
        if S is None or P1[0] == P2[0]:
            continue
        X = (P1[0], P2[0], S[0])           # x(-(P1+P2)) = x(P1+P2) = S[0]
        U = [eis(x) for x in X]
        s = [sextant(*u) for u in U]
        trip.append(tuple(s))
        J[s[0] * 6 + s[1]][s[2]] += 1
        both = 1 if (s[0] in pinned and s[1] in pinned) else 0
        stab[both][1 if s[2] in pinned else 0] += 1
        c = reduce_P((U[2][0] - U[0][0] - U[1][0]), (U[2][1] - U[0][1] - U[1][1]))
        c3_hist[c] = c3_hist.get(c, 0) + 1

    M = len(trip)
    # (a) coarse MI + matched null
    obs = mi_bits(J)
    keys = [(a, b) for (a, b, _) in trip]; s3s = [c for (_, _, c) in trip]
    nulls = []
    for _ in range(120):
        sh = s3s[:]; rng.shuffle(sh)
        Jn = [[0] * 6 for _ in range(36)]
        for (a, b), c in zip(keys, sh):
            Jn[a * 6 + b][c] += 1
        nulls.append(mi_bits(Jn))
    mu = sum(nulls) / len(nulls); sd = (sum((v - mu) ** 2 for v in nulls) / len(nulls)) ** 0.5
    z = (obs - mu) / sd if sd else 0.0

    # (c) correction spread
    distinct = len(c3_hist)
    topmass = max(c3_hist.values()) / M

    # (d) mu6-equivariance: simultaneous +2 shift invariance of the (s1,s2,s3) count
    from collections import Counter
    T = Counter(trip)
    Tsh = Counter(((a + 2) % 6, (b + 2) % 6, (c + 2) % 6) for (a, b, c) in trip)
    # correlation of the two 216-vectors
    allk = set(T) | set(Tsh)
    vt = [T[k] for k in allk]; vs = [Tsh[k] for k in allk]
    mt = sum(vt) / len(vt); ms = sum(vs) / len(vs)
    cov = sum((a - mt) * (b - ms) for a, b in zip(vt, vs))
    dd = (sum((a - mt) ** 2 for a in vt) * sum((b - ms) ** 2 for b in vs)) ** 0.5
    corr = cov / dd if dd else 0.0

    b0 = (stab[0][1] / max(stab[0][0] + stab[0][1], 1))
    b1 = (stab[1][1] / max(stab[1][0] + stab[1][1], 1))
    print(f"\n=== {name}  (M={M}, pinned={sorted(pinned)}) ===")
    print(f"  (a) coarse MI((s1,s2);s3) = {obs:.5f}  null {mu:.5f}+-{sd:.5f}  z={z:+.1f}")
    print(f"  (b) P(s3 pinned | s1,s2 both pinned) = {b1:.4f}   vs baseline "
          f"P(s3 pinned) = {(stab[0][1]+stab[1][1])/M:.4f}   (uniform-ish 1/4 if no effect)")
    print(f"  (c) 3-correction c3=U3-(U1+U2) reduced: distinct={distinct} "
          f"(uniform~{min(M,p)}), top-mass={topmass:.5f} (2-point law had ~0.75) => "
          f"{'CONCENTRATED' if topmass > 0.1 else 'SPREAD (no small-set additive law)'}")
    print(f"  (d) [diagnostic only] table vs simultaneous +2-shift corr = {corr:.4f} -- "
          f"NOT a real symmetry test: the angle law is mu2- (H(s)=H(s+3)) not mu3-symmetric, "
          f"so the raw joint is not +2-invariant; beta-equivariance is a point-level identity.")


def main():
    print("=" * 72)
    print("3-point lift law: the group law between independent points, on the Eisenstein lift")
    print("=" * 72)
    run("full-ish F_p p=1009", 1009, 30000, seed=1)
    run("full-ish F_p p=100003", 100003, 60000, seed=2)
    R1s, R2s = gauss_reduce((AP_SECP, BP_SECP), (-BP_SECP, AP_SECP - BP_SECP))
    run("secp random points", P_SECP, 40000, R1=R1s, R2=R2s, seed=3)


if __name__ == "__main__":
    main()
