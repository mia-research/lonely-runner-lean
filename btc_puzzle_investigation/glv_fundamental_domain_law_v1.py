#!/usr/bin/env python3
"""
glv_fundamental_domain_law_v1.py

FIRST exact 2-point (joint) law for the Eisenstein lift -- past the exhausted
single-x axis (angle law, norm-band law, chi6 uniform, sextant _|_ chi6 all charted).

The open frontier is joint / multi-point. The CM / GLV endomorphism phi(x,y)=(beta x, y),
beta a nontrivial cube root of 1 mod p, gives an EXACT relation between the lifts of the
2-point pair (X, beta*X). Because it IS the curve endomorphism, this is exactly the kind
of joint structure that survives any scalar scramble.

CLAIM (established exactly here):
  eis(beta X) = reduce_P( zeta . eis(X) ),   zeta in {omega, omega^2} the one matching beta,
where '.' is Z[omega] multiplication and reduce_P is Babai reduction into the rhombus P.
Since both sides reduce the SAME coset of (pi_p), this is an identity for EVERY X (checked).

Consequences measured exactly:
  * zeta.eis(X) preserves NORM (zeta a unit) and rotates sextant by a FIXED amount
    (+2 for omega, +4 for omega^2).
  * "Pure rotation" (zeta.eis(X) already in P, so eis(beta X) = zeta.eis(X) with no
    correction) happens with a probability equal to area(P ∩ zeta^-1 P)/area(P) -- a
    UNIVERSAL, theta-independent constant (rotating both rhombi by theta leaves the
    overlap fixed).
  * Otherwise a single lattice correction c in {0, +-R1, +-R2, +-(R1-R2)} applies; the
    correction cases are the ONLY source of sextant-parity flips and norm changes, i.e.
    the exact origin of the empirical "~98% orbit-sextant same parity".

Exact integers in the entire signal path. theta (deg) is float, used only to LABEL primes
(reporting), never in the counting path.
"""
import math
import random
from lift_sextant_rhombus_law_proof_v2 import reduced_basis, gauss_reduce, rdiv, enorm

P_SECP = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F
AP_SECP = 367917413016453100223835821029139468249
BP_SECP = 303414439467246543595250775667605759171


def sextant(u, v):
    """Exact 0..5 sextant of w=u+v*omega (copied verbatim from
    eisenstein_lift_sextant_exact_v1 to avoid its heavy import chain)."""
    if u == 0 and v == 0:
        return 0
    for k in range(6):
        if v >= 0 and (u - v) >= 0 and u > 0:
            return k
        u, v = v, v - u          # -60 degrees, exact
    return 0 if v >= 0 else 3


def om(w):                       # multiply by omega  : +120 deg  = +2 sextants
    u, v = w
    return (-v, u - v)


def om2(w):                      # multiply by omega^2: +240 deg  = +4 sextants
    u, v = w
    return (v - u, -u)


def make_lift(p, R1=None, R2=None):
    if R1 is None:
        R1, R2 = reduced_basis(p)
    DET = R1[0] * R2[1] - R1[1] * R2[0]

    def reduce_P(a, b):
        # Babai reduction of (a,b) against basis (R1,R2): (a,b)=c1 R1 + c2 R2, round c1,c2
        c1 = rdiv(a * R2[1] - b * R2[0], DET)
        c2 = rdiv(b * R1[0] - a * R1[1], DET)
        return (a - (c1 * R1[0] + c2 * R2[0]), b - (c1 * R1[1] + c2 * R2[1]))

    def eis(X):
        return reduce_P(X % p, 0)

    return R1, R2, DET, reduce_P, eis


def cube_roots(p):
    """The two nontrivial cube roots of unity mod p (p == 1 mod 3)."""
    e = (p - 1) // 3
    for g in range(2, 2000):
        b = pow(g, e, p)
        if b != 1 and pow(b, 3, p) == 1:
            return b, (b * b) % p
    raise RuntimeError("no cube root of unity found")


def theta_deg(R1):
    """arg of the reduced basis vector, folded to [0,60) -- LABEL ONLY (float)."""
    x = R1[0] - R1[1] / 2.0
    y = R1[1] * math.sqrt(3) / 2.0
    return math.degrees(math.atan2(y, x)) % 60.0


def _match_zeta(p, eis, reduce_P, beta, probe):
    """Return (zeta_fn, name, shift) s.t. eis(beta*X)==reduce_P(zeta(eis(X))) for probe X."""
    for zf, nm, sh in ((om, "omega", 2), (om2, "omega^2", 4)):
        if all(eis((beta * X) % p) == reduce_P(*zf(eis(X))) for X in probe):
            return zf, nm, sh
    return None, None, None


def analyze(name, p, Xs, R1=None, R2=None):
    R1, R2, DET, reduce_P, eis = make_lift(p, R1, R2)
    b1, b2 = cube_roots(p)
    probe = [x for x in Xs[:40] if x % p != 0]

    print(f"\n=== {name}  (p{'=%d' % p if p < 10**8 else ' = secp'}, "
          f"theta={theta_deg(R1):.2f} deg, |X|={len(Xs)}) ===")
    print(f"    reduced basis R1={R1}  R2={R2}   N(R1)={enorm(R1)==p} N(R2)={enorm(R2)==p}")

    for beta, tag in ((b1, "beta1"), (b2, "beta2")):
        zf, nm, shift = _match_zeta(p, eis, reduce_P, beta, probe)
        if zf is None:
            print(f"    {tag}={beta if p<10**8 else hex(beta)[:12]+'..'}: no zeta match (!)")
            continue

        # main exact pass
        identity_ok = 0
        pure_rot = 0
        dsext = [0] * 6
        norm_pre = 0
        same_par = 0
        corr = {}                     # correction vector -> count
        R1n, R2n = R1, R2
        for X in Xs:
            if X % p == 0:
                continue
            w = eis(X)
            zw = zf(w)                # zeta . eis(X)  (exact)
            wb = eis((beta * X) % p)  # eis(beta X)    (exact)
            rp = reduce_P(*zw)
            if rp == wb:
                identity_ok += 1
            # correction c = eis(beta X) - zeta.eis(X)  (in lattice, small set)
            c = (wb[0] - zw[0], wb[1] - zw[1])
            corr[c] = corr.get(c, 0) + 1
            if c == (0, 0):
                pure_rot += 1
            ds = (sextant(*wb) - sextant(*w)) % 6
            dsext[ds] += 1
            if (sextant(*wb) % 2) == (sextant(*w) % 2):
                same_par += 1
            if enorm(wb) == enorm(w):
                norm_pre += 1

        M = sum(1 for X in Xs if X % p != 0)
        print(f"    {tag}: matches *{nm} (fixed rotation +{shift} sextants); "
              f"eis(bX)=reduce(zeta.eis X) for {identity_ok}/{M} "
              f"({'IDENTITY HOLDS' if identity_ok == M else 'FAILS'})")
        print(f"       pure-rotation (no correction): {pure_rot}/{M} = {pure_rot/M:.4f}")
        print(f"       norm preserved: {norm_pre/M:.4f}   sextant same-parity: {same_par/M:.4f}")
        print(f"       Delta-sextant hist (index=+k mod6): {dsext}  (pure gives +{shift})")
        top = sorted(corr.items(), key=lambda kv: -kv[1])[:6]
        # express corrections in basis coords for readability
        def basis_coords(c):
            a, b = c
            c1 = (a * R2[1] - b * R2[0]) // DET
            c2 = (b * R1[0] - a * R1[1]) // DET
            return (c1, c2)
        print(f"       corrections (as m1*R1+m2*R2, count): "
              f"{[(basis_coords(c), n) for c, n in top]}")


def main():
    print("=" * 74)
    print("GLV / CM endomorphism acting on the Eisenstein fundamental domain")
    print("First exact 2-point (joint) law:  eis(beta X) = reduce_P( zeta . eis(X) )")
    print("=" * 74)

    # small primes, DIFFERENT theta -- full F_p, exact, to show universality of the
    # pure-rotation constant and the correction set
    import sympy
    small = [q for q in sympy.primerange(1000, 200000) if q % 3 == 1]
    # pick a spread of theta by sampling several primes
    picks = [small[0], small[len(small) // 4], small[len(small) // 2],
             small[3 * len(small) // 4], small[-1]]
    for p in picks:
        analyze(f"full F_p, p={p}", p, list(range(1, p)))

    # secp: uniform sample of X (exact integers); use the KNOWN pi_p basis directly
    rng = random.Random(2718)
    Xs = [rng.randrange(1, P_SECP) for _ in range(60000)]
    R1s, R2s = gauss_reduce((AP_SECP, BP_SECP), (-BP_SECP, AP_SECP - BP_SECP))
    analyze("secp uniform-X", P_SECP, Xs, R1=R1s, R2=R2s)


if __name__ == "__main__":
    main()
