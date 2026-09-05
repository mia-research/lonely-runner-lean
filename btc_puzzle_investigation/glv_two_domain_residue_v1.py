#!/usr/bin/env python3
"""
glv_two_domain_residue_v1.py

The TWO-DOMAIN residue against the known amicable slippage bridge.

Both p and n split in Z[omega]:
   Z[omega]/(pi_p) = F_p        <- x-COORDINATES live here     (lift eis_p, domain P_p)
   Z[omega]/(pi_n) = F_n = Z/n  <- SCALARS d live here,  pi_n = pi_p - 1  (eis_n, P_n)
The point [d]G, as a Z[omega]-module element, is d.g mod pi_n -- LINEAR in d.  The whole
DLP is the coordinate map  (module element) -> (x-coordinate),  i.e.  P_n -> P_p.

Handover-2 Sec.4 gives the EXACT linear scaffold of that map:
   P_p ∩ P_n overlap 1 - 4e-39,  C_n ⊆ C_p exactly,
   basis slippage R1_p - R1_n, R2_p - R2_n  (single-digit integer vectors).
Handover-2 Sec.5 probed coarse-GRID MI of eis_n(d) vs eis_p(x([d]G)) and saw null -- but
it never formed the ALGEBRAIC RESIDUE against that known linear bridge.  This does.

For known-d samples (d, x=x([d]G)):
   w = eis_n(d)              (scalar lift; ~ d as a Z[omega] point in P_n)
   v = eis_p(x)              (coordinate lift; always computable from the POINT alone)
   r_raw   = v - w                          (identity baseline)
   r_slip  = v - M.w    where M re-embeds the pi_n-basis coords of w into the pi_p basis
                                            (the EXACT slippage bridge as baseline)
We then ask, with matched-null MI + POPULATION SCALING (z~sqrt(N) real, flat noise) and a
shuffled-pairing CONTROL that must read ~0:
   does any cheap label of the residue r (sextant / eps / norm-bucket) carry information
   about d (its scalar-lift labels, or d mod small m)?
A concentrated/ growing signal = residual linearity of the coordinate map = a handle.
A flat null (control also ~0) = a scoped result at the exact-residue level (sharper than
the Sec.5 coarse grid), NOT closure -- reported as such.

x([d]G) = x([n-d]G): the coordinate lift only sees +-d, so scalar-side labels are taken
sign-symmetric (min(d,n-d) band; |.| norm) where a sign would otherwise wash the readout.

Exact integers in the point/lift/residue path.  Float only in the MI/z rank statistic vs a
matched permutation null.
"""
import math
import random
from collections import Counter
from fractions import Fraction as F

from ecc_secp256k1 import scalar_mul, N_ORDER
from glv_fundamental_domain_law_v1 import (make_lift, sextant, cube_roots,
                                           P_SECP, AP_SECP, BP_SECP)
from lift_sextant_rhombus_law_proof_v2 import gauss_reduce, enorm

P = P_SECP
N = N_ORDER


def om2(w):
    u, v = w
    return (v - u, -u)


def basis_coords(a, b, R1, R2, DET):
    """exact integer coords (c1,c2) of lattice point (a,b) = c1 R1 + c2 R2."""
    c1 = (a * R2[1] - b * R2[0]) // DET
    c2 = (b * R1[0] - a * R1[1]) // DET
    return c1, c2


def main():
    print("=" * 74)
    print("Two-domain residue: coordinate lift eis_p(x([d]G)) vs scalar lift eis_n(d)")
    print("against the exact amicable slippage bridge (secp256k1)")
    print("=" * 74)

    # ---- the two lifts ----
    R1p, R2p = gauss_reduce((AP_SECP, BP_SECP), (-BP_SECP, AP_SECP - BP_SECP))
    R1n, R2n = gauss_reduce((AP_SECP - 1, BP_SECP), (-BP_SECP, (AP_SECP - 1) - BP_SECP))
    R1p, R2p, DETp, reduce_p, eis_p = make_lift(P, R1p, R2p)
    R1n, R2n, DETn, reduce_n, eis_n = make_lift(N, R1n, R2n)
    print(f"  slippage R1_p-R1_n = {(R1p[0]-R1n[0], R1p[1]-R1n[1])}   "
          f"R2_p-R2_n = {(R2p[0]-R2n[0], R2p[1]-R2n[1])}")

    b1, b2 = cube_roots(P)
    beta = b1 if eis_p((b1 * 12345) % P) == reduce_p(*om2(eis_p(12345))) else b2
    R1pt, R2pt = tuple(R1p), tuple(R2p)

    def eps_of_x(x):
        U0 = eis_p(x)
        U1 = eis_p((beta * x) % P)
        c = (U1[0] - om2(U0)[0], U1[1] - om2(U0)[1])
        if c == (0, 0):
            return 1        # 0-core -> bucket 1
        if c == R1pt or c == R2pt:
            return 2
        if c == (-R1pt[0], -R1pt[1]) or c == (-R2pt[0], -R2pt[1]):
            return 0
        return 3

    def sextant6(w):
        return sextant(*w)

    def norm_b(w, mod):
        s = F(enorm(w), mod)
        return 0 if s < F(3, 16) else (1 if s < F(1, 4) else 2)

    # slippage map M: take pi_n-basis coords of w, re-embed with pi_p basis
    def M_embed(w):
        c1, c2 = basis_coords(w[0], w[1], R1n, R2n, DETn)
        return (c1 * R1p[0] + c2 * R2p[0], c1 * R1p[1] + c2 * R2p[1])

    # ---- generate known-d samples (exact point arithmetic) ----
    NMAX = 40000
    rng = random.Random(770077)
    recs = []
    for _ in range(NMAX):
        d = rng.randrange(1, N)
        pt = scalar_mul(d)
        if pt is None:
            continue
        x = pt[0]
        if x == 0:
            continue
        w = eis_n(d)                 # scalar lift  ~ d
        v = eis_p(x)                 # coordinate lift
        r_raw = (v[0] - w[0], v[1] - w[1])
        Mw = M_embed(w)
        r_slip = (v[0] - Mw[0], v[1] - Mw[1])
        dsign = min(d, N - d)        # sign-symmetric scalar band (x sees +-d)
        recs.append((d, x, w, v, r_raw, r_slip, dsign))
    M = len(recs)
    print(f"  known-d samples: {M}  (d uniform in [1,n), x = x([d]G) exact)\n")

    # ---------- helpers ----------
    def mi_bits(J):
        tot = sum(sum(r) for r in J)
        if not tot:
            return 0.0
        rs = [sum(r) for r in J]
        cs = [sum(J[i][j] for i in range(len(J))) for j in range(len(J[0]))]
        return sum((J[i][j] / tot) * math.log2((J[i][j] * tot) / (rs[i] * cs[j]))
                   for i in range(len(J)) for j in range(len(J[0]))
                   if J[i][j] and rs[i] and cs[j])

    def scaled(fx, tx, nf, nt, seed, control=False):
        """fx,tx: label lists. Return list of (N,obs,z) over scaling; control shuffles."""
        rr = random.Random(seed)
        out = []
        for NN in [M // 4, M // 2, M]:
            f = fx[:NN]; t = tx[:NN]
            if control:
                t = t[:]; rr.shuffle(t)
            J = [[0] * nt for _ in range(nf)]
            for a, b in zip(f, t):
                J[a][b] += 1
            obs = mi_bits(J)
            nulls = []
            for _ in range(120):
                sh = t[:]; rr.shuffle(sh)
                Jn = [[0] * nt for _ in range(nf)]
                for a, b in zip(f, sh):
                    Jn[a][b] += 1
                nulls.append(mi_bits(Jn))
            mu = sum(nulls) / len(nulls)
            sd = (sum((q - mu) ** 2 for q in nulls) / len(nulls)) ** 0.5
            out.append((NN, obs, mu, (obs - mu) / sd if sd else 0.0))
        return out

    # ---------- residue label distributions (are they even uniform?) ----------
    print("-" * 74)
    print("(0) residue label marginals (raw v-w and slippage-corrected v-Mw)")
    print("-" * 74)
    for nm, idx in [("r_raw", 4), ("r_slip", 5)]:
        sx = Counter(sextant6(r[idx]) for r in recs)
        print(f"    {nm} sextant: " + " ".join(f"{sx[k]/M:.3f}" for k in range(6)))

    # ---------- the core tests ----------
    # target labels of d (sign-symmetric where needed)
    d_mod6 = [r[6] % 6 for r in recs]                 # min(d,n-d) mod 6
    d_scal_sext = [sextant6(r[2]) for r in recs]      # scalar-lift sextant of d
    d_scal_norm = [norm_b(r[2], N) for r in recs]

    tests = [
        ("v sextant     vs d-scalar-lift sextant", [sextant6(r[3]) for r in recs], 6, d_scal_sext, 6),
        ("r_raw sextant vs d-scalar-lift sextant", [sextant6(r[4]) for r in recs], 6, d_scal_sext, 6),
        ("r_slip sextant vs d-scalar-lift sextant", [sextant6(r[5]) for r in recs], 6, d_scal_sext, 6),
        ("v eps         vs d(min) mod 6", [eps_of_x(r[1]) for r in recs], 4, d_mod6, 6),
        ("v sextant     vs d(min) mod 6", [sextant6(r[3]) for r in recs], 6, d_mod6, 6),
        ("v norm-bucket vs d-scalar norm-bucket", [norm_b(r[3], P) for r in recs], 3, d_scal_norm, 3),
    ]
    for name, fx, nf, tx, nt in tests:
        print("\n" + "-" * 74)
        print(f"({name})")
        print("-" * 74)
        res = scaled(fx, tx, nf, nt, seed=hash(name) & 0xffff)
        for NN, obs, mu, z in res:
            print(f"    N={NN:6d}: MI={obs:.5f} null={mu:.5f} z={z:+6.1f}")
        # control: shuffled pairing must read ~0
        cres = scaled(fx, tx, nf, nt, seed=1234, control=True)
        print(f"    CONTROL (shuffled d<->x): z at full N = {cres[-1][3]:+.1f}  (must be ~0)")

    print("\n" + "=" * 74)
    print("Reading: MI~1/N with flat/declining z = sampling noise (no residual linearity")
    print("at that label). z growing ~sqrt(N) with control~0 = a real handle. Any growth")
    print("is a lead to escalate, not a verdict; any flat is a scoped exact-residue result.")


if __name__ == "__main__":
    main()
