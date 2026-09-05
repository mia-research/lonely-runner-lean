#!/usr/bin/env python3
"""
glv_two_domain_residue_v2.py

CORRECTS v1.  v1 correlated the residue r = v - w against w itself -- circular
(r is BUILT from w; sextant(v-w) tracks sextant(w) as a pure subtraction artifact,
even for independent v,w; the huge z was an artifact, discarded).

The clean two-domain question is:  is the coordinate map (module element -> x-coord)
LINEAR up to a bounded wrap?  i.e. with
   w  = eis_n(d)         (scalar lift ~ d in P_n)
   v  = eis_p(x([d]G))   (coordinate lift, computable from the POINT alone)
   Mw = slippage-bridge image of w in P_p
does r = v - Mw take FEW distinct values (linear map + bounded wrap == a break-like
handle) or does it fill P_p (a scramble)?  And -- non-circularly -- does any cheap
label of v carry information about d that v does not trivially contain?

Tests (exact integers in the point/lift/residue path):
  (A) BOUNDEDNESS of r = v - Mw: distinct-count and top-mass over M samples.
      Uniform-in-P_p  => distinct ~ M, top-mass ~ 1/M  => NO linearization.
      Small set       => a linear coordinate map  => escalate hard.
  (B) NON-CIRCULAR leakage, matched-null MI + population scaling + shuffle CONTROL:
        sextant(v)      vs sextant(w)      [coord angle vs scalar angle]
        eps(v)          vs d mod 6
        sextant(v)      vs d mod 6
      Larger N to settle the v1 mild (z~1.8, non-scaling) coord-vs-scalar reading.
  Every 'signal' must (i) have MI >> null, (ii) z grow ~sqrt(N), (iii) control ~0.
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
    c1 = (a * R2[1] - b * R2[0]) // DET
    c2 = (b * R1[0] - a * R1[1]) // DET
    return c1, c2


def mi_bits(J):
    tot = sum(sum(r) for r in J)
    if not tot:
        return 0.0
    rs = [sum(r) for r in J]
    cs = [sum(J[i][j] for i in range(len(J))) for j in range(len(J[0]))]
    return sum((J[i][j] / tot) * math.log2((J[i][j] * tot) / (rs[i] * cs[j]))
               for i in range(len(J)) for j in range(len(J[0]))
               if J[i][j] and rs[i] and cs[j])


def main():
    R1p, R2p = gauss_reduce((AP_SECP, BP_SECP), (-BP_SECP, AP_SECP - BP_SECP))
    R1n, R2n = gauss_reduce((AP_SECP - 1, BP_SECP), (-BP_SECP, (AP_SECP - 1) - BP_SECP))
    R1p, R2p, DETp, reduce_p, eis_p = make_lift(P, R1p, R2p)
    R1n, R2n, DETn, reduce_n, eis_n = make_lift(N, R1n, R2n)
    b1, b2 = cube_roots(P)
    beta = b1 if eis_p((b1 * 12345) % P) == reduce_p(*om2(eis_p(12345))) else b2
    R1pt, R2pt = tuple(R1p), tuple(R2p)

    def eps_of_x(x):
        U0 = eis_p(x); U1 = eis_p((beta * x) % P)
        c = (U1[0] - om2(U0)[0], U1[1] - om2(U0)[1])
        if c == (0, 0):
            return 1
        if c == R1pt or c == R2pt:
            return 2
        if c == (-R1pt[0], -R1pt[1]) or c == (-R2pt[0], -R2pt[1]):
            return 0
        return 3

    def M_embed(w):
        c1, c2 = basis_coords(w[0], w[1], R1n, R2n, DETn)
        return (c1 * R1p[0] + c2 * R2p[0], c1 * R1p[1] + c2 * R2p[1])

    print("=" * 74)
    print("Two-domain residue v2 (corrected): is the coordinate map linear up to a")
    print("bounded wrap?  r = eis_p(x([d]G)) - M.eis_n(d)")
    print("=" * 74)

    NMAX = 90000
    rng = random.Random(31337)
    V = []; W = []; RES = []; DM6 = []; EPSV = []; SXV = []; SXW = []
    for _ in range(NMAX):
        d = rng.randrange(1, N)
        pt = scalar_mul(d)
        if pt is None or pt[0] == 0:
            continue
        x = pt[0]
        w = eis_n(d)
        v = eis_p(x)
        Mw = M_embed(w)
        r = (v[0] - Mw[0], v[1] - Mw[1])
        V.append(v); W.append(w); RES.append(r)
        SXV.append(sextant(*v)); SXW.append(sextant(*w))
        EPSV.append(eps_of_x(x)); DM6.append(min(d, N - d) % 6)
    M = len(V)
    print(f"  known-d samples: {M}\n")

    # ---- (A) boundedness of r ----
    print("-" * 74)
    print("(A) BOUNDEDNESS of r = v - M.w  (linear coordinate map <=> small set)")
    print("-" * 74)
    cr = Counter(RES)
    print(f"    distinct(r) = {len(cr)}  of M={M}   top-mass = {max(cr.values())/M:.6f}")
    print(f"    (uniform-in-P_p: distinct~M, top-mass~1/M={1/M:.6f} => NO linearization)")
    sxr = Counter(sextant(*r) for r in RES)
    print(f"    sextant(r) marginal: " + " ".join(f"{sxr[k]/M:.3f}" for k in range(6)))
    # magnitude: is |r| bounded (small) or ~2^128 (full domain)?
    mags = sorted(enorm(r) for r in RES)
    print(f"    N(r) median bit-length = {mags[M//2].bit_length()}  "
          f"(bounded wrap would be tiny; ~256 = fills P_p)")

    # ---- (B) non-circular leakage, scaling + control ----
    def scaled(fx, tx, nf, nt, seed):
        rr = random.Random(seed); out = []
        for NN in [M // 4, M // 2, M]:
            f = fx[:NN]; t = tx[:NN]
            J = [[0] * nt for _ in range(nf)]
            for a, b in zip(f, t):
                J[a][b] += 1
            obs = mi_bits(J)
            nulls = []
            for _ in range(160):
                sh = t[:]; rr.shuffle(sh)
                Jn = [[0] * nt for _ in range(nf)]
                for a, b in zip(f, sh):
                    Jn[a][b] += 1
                nulls.append(mi_bits(Jn))
            mu = sum(nulls) / len(nulls)
            sd = (sum((q - mu) ** 2 for q in nulls) / len(nulls)) ** 0.5
            out.append((NN, obs, mu, (obs - mu) / sd if sd else 0.0))
        # control: fixed full-N shuffle
        cf = fx[:]; ct = tx[:]; rr.shuffle(ct)
        Jc = [[0] * nt for _ in range(nf)]
        for a, b in zip(cf, ct):
            Jc[a][b] += 1
        cobs = mi_bits(Jc)
        cn = []
        for _ in range(160):
            sh = ct[:]; rr.shuffle(sh)
            Jn = [[0] * nt for _ in range(nf)]
            for a, b in zip(cf, sh):
                Jn[a][b] += 1
            cn.append(mi_bits(Jn))
        cmu = sum(cn) / len(cn); csd = (sum((q - cmu) ** 2 for q in cn) / len(cn)) ** 0.5
        return out, (cobs - cmu) / csd if csd else 0.0

    for name, fx, nf, tx, nt in [
            ("sextant(v) vs sextant(w)  [coord angle vs scalar angle]", SXV, 6, SXW, 6),
            ("eps(v)     vs d(min) mod 6", EPSV, 4, DM6, 6),
            ("sextant(v) vs d(min) mod 6", SXV, 6, DM6, 6)]:
        print("\n" + "-" * 74)
        print(f"(B) {name}")
        print("-" * 74)
        res, cz = scaled(fx, tx, nf, nt, seed=(hash(name) & 0xffff))
        for NN, obs, mu, z in res:
            print(f"    N={NN:6d}: MI={obs:.5f} null={mu:.5f} z={z:+6.1f}")
        print(f"    CONTROL (shuffled) z = {cz:+.1f}  (must be ~0; if it fires the null is bad)")

    print("\n" + "=" * 74)
    print("Verdict rule: a handle needs MI>>null AND z growing ~sqrt(N) AND control~0.")
    print("Flat/declining z or a firing control = sampling noise / bad null = scoped")
    print("exact-residue result (no linearization found), NOT closure.")


if __name__ == "__main__":
    main()
