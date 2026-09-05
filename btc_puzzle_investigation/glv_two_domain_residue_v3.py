#!/usr/bin/env python3
"""
glv_two_domain_residue_v3.py

DE-TAUTOLOGIZES the v1 "artifact".  v1 measured MI(sextant(v-w); sextant(w)) and
got a big, STABLE-across-N value (raw 0.48, slip 0.64).  v2 discarded it as a
subtraction artifact.  But: (i) it is stable (=> deterministic geometry, not
noise); (ii) the slippage-bridge form (0.64) BEATS the raw form (0.48), so the
bridge M matters -- M.w = c1 R1p + c2 R2p is a COARSE-CELL quantization of w
(c1,c2 the small-integer basis coords of the reduced w), so v - M.w reads v
against a coarse bridge-lattice cell of w.  A tautology can still carry structure
(cf. the (n,k,D) identity -> Eisenstein).  So decompose it properly:

  ARTIFACT baseline: MI(sextant(v_i - w_sigma(i)); sextant(w_sigma(i)))  -- keeps
      the SUBTRACTION geometry, breaks the true d<->x coupling (sigma a derangement).
  TRUE:              MI(sextant(v_i - w_i);       sextant(w_i))          -- same d.
  EXCESS = TRUE - mean(ARTIFACT);  z = EXCESS / sd(ARTIFACT) over many sigma.

v1's control (shuffle the LABEL) destroyed the artifact entirely, so it could
only see "artifact present" -- never SIGNAL riding on the artifact.  This null
holds the artifact fixed and asks only whether v's OWN w couples beyond geometry.
Positive, scaling excess = real d<->x structure the coarse marginals missed.
Flat excess = the tautology is pure geometry (now properly controlled).

Also diagnoses the cell mechanism: distribution of (c1,c2)=basiscoords(w) and the
raw-vs-slip artifact gap.  Exact integers in point/lift/residue path.
"""
import math
import random
from collections import Counter

from ecc_secp256k1 import scalar_mul, N_ORDER
from glv_fundamental_domain_law_v1 import (make_lift, sextant, cube_roots,
                                           P_SECP, AP_SECP, BP_SECP)
from lift_sextant_rhombus_law_proof_v2 import gauss_reduce

P = P_SECP
N = N_ORDER


def om2(w):
    u, v = w
    return (v - u, -u)


def basis_coords(a, b, R1, R2, DET):
    c1 = (a * R2[1] - b * R2[0]) // DET
    c2 = (b * R1[0] - a * R1[1]) // DET
    return c1, c2


def mi_bits_pair(fs, ts, nf, nt):
    J = [[0] * nt for _ in range(nf)]
    for a, b in zip(fs, ts):
        J[a][b] += 1
    tot = len(fs)
    rs = [sum(r) for r in J]
    cs = [sum(J[i][j] for i in range(nf)) for j in range(nt)]
    return sum((J[i][j] / tot) * math.log2((J[i][j] * tot) / (rs[i] * cs[j]))
               for i in range(nf) for j in range(nt) if J[i][j] and rs[i] and cs[j])


def main():
    R1p, R2p = gauss_reduce((AP_SECP, BP_SECP), (-BP_SECP, AP_SECP - BP_SECP))
    R1n, R2n = gauss_reduce((AP_SECP - 1, BP_SECP), (-BP_SECP, (AP_SECP - 1) - BP_SECP))
    R1p, R2p, DETp, reduce_p, eis_p = make_lift(P, R1p, R2p)
    R1n, R2n, DETn, reduce_n, eis_n = make_lift(N, R1n, R2n)

    def M_embed(w):
        c1, c2 = basis_coords(w[0], w[1], R1n, R2n, DETn)
        return (c1, c2, (c1 * R1p[0] + c2 * R2p[0], c1 * R1p[1] + c2 * R2p[1]))

    print("=" * 74)
    print("Two-domain residue v3: de-tautologized artifact decomposition")
    print("=" * 74)

    NMAX = 80000
    rng = random.Random(24601)
    Vs = []; Ws = []; MWs = []; cells = Counter()
    for _ in range(NMAX):
        d = rng.randrange(1, N)
        pt = scalar_mul(d)
        if pt is None or pt[0] == 0:
            continue
        w = eis_n(d)
        v = eis_p(pt[0])
        c1, c2, Mw = M_embed(w)
        cells[(c1, c2)] += 1
        Vs.append(v); Ws.append(w); MWs.append(Mw)
    M = len(Vs)
    print(f"  known-d samples: {M}")
    print(f"  (c1,c2) = basiscoords(w) cell census (mechanism of M): "
          f"{dict(sorted(cells.items(), key=lambda kv:-kv[1])[:9])}")
    print(f"  distinct cells = {len(cells)}  (small set => M.w is a coarse-cell "
          f"quantization of w)\n")

    sxW = [sextant(*w) for w in Ws]

    def decompose(name, resid_fn):
        # resid_fn(v, w_or_Mw) -> residue vector; we pass matched lists
        # TRUE: pair i with i
        rt = [sextant(*resid_fn(Vs[i], i)) for i in range(M)]
        for NN in [M // 4, M // 2, M]:
            true_mi = mi_bits_pair(rt[:NN], sxW[:NN], 6, 6)
            arts = []
            for _ in range(200):
                perm = list(range(NN))
                rng.shuffle(perm)
                # artifact: residue of v_i against w_perm(i); target sextant(w_perm(i))
                fs = [sextant(*resid_fn(Vs[i], perm[i])) for i in range(NN)]
                ts = [sxW[perm[i]] for i in range(NN)]
                arts.append(mi_bits_pair(fs, ts, 6, 6))
            mu = sum(arts) / len(arts)
            sd = (sum((a - mu) ** 2 for a in arts) / len(arts)) ** 0.5
            z = (true_mi - mu) / sd if sd else 0.0
            print(f"    {name} N={NN:6d}: TRUE_MI={true_mi:.5f}  "
                  f"ARTIFACT={mu:.5f}+-{sd:.5f}  EXCESS z={z:+6.2f}")

    print("-" * 74)
    print("(A) r_raw = v - w :  TRUE vs ARTIFACT(independent v,w) baseline")
    print("-" * 74)
    decompose("raw ", lambda v, i: (v[0] - Ws[i][0], v[1] - Ws[i][1]))

    print("\n" + "-" * 74)
    print("(B) r_slip = v - M.w :  TRUE vs ARTIFACT baseline")
    print("-" * 74)
    decompose("slip", lambda v, i: (v[0] - MWs[i][0], v[1] - MWs[i][1]))

    print("\n" + "=" * 74)
    print("Reading: EXCESS z ~ 0 (stable) => the tautology IS pure subtraction")
    print("geometry (properly controlled now).  EXCESS z growing ~sqrt(N) => real")
    print("d<->x coupling that the coarse-marginal tests missed -- a lead to dig into")
    print("(then: which cells carry it, and does it sharpen a scalar readout of d).")


if __name__ == "__main__":
    main()
