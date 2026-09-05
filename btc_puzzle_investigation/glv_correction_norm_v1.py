#!/usr/bin/env python3
"""
glv_correction_norm_v1.py

Direction (3): where does the CM correction (the +-R flap) live in NORM terms?

The flap = P \\ (P ∩ omega^2 P) is the far-vertex "tips" of the rhombus that swing out
under 120-deg rotation. Far vertices carry the largest norm (N -> 3p/4). So the correction
should fire on the HIGH-NORM shell -- tying the 2-point CM law to the OTHER proved single-x
invariant, the norm-band law (norm_band_law_v1: s = N/p on [0,3/4], mean 1/6).

We bin every lattice point by norm-band s = N(eis X)/p (exact: bin = 16*N // p, twelve bins
over [0,3/4]) and report the flap-rate per band -- overall and inside the max-area sextant
pair (where the flap concentrates). Exact integers throughout.
"""
import random
from glv_fundamental_domain_law_v1 import make_lift, sextant, P_SECP, AP_SECP, BP_SECP
from lift_sextant_rhombus_law_proof_v2 import gauss_reduce, sector_props, enorm
from fractions import Fraction as F


def om(w):
    u, v = w
    return (-v, u - v)


def run(name, p, Xs, R1=None, R2=None):
    R1, R2, DET, reduce_P, eis = make_lift(p, R1, R2)
    props = sector_props(R1, R2)
    maxpair = set(sorted(range(6), key=lambda t: props[t])[-2:])

    NB = 12                                   # bins over s in [0, 3/4], width 1/16
    tot = [0] * NB; flp = [0] * NB
    tot_mx = [0] * NB; flp_mx = [0] * NB
    flap_norms = []; pure_norms = []
    for X in Xs:
        w = eis(X)
        Nrm = enorm(w)
        b = (16 * Nrm) // p                    # exact band index
        if b >= NB:
            b = NB - 1
        wr = om(w)
        c = (reduce_P(*wr)[0] - wr[0], reduce_P(*wr)[1] - wr[1])
        isflap = (c != (0, 0))
        tot[b] += 1; flp[b] += isflap
        if sextant(*w) in maxpair:
            tot_mx[b] += 1; flp_mx[b] += isflap
        (flap_norms if isflap else pure_norms).append(F(Nrm, p))

    print(f"\n=== {name} ===  max-area sextant pair = {sorted(maxpair)}")
    print(f"    band s=N/p     all: rate (n)          max-pair: rate (n)")
    for b in range(NB):
        lo = F(b, 16); hi = F(b + 1, 16)
        r = flp[b] / tot[b] if tot[b] else 0
        rm = flp_mx[b] / tot_mx[b] if tot_mx[b] else 0
        bar = "#" * int(round(r * 30))
        print(f"    [{float(lo):.4f},{float(hi):.4f})  {r:.3f} ({tot[b]:6d})    "
              f"{rm:.3f} ({tot_mx[b]:6d})  {bar}")
    if flap_norms and pure_norms:
        print(f"    flap norm-band s: min={float(min(flap_norms)):.4f} "
              f"mean={float(sum(flap_norms)/len(flap_norms)):.4f}  |  "
              f"pure s: max={float(max(pure_norms)):.4f} "
              f"mean={float(sum(pure_norms)/len(pure_norms)):.4f}")
        thr = min(flap_norms)
        below = sum(1 for s in pure_norms if s < thr)
        print(f"    lowest flap band = {thr} ; pure points below it = "
              f"{below}/{len(pure_norms)} (=> flap is the OUTER/high-norm shell)")


def main():
    print("=" * 70)
    print("Where the CM correction lives in NORM: the +-R flap vs the norm-band law")
    print("=" * 70)
    for p in (10009, 100003):
        run(f"full F_p p={p}", p, list(range(1, p)))
    rng = random.Random(2024)
    Xs = [rng.randrange(1, P_SECP) for _ in range(120000)]
    R1s, R2s = gauss_reduce((AP_SECP, BP_SECP), (-BP_SECP, AP_SECP - BP_SECP))
    run("secp uniform-X", P_SECP, Xs, R1=R1s, R2=R2s)


if __name__ == "__main__":
    main()
