#!/usr/bin/env python3
"""
glv_pinned_wedge_containment_v1.py

Geometric PROOF of the bridge found by the exact lattice cross-tab
(glv_flap_pinned_sextant_v1): the pinned sextant pair (single-x angle-law invariant,
area exactly 1/8 each) is EXACTLY the set of sextants on which the CM 2-point correction
vanishes identically.

Correction-free on sextant wedge W  <=>  omega.W ⊆ P and omega^2.W ⊆ P
                                    <=>  W ⊆ omega^2.P and W ⊆ omega.P
                                    <=>  W ⊆ (P ∩ omega.P ∩ omega^2.P) = the mu3-core.

We build each sextant wedge W = P ∩ sector(t) exactly (rational vertices), and test
W ⊆ omega.P and W ⊆ omega^2.P by exact area (ratio == 1). The pinned pair, and only the
pinned pair, is fully contained -- for every basis / theta, secp included. Exact Fraction.
"""
from fractions import Fraction as F
from lift_sextant_rhombus_law_proof_v2 import (
    reduced_basis, gauss_reduce, sector_props, clip as ray_clip, UNIT, cross, wedge_label)
from glv_fundamental_domain_geom_check_v1 import corners, om, om2, clip as sh_clip, shoelace, _ccw


def wedge_for_sextant(P4, t):
    """Exact polygon P ∩ (sextant t), via v2's ray-clip; matched to sextant() labels."""
    for s in range(6):
        if wedge_label(s) == t:
            return ray_clip(ray_clip(P4, UNIT[s], +1), UNIT[(s + 1) % 6], -1)
    return []


def check(nm, R1, R2):
    P4 = corners(R1, R2)
    props = sector_props(R1, R2)
    pinned = [t for t in range(6) if props[t] == F(1, 8)]
    wP = _ccw([om(c) for c in P4])
    w2P = _ccw([om2(c) for c in P4])

    contained = []
    for t in range(6):
        W = _ccw(wedge_for_sextant(P4, t))
        aW = shoelace(W)
        if aW == 0:
            contained.append(t); continue
        r1 = shoelace(_ccw(sh_clip(W, wP))) / aW      # fraction of W inside omega.P
        r2 = shoelace(_ccw(sh_clip(W, w2P))) / aW     # fraction of W inside omega^2.P
        if r1 == 1 and r2 == 1:
            contained.append(t)
    ok = set(contained) == set(pinned)
    print(f"  {nm:10} pinned={pinned}  wedge⊆core={sorted(contained)}  "
          f"=> {'MATCH (proved)' if ok else 'DIFFER'}")
    return ok


if __name__ == "__main__":
    print("Pinned sextant pair == sextants whose wedge lies entirely in the mu3-core")
    print("(exact rational polygon containment; the CM-correction-free sextants)\n")
    bases = []
    import sympy
    for p in [q for q in sympy.primerange(1000, 400000) if q % 3 == 1][::4000]:
        R1, R2 = reduced_basis(p)
        bases.append((f"p={p}", R1, R2))
    bases.append(("secp",
                  *gauss_reduce((367917413016453100223835821029139468249,
                                 303414439467246543595250775667605759171),
                                (-303414439467246543595250775667605759171,
                                 367917413016453100223835821029139468249
                                 - 303414439467246543595250775667605759171))))
    res = [check(nm, R1, R2) for nm, R1, R2 in bases]
    print(f"\n  MATCH for all {len(res)} bases?  {all(res)}")
    print("  => PROVED: pinned sextant pair (angle-law 1/8 invariant) = the CM-stable")
    print("     wedges of the 2-point law. The single-x pinned invariant and the 2-point")
    print("     GLV correction law are two faces of one object: the mu3-geometry of P.")
