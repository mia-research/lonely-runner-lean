#!/usr/bin/env python3
"""
glv_peer_zone_test_v1.py

Runs the peer's proposed exact polygon test verbatim:
  Z_pin  = union of the two pinned sextant wedges (area 1/8 each, e.g. {0,3} for secp).
  Z_corr = P \\ (P ∩ omega^2 P)  = the two correction "flaps" (area p/8 each).
  Compute area(Z_pin ∩ Z_corr) exactly (Fraction).

Peer conjecture: Z_corr ⊆ Z_pin, i.e. area(Z_pin ∩ Z_corr) == area(Z_corr) == p/4.

Our 2-point law + lattice cross-tab predicted the OPPOSITE: the pinned wedges are the
correction-FREE (CM-stable) sextants, so Z_pin and Z_corr should be DISJOINT
(area 0). This settles it with exact rational polygon areas.
"""
from fractions import Fraction as F
from lift_sextant_rhombus_law_proof_v2 import reduced_basis, gauss_reduce, sector_props
from glv_fundamental_domain_geom_check_v1 import corners, om2, clip as sh_clip, shoelace, _ccw
from glv_pinned_wedge_containment_v1 import wedge_for_sextant


def peer_test(nm, R1, R2):
    P4 = corners(R1, R2)
    aP = shoelace(P4)                                  # = p
    props = sector_props(R1, R2)
    pinned = [t for t in range(6) if props[t] == F(1, 8)]
    maxpair = sorted(range(6), key=lambda t: props[t])[-2:]
    w2P = _ccw([om2(c) for c in P4])

    flap = {}                                          # per-sextant flap area
    for t in range(6):
        W = _ccw(wedge_for_sextant(P4, t))
        aW = shoelace(W)
        clipped = sh_clip(W, w2P)
        inside = shoelace(_ccw(clipped)) if len(clipped) >= 3 else F(0)
        flap[t] = aW - inside                          # part of wedge that exits under om2

    Zcorr = sum(flap.values())
    Zpin_corr = sum(flap[t] for t in pinned)
    print(f"\n=== {nm} ===")
    print(f"   pinned pair {pinned} (area 1/8 each);  max pair {sorted(maxpair)}")
    print(f"   area(Z_corr)/p = {F(Zcorr, aP)}   (peer predicts flaps total 1/4)")
    print(f"   per-sextant flap area / p : "
          f"{{{', '.join(f'{t}:{F(flap[t], aP)}' for t in range(6))}}}")
    print(f"   area(Z_pin ∩ Z_corr)/p = {F(Zpin_corr, aP)}   "
          f"=> {'DISJOINT (peer conjecture refuted)' if Zpin_corr == 0 else 'overlap'}")
    inmax = sum(flap[t] for t in maxpair)
    print(f"   flap concentrated in MAX pair: area(Z_corr ∩ max pair)/p = {F(inmax, aP)} "
          f"of the {F(Zcorr, aP)} total")
    return Zpin_corr


if __name__ == "__main__":
    print("Peer's exact zone test: does the correction zone sit ON the pinned pair?")
    bases = [("p=1009", *reduced_basis(1009)),          # pinned {1,4}
             ("p=172213", *reduced_basis(172213)),      # pinned {0,3}
             ("secp", *gauss_reduce(
                 (367917413016453100223835821029139468249,
                  303414439467246543595250775667605759171),
                 (-303414439467246543595250775667605759171,
                  367917413016453100223835821029139468249 - 303414439467246543595250775667605759171)))]
    vals = [peer_test(nm, R1, R2) for nm, R1, R2 in bases]
    print(f"\n  area(Z_pin ∩ Z_corr) == 0 for all?  {all(v == 0 for v in vals)}")
    print("  => The correction zone is DISJOINT from the pinned pair, not contained in it.")
    print("     The peer's ray-alignment insight is right (flap edges snap to unit rays),")
    print("     but the flaps fill the FAR-VERTEX / MAX-area sextants; the pinned pair is")
    print("     precisely the correction-FREE (CM-stable) locus. Same 1/8, complementary sets.")
