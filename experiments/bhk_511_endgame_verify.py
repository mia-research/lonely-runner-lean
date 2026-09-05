"""
Numerical verification of the BHK Case 5.1.1 endgame (subcase_511) reconstruction.

Normalised units: v3 = 1, so x_i = v3 / v_i.
Established facts entering the endgame:
  - x4 in (25/32, 1)            [from 511_x4_bound: 25 v4 < 32 v3, and v3 < v4]
  - 0 < x5 < x4                 [v5 > v4 > v3 > 0]

Covering assumption => every 1234-gap [a,b] is contained in a single runner-5 block
  block(i) = [(i - 1/6) x5, (i + 1/6) x5],  i in Z, i >= 1.
"coverable(gap)" := exists integer i >= 1 with (i-1/6) x5 < a  and  b < (i+1/6) x5.
(strict, matching Lean's block_containment on open blocks)

Candidate 1234-gaps (all subset of the 123-gap [21/16, 11/6]):
  gap1  = [21/16, (11/6) x4]                      (runner-4 k=1..k=2 4-gap)
  gap2a = [13 x4 / 6, 11/6]     when 13 x4 <= 11  (runner-4 k=2..k=3 4-gap)
  gap2b = [21/16, 121/78]       when 13 x4  > 11  (runner-4 k=1..k=2 4-gap)

CLAIM to verify: for every valid (x4, x5), NOT (coverable(gap1) AND coverable(gap2)),
where gap2 = gap2a if 13 x4 <= 11 else gap2b.  (Hence runner 5 fails some gap =>
contradiction with covering.)

Also verifies the structural sub-claims used in the Lean proof:
  (S1) coverable(gap1) => i1 in {2,3}  and  19 x5 > 11 x4.
  (S2) branch B (13x4>11): gap2b never coverable (k>=2 from right, k<=1 from left).
  (S3) branch A k=2 impossible: needs x5 > 11/13 >= x4 (contra x5 < x4).
  (S4) branch A k=3 + gap1(i in{2,3}) impossible (disjoint x5 ranges).
"""
from fractions import Fraction as F

def blocks_covering(a, b, x5, imax=12):
    """integers i>=1 with (i-1/6)x5 < a and b < (i+1/6)x5 (strict)."""
    out = []
    for i in range(1, imax + 1):
        if (i - F(1,6)) * x5 < a and b < (i + F(1,6)) * x5:
            out.append(i)
    return out

def check_point(x4, x5):
    """Return (ok, info). ok=True means the argument yields a contradiction."""
    assert F(25,32) < x4 < 1
    assert 0 < x5 < x4
    g1 = (F(21,16), F(11,6) * x4)
    cov1 = blocks_covering(*g1, x5)
    if F(13,1) * x4 <= 11:
        branch = 'A'
        g2 = (F(13,1) * x4 / 6, F(11,6))
    else:
        branch = 'B'
        g2 = (F(21,16), F(121,78))
    cov2 = blocks_covering(*g2, x5)
    # The contradiction the proof derives: NOT both coverable.
    both = (len(cov1) > 0) and (len(cov2) > 0)
    return (not both), dict(branch=branch, cov1=cov1, cov2=cov2, g1=g1, g2=g2)

def main():
    # ---- structural checks on a fine rational grid -----------------------
    N = 480
    bad = []
    s1_violations = []
    cov1_iset = set()
    branchA_k_seen = set()
    branchB_cov2_nonempty = 0
    total = 0
    for p in range(1, N):
        x4 = F(25,32) + (F(1,1) - F(25,32)) * F(p, N)   # in (25/32, 1)
        if not (F(25,32) < x4 < 1):
            continue
        for q in range(1, N):
            x5 = x4 * F(q, N)                            # in (0, x4)
            if not (0 < x5 < x4):
                continue
            total += 1
            ok, info = check_point(x4, x5)
            if not ok:
                bad.append((x4, x5, info))
            # (S1): if gap1 coverable, i in {2,3} and 19 x5 > 11 x4
            if info['cov1']:
                cov1_iset |= set(info['cov1'])
                if not all(i in (2, 3) for i in info['cov1']):
                    s1_violations.append(('i-range', x4, x5, info['cov1']))
                if not (19 * x5 > 11 * x4):
                    s1_violations.append(('19x5>11x4', x4, x5, info['cov1']))
            # (S2): branch B gap2b never coverable
            if info['branch'] == 'B' and info['cov2']:
                branchB_cov2_nonempty += 1
            # branch A: which k can cover gap2a
            if info['branch'] == 'A':
                branchA_k_seen |= set(info['cov2'])

    print(f"grid points tested: {total}")
    print(f"MAIN CLAIM violations (both gaps coverable): {len(bad)}")
    for x4, x5, info in bad[:8]:
        print("   ", float(x4), float(x5), info['branch'], info['cov1'], info['cov2'])
    print(f"(S1) cov1 i-values ever seen: {sorted(cov1_iset)}  (expect subset of {{2,3}})")
    print(f"(S1) violations of [i in 2,3] or [19x5>11x4]: {len(s1_violations)}")
    for v in s1_violations[:8]:
        print("   ", v[0], float(v[1]), float(v[2]), v[3])
    print(f"(S2) branch-B points where gap2b WAS coverable: {branchB_cov2_nonempty}  (expect 0)")
    print(f"branch-A k-values that ever cover gap2a: {sorted(branchA_k_seen)}")

    # ---- (S2) exact: branch B bucket argument, symbolic over r=v5/v3 -----
    # gap2b=[21/16,121/78]; containment gives k with (121/78) r < k+1/6 and k-1/6 < (21/16) r.
    # width => (149/624) r < 1/3 => r < 208/149.  r>1.
    # k > (121/78) r - 1/6 > 18/13  => k>=2 ; k < (21/16) r + 1/6 < (21/16)(208/149)+1/6
    rmax = F(208,149)
    k_upper = F(21,16) * rmax + F(1,6)
    k_lower_at_r1 = F(121,78) * 1 - F(1,6)
    print("\n(S2 exact) r < 208/149 =", float(rmax))
    print("   upper bound on k:  (21/16)(208/149)+1/6 =", float(k_upper), " < 2 ?", k_upper < 2)
    print("   lower bound on k:  (121/78)(1)-1/6      =", float(k_lower_at_r1), " > 1 ?", k_lower_at_r1 > 1)
    print("   => k>=2 and k<=1: contradiction =", (k_upper < 2) and (k_lower_at_r1 > 1))

    # ---- (S3) exact: branch A k=2 needs x5 > 11/13 >= x4 > x5 ------------
    # k=2 right edge past gap2a right end 11/6: (13/6) x5 > 11/6 => x5 > 11/13.
    # branch A: 13 x4 <= 11 => x4 <= 11/13.  x5 < x4 <= 11/13 < x5 contra.
    print("\n(S3 exact) branch A k=2: x5>11/13 but x5<x4<=11/13 -> contradiction (11/13 =",
          float(F(11,13)), ")")

    # ---- (S4) exact: branch A k=3 vs gap1 i in {2,3} --------------------
    # branch A k=3: (17/6)x5 < (13/6)x4 => 17 x5 < 13 x4 => x5 < (13/17) x4
    #               (19/6)x5 > 11/6     => 19 x5 > 11   => x5 > 11/19
    # gap1 i=3: (17/6)x5 < 21/16 => x5 < 63/136 ;  (19/6)x5 > (11/6)x4 => 19 x5 > 11 x4
    # gap1 i=2: (11/6)x5 < 21/16 => x5 < 63/88  ;  (13/6)x5 > (11/6)x4 => 13 x5 > 11 x4 => x5 > 11x4/13
    # Sub-branch gap1=i3: x5 < 63/136 ~0.463 but k3 => x5 > 11/19 ~0.579. contra.
    # Sub-branch gap1=i2: x5 > 11x4/13 ; k3 => x5 < 13x4/17 ; 11/13 > 13/17 => 11x4/13 > 13x4/17 > x5. contra.
    print("\n(S4 exact) branch A, k=3:")
    print("   gap1=i3 sub-branch: x5<63/136=", float(F(63,136)), " vs k3: x5>11/19=", float(F(11,19)),
          " -> contra:", F(63,136) <= F(11,19))
    print("   gap1=i2 sub-branch: need 11/13 > 13/17 :", F(11,13) > F(13,17),
          " (so 11x4/13 > 13x4/17 >= x5 contradicts x5>11x4/13)")

if __name__ == "__main__":
    main()
