#!/usr/bin/env python3
"""
test_anew_identification_controls_v1.py  --  2026-07-30

Firing controls for test_anew_identification_v1.py.  Without these, T1/T2/T3 are
self-consistency checks from an instrument never shown able to REJECT.

FC1  T1 (#C(F_p) = p+1-a_p, i.e. b_1 = 0) run at p = 1 mod 4, where the mu_4
     conjugation argument does NOT force b_1 = 0.  If T1 still passes everywhere the
     statistic is vacuous.  EXPECT: failures.
FC2  T2 (b_2 = S) fed a PERTURBED S (S+1).  EXPECT: total failure.
FC3  T2 fed the S of a DIFFERENT B at the same prime (a real, correctly-computed value
     for the wrong cell).  EXPECT: failure wherever the two S differ.

Exact integers only.
"""
import importlib.util, sys, os

spec = importlib.util.spec_from_file_location(
    "base", os.path.join(os.path.dirname(os.path.abspath(__file__)),
                         "test_anew_identification_v1.py"))
# import the helpers without re-running the report
src = open(spec.origin).read().split('print("=" * 96)')[0]
ns = {}
exec(compile(src, spec.origin, "exec"), ns)
count_C_Fp, count_C_Fp2 = ns["count_C_Fp"], ns["count_C_Fp2"]
a_p_of_E, S_exact = ns["a_p_of_E"], ns["S_exact"]

print("=" * 86)
print("FC1 -- T1 at p = 1 mod 4 (b_1 = 0 NOT forced there).  Must FAIL somewhere.")
print("=" * 86)
f1 = [0, 0]
for p in [5, 13, 17, 29, 37, 41, 53, 61]:
    for B in [7, 2, 1]:
        if B % p == 0:
            continue
        ap = a_p_of_E(p, B)
        held = (count_C_Fp(p, B) == p + 1 - ap)
        f1[0 if held else 1] += 1
        print(f"   p={p:>3} B={B:>2}  #C(F_p)={count_C_Fp(p,B):>5}  p+1-a_p={p+1-ap:>5}  "
              f"{'holds' if held else 'FAILS  <-- control fires'}")
print(f"\n   FC1: {f1[0]} hold / {f1[1]} fail  ->  "
      f"{'FIRES (statistic discriminates)' if f1[1] else 'DOES NOT FIRE -- T1 is VACUOUS'}")

print()
print("=" * 86)
print("FC2 / FC3 -- T2 (b_2 = S) with a perturbed and a mis-assigned S.  Must FAIL.")
print("=" * 86)
f2 = [0, 0]
f3 = [0, 0]
for p in [7, 19, 31, 43]:
    # B = 0 mod p makes y^2 = x^3 + B singular -- must be excluded (same skip as the main run)
    Bs = [B for B in (7, 2, 1) if B % p != 0]
    Ss = {}
    for B in Bs:
        Ss[B] = S_exact(p, B)[0]
    for B in Bs:
        ap = a_p_of_E(p, B)
        cC2 = count_C_Fp2(p, B)
        true_S = Ss[B]
        rhs = lambda S: p * p + 1 - ap * ap + 2 * p + 2 * S
        assert cC2 == rhs(true_S), "true S must pass"
        # FC2: perturb
        bad = (cC2 == rhs(true_S + 1))
        f2[1 if bad else 0] += 1
        # FC3: S of a different B (only counts when the two values differ)
        other = [Ss[b] for b in Ss if b != B and Ss[b] != true_S]
        for o in other:
            f3[1 if cC2 == rhs(o) else 0] += 1
        print(f"   p={p:>3} B={B:>2}  S={true_S:>6}  perturbed S+1 accepted? "
              f"{'YES (BAD)' if bad else 'no  <- fires'}   "
              f"other-B S values tried: {len(other)}")
print(f"\n   FC2: rejected {f2[0]}/{f2[0]+f2[1]} perturbations  ->  "
      f"{'FIRES' if f2[1] == 0 else 'DOES NOT FIRE'}")
print(f"   FC3: rejected {f3[0]}/{f3[0]+f3[1]} mis-assigned S  ->  "
      f"{'FIRES' if f3[1] == 0 else 'DOES NOT FIRE'}")

print()
print("=" * 86)
print("FORCED / UNFORCED accounting for the 38 rows of the main run")
print("=" * 86)
print("""
  T1 (b_1 = 0):  FORCED by the mu_4 conjugation argument that section A1.1 derives.
     All 38 rows are an INSTRUMENT CHECK ON THE CODE, not evidence for b_1 = 0.
     (This matches RESULT_anew_isogeny_type_correction_v1.md:32, which grades its own
     22/22 the same way.)  FC1 shows the check is not vacuous as a check.

  T3 (m = S/p matches the A2.1 branch):  S depends on B only through chi_3(B), and the
     two cubic NON-residue classes give the same S (both = -J, since omega+omega^2 = -1).
     So per prime the distinct outcomes are at most 2 (residue / non-residue), and at
     p = 11 mod 12 exactly 1 (S = 2p, B-independent).
       p = 11 mod 12 : 4 primes x 1 branch  =  4 distinct
       p =  7 mod 12 : 4 primes x 2 branches = 8 distinct
       => 12 DISTINCT configurations, not 38.  26 of the 38 rows are forced repeats.

  T2 (b_2 = S):  the natural unit is (p,B), because #C(F_p^2) and a_p both vary with B
     even where S does not.  Each row is a separate equation between three independently
     computed integers, so 38 rows = 38 equations -- but they test the point-count
     DICTIONARY, which is a step of the derivation, not the m-law.  Zero independent
     weight for the m-law itself.
""")
