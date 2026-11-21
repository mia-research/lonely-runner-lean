import Mathlib

/-!
# UniformAnchored_R1: per-base-instance killing-shape lemmas for the R1-edge
anchored cycles

GENERATED FILE (uniform_gen_anchored_v1.py, 6 theorems; regenerate, do not edit).  The
per-base-instance forms of the uniformity lemma for the ANCHORED family's killing shapes
of the v3 uniformity lemma: per shape and realized (offset pattern tau, orbit base k)
occurrence, the shape's cycle product P_tau(k) = A_tau(k)/B_tau(k) -- the product of the
cycle's literal row factors at the realized laps -- is strictly below 1.  Each theorem is
an UNCONDITIONAL Q fact (the laps are realized integer literals; the kill criterion
"P <= 1 with a strict edge" is met as P < 1, the strict candidate edge carried on every
cycle).  Shapes with no free slots (every lap pinned by region/base rows -- the low-zone
cycles) emit one base-independent theorem `shape_a<id>_const` each; the multi-base ones
among them are the verbatim absolute low-zone cycles (89/95 at (12,11), 267/299, 81/89).

Provenance: experiments/n8/uniform_gen_anchored_v1.py replays the nonvacuous anchored
members (y6k15/y6k17/y6k25 -- the realized bases {15, 17, 25}; the regime beyond the base
period is vacuous, E892) through the instrument module (import of
v3_uniformity_lemma_v1.py), validates the replay exactly (rejection multisets
19/19, products 145/145, irred corrections 9/9),
clusters the 145 killing cycles into 58 shapes (greedy clique cover, role rule:
abs / tied-to-base / free on window-determined slots -- candidate lap, death-frontier lap,
anchored reading-6 laps), and for each realized (pattern, base) occurrence emits the
product inequality with the deficit D_tau(k) = B_tau(k) - A_tau(k) recorded in the
docstring (exact Fractions; the pattern's killing-set kind over k >= 13 noted for
provenance -- ALL means the pattern kills on the whole realized-regime half-line, SEGMENTS
means only on the stated intervals, which always contain the occurrence base).
Every proof is a constant `norm_num` evaluation -- no folds, no new axioms.  Every theorem
carries #print axioms; the accepted profile is the standard three (propext,
Classical.choice, Quot.sound).
-/

namespace Fresh.UniformAnchored

-- a001 [1-edge cycle] 4->(closed) | cand_entry
--   roles: abs=7, abs=6; 4 instances at bases [15]; worst realized 49/55
/-- 4->(closed) | cand_entry | pattern tau=() (all laps absolute): the cycle's row factors (cand_entry@(7, 6)) have product 49/55 < 1, i.e. the deficit D_tau = B_tau - A_tau at the realized base is 6 > 0 (kind ALL over k >= 13: [13,inf); Sturm real-half-line: D > 0).  Unconditional Q fact. -/
theorem shape_a001_const : ((49:ℚ) / (55:ℚ)) < 1 := by
  norm_num
#print axioms shape_a001_const

-- a002 [1-edge cycle] 5->(closed) | cand_entry
--   roles: abs=12, abs=11; 9 instances at bases [15, 17]; worst realized 89/95
/-- 5->(closed) | cand_entry | pattern tau=() (all laps absolute): the cycle's row factors (cand_entry@(12, 11)) have product 89/95 < 1, i.e. the deficit D_tau = B_tau - A_tau at the realized base is 6 > 0 (kind ALL over k >= 13: [13,inf); Sturm real-half-line: D > 0).  Unconditional Q fact. -/
theorem shape_a002_const : ((89:ℚ) / (95:ℚ)) < 1 := by
  norm_num
#print axioms shape_a002_const

-- a003 [1-edge cycle] 5->(closed) | cand_progress
--   roles: abs=10, abs=11; 6 instances at bases [15, 17]; worst realized 81/89
/-- 5->(closed) | cand_progress | pattern tau=() (all laps absolute): the cycle's row factors (cand_progress@(10, 11)) have product 81/89 < 1, i.e. the deficit D_tau = B_tau - A_tau at the realized base is 8 > 0 (kind ALL over k >= 13: [13,inf); Sturm real-half-line: D > 0).  Unconditional Q fact. -/
theorem shape_a003_const : ((81:ℚ) / (89:ℚ)) < 1 := by
  norm_num
#print axioms shape_a003_const

-- a004 [1-edge cycle] 6->(closed) | cand_entry
--   roles: free+1..+2, free+0..+1; 6 instances at bases [15, 25]; worst realized 67/69
/-- 6->(closed) | cand_entry | pattern tau=(1,0) at base k=25: the cycle's row factors (cand_entry@(26, 25)) have product 67/69 < 1, i.e. the deficit D_tau = B_tau - A_tau at the realized base is 6 > 0 (kind ALL over k >= 13: [13,inf); Sturm real-half-line: D > 0).  Unconditional Q fact. -/
theorem shape_a004_pat1_k25 : ((201:ℚ) / (207:ℚ)) < 1 := by
  norm_num
#print axioms shape_a004_pat1_k25

/-- 6->(closed) | cand_entry | pattern tau=(2,1) at base k=15: the cycle's row factors (cand_entry@(17, 16)) have product 43/45 < 1, i.e. the deficit D_tau = B_tau - A_tau at the realized base is 6 > 0 (kind ALL over k >= 13: [13,inf); Sturm real-half-line: D > 0).  Unconditional Q fact. -/
theorem shape_a004_pat2_k15 : ((129:ℚ) / (135:ℚ)) < 1 := by
  norm_num
#print axioms shape_a004_pat2_k15

-- a005 [1-edge cycle] 6->(closed) | cand_progress
--   roles: abs=24, abs=25; 4 instances at bases [25]; worst realized 193/201
/-- 6->(closed) | cand_progress | pattern tau=() (all laps absolute): the cycle's row factors (cand_progress@(24, 25)) have product 193/201 < 1, i.e. the deficit D_tau = B_tau - A_tau at the realized base is 8 > 0 (kind ALL over k >= 13: [13,inf); Sturm real-half-line: D > 0).  Unconditional Q fact. -/
theorem shape_a005_const : ((193:ℚ) / (201:ℚ)) < 1 := by
  norm_num
#print axioms shape_a005_const

