import Mathlib

/-!
# UniformAnchored_R3: per-base-instance killing-shape lemmas for the R3-edge
anchored cycles

GENERATED FILE (uniform_gen_anchored_v1.py, 20 theorems; regenerate, do not edit).  The
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

-- a019 [3-edge cycle] 1->4->5->(closed) | cand_entry+z_entry+z_entry
--   roles: abs=3, abs=6, abs=4, abs=7, abs=5, abs=1; 3 instances at bases [15]; worst realized 8379/9269
/-- 1->4->5->(closed) | cand_entry+z_entry+z_entry | pattern tau=() (all laps absolute): the cycle's row factors (cand_entry@(3, 6); z_entry@(4, 7); z_entry@(5, 1)) have product 8379/9269 < 1, i.e. the deficit D_tau = B_tau - A_tau at the realized base is 2670 > 0 (kind ALL over k >= 13: [13,inf); Sturm real-half-line: D > 0).  Unconditional Q fact. -/
theorem shape_a019_const : ((49:ℚ) / (23:ℚ)) * ((57:ℚ) / (31:ℚ)) * ((9:ℚ) / (39:ℚ)) < 1 := by
  norm_num
#print axioms shape_a019_const

-- a020 [3-edge cycle] 1->5->2->(closed) | cand_entry+z_entry+z_entry
--   roles: abs=3, abs=11, abs=7, abs=2, abs=3, abs=2; 2 instances at bases [15]; worst realized 25721/29095
/-- 1->5->2->(closed) | cand_entry+z_entry+z_entry | pattern tau=() (all laps absolute): the cycle's row factors (cand_entry@(3, 11); z_entry@(7, 2); z_entry@(3, 2)) have product 25721/29095 < 1, i.e. the deficit D_tau = B_tau - A_tau at the realized base is 3374 > 0 (kind ALL over k >= 13: [13,inf); Sturm real-half-line: D > 0).  Unconditional Q fact. -/
theorem shape_a020_const : ((89:ℚ) / (23:ℚ)) * ((17:ℚ) / (55:ℚ)) * ((17:ℚ) / (23:ℚ)) < 1 := by
  norm_num
#print axioms shape_a020_const

-- a021 [3-edge cycle] 1->6->3->(closed) | cand_entry+z_entry+z_entry
--   roles: abs=3, abs=16, abs=15, abs=4, abs=2, abs=1; 1 instances at bases [15]; worst realized 12771/13685
/-- 1->6->3->(closed) | cand_entry+z_entry+z_entry | pattern tau=() (all laps absolute): the cycle's row factors (cand_entry@(3, 16); z_entry@(15, 4); z_entry@(2, 1)) have product 12771/13685 < 1, i.e. the deficit D_tau = B_tau - A_tau at the realized base is 2742 > 0 (kind ALL over k >= 13: [13,inf); Sturm real-half-line: D > 0).  Unconditional Q fact. -/
theorem shape_a021_const : ((129:ℚ) / (23:ℚ)) * ((33:ℚ) / (119:ℚ)) * ((9:ℚ) / (15:ℚ)) < 1 := by
  norm_num
#print axioms shape_a021_const

-- a022 [3-edge cycle] 1->6->5->(closed) | cand_entry+z_entry+z_entry
--   roles: abs=3, abs=16, abs=10, abs=7, abs=5, abs=1; 1 instances at bases [15]; worst realized 22059/23621
/-- 1->6->5->(closed) | cand_entry+z_entry+z_entry | pattern tau=() (all laps absolute): the cycle's row factors (cand_entry@(3, 16); z_entry@(10, 7); z_entry@(5, 1)) have product 22059/23621 < 1, i.e. the deficit D_tau = B_tau - A_tau at the realized base is 4686 > 0 (kind ALL over k >= 13: [13,inf); Sturm real-half-line: D > 0).  Unconditional Q fact. -/
theorem shape_a022_const : ((129:ℚ) / (23:ℚ)) * ((57:ℚ) / (79:ℚ)) * ((9:ℚ) / (39:ℚ)) < 1 := by
  norm_num
#print axioms shape_a022_const

-- a023 [3-edge cycle] 2->4->5->(closed) | cand_entry+z_entry+z_entry
--   roles: abs=4, abs=6, abs=4, abs=7, abs=7, abs=2; 3 instances at bases [15]; worst realized 47481/52855
/-- 2->4->5->(closed) | cand_entry+z_entry+z_entry | pattern tau=() (all laps absolute): the cycle's row factors (cand_entry@(4, 6); z_entry@(4, 7); z_entry@(7, 2)) have product 47481/52855 < 1, i.e. the deficit D_tau = B_tau - A_tau at the realized base is 5374 > 0 (kind ALL over k >= 13: [13,inf); Sturm real-half-line: D > 0).  Unconditional Q fact. -/
theorem shape_a023_const : ((49:ℚ) / (31:ℚ)) * ((57:ℚ) / (31:ℚ)) * ((17:ℚ) / (55:ℚ)) < 1 := by
  norm_num
#print axioms shape_a023_const

-- a024 [3-edge cycle] 2->6->5->(closed) | cand_entry+z_entry+z_entry
--   roles: abs=4, abs=16, abs=10, abs=7, abs=7, abs=2; 1 instances at bases [15]; worst realized 125001/134695
/-- 2->6->5->(closed) | cand_entry+z_entry+z_entry | pattern tau=() (all laps absolute): the cycle's row factors (cand_entry@(4, 16); z_entry@(10, 7); z_entry@(7, 2)) have product 125001/134695 < 1, i.e. the deficit D_tau = B_tau - A_tau at the realized base is 9694 > 0 (kind ALL over k >= 13: [13,inf); Sturm real-half-line: D > 0).  Unconditional Q fact. -/
theorem shape_a024_const : ((129:ℚ) / (31:ℚ)) * ((57:ℚ) / (79:ℚ)) * ((17:ℚ) / (55:ℚ)) < 1 := by
  norm_num
#print axioms shape_a024_const

-- a025 [3-edge cycle] 2->6->5->(closed) | cand_entry+z_entry+z_entry
--   roles: abs=4, abs=25, abs=9, abs=5, abs=5, abs=1; 4 instances at bases [25]; worst realized 24723/28613
/-- 2->6->5->(closed) | cand_entry+z_entry+z_entry | pattern tau=() (all laps absolute): the cycle's row factors (cand_entry@(4, 25); z_entry@(9, 5); z_entry@(5, 1)) have product 24723/28613 < 1, i.e. the deficit D_tau = B_tau - A_tau at the realized base is 11670 > 0 (kind ALL over k >= 13: [13,inf); Sturm real-half-line: D > 0).  Unconditional Q fact. -/
theorem shape_a025_const : ((201:ℚ) / (31:ℚ)) * ((41:ℚ) / (71:ℚ)) * ((9:ℚ) / (39:ℚ)) < 1 := by
  norm_num
#print axioms shape_a025_const

-- a026 [3-edge cycle] 3->5->2->(closed) | cand_entry+z_entry+z_irred
--   roles: abs=5, abs=11, abs=7, abs=2, abs=4, abs=3; 2 instances at bases [15]; worst realized 46903/53625
/-- 3->5->2->(closed) | cand_entry+z_entry+z_irred | pattern tau=() (all laps absolute): the cycle's row factors (cand_entry@(5, 11); z_entry@(7, 2); z_irred@(4, 3)) have product 46903/53625 < 1, i.e. the deficit D_tau = B_tau - A_tau at the realized base is 6722 > 0 (kind ALL over k >= 13: [13,inf); Sturm real-half-line: D > 0).  Unconditional Q fact. -/
theorem shape_a026_const : ((89:ℚ) / (39:ℚ)) * ((17:ℚ) / (55:ℚ)) * ((31:ℚ) / (25:ℚ)) < 1 := by
  norm_num
#print axioms shape_a026_const

-- a027 [3-edge cycle] 3->5->6->(closed) | cand_entry+z_entry+z_entry
--   roles: abs=5, abs=11, abs=6, free-8..-7, tied=base, abs=4; 4 instances at bases [15, 17]; worst realized 4895/5593
/-- 3->5->6->(closed) | cand_entry+z_entry+z_entry | pattern tau=(-8) at base k=17: the cycle's row factors (cand_entry@(5, 11); z_entry@(6, 9); z_entry@(17, 4)) have product 71467/82485 < 1, i.e. the deficit D_tau = B_tau - A_tau at the realized base is 33054 > 0 (kind FINITE over k >= 13: [13,20]; Sturm real-half-line: real roots in [lo,big)=1).  Unconditional Q fact. -/
theorem shape_a027_pat1_k17 : ((89:ℚ) / (39:ℚ)) * ((73:ℚ) / (47:ℚ)) * ((33:ℚ) / (135:ℚ)) < 1 := by
  norm_num
#print axioms shape_a027_pat1_k17

/-- 3->5->6->(closed) | cand_entry+z_entry+z_entry | pattern tau=(-7) at base k=15: the cycle's row factors (cand_entry@(5, 11); z_entry@(6, 8); z_entry@(15, 4)) have product 4895/5593 < 1, i.e. the deficit D_tau = B_tau - A_tau at the realized base is 27222 > 0 (kind FINITE over k >= 13: [13,18]; Sturm real-half-line: real roots in [lo,big)=1).  Unconditional Q fact. -/
theorem shape_a027_pat2_k15 : ((89:ℚ) / (39:ℚ)) * ((65:ℚ) / (47:ℚ)) * ((33:ℚ) / (119:ℚ)) < 1 := by
  norm_num
#print axioms shape_a027_pat2_k15

-- a028 [3-edge cycle] 4->5->6->(closed) | cand_entry+z_entry+z_entry
--   roles: abs=7, abs=11, abs=6, abs=8, abs=8, abs=3; 4 instances at bases [15]; worst realized 28925/32571
/-- 4->5->6->(closed) | cand_entry+z_entry+z_entry | pattern tau=() (all laps absolute): the cycle's row factors (cand_entry@(7, 11); z_entry@(6, 8); z_entry@(8, 3)) have product 28925/32571 < 1, i.e. the deficit D_tau = B_tau - A_tau at the realized base is 18230 > 0 (kind ALL over k >= 13: [13,inf); Sturm real-half-line: D > 0).  Unconditional Q fact. -/
theorem shape_a028_const : ((89:ℚ) / (55:ℚ)) * ((65:ℚ) / (47:ℚ)) * ((25:ℚ) / (63:ℚ)) < 1 := by
  norm_num
#print axioms shape_a028_const

-- a029 [3-edge cycle] 4->6->5->(closed) | cand_entry+z_entry+z_entry
--   roles: abs=7, abs=16, abs=10, abs=7, abs=6, abs=3; 1 instances at bases [15]; worst realized 36765/40843
/-- 4->6->5->(closed) | cand_entry+z_entry+z_entry | pattern tau=() (all laps absolute): the cycle's row factors (cand_entry@(7, 16); z_entry@(10, 7); z_entry@(6, 3)) have product 36765/40843 < 1, i.e. the deficit D_tau = B_tau - A_tau at the realized base is 20390 > 0 (kind ALL over k >= 13: [13,inf); Sturm real-half-line: D > 0).  Unconditional Q fact. -/
theorem shape_a029_const : ((129:ℚ) / (55:ℚ)) * ((57:ℚ) / (79:ℚ)) * ((25:ℚ) / (47:ℚ)) < 1 := by
  norm_num
#print axioms shape_a029_const

-- a030 [3-edge cycle] 4->6->5->(closed) | cand_entry+z_entry+z_entry
--   roles: abs=8, abs=25, abs=9, abs=5, abs=8, abs=4; 4 instances at bases [25]; worst realized 30217/31311
/-- 4->6->5->(closed) | cand_entry+z_entry+z_entry | pattern tau=() (all laps absolute): the cycle's row factors (cand_entry@(8, 25); z_entry@(9, 5); z_entry@(8, 4)) have product 30217/31311 < 1, i.e. the deficit D_tau = B_tau - A_tau at the realized base is 9846 > 0 (kind ALL over k >= 13: [13,inf); Sturm real-half-line: D > 0).  Unconditional Q fact. -/
theorem shape_a030_const : ((201:ℚ) / (63:ℚ)) * ((41:ℚ) / (71:ℚ)) * ((33:ℚ) / (63:ℚ)) < 1 := by
  norm_num
#print axioms shape_a030_const

-- a031 [3-edge cycle] 5->4->2->(closed) | cand_entry+z_irred+z_entry
--   roles: abs=12, abs=6, abs=3, abs=5, abs=2, abs=6; 1 instances at bases [15]; worst realized 55223/58425
/-- 5->4->2->(closed) | cand_entry+z_irred+z_entry | pattern tau=() (all laps absolute): the cycle's row factors (cand_entry@(12, 6); z_irred@(3, 5); z_entry@(2, 6)) have product 55223/58425 < 1, i.e. the deficit D_tau = B_tau - A_tau at the realized base is 3202 > 0 (kind ALL over k >= 13: [13,inf); Sturm real-half-line: D > 0).  Unconditional Q fact. -/
theorem shape_a031_const : ((49:ℚ) / (95:ℚ)) * ((23:ℚ) / (41:ℚ)) * ((49:ℚ) / (15:ℚ)) < 1 := by
  norm_num
#print axioms shape_a031_const

-- a032 [3-edge cycle] 5->6->3->(closed) | cand_entry+z_entry+z_progress
--   roles: abs=12, abs=16, abs=15, abs=4, abs=8, abs=3; 1 instances at bases [15]; worst realized 55341/56525
/-- 5->6->3->(closed) | cand_entry+z_entry+z_progress | pattern tau=() (all laps absolute): the cycle's row factors (cand_entry@(12, 16); z_entry@(15, 4); z_progress@(8, 3)) have product 55341/56525 < 1, i.e. the deficit D_tau = B_tau - A_tau at the realized base is 5920 > 0 (kind ALL over k >= 13: [13,inf); Sturm real-half-line: D > 0).  Unconditional Q fact. -/
theorem shape_a032_const : ((129:ℚ) / (95:ℚ)) * ((33:ℚ) / (119:ℚ)) * ((65:ℚ) / (25:ℚ)) < 1 := by
  norm_num
#print axioms shape_a032_const

-- a033 [3-edge cycle] 6->4->5->(closed) | cand_entry+z_entry+z_entry
--   roles: abs=16, abs=6, abs=4, abs=7, abs=6, abs=8; 3 instances at bases [15]; worst realized 181545/185039
/-- 6->4->5->(closed) | cand_entry+z_entry+z_entry | pattern tau=() (all laps absolute): the cycle's row factors (cand_entry@(16, 6); z_entry@(4, 7); z_entry@(6, 8)) have product 181545/185039 < 1, i.e. the deficit D_tau = B_tau - A_tau at the realized base is 3494 > 0 (kind ALL over k >= 13: [13,inf); Sturm real-half-line: D > 0).  Unconditional Q fact. -/
theorem shape_a033_const : ((49:ℚ) / (127:ℚ)) * ((57:ℚ) / (31:ℚ)) * ((65:ℚ) / (47:ℚ)) < 1 := by
  norm_num
#print axioms shape_a033_const

-- a034 [3-edge cycle] 6->4->5->(closed) | cand_irred+z_entry+z_entry
--   roles: abs=6, tied=base, abs=4, abs=7, abs=6, free-8..-7; 4 instances at bases [15, 17]; worst realized 3705/3751
/-- 6->4->5->(closed) | cand_irred+z_entry+z_entry | pattern tau=(-8) at base k=17: the cycle's row factors (cand_irred@(6, 17); z_entry@(4, 7); z_entry@(6, 9)) have product 4161/4247 < 1, i.e. the deficit D_tau = B_tau - A_tau at the realized base is 4042 > 0 (kind FINITE over k >= 13: [13,17]; Sturm real-half-line: real roots in [lo,big)=1).  Unconditional Q fact. -/
theorem shape_a034_pat1_k17 : ((47:ℚ) / (137:ℚ)) * ((57:ℚ) / (31:ℚ)) * ((73:ℚ) / (47:ℚ)) < 1 := by
  norm_num
#print axioms shape_a034_pat1_k17

/-- 6->4->5->(closed) | cand_irred+z_entry+z_entry | pattern tau=(-7) at base k=15: the cycle's row factors (cand_irred@(6, 15); z_entry@(4, 7); z_entry@(6, 8)) have product 3705/3751 < 1, i.e. the deficit D_tau = B_tau - A_tau at the realized base is 2162 > 0 (kind FINITE over k >= 13: [13,15]; Sturm real-half-line: real roots in [lo,big)=1).  Unconditional Q fact. -/
theorem shape_a034_pat2_k15 : ((47:ℚ) / (121:ℚ)) * ((57:ℚ) / (31:ℚ)) * ((65:ℚ) / (47:ℚ)) < 1 := by
  norm_num
#print axioms shape_a034_pat2_k15

-- a035 [3-edge cycle] 6->5->2->(closed) | cand_entry+z_entry+z_irred
--   roles: abs=16, abs=11, abs=7, abs=2, abs=14, abs=3; 2 instances at bases [15]; worst realized 167943/174625
/-- 6->5->2->(closed) | cand_entry+z_entry+z_irred | pattern tau=() (all laps absolute): the cycle's row factors (cand_entry@(16, 11); z_entry@(7, 2); z_irred@(14, 3)) have product 167943/174625 < 1, i.e. the deficit D_tau = B_tau - A_tau at the realized base is 6682 > 0 (kind ALL over k >= 13: [13,inf); Sturm real-half-line: D > 0).  Unconditional Q fact. -/
theorem shape_a035_const : ((89:ℚ) / (127:ℚ)) * ((17:ℚ) / (55:ℚ)) * ((111:ℚ) / (25:ℚ)) < 1 := by
  norm_num
#print axioms shape_a035_const

-- a036 [3-edge cycle] 6->5->4->(closed) | cand_progress+z_entry+z_entry
--   roles: abs=14, abs=25, abs=8, abs=4, abs=5, abs=16; 4 instances at bases [25]; worst realized 53449/54873
/-- 6->5->4->(closed) | cand_progress+z_entry+z_entry | pattern tau=() (all laps absolute): the cycle's row factors (cand_progress@(14, 25); z_entry@(8, 4); z_entry@(5, 16)) have product 53449/54873 < 1, i.e. the deficit D_tau = B_tau - A_tau at the realized base is 12816 > 0 (kind ALL over k >= 13: [13,inf); Sturm real-half-line: D > 0).  Unconditional Q fact. -/
theorem shape_a036_const : ((113:ℚ) / (201:ℚ)) * ((33:ℚ) / (63:ℚ)) * ((129:ℚ) / (39:ℚ)) < 1 := by
  norm_num
#print axioms shape_a036_const

