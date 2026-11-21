import Mathlib

/-!
# UniformAnchored_R4: per-base-instance killing-shape lemmas for the R4-edge
anchored cycles

GENERATED FILE (uniform_gen_anchored_v1.py, 18 theorems; regenerate, do not edit).  The
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

-- a037 [4-edge cycle] 1->4->2->5->(closed) | cand_entry+z_irred+z_entry+z_entry
--   roles: abs=3, abs=6, abs=3, abs=5, abs=2, abs=6, abs=5, abs=1; 1 instances at bases [15]; worst realized 2401/2665
/-- 1->4->2->5->(closed) | cand_entry+z_irred+z_entry+z_entry | pattern tau=() (all laps absolute): the cycle's row factors (cand_entry@(3, 6); z_irred@(3, 5); z_entry@(2, 6); z_entry@(5, 1)) have product 2401/2665 < 1, i.e. the deficit D_tau = B_tau - A_tau at the realized base is 54648 > 0 (kind ALL over k >= 13: [13,inf); Sturm real-half-line: D > 0).  Unconditional Q fact. -/
theorem shape_a037_const : ((49:ℚ) / (23:ℚ)) * ((23:ℚ) / (41:ℚ)) * ((49:ℚ) / (15:ℚ)) * ((9:ℚ) / (39:ℚ)) < 1 := by
  norm_num
#print axioms shape_a037_const

-- a038 [4-edge cycle] 1->6->5->2->(closed) | cand_entry+z_entry+z_entry+z_entry
--   roles: abs=3, abs=25, abs=9, abs=5, abs=5, abs=1, abs=3, abs=2; 4 instances at bases [25]; worst realized 420291/488267
/-- 1->6->5->2->(closed) | cand_entry+z_entry+z_entry+z_entry | pattern tau=() (all laps absolute): the cycle's row factors (cand_entry@(3, 25); z_entry@(9, 5); z_entry@(5, 1); z_entry@(3, 2)) have product 420291/488267 < 1, i.e. the deficit D_tau = B_tau - A_tau at the realized base is 203928 > 0 (kind ALL over k >= 13: [13,inf); Sturm real-half-line: D > 0).  Unconditional Q fact. -/
theorem shape_a038_const : ((201:ℚ) / (23:ℚ)) * ((41:ℚ) / (71:ℚ)) * ((9:ℚ) / (39:ℚ)) * ((17:ℚ) / (23:ℚ)) < 1 := by
  norm_num
#print axioms shape_a038_const

-- a039 [4-edge cycle] 2->5->6->3->(closed) | cand_entry+z_entry+z_entry+z_entry
--   roles: abs=4, abs=11, abs=6, abs=9, abs=17, abs=4, abs=4, abs=3; 2 instances at bases [17]; worst realized 357335/406503
/-- 2->5->6->3->(closed) | cand_entry+z_entry+z_entry+z_entry | pattern tau=() (all laps absolute): the cycle's row factors (cand_entry@(4, 11); z_entry@(6, 9); z_entry@(17, 4); z_entry@(4, 3)) have product 357335/406503 < 1, i.e. the deficit D_tau = B_tau - A_tau at the realized base is 737520 > 0 (kind ALL over k >= 13: [13,inf); Sturm real-half-line: D > 0).  Unconditional Q fact. -/
theorem shape_a039_const : ((89:ℚ) / (31:ℚ)) * ((73:ℚ) / (47:ℚ)) * ((33:ℚ) / (135:ℚ)) * ((25:ℚ) / (31:ℚ)) < 1 := by
  norm_num
#print axioms shape_a039_const

-- a040 [4-edge cycle] 2->5->6->4->(closed) | cand_entry+z_entry+z_entry+z_irred
--   roles: abs=4, abs=11, abs=6, abs=8, abs=8, abs=3, abs=3, abs=5; 1 instances at bases [15]; worst realized 3326375/3763431
/-- 2->5->6->4->(closed) | cand_entry+z_entry+z_entry+z_irred | pattern tau=() (all laps absolute): the cycle's row factors (cand_entry@(4, 11); z_entry@(6, 8); z_entry@(8, 3); z_irred@(3, 5)) have product 3326375/3763431 < 1, i.e. the deficit D_tau = B_tau - A_tau at the realized base is 437056 > 0 (kind ALL over k >= 13: [13,inf); Sturm real-half-line: D > 0).  Unconditional Q fact. -/
theorem shape_a040_const : ((89:ℚ) / (31:ℚ)) * ((65:ℚ) / (47:ℚ)) * ((25:ℚ) / (63:ℚ)) * ((23:ℚ) / (41:ℚ)) < 1 := by
  norm_num
#print axioms shape_a040_const

-- a041 [4-edge cycle] 2->6->3->5->(closed) | cand_entry+z_entry+z_progress+z_entry
--   roles: abs=4, abs=16, abs=15, abs=4, abs=8, abs=3, abs=7, abs=2; 1 instances at bases [15]; worst realized 5031/5425
/-- 2->6->3->5->(closed) | cand_entry+z_entry+z_progress+z_entry | pattern tau=() (all laps absolute): the cycle's row factors (cand_entry@(4, 16); z_entry@(15, 4); z_progress@(8, 3); z_entry@(7, 2)) have product 5031/5425 < 1, i.e. the deficit D_tau = B_tau - A_tau at the realized base is 368390 > 0 (kind ALL over k >= 13: [13,inf); Sturm real-half-line: D > 0).  Unconditional Q fact. -/
theorem shape_a041_const : ((129:ℚ) / (31:ℚ)) * ((33:ℚ) / (119:ℚ)) * ((65:ℚ) / (25:ℚ)) * ((17:ℚ) / (55:ℚ)) < 1 := by
  norm_num
#print axioms shape_a041_const

-- a042 [4-edge cycle] 3->4->5->2->(closed) | cand_entry+z_entry+z_entry+z_irred
--   roles: abs=5, abs=6, abs=4, abs=7, abs=7, abs=2, abs=4, abs=3; 2 instances at bases [15]; worst realized 15827/17875
/-- 3->4->5->2->(closed) | cand_entry+z_entry+z_entry+z_irred | pattern tau=() (all laps absolute): the cycle's row factors (cand_entry@(5, 6); z_entry@(4, 7); z_entry@(7, 2); z_irred@(4, 3)) have product 15827/17875 < 1, i.e. the deficit D_tau = B_tau - A_tau at the realized base is 190464 > 0 (kind ALL over k >= 13: [13,inf); Sturm real-half-line: D > 0).  Unconditional Q fact. -/
theorem shape_a042_const : ((49:ℚ) / (39:ℚ)) * ((57:ℚ) / (31:ℚ)) * ((17:ℚ) / (55:ℚ)) * ((31:ℚ) / (25:ℚ)) < 1 := by
  norm_num
#print axioms shape_a042_const

-- a043 [4-edge cycle] 3->4->5->6->(closed) | cand_entry+z_entry+z_entry+z_entry
--   roles: abs=5, abs=6, abs=4, abs=7, abs=6, abs=8, abs=15, abs=4; 1 instances at bases [15]; worst realized 21945/24769
/-- 3->4->5->6->(closed) | cand_entry+z_entry+z_entry+z_entry | pattern tau=() (all laps absolute): the cycle's row factors (cand_entry@(5, 6); z_entry@(4, 7); z_entry@(6, 8); z_entry@(15, 4)) have product 21945/24769 < 1, i.e. the deficit D_tau = B_tau - A_tau at the realized base is 770952 > 0 (kind ALL over k >= 13: [13,inf); Sturm real-half-line: D > 0).  Unconditional Q fact. -/
theorem shape_a043_const : ((49:ℚ) / (39:ℚ)) * ((57:ℚ) / (31:ℚ)) * ((65:ℚ) / (47:ℚ)) * ((33:ℚ) / (119:ℚ)) < 1 := by
  norm_num
#print axioms shape_a043_const

-- a044 [4-edge cycle] 3->5->2->1->(closed) | cand_entry+z_entry+z_entry+z_irred
--   roles: abs=5, abs=11, abs=7, abs=2, abs=3, abs=2, abs=2, abs=1; 1 instances at bases [15]; worst realized 25721/29601
/-- 3->5->2->1->(closed) | cand_entry+z_entry+z_entry+z_irred | pattern tau=() (all laps absolute): the cycle's row factors (cand_entry@(5, 11); z_entry@(7, 2); z_entry@(3, 2); z_irred@(2, 1)) have product 25721/29601 < 1, i.e. the deficit D_tau = B_tau - A_tau at the realized base is 58200 > 0 (kind ALL over k >= 13: [13,inf); Sturm real-half-line: D > 0).  Unconditional Q fact. -/
theorem shape_a044_const : ((89:ℚ) / (39:ℚ)) * ((17:ℚ) / (55:ℚ)) * ((17:ℚ) / (23:ℚ)) * ((15:ℚ) / (9:ℚ)) < 1 := by
  norm_num
#print axioms shape_a044_const

-- a045 [4-edge cycle] 3->5->2->6->(closed) | cand_entry+z_entry+z_irred+z_entry
--   roles: abs=5, abs=11, abs=7, abs=2, abs=14, abs=3, abs=15, abs=4; 2 instances at bases [15]; worst realized 9879/11375
/-- 3->5->2->6->(closed) | cand_entry+z_entry+z_irred+z_entry | pattern tau=() (all laps absolute): the cycle's row factors (cand_entry@(5, 11); z_entry@(7, 2); z_irred@(14, 3); z_entry@(15, 4)) have product 9879/11375 < 1, i.e. the deficit D_tau = B_tau - A_tau at the realized base is 839256 > 0 (kind ALL over k >= 13: [13,inf); Sturm real-half-line: D > 0).  Unconditional Q fact. -/
theorem shape_a045_const : ((89:ℚ) / (39:ℚ)) * ((17:ℚ) / (55:ℚ)) * ((111:ℚ) / (25:ℚ)) * ((33:ℚ) / (119:ℚ)) < 1 := by
  norm_num
#print axioms shape_a045_const

-- a046 [4-edge cycle] 3->6->5->2->(closed) | cand_entry+z_entry+z_entry+z_irred
--   roles: abs=5, abs=25, abs=9, abs=5, abs=5, abs=1, abs=4, abs=3; 2 instances at bases [25]; worst realized 255471/299975
/-- 3->6->5->2->(closed) | cand_entry+z_entry+z_entry+z_irred | pattern tau=() (all laps absolute): the cycle's row factors (cand_entry@(5, 25); z_entry@(9, 5); z_entry@(5, 1); z_irred@(4, 3)) have product 255471/299975 < 1, i.e. the deficit D_tau = B_tau - A_tau at the realized base is 400536 > 0 (kind ALL over k >= 13: [13,inf); Sturm real-half-line: D > 0).  Unconditional Q fact. -/
theorem shape_a046_const : ((201:ℚ) / (39:ℚ)) * ((41:ℚ) / (71:ℚ)) * ((9:ℚ) / (39:ℚ)) * ((31:ℚ) / (25:ℚ)) < 1 := by
  norm_num
#print axioms shape_a046_const

-- a047 [4-edge cycle] 4->5->2->3->(closed) | cand_progress+z_entry+z_irred+z_irred
--   roles: abs=11, abs=6, abs=7, abs=2, abs=4, abs=3, abs=6, abs=4; 2 instances at bases [15]; worst realized 2204441/2223375
/-- 4->5->2->3->(closed) | cand_progress+z_entry+z_irred+z_irred | pattern tau=() (all laps absolute): the cycle's row factors (cand_progress@(11, 6); z_entry@(7, 2); z_irred@(4, 3); z_irred@(6, 4)) have product 2204441/2223375 < 1, i.e. the deficit D_tau = B_tau - A_tau at the realized base is 18934 > 0 (kind ALL over k >= 13: [13,inf); Sturm real-half-line: D > 0).  Unconditional Q fact. -/
theorem shape_a047_const : ((89:ℚ) / (49:ℚ)) * ((17:ℚ) / (55:ℚ)) * ((31:ℚ) / (25:ℚ)) * ((47:ℚ) / (33:ℚ)) < 1 := by
  norm_num
#print axioms shape_a047_const

-- a048 [4-edge cycle] 4->5->2->6->(closed) | cand_entry+z_entry+z_irred+z_entry
--   roles: abs=7, abs=11, abs=7, abs=2, abs=14, abs=3, abs=8, abs=3; 2 instances at bases [15]; worst realized 55981/63525
/-- 4->5->2->6->(closed) | cand_entry+z_entry+z_irred+z_entry | pattern tau=() (all laps absolute): the cycle's row factors (cand_entry@(7, 11); z_entry@(7, 2); z_irred@(14, 3); z_entry@(8, 3)) have product 55981/63525 < 1, i.e. the deficit D_tau = B_tau - A_tau at the realized base is 565800 > 0 (kind ALL over k >= 13: [13,inf); Sturm real-half-line: D > 0).  Unconditional Q fact. -/
theorem shape_a048_const : ((89:ℚ) / (55:ℚ)) * ((17:ℚ) / (55:ℚ)) * ((111:ℚ) / (25:ℚ)) * ((25:ℚ) / (63:ℚ)) < 1 := by
  norm_num
#print axioms shape_a048_const

-- a049 [4-edge cycle] 4->5->6->3->(closed) | cand_entry+z_entry+z_entry+z_entry
--   roles: abs=7, abs=11, abs=6, abs=9, abs=17, abs=4, abs=3, abs=4; 1 instances at bases [17]; worst realized 71467/81075
/-- 4->5->6->3->(closed) | cand_entry+z_entry+z_entry+z_entry | pattern tau=() (all laps absolute): the cycle's row factors (cand_entry@(7, 11); z_entry@(6, 9); z_entry@(17, 4); z_entry@(3, 4)) have product 71467/81075 < 1, i.e. the deficit D_tau = B_tau - A_tau at the realized base is 951192 > 0 (kind ALL over k >= 13: [13,inf); Sturm real-half-line: D > 0).  Unconditional Q fact. -/
theorem shape_a049_const : ((89:ℚ) / (55:ℚ)) * ((73:ℚ) / (47:ℚ)) * ((33:ℚ) / (135:ℚ)) * ((33:ℚ) / (23:ℚ)) < 1 := by
  norm_num
#print axioms shape_a049_const

-- a050 [4-edge cycle] 4->5->6->3->(closed) | cand_progress+z_entry+z_entry+z_irred
--   roles: abs=11, abs=6, abs=6, abs=8, abs=15, abs=4, abs=6, abs=4; 2 instances at bases [15]; worst realized 5785/5831
/-- 4->5->6->3->(closed) | cand_progress+z_entry+z_entry+z_irred | pattern tau=() (all laps absolute): the cycle's row factors (cand_progress@(11, 6); z_entry@(6, 8); z_entry@(15, 4); z_irred@(6, 4)) have product 5785/5831 < 1, i.e. the deficit D_tau = B_tau - A_tau at the realized base is 71346 > 0 (kind ALL over k >= 13: [13,inf); Sturm real-half-line: D > 0).  Unconditional Q fact. -/
theorem shape_a050_const : ((89:ℚ) / (49:ℚ)) * ((65:ℚ) / (47:ℚ)) * ((33:ℚ) / (119:ℚ)) * ((47:ℚ) / (33:ℚ)) < 1 := by
  norm_num
#print axioms shape_a050_const

-- a051 [4-edge cycle] 4->6->3->5->(closed) | cand_entry+z_entry+z_progress+z_entry
--   roles: abs=7, abs=16, abs=15, abs=4, abs=8, abs=3, abs=6, abs=3; 1 instances at bases [15]; worst realized 5031/5593
/-- 4->6->3->5->(closed) | cand_entry+z_entry+z_progress+z_entry | pattern tau=() (all laps absolute): the cycle's row factors (cand_entry@(7, 16); z_entry@(15, 4); z_progress@(8, 3); z_entry@(6, 3)) have product 5031/5593 < 1, i.e. the deficit D_tau = B_tau - A_tau at the realized base is 772750 > 0 (kind ALL over k >= 13: [13,inf); Sturm real-half-line: D > 0).  Unconditional Q fact. -/
theorem shape_a051_const : ((129:ℚ) / (55:ℚ)) * ((33:ℚ) / (119:ℚ)) * ((65:ℚ) / (25:ℚ)) * ((25:ℚ) / (47:ℚ)) < 1 := by
  norm_num
#print axioms shape_a051_const

-- a052 [4-edge cycle] 6->4->2->5->(closed) | cand_entry+z_irred+z_entry+z_entry
--   roles: abs=16, abs=6, abs=3, abs=5, abs=2, abs=6, abs=6, abs=8; 1 instances at bases [15]; worst realized 717899/734187
/-- 6->4->2->5->(closed) | cand_entry+z_irred+z_entry+z_entry | pattern tau=() (all laps absolute): the cycle's row factors (cand_entry@(16, 6); z_irred@(3, 5); z_entry@(2, 6); z_entry@(6, 8)) have product 717899/734187 < 1, i.e. the deficit D_tau = B_tau - A_tau at the realized base is 81440 > 0 (kind ALL over k >= 13: [13,inf); Sturm real-half-line: D > 0).  Unconditional Q fact. -/
theorem shape_a052_const : ((49:ℚ) / (127:ℚ)) * ((23:ℚ) / (41:ℚ)) * ((49:ℚ) / (15:ℚ)) * ((65:ℚ) / (47:ℚ)) < 1 := by
  norm_num
#print axioms shape_a052_const

-- a053 [4-edge cycle] 6->4->2->5->(closed) | cand_irred+z_irred+z_entry+z_entry
--   roles: abs=6, abs=15, abs=3, abs=5, abs=2, abs=6, abs=6, abs=8; 1 instances at bases [15]; worst realized 14651/14883
/-- 6->4->2->5->(closed) | cand_irred+z_irred+z_entry+z_entry | pattern tau=() (all laps absolute): the cycle's row factors (cand_irred@(6, 15); z_irred@(3, 5); z_entry@(2, 6); z_entry@(6, 8)) have product 14651/14883 < 1, i.e. the deficit D_tau = B_tau - A_tau at the realized base is 54520 > 0 (kind ALL over k >= 13: [13,inf); Sturm real-half-line: D > 0).  Unconditional Q fact. -/
theorem shape_a053_const : ((47:ℚ) / (121:ℚ)) * ((23:ℚ) / (41:ℚ)) * ((49:ℚ) / (15:ℚ)) * ((65:ℚ) / (47:ℚ)) < 1 := by
  norm_num
#print axioms shape_a053_const

-- a054 [4-edge cycle] 6->4->5->2->(closed) | cand_irred+z_entry+z_entry+z_irred
--   roles: abs=6, abs=15, abs=4, abs=7, abs=7, abs=2, abs=14, abs=3; 2 instances at bases [15]; worst realized 5055273/5157625
/-- 6->4->5->2->(closed) | cand_irred+z_entry+z_entry+z_irred | pattern tau=() (all laps absolute): the cycle's row factors (cand_irred@(6, 15); z_entry@(4, 7); z_entry@(7, 2); z_irred@(14, 3)) have product 5055273/5157625 < 1, i.e. the deficit D_tau = B_tau - A_tau at the realized base is 102352 > 0 (kind ALL over k >= 13: [13,inf); Sturm real-half-line: D > 0).  Unconditional Q fact. -/
theorem shape_a054_const : ((47:ℚ) / (121:ℚ)) * ((57:ℚ) / (31:ℚ)) * ((17:ℚ) / (55:ℚ)) * ((111:ℚ) / (25:ℚ)) < 1 := by
  norm_num
#print axioms shape_a054_const

