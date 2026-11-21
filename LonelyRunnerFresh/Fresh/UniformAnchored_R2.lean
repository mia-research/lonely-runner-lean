import Mathlib

/-!
# UniformAnchored_R2: per-base-instance killing-shape lemmas for the R2-edge
anchored cycles

GENERATED FILE (uniform_gen_anchored_v1.py, 15 theorems; regenerate, do not edit).  The
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

-- a006 [2-edge cycle] 1->5->(closed) | cand_entry+z_entry
--   roles: abs=3, abs=11, abs=5, abs=1; 7 instances at bases [15, 17]; worst realized 267/299
/-- 1->5->(closed) | cand_entry+z_entry | pattern tau=() (all laps absolute): the cycle's row factors (cand_entry@(3, 11); z_entry@(5, 1)) have product 267/299 < 1, i.e. the deficit D_tau = B_tau - A_tau at the realized base is 96 > 0 (kind ALL over k >= 13: [13,inf); Sturm real-half-line: D > 0).  Unconditional Q fact. -/
theorem shape_a006_const : ((89:ℚ) / (23:ℚ)) * ((9:ℚ) / (39:ℚ)) < 1 := by
  norm_num
#print axioms shape_a006_const

-- a007 [2-edge cycle] 2->4->(closed) | cand_entry+z_irred
--   roles: abs=4, abs=6, abs=3, abs=5; 1 instances at bases [15]; worst realized 1127/1271
/-- 2->4->(closed) | cand_entry+z_irred | pattern tau=() (all laps absolute): the cycle's row factors (cand_entry@(4, 6); z_irred@(3, 5)) have product 1127/1271 < 1, i.e. the deficit D_tau = B_tau - A_tau at the realized base is 144 > 0 (kind ALL over k >= 13: [13,inf); Sturm real-half-line: D > 0).  Unconditional Q fact. -/
theorem shape_a007_const : ((49:ℚ) / (31:ℚ)) * ((23:ℚ) / (41:ℚ)) < 1 := by
  norm_num
#print axioms shape_a007_const

-- a008 [2-edge cycle] 2->5->(closed) | cand_entry+z_entry
--   roles: abs=4, abs=11, abs=7, abs=2; 6 instances at bases [15]; worst realized 1513/1705
/-- 2->5->(closed) | cand_entry+z_entry | pattern tau=() (all laps absolute): the cycle's row factors (cand_entry@(4, 11); z_entry@(7, 2)) have product 1513/1705 < 1, i.e. the deficit D_tau = B_tau - A_tau at the realized base is 192 > 0 (kind ALL over k >= 13: [13,inf); Sturm real-half-line: D > 0).  Unconditional Q fact. -/
theorem shape_a008_const : ((89:ℚ) / (31:ℚ)) * ((17:ℚ) / (55:ℚ)) < 1 := by
  norm_num
#print axioms shape_a008_const

-- a009 [2-edge cycle] 3->6->(closed) | cand_entry+z_entry
--   roles: abs=5, abs=25, abs=19, abs=3; 1 instances at bases [25]; worst realized 1675/1963
/-- 3->6->(closed) | cand_entry+z_entry | pattern tau=() (all laps absolute): the cycle's row factors (cand_entry@(5, 25); z_entry@(19, 3)) have product 1675/1963 < 1, i.e. the deficit D_tau = B_tau - A_tau at the realized base is 864 > 0 (kind ALL over k >= 13: [13,inf); Sturm real-half-line: D > 0).  Unconditional Q fact. -/
theorem shape_a009_const : ((201:ℚ) / (39:ℚ)) * ((25:ℚ) / (151:ℚ)) < 1 := by
  norm_num
#print axioms shape_a009_const

-- a010 [2-edge cycle] 3->6->(closed) | cand_entry+z_entry
--   roles: abs=5, free+0..+1, tied=base, abs=4; 3 instances at bases [15, 25]; worst realized 1419/1547
/-- 3->6->(closed) | cand_entry+z_entry | pattern tau=(0) at base k=25: the cycle's row factors (cand_entry@(5, 25); z_entry@(25, 4)) have product 2211/2587 < 1, i.e. the deficit D_tau = B_tau - A_tau at the realized base is 1128 > 0 (kind ALL over k >= 13: [13,inf); Sturm real-half-line: D > 0).  Unconditional Q fact. -/
theorem shape_a010_pat1_k25 : ((201:ℚ) / (39:ℚ)) * ((33:ℚ) / (199:ℚ)) < 1 := by
  norm_num
#print axioms shape_a010_pat1_k25

/-- 3->6->(closed) | cand_entry+z_entry | pattern tau=(1) at base k=15: the cycle's row factors (cand_entry@(5, 16); z_entry@(15, 4)) have product 1419/1547 < 1, i.e. the deficit D_tau = B_tau - A_tau at the realized base is 384 > 0 (kind ALL over k >= 13: [13,inf); Sturm real-half-line: D > 0).  Unconditional Q fact. -/
theorem shape_a010_pat2_k15 : ((129:ℚ) / (39:ℚ)) * ((33:ℚ) / (119:ℚ)) < 1 := by
  norm_num
#print axioms shape_a010_pat2_k15

-- a011 [2-edge cycle] 4->5->(closed) | cand_entry+z_irred
--   roles: abs=7, abs=11, abs=4, abs=7; 1 instances at bases [17]; worst realized 2759/3135
/-- 4->5->(closed) | cand_entry+z_irred | pattern tau=() (all laps absolute): the cycle's row factors (cand_entry@(7, 11); z_irred@(4, 7)) have product 2759/3135 < 1, i.e. the deficit D_tau = B_tau - A_tau at the realized base is 376 > 0 (kind ALL over k >= 13: [13,inf); Sturm real-half-line: D > 0).  Unconditional Q fact. -/
theorem shape_a011_const : ((89:ℚ) / (55:ℚ)) * ((31:ℚ) / (57:ℚ)) < 1 := by
  norm_num
#print axioms shape_a011_const

-- a012 [2-edge cycle] 5->4->(closed) | cand_entry+z_entry
--   roles: abs=12, abs=6, abs=4, abs=7; 3 instances at bases [15]; worst realized 147/155
/-- 5->4->(closed) | cand_entry+z_entry | pattern tau=() (all laps absolute): the cycle's row factors (cand_entry@(12, 6); z_entry@(4, 7)) have product 147/155 < 1, i.e. the deficit D_tau = B_tau - A_tau at the realized base is 152 > 0 (kind ALL over k >= 13: [13,inf); Sturm real-half-line: D > 0).  Unconditional Q fact. -/
theorem shape_a012_const : ((49:ℚ) / (95:ℚ)) * ((57:ℚ) / (31:ℚ)) < 1 := by
  norm_num
#print axioms shape_a012_const

-- a013 [2-edge cycle] 5->4->(closed) | cand_progress+z_entry
--   roles: abs=5, abs=11, abs=4, abs=7; 2 instances at bases [15]; worst realized 2337/2759
/-- 5->4->(closed) | cand_progress+z_entry | pattern tau=() (all laps absolute): the cycle's row factors (cand_progress@(5, 11); z_entry@(4, 7)) have product 2337/2759 < 1, i.e. the deficit D_tau = B_tau - A_tau at the realized base is 422 > 0 (kind ALL over k >= 13: [13,inf); Sturm real-half-line: D > 0).  Unconditional Q fact. -/
theorem shape_a013_const : ((41:ℚ) / (89:ℚ)) * ((57:ℚ) / (31:ℚ)) < 1 := by
  norm_num
#print axioms shape_a013_const

-- a014 [2-edge cycle] 5->6->(closed) | cand_entry+z_entry
--   roles: abs=12, abs=16, abs=10, abs=7; 1 instances at bases [15]; worst realized 387/395
/-- 5->6->(closed) | cand_entry+z_entry | pattern tau=() (all laps absolute): the cycle's row factors (cand_entry@(12, 16); z_entry@(10, 7)) have product 387/395 < 1, i.e. the deficit D_tau = B_tau - A_tau at the realized base is 152 > 0 (kind ALL over k >= 13: [13,inf); Sturm real-half-line: D > 0).  Unconditional Q fact. -/
theorem shape_a014_const : ((129:ℚ) / (95:ℚ)) * ((57:ℚ) / (79:ℚ)) < 1 := by
  norm_num
#print axioms shape_a014_const

-- a015 [2-edge cycle] 5->6->(closed) | cand_entry+z_entry
--   roles: abs=15, abs=25, abs=9, abs=5; 4 instances at bases [25]; worst realized 8241/8449
/-- 5->6->(closed) | cand_entry+z_entry | pattern tau=() (all laps absolute): the cycle's row factors (cand_entry@(15, 25); z_entry@(9, 5)) have product 8241/8449 < 1, i.e. the deficit D_tau = B_tau - A_tau at the realized base is 208 > 0 (kind ALL over k >= 13: [13,inf); Sturm real-half-line: D > 0).  Unconditional Q fact. -/
theorem shape_a015_const : ((201:ℚ) / (119:ℚ)) * ((41:ℚ) / (71:ℚ)) < 1 := by
  norm_num
#print axioms shape_a015_const

-- a016 [2-edge cycle] 6->4->(closed) | cand_irred+z_entry
--   roles: abs=6, abs=17, abs=4, abs=11; 1 instances at bases [17]; worst realized 4183/4247
/-- 6->4->(closed) | cand_irred+z_entry | pattern tau=() (all laps absolute): the cycle's row factors (cand_irred@(6, 17); z_entry@(4, 11)) have product 4183/4247 < 1, i.e. the deficit D_tau = B_tau - A_tau at the realized base is 64 > 0 (kind ALL over k >= 13: [13,inf); Sturm real-half-line: D > 0).  Unconditional Q fact. -/
theorem shape_a016_const : ((47:ℚ) / (137:ℚ)) * ((89:ℚ) / (31:ℚ)) < 1 := by
  norm_num
#print axioms shape_a016_const

-- a017 [2-edge cycle] 6->4->(closed) | cand_progress+z_entry
--   roles: abs=7, abs=25, abs=5, abs=16; 2 instances at bases [25]; worst realized 817/871
/-- 6->4->(closed) | cand_progress+z_entry | pattern tau=() (all laps absolute): the cycle's row factors (cand_progress@(7, 25); z_entry@(5, 16)) have product 817/871 < 1, i.e. the deficit D_tau = B_tau - A_tau at the realized base is 486 > 0 (kind ALL over k >= 13: [13,inf); Sturm real-half-line: D > 0).  Unconditional Q fact. -/
theorem shape_a017_const : ((57:ℚ) / (201:ℚ)) * ((129:ℚ) / (39:ℚ)) < 1 := by
  norm_num
#print axioms shape_a017_const

-- a018 [2-edge cycle] 6->5->(closed) | cand_entry+z_entry
--   roles: tied+1, abs=11, abs=6, free-8..-7; 6 instances at bases [15, 17]; worst realized 5785/5969
/-- 6->5->(closed) | cand_entry+z_entry | pattern tau=(-8) at base k=17: the cycle's row factors (cand_entry@(18, 11); z_entry@(6, 9)) have product 6497/6721 < 1, i.e. the deficit D_tau = B_tau - A_tau at the realized base is 224 > 0 (kind FINITE over k >= 13: [13,17]; Sturm real-half-line: real roots in [lo,big)=1).  Unconditional Q fact. -/
theorem shape_a018_pat1_k17 : ((89:ℚ) / (143:ℚ)) * ((73:ℚ) / (47:ℚ)) < 1 := by
  norm_num
#print axioms shape_a018_pat1_k17

/-- 6->5->(closed) | cand_entry+z_entry | pattern tau=(-7) at base k=15: the cycle's row factors (cand_entry@(16, 11); z_entry@(6, 8)) have product 5785/5969 < 1, i.e. the deficit D_tau = B_tau - A_tau at the realized base is 184 > 0 (kind FINITE over k >= 13: [13,15]; Sturm real-half-line: real roots in [lo,big)=1).  Unconditional Q fact. -/
theorem shape_a018_pat2_k15 : ((89:ℚ) / (127:ℚ)) * ((65:ℚ) / (47:ℚ)) < 1 := by
  norm_num
#print axioms shape_a018_pat2_k15

