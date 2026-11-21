import Mathlib

/-!
# UniformAnchored_R5: per-base-instance killing-shape lemmas for the R5-edge
anchored cycles

GENERATED FILE (uniform_gen_anchored_v1.py, 1 theorems; regenerate, do not edit).  The
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

-- a055 [5-edge cycle] 3->4->2->5->6->(closed) | cand_entry+z_irred+z_entry+z_entry+z_entry
--   roles: abs=5, abs=6, abs=3, abs=5, abs=2, abs=6, abs=6, abs=8, abs=15, abs=4; 1 instances at bases [15]; worst realized 86779/98277
/-- 3->4->2->5->6->(closed) | cand_entry+z_irred+z_entry+z_entry+z_entry | pattern tau=() (all laps absolute): the cycle's row factors (cand_entry@(5, 6); z_irred@(3, 5); z_entry@(2, 6); z_entry@(6, 8); z_entry@(15, 4)) have product 86779/98277 < 1, i.e. the deficit D_tau = B_tau - A_tau at the realized base is 15694770 > 0 (kind ALL over k >= 13: [13,inf); Sturm real-half-line: D > 0).  Unconditional Q fact. -/
theorem shape_a055_const : ((49:ℚ) / (39:ℚ)) * ((23:ℚ) / (41:ℚ)) * ((49:ℚ) / (15:ℚ)) * ((65:ℚ) / (47:ℚ)) * ((33:ℚ) / (119:ℚ)) < 1 := by
  norm_num
#print axioms shape_a055_const

