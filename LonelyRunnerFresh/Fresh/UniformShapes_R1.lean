import Mathlib

/-!
# UniformShapes_R1: generated uniformity lemmas for the R1-edge killing shapes

GENERATED FILE (uniform_gen_v1.py, 41 theorems; regenerate, do not edit).  The half-line
forms of the uniformity lemma (E902 item 4's [P->L] residue) for the PROVED-UNIFORM
self-family killing shapes of the v3 uniformity lemma: per shape and realized offset
pattern tau, the deficit D_tau(m) = B_tau(m) - A_tau(m) of the shape's cycle product
P_tau(m) = A_tau(m)/B_tau(m) is strictly positive (or, at tangency patterns, nonnegative
with the strict edge carried; or, for the ZERO patterns, A and B coincide identically)
for EVERY integer base m >= 5 -- the instrument's exact PROVED-UNIFORM verdict
(v3_uniformity_lemma_v1.out, self family: 907 of 1107 shapes, all patterns kind ALL or
ZERO, replay-validated 1219/1219 death nodes and 13741/13741 certificate products).

Provenance: experiments/n8/uniform_gen_v1.py rebuilds the censuses via the instrument
module (import of v3_uniformity_lemma_v1.py), clusters the 13596 self-family killing
cycles into the 1107 shapes, takes the 907 PROVED-UNIFORM ones, and for each realized
pattern re-derives the exact A_tau, B_tau (symbolic self-check against every recorded
instance product), shifts t = m - 5, and emits a certificate proving the sign on the
half-line:
  mono        all shifted coefficients nonneg, e0 > 0 (strict) or = 0 (weak/tangency);
  quad_vertex E = e2*(t + s)^2 + k with k > 0 (or = 0 at tangency);
  lukas       E = (t + a)^2*Q + c1*t + c0, Q certified recursively, c1, c0 >= 0;
  intmono     the integer Newton ladder: all finite differences Delta^j E(0) >= 0
              (the honest form when the real half-line fails but every INTEGER base
              kills -- the instrument's verdict is a claim about integer bases);
  zero        A = B identically (D == 0).
Each theorem's statement is the explicit expanded polynomial inequality in the base
(rational coefficients, exact); every proof is linarith/nlinarith/ring/norm_num over the
emitted certificate -- no folds, no new axioms.  Every theorem carries #print axioms;
the accepted profile is the standard three (propext, Classical.choice, Quot.sound).
-/

namespace Fresh.UniformShapes

-- u001 [1-edge cycle] 2->(closed) | cand_entry
--   roles: free-1..+3, free-2..+2; 22 instances at bases [5, 6, 7, 8, 9, 10]; all_strict=True; worst realized 97/103
/-- pattern tau=(-1,-2): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u001_pat1_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (6:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u001_pat1_uniform
/-- pattern tau=(0,-1): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u001_pat2_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (6:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u001_pat2_uniform
/-- pattern tau=(1,0): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u001_pat3_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (6:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u001_pat3_uniform
/-- pattern tau=(2,1): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u001_pat4_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (6:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u001_pat4_uniform
/-- pattern tau=(3,2): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u001_pat5_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (6:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u001_pat5_uniform
-- u002 [1-edge cycle] 2->(closed) | cand_progress
--   roles: free+0..+1, free+1..+2; 9 instances at bases [6, 7, 10]; all_strict=True; worst realized 89/97
/-- pattern tau=(0,1): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u002_pat1_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (8:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u002_pat1_uniform
/-- pattern tau=(1,2): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u002_pat2_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (8:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u002_pat2_uniform
-- u003 [1-edge cycle] 3->(closed) | cand_entry
--   roles: free+2..+5, free+1..+4; 167 instances at bases [5, 6, 7, 8, 9, 10]; all_strict=True; worst realized 113/119
/-- pattern tau=(2,1): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u003_pat1_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (6:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u003_pat1_uniform
/-- pattern tau=(3,2): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u003_pat2_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (6:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u003_pat2_uniform
/-- pattern tau=(4,3): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u003_pat3_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (6:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u003_pat3_uniform
/-- pattern tau=(5,4): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u003_pat4_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (6:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u003_pat4_uniform
-- u004 [1-edge cycle] 3->(closed) | cand_progress
--   roles: free+1..+3, free+2..+4; 91 instances at bases [5, 6, 7, 8, 9, 10]; all_strict=True; worst realized 105/113
/-- pattern tau=(1,2): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u004_pat1_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (8:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u004_pat1_uniform
/-- pattern tau=(2,3): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u004_pat2_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (8:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u004_pat2_uniform
/-- pattern tau=(3,4): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u004_pat3_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (8:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u004_pat3_uniform
-- u005 [1-edge cycle] 4->(closed) | cand_entry
--   roles: free+2..+6, free+1..+5; 199 instances at bases [5, 6, 7, 8, 9, 10]; all_strict=True; worst realized 121/127
/-- pattern tau=(2,1): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u005_pat1_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (6:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u005_pat1_uniform
/-- pattern tau=(3,2): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u005_pat2_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (6:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u005_pat2_uniform
/-- pattern tau=(4,3): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u005_pat3_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (6:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u005_pat3_uniform
/-- pattern tau=(5,4): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u005_pat4_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (6:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u005_pat4_uniform
/-- pattern tau=(6,5): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u005_pat5_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (6:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u005_pat5_uniform
-- u006 [1-edge cycle] 4->(closed) | cand_progress
--   roles: free+1..+4, free+2..+5; 153 instances at bases [5, 6, 7, 8, 9, 10]; all_strict=True; worst realized 113/121
/-- pattern tau=(1,2): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u006_pat1_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (8:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u006_pat1_uniform
/-- pattern tau=(2,3): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u006_pat2_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (8:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u006_pat2_uniform
/-- pattern tau=(3,4): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u006_pat3_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (8:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u006_pat3_uniform
/-- pattern tau=(4,5): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u006_pat4_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (8:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u006_pat4_uniform
-- u007 [1-edge cycle] 5->(closed) | cand_entry
--   roles: free+3..+7, free+2..+6; 381 instances at bases [5, 6, 7, 8, 9, 10]; all_strict=True; worst realized 43/45
/-- pattern tau=(3,2): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u007_pat1_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (6:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u007_pat1_uniform
/-- pattern tau=(4,3): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u007_pat2_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (6:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u007_pat2_uniform
/-- pattern tau=(5,4): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u007_pat3_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (6:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u007_pat3_uniform
/-- pattern tau=(6,5): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u007_pat4_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (6:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u007_pat4_uniform
/-- pattern tau=(7,6): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u007_pat5_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (6:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u007_pat5_uniform
-- u008 [1-edge cycle] 5->(closed) | cand_progress
--   roles: free+2..+5, free+3..+6; 199 instances at bases [5, 6, 7, 8, 9, 10]; all_strict=True; worst realized 121/129
/-- pattern tau=(2,3): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u008_pat1_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (8:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u008_pat1_uniform
/-- pattern tau=(3,4): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u008_pat2_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (8:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u008_pat2_uniform
/-- pattern tau=(4,5): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u008_pat3_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (8:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u008_pat3_uniform
/-- pattern tau=(5,6): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u008_pat4_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (8:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u008_pat4_uniform
-- u009 [1-edge cycle] 6->(closed) | cand_entry
--   roles: free+3..+7, free+2..+6; 431 instances at bases [5, 6, 7, 8, 9, 10]; all_strict=True; worst realized 43/45
/-- pattern tau=(3,2): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u009_pat1_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (6:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u009_pat1_uniform
/-- pattern tau=(4,3): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u009_pat2_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (6:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u009_pat2_uniform
/-- pattern tau=(5,4): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u009_pat3_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (6:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u009_pat3_uniform
/-- pattern tau=(6,5): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u009_pat4_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (6:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u009_pat4_uniform
/-- pattern tau=(7,6): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u009_pat5_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (6:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u009_pat5_uniform
-- u010 [1-edge cycle] 6->(closed) | cand_progress
--   roles: free+2..+5, free+3..+6; 165 instances at bases [5, 6, 7, 8, 9, 10]; all_strict=True; worst realized 121/129
/-- pattern tau=(2,3): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u010_pat1_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (8:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u010_pat1_uniform
/-- pattern tau=(3,4): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u010_pat2_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (8:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u010_pat2_uniform
/-- pattern tau=(4,5): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u010_pat3_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (8:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u010_pat3_uniform
/-- pattern tau=(5,6): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u010_pat4_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (8:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u010_pat4_uniform
