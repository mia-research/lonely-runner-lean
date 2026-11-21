import Mathlib

/-!
# UniformShapes_R2: generated uniformity lemmas for the R2-edge killing shapes

GENERATED FILE (uniform_gen_v1.py, 229 theorems; regenerate, do not edit).  The half-line
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

-- u011 [2-edge cycle] 1->2->(closed) | cand_entry+z_entry
--   roles: abs=4, abs=7, abs=7, abs=3; 1 instances at bases [7]; all_strict=True; worst realized 285/341
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u011_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (280:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u011_uniform
-- u012 [2-edge cycle] 1->2->(closed) | cand_entry+z_entry
--   roles: abs=2, abs=12, abs=12, abs=1; 1 instances at bases [10]; all_strict=True; worst realized 291/475
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u012_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (552:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u012_uniform
-- u013 [2-edge cycle] 1->2->(closed) | cand_entry+z_irred
--   roles: tied-5, abs=8, tied-6, tied-1; 2 instances at bases [7, 8]; all_strict=True; worst realized 325/437
/-- pattern tau=(): real half-line form, quad_vertex certificate (kind ALL, strict=True, deg D = 2). -/
theorem shape_u013_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (64:ℚ) * m ^ 2 - (904:ℚ) * m + (3472:ℚ) := by
  intro m hm
  have hsq : (0:ℚ) ≤ (m - 5 + (-33 / 16:ℚ)) ^ 2 := sq_nonneg _
  have hexp : (m - 5 + (-33 / 16:ℚ)) ^ 2 = (m - 5) ^ 2 + (-33 / 8:ℚ) * (m - 5) + (1089 / 256:ℚ) := by ring
  have hshift : (64:ℚ) * ((m - 5) ^ 2 + (-33 / 8:ℚ) * (m - 5) + (1089 / 256:ℚ)) + (1119 / 4:ℚ) = (64:ℚ) * m ^ 2 - (904:ℚ) * m + (3472:ℚ) := by ring
  linarith [hsq, hexp, hshift]
#print axioms shape_u013_uniform
-- u014 [2-edge cycle] 1->2->(closed) | cand_entry+z_irred
--   roles: abs=3, abs=7, abs=2, abs=6; 1 instances at bases [7]; all_strict=True; worst realized 855/1127
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u014_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (272:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u014_uniform
-- u015 [2-edge cycle] 1->2->(closed) | cand_entry+z_irred
--   roles: abs=3, abs=8, abs=2, abs=7; 1 instances at bases [9]; all_strict=True; worst realized 325/437
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u015_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (336:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u015_uniform
-- u016 [2-edge cycle] 1->2->(closed) | cand_irred+z_irred
--   roles: abs=4, abs=1, abs=1, abs=3; 2 instances at bases [6]; all_strict=True; worst realized 217/225
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u016_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (8:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u016_uniform
-- u017 [2-edge cycle] 1->2->(closed) | cand_irred+z_irred
--   roles: abs=7, abs=2, abs=2, abs=6; 7 instances at bases [6, 7, 8]; all_strict=True; worst realized 825/833
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u017_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (8:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u017_uniform
-- u018 [2-edge cycle] 1->2->(closed) | cand_irred+z_irred
--   roles: abs=8, abs=1, abs=1, abs=6; 6 instances at bases [6, 7, 8]; all_strict=True; worst realized 1
/-- pattern tau=(): D ≡ 0 identically (weak kill: P ≡ 1 with the strict candidate edge); A and B coincide as polynomials. -/
theorem shape_u018_uniform : ∀ m : ℚ, 5 ≤ m → (441:ℚ) = (441:ℚ) := fun _ _ => rfl
#print axioms shape_u018_uniform
-- u019 [2-edge cycle] 1->2->(closed) | cand_irred+z_irred
--   roles: abs=8, abs=2, abs=2, abs=7; 6 instances at bases [7, 8, 9]; all_strict=True; worst realized 315/323
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u019_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (24:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u019_uniform
-- u020 [2-edge cycle] 1->2->(closed) | cand_irred+z_irred
--   roles: abs=10, abs=3, abs=3, abs=9; 4 instances at bases [9, 10]; all_strict=True; worst realized 1817/1825
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u020_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (8:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u020_uniform
-- u021 [2-edge cycle] 1->2->(closed) | cand_irred+z_irred
--   roles: abs=11, abs=3, abs=3, abs=10; 2 instances at bases [10]; all_strict=True; worst realized 667/675
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u021_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (24:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u021_uniform
-- u022 [2-edge cycle] 1->2->(closed) | cand_irred+z_irred
--   roles: abs=13, abs=1, abs=1, abs=10; 1 instances at bases [10]; all_strict=True; worst realized 721/729
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u022_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (8:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u022_uniform
-- u023 [2-edge cycle] 1->3->(closed) | cand_entry+z_entry
--   roles: abs=2, free+3..+4, tied+3, abs=1; 6 instances at bases [5, 7]; all_strict=True; worst realized 73/105
/-- pattern tau=(3): real half-line form, mono certificate (kind ALL, strict=True, deg D = 1). -/
theorem shape_u023_pat1_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (48:ℚ) * m + (120:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have hshift : (48:ℚ) * (m - 5) + (360:ℚ) = (48:ℚ) * m + (120:ℚ) := by ring
  linarith [ht, hshift]
#print axioms shape_u023_pat1_uniform
/-- pattern tau=(4): real half-line form, mono certificate (kind ALL, strict=True, deg D = 1). -/
theorem shape_u023_pat2_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (48:ℚ) * m + (48:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have hshift : (48:ℚ) * (m - 5) + (288:ℚ) = (48:ℚ) * m + (48:ℚ) := by ring
  linarith [ht, hshift]
#print axioms shape_u023_pat2_uniform
-- u024 [2-edge cycle] 1->3->(closed) | cand_entry+z_entry
--   roles: abs=3, abs=7, abs=7, abs=2; 5 instances at bases [5]; all_strict=True; worst realized 969/1265
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u024_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (296:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u024_uniform
-- u025 [2-edge cycle] 1->3->(closed) | cand_entry+z_entry
--   roles: abs=2, tied+4, tied+4, abs=1; 5 instances at bases [9, 10]; all_strict=True; worst realized 63/103
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 1). -/
theorem shape_u025_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (48:ℚ) * m + (168:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have hshift : (48:ℚ) * (m - 5) + (408:ℚ) = (48:ℚ) * m + (168:ℚ) := by ring
  linarith [ht, hshift]
#print axioms shape_u025_uniform
-- u026 [2-edge cycle] 1->3->(closed) | cand_entry+z_irred
--   roles: abs=3, free+2..+3, abs=2, tied+1; 6 instances at bases [5, 6, 7]; all_strict=True; worst realized 243/299
/-- pattern tau=(2): real half-line form, mono certificate (kind ALL, strict=True, deg D = 1). -/
theorem shape_u026_pat1_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (64:ℚ) * m - (48:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have hshift : (64:ℚ) * (m - 5) + (272:ℚ) = (64:ℚ) * m - (48:ℚ) := by ring
  linarith [ht, hshift]
#print axioms shape_u026_pat1_uniform
/-- pattern tau=(3): real half-line form, mono certificate (kind ALL, strict=True, deg D = 1). -/
theorem shape_u026_pat2_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (64:ℚ) * m - (168:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have hshift : (64:ℚ) * (m - 5) + (152:ℚ) = (64:ℚ) * m - (168:ℚ) := by ring
  linarith [ht, hshift]
#print axioms shape_u026_pat2_uniform
-- u027 [2-edge cycle] 1->3->(closed) | cand_entry+z_irred
--   roles: abs=5, tied+2, abs=4, tied+1; 3 instances at bases [8, 9, 10]; all_strict=True; worst realized 837/949
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 1). -/
theorem shape_u027_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (64:ℚ) * m - (176:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have hshift : (64:ℚ) * (m - 5) + (144:ℚ) = (64:ℚ) * m - (176:ℚ) := by ring
  linarith [ht, hshift]
#print axioms shape_u027_uniform
-- u028 [2-edge cycle] 1->3->(closed) | cand_entry+z_irred
--   roles: abs=6, tied+2, abs=5, tied+1; 3 instances at bases [8, 9, 10]; all_strict=True; worst realized 3159/3431
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 1). -/
theorem shape_u028_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (64:ℚ) * m - (240:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have hshift : (64:ℚ) * (m - 5) + (80:ℚ) = (64:ℚ) * m - (240:ℚ) := by ring
  linarith [ht, hshift]
#print axioms shape_u028_uniform
-- u029 [2-edge cycle] 1->3->(closed) | cand_entry+z_irred
--   roles: abs=2, abs=13, abs=1, abs=10; 2 instances at bases [9]; all_strict=True; worst realized 49/81
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u029_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (480:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u029_uniform
-- u030 [2-edge cycle] 1->3->(closed) | cand_entry+z_irred
--   roles: abs=4, tied+2, abs=3, tied+1; 4 instances at bases [9, 10]; all_strict=True; worst realized 2047/2511
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 1). -/
theorem shape_u030_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (64:ℚ) * m - (112:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have hshift : (64:ℚ) * (m - 5) + (208:ℚ) = (64:ℚ) * m - (112:ℚ) := by ring
  linarith [ht, hshift]
#print axioms shape_u030_uniform
-- u031 [2-edge cycle] 1->3->(closed) | cand_entry+z_irred
--   roles: abs=7, abs=12, abs=6, abs=11; 1 instances at bases [10]; all_strict=True; worst realized 4559/4895
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u031_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (336:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u031_uniform
-- u032 [2-edge cycle] 1->3->(closed) | cand_irred+z_irred
--   roles: tied+2, abs=2, abs=2, tied+1; 3 instances at bases [5, 6]; all_strict=True; worst realized 825/833
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 1). -/
theorem shape_u032_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (16:ℚ) * m - (72:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have hshift : (16:ℚ) * (m - 5) + (8:ℚ) = (16:ℚ) * m - (72:ℚ) := by ring
  linarith [ht, hshift]
#print axioms shape_u032_uniform
-- u033 [2-edge cycle] 1->3->(closed) | cand_irred+z_irred
--   roles: abs=11, abs=3, abs=3, abs=10; 1 instances at bases [9]; all_strict=True; worst realized 667/675
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u033_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (24:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u033_uniform
-- u034 [2-edge cycle] 1->4->(closed) | cand_entry+z_entry
--   roles: abs=3, tied+2, tied+2, abs=2; 7 instances at bases [5, 6]; all_strict=True; worst realized 969/1265
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 1). -/
theorem shape_u034_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (48:ℚ) * m + (56:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have hshift : (48:ℚ) * (m - 5) + (296:ℚ) = (48:ℚ) * m + (56:ℚ) := by ring
  linarith [ht, hshift]
#print axioms shape_u034_uniform
-- u035 [2-edge cycle] 1->4->(closed) | cand_entry+z_entry
--   roles: abs=4, tied+2, tied+2, abs=3; 20 instances at bases [5, 6, 7, 8, 9, 10]; all_strict=True; worst realized 285/341
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 1). -/
theorem shape_u035_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (48:ℚ) * m + (40:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have hshift : (48:ℚ) * (m - 5) + (280:ℚ) = (48:ℚ) * m + (40:ℚ) := by ring
  linarith [ht, hshift]
#print axioms shape_u035_uniform
-- u036 [2-edge cycle] 1->4->(closed) | cand_entry+z_entry
--   roles: abs=5, tied+2, tied+2, abs=4; 11 instances at bases [5, 6, 7, 8, 9]; all_strict=True; worst realized 57/65
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 1). -/
theorem shape_u036_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (48:ℚ) * m + (24:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have hshift : (48:ℚ) * (m - 5) + (264:ℚ) = (48:ℚ) * m + (24:ℚ) := by ring
  linarith [ht, hshift]
#print axioms shape_u036_uniform
-- u037 [2-edge cycle] 1->4->(closed) | cand_entry+z_entry
--   roles: abs=2, abs=9, abs=9, abs=1; 5 instances at bases [6]; all_strict=True; worst realized 219/355
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u037_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (408:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u037_uniform
-- u038 [2-edge cycle] 1->4->(closed) | cand_entry+z_entry
--   roles: abs=2, free+4..+5, tied+4, abs=1; 7 instances at bases [6, 7, 8, 9]; all_strict=True; worst realized 267/395
/-- pattern tau=(4): real half-line form, mono certificate (kind ALL, strict=True, deg D = 1). -/
theorem shape_u038_pat1_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (48:ℚ) * m + (168:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have hshift : (48:ℚ) * (m - 5) + (408:ℚ) = (48:ℚ) * m + (168:ℚ) := by ring
  linarith [ht, hshift]
#print axioms shape_u038_pat1_uniform
/-- pattern tau=(5): real half-line form, mono certificate (kind ALL, strict=True, deg D = 1). -/
theorem shape_u038_pat2_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (48:ℚ) * m + (96:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have hshift : (48:ℚ) * (m - 5) + (336:ℚ) = (48:ℚ) * m + (96:ℚ) := by ring
  linarith [ht, hshift]
#print axioms shape_u038_pat2_uniform
-- u039 [2-edge cycle] 1->4->(closed) | cand_entry+z_entry
--   roles: abs=6, tied+2, tied+2, abs=5; 5 instances at bases [6, 7, 8, 9]; all_strict=True; worst realized 2665/2961
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 1). -/
theorem shape_u039_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (48:ℚ) * m + (8:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have hshift : (48:ℚ) * (m - 5) + (248:ℚ) = (48:ℚ) * m + (8:ℚ) := by ring
  linarith [ht, hshift]
#print axioms shape_u039_uniform
-- u040 [2-edge cycle] 1->4->(closed) | cand_entry+z_entry
--   roles: abs=7, tied+2, tied+2, abs=6; 3 instances at bases [7, 8, 9]; all_strict=True; worst realized 3577/3905
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 1). -/
theorem shape_u040_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (48:ℚ) * m - (8:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have hshift : (48:ℚ) * (m - 5) + (232:ℚ) = (48:ℚ) * m - (8:ℚ) := by ring
  linarith [ht, hshift]
#print axioms shape_u040_uniform
-- u041 [2-edge cycle] 1->4->(closed) | cand_entry+z_entry
--   roles: abs=3, tied+3, tied+3, abs=2; 3 instances at bases [9, 10]; all_strict=True; worst realized 1649/2185
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 1). -/
theorem shape_u041_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (48:ℚ) * m + (104:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have hshift : (48:ℚ) * (m - 5) + (344:ℚ) = (48:ℚ) * m + (104:ℚ) := by ring
  linarith [ht, hshift]
#print axioms shape_u041_uniform
-- u042 [2-edge cycle] 1->4->(closed) | cand_entry+z_entry
--   roles: abs=8, tied+2, tied+2, abs=7; 2 instances at bases [9, 10]; all_strict=True; worst realized 1691/1827
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 1). -/
theorem shape_u042_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (48:ℚ) * m - (24:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have hshift : (48:ℚ) * (m - 5) + (216:ℚ) = (48:ℚ) * m - (24:ℚ) := by ring
  linarith [ht, hshift]
#print axioms shape_u042_uniform
-- u043 [2-edge cycle] 1->4->(closed) | cand_entry+z_entry
--   roles: abs=2, abs=15, abs=15, abs=1; 1 instances at bases [10]; all_strict=True; worst realized 363/595
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u043_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (696:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u043_uniform
-- u044 [2-edge cycle] 1->4->(closed) | cand_entry+z_entry
--   roles: abs=9, abs=12, abs=12, abs=8; 1 instances at bases [10]; all_strict=True; worst realized 1261/1349
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u044_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (440:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u044_uniform
-- u045 [2-edge cycle] 1->5->(closed) | cand_entry+z_entry
--   roles: abs=2, free+4..+5, tied+4, abs=1; 19 instances at bases [5, 6, 7, 8]; all_strict=True; worst realized 267/395
/-- pattern tau=(4): real half-line form, mono certificate (kind ALL, strict=True, deg D = 1). -/
theorem shape_u045_pat1_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (48:ℚ) * m + (168:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have hshift : (48:ℚ) * (m - 5) + (408:ℚ) = (48:ℚ) * m + (168:ℚ) := by ring
  linarith [ht, hshift]
#print axioms shape_u045_pat1_uniform
/-- pattern tau=(5): real half-line form, mono certificate (kind ALL, strict=True, deg D = 1). -/
theorem shape_u045_pat2_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (48:ℚ) * m + (96:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have hshift : (48:ℚ) * (m - 5) + (336:ℚ) = (48:ℚ) * m + (96:ℚ) := by ring
  linarith [ht, hshift]
#print axioms shape_u045_pat2_uniform
-- u046 [2-edge cycle] 1->5->(closed) | cand_entry+z_entry
--   roles: abs=2, free+5..+6, tied+5, abs=1; 6 instances at bases [5, 6, 9]; all_strict=True; worst realized 121/185
/-- pattern tau=(5): real half-line form, mono certificate (kind ALL, strict=True, deg D = 1). -/
theorem shape_u046_pat1_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (48:ℚ) * m + (216:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have hshift : (48:ℚ) * (m - 5) + (456:ℚ) = (48:ℚ) * m + (216:ℚ) := by ring
  linarith [ht, hshift]
#print axioms shape_u046_pat1_uniform
/-- pattern tau=(6): real half-line form, mono certificate (kind ALL, strict=True, deg D = 1). -/
theorem shape_u046_pat2_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (48:ℚ) * m + (144:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have hshift : (48:ℚ) * (m - 5) + (384:ℚ) = (48:ℚ) * m + (144:ℚ) := by ring
  linarith [ht, hshift]
#print axioms shape_u046_pat2_uniform
-- u047 [2-edge cycle] 1->5->(closed) | cand_entry+z_entry
--   roles: abs=3, tied+3, tied+3, abs=2; 20 instances at bases [5, 6, 7, 8, 9, 10]; all_strict=True; worst realized 1105/1449
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 1). -/
theorem shape_u047_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (48:ℚ) * m + (104:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have hshift : (48:ℚ) * (m - 5) + (344:ℚ) = (48:ℚ) * m + (104:ℚ) := by ring
  linarith [ht, hshift]
#print axioms shape_u047_uniform
-- u048 [2-edge cycle] 1->5->(closed) | cand_entry+z_entry
--   roles: abs=4, tied+2, tied+2, abs=3; 12 instances at bases [5, 6, 7]; all_strict=True; worst realized 285/341
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 1). -/
theorem shape_u048_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (48:ℚ) * m + (40:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have hshift : (48:ℚ) * (m - 5) + (280:ℚ) = (48:ℚ) * m + (40:ℚ) := by ring
  linarith [ht, hshift]
#print axioms shape_u048_uniform
-- u049 [2-edge cycle] 1->5->(closed) | cand_entry+z_entry
--   roles: abs=5, tied+2, tied+2, abs=4; 20 instances at bases [5, 6, 7, 8, 9]; all_strict=True; worst realized 57/65
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 1). -/
theorem shape_u049_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (48:ℚ) * m + (24:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have hshift : (48:ℚ) * (m - 5) + (264:ℚ) = (48:ℚ) * m + (24:ℚ) := by ring
  linarith [ht, hshift]
#print axioms shape_u049_uniform
-- u050 [2-edge cycle] 1->5->(closed) | cand_entry+z_entry
--   roles: abs=6, tied+2, tied+2, abs=5; 19 instances at bases [6, 7, 8, 9, 10]; all_strict=True; worst realized 2665/2961
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 1). -/
theorem shape_u050_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (48:ℚ) * m + (8:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have hshift : (48:ℚ) * (m - 5) + (248:ℚ) = (48:ℚ) * m + (8:ℚ) := by ring
  linarith [ht, hshift]
#print axioms shape_u050_uniform
-- u051 [2-edge cycle] 1->5->(closed) | cand_entry+z_entry
--   roles: abs=7, tied+2, tied+2, abs=6; 11 instances at bases [7, 8, 9, 10]; all_strict=True; worst realized 3577/3905
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 1). -/
theorem shape_u051_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (48:ℚ) * m - (8:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have hshift : (48:ℚ) * (m - 5) + (232:ℚ) = (48:ℚ) * m - (8:ℚ) := by ring
  linarith [ht, hshift]
#print axioms shape_u051_uniform
-- u052 [2-edge cycle] 1->5->(closed) | cand_entry+z_entry
--   roles: abs=8, tied+2, tied+2, abs=7; 4 instances at bases [8, 9, 10]; all_strict=True; worst realized 513/553
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 1). -/
theorem shape_u052_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (48:ℚ) * m - (24:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have hshift : (48:ℚ) * (m - 5) + (216:ℚ) = (48:ℚ) * m - (24:ℚ) := by ring
  linarith [ht, hshift]
#print axioms shape_u052_uniform
-- u053 [2-edge cycle] 1->5->(closed) | cand_entry+z_entry
--   roles: abs=9, tied+2, tied+2, abs=8; 2 instances at bases [9, 10]; all_strict=True; worst realized 5785/6177
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 1). -/
theorem shape_u053_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (48:ℚ) * m - (40:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have hshift : (48:ℚ) * (m - 5) + (200:ℚ) = (48:ℚ) * m - (40:ℚ) := by ring
  linarith [ht, hshift]
#print axioms shape_u053_uniform
-- u054 [2-edge cycle] 1->5->(closed) | cand_entry+z_entry
--   roles: abs=4, abs=13, abs=13, abs=3; 2 instances at bases [10]; all_strict=True; worst realized 2625/3193
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u054_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (568:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u054_uniform
-- u055 [2-edge cycle] 1->5->(closed) | cand_entry+z_entry
--   roles: abs=10, abs=12, abs=12, abs=9; 1 instances at bases [10]; all_strict=True; worst realized 7081/7505
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u055_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (424:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u055_uniform
-- u056 [2-edge cycle] 1->5->(closed) | cand_entry+z_irred
--   roles: abs=3, abs=7, abs=2, abs=6; 3 instances at bases [5]; all_strict=True; worst realized 855/1127
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u056_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (272:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u056_uniform
-- u057 [2-edge cycle] 1->5->(closed) | cand_entry+z_irred
--   roles: abs=2, tied+4, abs=1, tied+1; 5 instances at bases [8, 9]; all_strict=True; worst realized 679/1095
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 1). -/
theorem shape_u057_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (64:ℚ) * m - (96:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have hshift : (64:ℚ) * (m - 5) + (224:ℚ) = (64:ℚ) * m - (96:ℚ) := by ring
  linarith [ht, hshift]
#print axioms shape_u057_uniform
-- u058 [2-edge cycle] 1->5->(closed) | cand_entry+z_irred
--   roles: abs=4, tied+2, abs=3, tied+1; 4 instances at bases [8, 9]; all_strict=True; worst realized 1863/2263
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 1). -/
theorem shape_u058_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (64:ℚ) * m - (112:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have hshift : (64:ℚ) * (m - 5) + (208:ℚ) = (64:ℚ) * m - (112:ℚ) := by ring
  linarith [ht, hshift]
#print axioms shape_u058_uniform
-- u059 [2-edge cycle] 1->5->(closed) | cand_irred+z_irred
--   roles: abs=8, abs=1, abs=1, abs=6; 1 instances at bases [5]; all_strict=True; worst realized 1
/-- pattern tau=(): D ≡ 0 identically (weak kill: P ≡ 1 with the strict candidate edge); A and B coincide as polynomials. -/
theorem shape_u059_uniform : ∀ m : ℚ, 5 ≤ m → (441:ℚ) = (441:ℚ) := fun _ _ => rfl
#print axioms shape_u059_uniform
-- u060 [2-edge cycle] 1->6->(closed) | cand_entry+z_entry
--   roles: abs=5, tied+2, tied+2, abs=4; 6 instances at bases [5, 6]; all_strict=True; worst realized 57/65
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 1). -/
theorem shape_u060_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (48:ℚ) * m + (24:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have hshift : (48:ℚ) * (m - 5) + (264:ℚ) = (48:ℚ) * m + (24:ℚ) := by ring
  linarith [ht, hshift]
#print axioms shape_u060_uniform
-- u061 [2-edge cycle] 1->6->(closed) | cand_entry+z_entry
--   roles: abs=6, tied+2, tied+2, abs=5; 13 instances at bases [5, 6, 7, 8]; all_strict=True; worst realized 2337/2585
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 1). -/
theorem shape_u061_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (48:ℚ) * m + (8:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have hshift : (48:ℚ) * (m - 5) + (248:ℚ) = (48:ℚ) * m + (8:ℚ) := by ring
  linarith [ht, hshift]
#print axioms shape_u061_uniform
-- u062 [2-edge cycle] 1->6->(closed) | cand_entry+z_entry
--   roles: abs=2, abs=12, abs=12, abs=1; 2 instances at bases [6]; all_strict=True; worst realized 291/475
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u062_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (552:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u062_uniform
-- u063 [2-edge cycle] 1->6->(closed) | cand_entry+z_entry
--   roles: abs=3, tied+3, tied+3, abs=2; 17 instances at bases [6, 7, 8, 9]; all_strict=True; worst realized 1241/1633
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 1). -/
theorem shape_u063_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (48:ℚ) * m + (104:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have hshift : (48:ℚ) * (m - 5) + (344:ℚ) = (48:ℚ) * m + (104:ℚ) := by ring
  linarith [ht, hshift]
#print axioms shape_u063_uniform
-- u064 [2-edge cycle] 1->6->(closed) | cand_entry+z_entry
--   roles: abs=7, tied+2, tied+2, abs=6; 17 instances at bases [6, 7, 8, 9, 10]; all_strict=True; worst realized 91/99
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 1). -/
theorem shape_u064_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (48:ℚ) * m - (8:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have hshift : (48:ℚ) * (m - 5) + (232:ℚ) = (48:ℚ) * m - (8:ℚ) := by ring
  linarith [ht, hshift]
#print axioms shape_u064_uniform
-- u065 [2-edge cycle] 1->6->(closed) | cand_entry+z_entry
--   roles: abs=8, tied+2, tied+2, abs=7; 16 instances at bases [7, 8, 9, 10]; all_strict=True; worst realized 1387/1491
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 1). -/
theorem shape_u065_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (48:ℚ) * m - (24:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have hshift : (48:ℚ) * (m - 5) + (216:ℚ) = (48:ℚ) * m - (24:ℚ) := by ring
  linarith [ht, hshift]
#print axioms shape_u065_uniform
-- u066 [2-edge cycle] 1->6->(closed) | cand_entry+z_entry
--   roles: abs=4, tied+3, tied+3, abs=3; 3 instances at bases [8, 9, 10]; all_strict=True; worst realized 2225/2697
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 1). -/
theorem shape_u066_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (48:ℚ) * m + (88:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have hshift : (48:ℚ) * (m - 5) + (328:ℚ) = (48:ℚ) * m + (88:ℚ) := by ring
  linarith [ht, hshift]
#print axioms shape_u066_uniform
-- u067 [2-edge cycle] 1->6->(closed) | cand_entry+z_entry
--   roles: abs=9, tied+2, tied+2, abs=8; 11 instances at bases [8, 9, 10]; all_strict=True; worst realized 5265/5609
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 1). -/
theorem shape_u067_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (48:ℚ) * m - (40:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have hshift : (48:ℚ) * (m - 5) + (200:ℚ) = (48:ℚ) * m - (40:ℚ) := by ring
  linarith [ht, hshift]
#print axioms shape_u067_uniform
-- u068 [2-edge cycle] 1->6->(closed) | cand_entry+z_entry
--   roles: abs=10, tied+2, tied+2, abs=9; 6 instances at bases [9, 10]; all_strict=True; worst realized 6497/6873
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 1). -/
theorem shape_u068_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (48:ℚ) * m - (56:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have hshift : (48:ℚ) * (m - 5) + (184:ℚ) = (48:ℚ) * m - (56:ℚ) := by ring
  linarith [ht, hshift]
#print axioms shape_u068_uniform
-- u069 [2-edge cycle] 1->6->(closed) | cand_entry+z_entry
--   roles: abs=5, abs=13, abs=13, abs=4; 2 instances at bases [10]; all_strict=True; worst realized 1155/1339
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u069_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (552:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u069_uniform
-- u070 [2-edge cycle] 1->6->(closed) | cand_entry+z_entry
--   roles: abs=11, abs=12, abs=12, abs=10; 2 instances at bases [10]; all_strict=True; worst realized 2619/2755
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u070_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (408:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u070_uniform
-- u071 [2-edge cycle] 1->6->(closed) | cand_entry+z_irred
--   roles: abs=4, abs=7, abs=3, abs=6; 6 instances at bases [5]; all_strict=True; worst realized 1311/1519
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u071_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (208:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u071_uniform
-- u072 [2-edge cycle] 1->6->(closed) | cand_entry+z_irred
--   roles: tied=base, tied+2, tied-1, tied+1; 5 instances at bases [5, 6]; all_strict=True; worst realized 845/893
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u072_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (144:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u072_uniform
-- u073 [2-edge cycle] 2->1->(closed) | cand_progress+z_progress
--   roles: abs=1, abs=7, abs=7, abs=2; 2 instances at bases [7, 8]; all_strict=True; worst realized 9/17
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u073_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (456:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u073_uniform
-- u074 [2-edge cycle] 2->1->(closed) | cand_progress+z_progress
--   roles: abs=1, abs=8, abs=8, abs=2; 2 instances at bases [8, 9]; all_strict=True; worst realized 9/17
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u074_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (520:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u074_uniform
-- u075 [2-edge cycle] 2->1->(closed) | cand_progress+z_progress
--   roles: abs=2, abs=9, abs=9, abs=3; 1 instances at bases [9]; all_strict=True; worst realized 17/25
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u075_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (584:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u075_uniform
-- u076 [2-edge cycle] 2->1->(closed) | cand_progress+z_progress
--   roles: abs=1, abs=10, abs=10, abs=2; 1 instances at bases [10]; all_strict=True; worst realized 9/17
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u076_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (648:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u076_uniform
-- u077 [2-edge cycle] 2->3->(closed) | cand_entry+z_entry
--   roles: abs=4, abs=7, abs=7, abs=3; 1 instances at bases [5]; all_strict=True; worst realized 285/341
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u077_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (280:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u077_uniform
-- u078 [2-edge cycle] 2->3->(closed) | cand_entry+z_entry
--   roles: abs=7, abs=7, abs=7, abs=6; 2 instances at bases [5]; all_strict=True; worst realized 2793/3025
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u078_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (232:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u078_uniform
-- u079 [2-edge cycle] 2->3->(closed) | cand_entry+z_entry
--   roles: abs=6, abs=10, abs=10, abs=5; 2 instances at bases [7]; all_strict=True; worst realized 3321/3713
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u079_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (392:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u079_uniform
-- u080 [2-edge cycle] 2->3->(closed) | cand_entry+z_entry
--   roles: abs=10, abs=10, abs=10, abs=9; 1 instances at bases [7]; all_strict=True; worst realized 5913/6241
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u080_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (328:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u080_uniform
-- u081 [2-edge cycle] 2->3->(closed) | cand_entry+z_entry
--   roles: tied+4, tied+4, tied+4, tied+3; 5 instances at bases [9, 10]; all_strict=True; worst realized 3955/4107
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 1). -/
theorem shape_u081_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (32:ℚ) * m + (136:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have hshift : (32:ℚ) * (m - 5) + (296:ℚ) = (32:ℚ) * m + (136:ℚ) := by ring
  linarith [ht, hshift]
#print axioms shape_u081_uniform
-- u082 [2-edge cycle] 2->3->(closed) | cand_irred+z_entry
--   roles: abs=11, abs=7, abs=8, abs=5; 2 instances at bases [7]; all_strict=True; worst realized 1189/1197
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u082_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (24:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u082_uniform
-- u083 [2-edge cycle] 2->3->(closed) | cand_irred+z_entry
--   roles: abs=15, abs=11, abs=11, abs=8; 1 instances at bases [10]; all_strict=True; worst realized 7735/7743
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u083_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (8:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u083_uniform
-- u084 [2-edge cycle] 2->4->(closed) | cand_entry+z_entry
--   roles: abs=5, abs=7, abs=7, abs=4; 4 instances at bases [5]; all_strict=True; worst realized 57/65
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u084_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (264:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u084_uniform
-- u085 [2-edge cycle] 2->4->(closed) | cand_entry+z_entry
--   roles: abs=6, abs=7, abs=7, abs=5; 1 instances at bases [5]; all_strict=True; worst realized 2337/2585
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u085_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (248:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u085_uniform
-- u086 [2-edge cycle] 2->4->(closed) | cand_entry+z_entry
--   roles: abs=7, abs=7, abs=7, abs=6; 2 instances at bases [5]; all_strict=True; worst realized 2793/3025
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u086_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (232:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u086_uniform
-- u087 [2-edge cycle] 2->4->(closed) | cand_entry+z_entry
--   roles: tied=base, tied+3, tied+3, tied-1; 12 instances at bases [6, 7]; all_strict=True; worst realized 3969/4345
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 1). -/
theorem shape_u087_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (32:ℚ) * m + (152:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have hshift : (32:ℚ) * (m - 5) + (312:ℚ) = (32:ℚ) * m + (152:ℚ) := by ring
  linarith [ht, hshift]
#print axioms shape_u087_uniform
-- u088 [2-edge cycle] 2->4->(closed) | cand_entry+z_entry
--   roles: abs=7, abs=11, abs=11, abs=6; 2 instances at bases [8]; all_strict=True; worst realized 4361/4785
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u088_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (424:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u088_uniform
-- u089 [2-edge cycle] 2->5->(closed) | cand_entry+z_entry
--   roles: abs=4, abs=7, abs=7, abs=3; 1 instances at bases [5]; all_strict=True; worst realized 285/341
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u089_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (280:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u089_uniform
-- u090 [2-edge cycle] 2->5->(closed) | cand_entry+z_entry
--   roles: abs=5, abs=7, abs=7, abs=4; 2 instances at bases [5]; all_strict=True; worst realized 57/65
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u090_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (264:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u090_uniform
-- u091 [2-edge cycle] 2->5->(closed) | cand_entry+z_entry
--   roles: abs=6, abs=7, abs=7, abs=5; 4 instances at bases [5]; all_strict=True; worst realized 2337/2585
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u091_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (248:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u091_uniform
-- u092 [2-edge cycle] 2->5->(closed) | cand_entry+z_entry
--   roles: abs=7, abs=7, abs=7, abs=6; 4 instances at bases [5]; all_strict=True; worst realized 2793/3025
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u092_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (232:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u092_uniform
-- u093 [2-edge cycle] 2->5->(closed) | cand_entry+z_entry
--   roles: tied=base, tied+3, tied+3, tied-1; 6 instances at bases [8, 10]; all_strict=True; worst realized 7665/8137
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 1). -/
theorem shape_u093_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (32:ℚ) * m + (152:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have hshift : (32:ℚ) * (m - 5) + (312:ℚ) = (32:ℚ) * m + (152:ℚ) := by ring
  linarith [ht, hshift]
#print axioms shape_u093_uniform
-- u094 [2-edge cycle] 2->5->(closed) | cand_entry+z_entry
--   roles: abs=10, abs=12, abs=12, abs=9; 1 instances at bases [8]; all_strict=True; worst realized 7081/7505
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u094_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (424:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u094_uniform
-- u095 [2-edge cycle] 2->5->(closed) | cand_entry+z_entry
--   roles: abs=13, abs=15, abs=15, abs=12; 3 instances at bases [10]; all_strict=True; worst realized 11737/12257
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u095_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (520:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u095_uniform
-- u096 [2-edge cycle] 2->6->(closed) | cand_entry+z_entry
--   roles: abs=5, free+2..+3, tied+2, abs=4; 4 instances at bases [5, 7]; all_strict=True; worst realized 891/923
/-- pattern tau=(2): real half-line form, mono certificate (kind ALL, strict=True, deg D = 1). -/
theorem shape_u096_pat1_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (48:ℚ) * m + (24:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have hshift : (48:ℚ) * (m - 5) + (264:ℚ) = (48:ℚ) * m + (24:ℚ) := by ring
  linarith [ht, hshift]
#print axioms shape_u096_pat1_uniform
/-- pattern tau=(3): real half-line form, mono certificate (kind ALL, strict=False, deg D = 1). -/
theorem shape_u096_pat2_uniform : ∀ m : ℚ, 5 ≤ m → 0 ≤ (48:ℚ) * m - (240:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have hshift : (48:ℚ) * (m - 5) = (48:ℚ) * m - (240:ℚ) := by ring
  linarith [ht, hshift]
#print axioms shape_u096_pat2_uniform
-- u097 [2-edge cycle] 2->6->(closed) | cand_entry+z_entry
--   roles: tied+1, tied+2, tied+2, tied=base; 4 instances at bases [5, 6]; all_strict=True; worst realized 91/99
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 1). -/
theorem shape_u097_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (32:ℚ) * m + (88:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have hshift : (32:ℚ) * (m - 5) + (248:ℚ) = (32:ℚ) * m + (88:ℚ) := by ring
  linarith [ht, hshift]
#print axioms shape_u097_uniform
-- u098 [2-edge cycle] 2->6->(closed) | cand_entry+z_entry
--   roles: abs=8, tied+3, tied+3, abs=7; 6 instances at bases [6, 7]; all_strict=True; worst realized 1387/1491
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 1). -/
theorem shape_u098_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (48:ℚ) * m + (24:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have hshift : (48:ℚ) * (m - 5) + (264:ℚ) = (48:ℚ) * m + (24:ℚ) := by ring
  linarith [ht, hshift]
#print axioms shape_u098_uniform
-- u099 [2-edge cycle] 2->6->(closed) | cand_entry+z_entry
--   roles: abs=9, tied+3, tied+3, abs=8; 6 instances at bases [7, 8]; all_strict=True; worst realized 5265/5609
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 1). -/
theorem shape_u099_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (48:ℚ) * m + (8:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have hshift : (48:ℚ) * (m - 5) + (248:ℚ) = (48:ℚ) * m + (8:ℚ) := by ring
  linarith [ht, hshift]
#print axioms shape_u099_uniform
-- u100 [2-edge cycle] 2->6->(closed) | cand_entry+z_entry
--   roles: tied+1, tied+3, tied+3, tied=base; 7 instances at bases [9, 10]; all_strict=True; worst realized 2835/2987
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 1). -/
theorem shape_u100_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (32:ℚ) * m + (136:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have hshift : (32:ℚ) * (m - 5) + (296:ℚ) = (32:ℚ) * m + (136:ℚ) := by ring
  linarith [ht, hshift]
#print axioms shape_u100_uniform
-- u101 [2-edge cycle] 2->6->(closed) | cand_entry+z_irred
--   roles: abs=2, free+5..+6, abs=1, tied+1; 3 instances at bases [5, 6]; all_strict=True; worst realized 679/855
/-- pattern tau=(5): real half-line form, mono certificate (kind ALL, strict=True, deg D = 1). -/
theorem shape_u101_pat1_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (64:ℚ) * m - (152:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have hshift : (64:ℚ) * (m - 5) + (168:ℚ) = (64:ℚ) * m - (152:ℚ) := by ring
  linarith [ht, hshift]
#print axioms shape_u101_pat1_uniform
/-- pattern tau=(6): real half-line form, mono certificate (kind ALL, strict=True, deg D = 1). -/
theorem shape_u101_pat2_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (64:ℚ) * m - (208:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have hshift : (64:ℚ) * (m - 5) + (112:ℚ) = (64:ℚ) * m - (208:ℚ) := by ring
  linarith [ht, hshift]
#print axioms shape_u101_pat2_uniform
-- u102 [2-edge cycle] 2->6->(closed) | cand_entry+z_irred
--   roles: abs=4, free+2..+3, abs=3, tied+1; 5 instances at bases [5, 6]; all_strict=True; worst realized 1679/1767
/-- pattern tau=(2): real half-line form, mono certificate (kind ALL, strict=True, deg D = 1). -/
theorem shape_u102_pat1_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (64:ℚ) * m - (112:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have hshift : (64:ℚ) * (m - 5) + (208:ℚ) = (64:ℚ) * m - (112:ℚ) := by ring
  linarith [ht, hshift]
#print axioms shape_u102_pat1_uniform
/-- pattern tau=(3): real half-line form, mono certificate (kind ALL, strict=True, deg D = 1). -/
theorem shape_u102_pat2_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (64:ℚ) * m - (296:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have hshift : (64:ℚ) * (m - 5) + (24:ℚ) = (64:ℚ) * m - (296:ℚ) := by ring
  linarith [ht, hshift]
#print axioms shape_u102_pat2_uniform
-- u103 [2-edge cycle] 2->6->(closed) | cand_entry+z_irred
--   roles: abs=3, abs=9, abs=2, abs=7; 2 instances at bases [6]; all_strict=True; worst realized 365/437
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u103_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (216:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u103_uniform
-- u104 [2-edge cycle] 2->6->(closed) | cand_entry+z_irred
--   roles: abs=4, abs=12, abs=3, abs=11; 1 instances at bases [6]; all_strict=True; worst realized 2231/2759
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u104_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (528:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u104_uniform
-- u105 [2-edge cycle] 2->6->(closed) | cand_irred+z_irred
--   roles: abs=9, abs=6, abs=5, abs=7; 3 instances at bases [6]; all_strict=True; worst realized 923/931
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u105_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (24:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u105_uniform
-- u106 [2-edge cycle] 2->6->(closed) | cand_progress+z_irred
--   roles: abs=11, abs=8, abs=7, abs=10; 1 instances at bases [9]; all_strict=True; worst realized 979/1053
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u106_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (370:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u106_uniform
-- u107 [2-edge cycle] 3->1->(closed) | cand_progress+z_entry
--   roles: abs=1, abs=7, abs=2, abs=6; 2 instances at bases [5]; all_strict=True; worst realized 49/95
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u107_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (414:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u107_uniform
-- u108 [2-edge cycle] 3->1->(closed) | cand_progress+z_entry
--   roles: abs=3, abs=12, abs=4, abs=11; 1 instances at bases [10]; all_strict=True; worst realized 2225/3007
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u108_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (782:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u108_uniform
-- u109 [2-edge cycle] 3->1->(closed) | cand_progress+z_irred
--   roles: abs=1, tied+2, tied+2, abs=2; 7 instances at bases [5, 8]; all_strict=True; worst realized 79/153
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 1). -/
theorem shape_u109_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (64:ℚ) * m + (154:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have hshift : (64:ℚ) * (m - 5) + (474:ℚ) = (64:ℚ) * m + (154:ℚ) := by ring
  linarith [ht, hshift]
#print axioms shape_u109_uniform
-- u110 [2-edge cycle] 3->1->(closed) | cand_progress+z_irred
--   roles: abs=2, tied+2, tied+2, abs=3; 3 instances at bases [8, 9, 10]; all_strict=True; worst realized 323/485
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 1). -/
theorem shape_u110_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (64:ℚ) * m + (170:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have hshift : (64:ℚ) * (m - 5) + (490:ℚ) = (64:ℚ) * m + (170:ℚ) := by ring
  linarith [ht, hshift]
#print axioms shape_u110_uniform
-- u111 [2-edge cycle] 3->1->(closed) | cand_progress+z_irred
--   roles: abs=3, tied+2, tied+2, abs=4; 2 instances at bases [9, 10]; all_strict=True; worst realized 2375/3201
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 1). -/
theorem shape_u111_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (64:ℚ) * m + (186:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have hshift : (64:ℚ) * (m - 5) + (506:ℚ) = (64:ℚ) * m + (186:ℚ) := by ring
  linarith [ht, hshift]
#print axioms shape_u111_uniform
-- u112 [2-edge cycle] 3->1->(closed) | cand_progress+z_progress
--   roles: abs=1, tied+2, tied+2, abs=2; 16 instances at bases [5, 6, 7, 8, 9, 10]; all_strict=True; worst realized 9/17
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 1). -/
theorem shape_u112_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (64:ℚ) * m + (136:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have hshift : (64:ℚ) * (m - 5) + (456:ℚ) = (64:ℚ) * m + (136:ℚ) := by ring
  linarith [ht, hshift]
#print axioms shape_u112_uniform
-- u113 [2-edge cycle] 3->1->(closed) | cand_progress+z_progress
--   roles: tied-3, tied+1, tied+1, tied-2; 9 instances at bases [5, 6, 7, 8]; all_strict=True; worst realized 41/49
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 1). -/
theorem shape_u113_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (64:ℚ) * m + (72:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have hshift : (64:ℚ) * (m - 5) + (392:ℚ) = (64:ℚ) * m + (72:ℚ) := by ring
  linarith [ht, hshift]
#print axioms shape_u113_uniform
-- u114 [2-edge cycle] 3->1->(closed) | cand_progress+z_progress
--   roles: abs=3, tied+1, tied+1, abs=4; 6 instances at bases [5, 7]; all_strict=True; worst realized 25/33
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 1). -/
theorem shape_u114_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (64:ℚ) * m + (72:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have hshift : (64:ℚ) * (m - 5) + (392:ℚ) = (64:ℚ) * m + (72:ℚ) := by ring
  linarith [ht, hshift]
#print axioms shape_u114_uniform
-- u115 [2-edge cycle] 3->1->(closed) | cand_progress+z_progress
--   roles: abs=4, tied+1, tied+1, abs=5; 6 instances at bases [8, 9]; all_strict=True; worst realized 33/41
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 1). -/
theorem shape_u115_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (64:ℚ) * m + (72:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have hshift : (64:ℚ) * (m - 5) + (392:ℚ) = (64:ℚ) * m + (72:ℚ) := by ring
  linarith [ht, hshift]
#print axioms shape_u115_uniform
-- u116 [2-edge cycle] 3->1->(closed) | cand_progress+z_progress
--   roles: abs=2, tied+2, tied+2, abs=3; 4 instances at bases [9, 10]; all_strict=True; worst realized 17/25
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 1). -/
theorem shape_u116_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (64:ℚ) * m + (136:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have hshift : (64:ℚ) * (m - 5) + (456:ℚ) = (64:ℚ) * m + (136:ℚ) := by ring
  linarith [ht, hshift]
#print axioms shape_u116_uniform
-- u117 [2-edge cycle] 3->1->(closed) | cand_progress+z_progress
--   roles: abs=5, tied+1, tied+1, abs=6; 4 instances at bases [9, 10]; all_strict=True; worst realized 41/49
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 1). -/
theorem shape_u117_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (64:ℚ) * m + (72:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have hshift : (64:ℚ) * (m - 5) + (392:ℚ) = (64:ℚ) * m + (72:ℚ) := by ring
  linarith [ht, hshift]
#print axioms shape_u117_uniform
-- u118 [2-edge cycle] 3->1->(closed) | cand_progress+z_progress
--   roles: abs=6, abs=11, abs=11, abs=7; 1 instances at bases [10]; all_strict=True; worst realized 49/57
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u118_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (712:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u118_uniform
-- u119 [2-edge cycle] 3->2->(closed) | cand_entry+z_entry
--   roles: tied+4, tied+1, tied+1, tied+3; 2 instances at bases [6, 7]; all_strict=True; worst realized 195/203
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 1). -/
theorem shape_u119_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (32:ℚ) * m - (8:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have hshift : (32:ℚ) * (m - 5) + (152:ℚ) = (32:ℚ) * m - (8:ℚ) := by ring
  linarith [ht, hshift]
#print axioms shape_u119_uniform
-- u120 [2-edge cycle] 3->2->(closed) | cand_progress+z_irred
--   roles: tied-3, tied+1, tied+1, tied-2; 3 instances at bases [5, 7, 9]; all_strict=True; worst realized 3871/4617
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 1). -/
theorem shape_u120_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (80:ℚ) * m + (26:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have hshift : (80:ℚ) * (m - 5) + (426:ℚ) = (80:ℚ) * m + (26:ℚ) := by ring
  linarith [ht, hshift]
#print axioms shape_u120_uniform
-- u121 [2-edge cycle] 3->2->(closed) | cand_progress+z_irred
--   roles: abs=2, abs=7, abs=7, abs=3; 1 instances at bases [5]; all_strict=True; worst realized 187/285
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u121_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (490:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u121_uniform
-- u122 [2-edge cycle] 3->2->(closed) | cand_progress+z_irred
--   roles: abs=3, tied+1, tied+1, abs=4; 2 instances at bases [5, 7]; all_strict=True; worst realized 105/143
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 1). -/
theorem shape_u122_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (64:ℚ) * m + (122:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have hshift : (64:ℚ) * (m - 5) + (442:ℚ) = (64:ℚ) * m + (122:ℚ) := by ring
  linarith [ht, hshift]
#print axioms shape_u122_uniform
-- u123 [2-edge cycle] 3->2->(closed) | cand_progress+z_irred
--   roles: abs=3, abs=7, abs=7, abs=4; 1 instances at bases [5]; all_strict=True; worst realized 125/171
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u123_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (506:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u123_uniform
-- u124 [2-edge cycle] 3->2->(closed) | cand_progress+z_irred
--   roles: tied-2, tied+1, tied+1, tied-1; 2 instances at bases [7, 9]; all_strict=True; worst realized 1501/1755
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 1). -/
theorem shape_u124_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (80:ℚ) * m + (42:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have hshift : (80:ℚ) * (m - 5) + (442:ℚ) = (80:ℚ) * m + (42:ℚ) := by ring
  linarith [ht, hshift]
#print axioms shape_u124_uniform
-- u125 [2-edge cycle] 3->2->(closed) | cand_progress+z_irred
--   roles: abs=8, abs=10, abs=10, abs=9; 1 instances at bases [7]; all_strict=True; worst realized 5135/5913
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u125_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (778:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u125_uniform
-- u126 [2-edge cycle] 3->2->(closed) | cand_progress+z_irred
--   roles: tied+2, tied+4, tied+4, tied+3; 5 instances at bases [9, 10]; all_strict=True; worst realized 3589/3955
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 1). -/
theorem shape_u126_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (80:ℚ) * m + (298:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have hshift : (80:ℚ) * (m - 5) + (698:ℚ) = (80:ℚ) * m + (298:ℚ) := by ring
  linarith [ht, hshift]
#print axioms shape_u126_uniform
-- u127 [2-edge cycle] 3->2->(closed) | cand_progress+z_progress
--   roles: abs=4, abs=6, abs=6, abs=5; 1 instances at bases [5]; all_strict=True; worst realized 33/41
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u127_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (392:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u127_uniform
-- u128 [2-edge cycle] 4->1->(closed) | cand_progress+z_entry
--   roles: abs=1, tied+2, abs=2, tied+1; 3 instances at bases [5, 6]; all_strict=True; worst realized 171/325
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 1). -/
theorem shape_u128_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (48:ℚ) * m + (174:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have hshift : (48:ℚ) * (m - 5) + (414:ℚ) = (48:ℚ) * m + (174:ℚ) := by ring
  linarith [ht, hshift]
#print axioms shape_u128_uniform
-- u129 [2-edge cycle] 4->1->(closed) | cand_progress+z_entry
--   roles: abs=2, tied+2, abs=3, tied+1; 5 instances at bases [7, 8, 9, 10]; all_strict=True; worst realized 1513/2231
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 1). -/
theorem shape_u129_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (48:ℚ) * m + (238:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have hshift : (48:ℚ) * (m - 5) + (478:ℚ) = (48:ℚ) * m + (238:ℚ) := by ring
  linarith [ht, hshift]
#print axioms shape_u129_uniform
-- u130 [2-edge cycle] 4->1->(closed) | cand_progress+z_entry
--   roles: abs=3, abs=12, abs=4, abs=11; 2 instances at bases [10]; all_strict=True; worst realized 2225/3007
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u130_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (782:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u130_uniform
-- u131 [2-edge cycle] 4->1->(closed) | cand_progress+z_irred
--   roles: abs=1, tied+2, tied+2, abs=2; 3 instances at bases [5, 6]; all_strict=True; worst realized 567/1105
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 1). -/
theorem shape_u131_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (64:ℚ) * m + (154:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have hshift : (64:ℚ) * (m - 5) + (474:ℚ) = (64:ℚ) * m + (154:ℚ) := by ring
  linarith [ht, hshift]
#print axioms shape_u131_uniform
-- u132 [2-edge cycle] 4->1->(closed) | cand_progress+z_irred
--   roles: abs=2, tied+2, tied+2, abs=3; 7 instances at bases [8, 9, 10]; all_strict=True; worst realized 323/485
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 1). -/
theorem shape_u132_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (64:ℚ) * m + (170:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have hshift : (64:ℚ) * (m - 5) + (490:ℚ) = (64:ℚ) * m + (170:ℚ) := by ring
  linarith [ht, hshift]
#print axioms shape_u132_uniform
-- u133 [2-edge cycle] 4->1->(closed) | cand_progress+z_progress
--   roles: abs=1, tied+2, tied+2, abs=2; 19 instances at bases [5, 6, 7, 8]; all_strict=True; worst realized 9/17
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 1). -/
theorem shape_u133_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (64:ℚ) * m + (136:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have hshift : (64:ℚ) * (m - 5) + (456:ℚ) = (64:ℚ) * m + (136:ℚ) := by ring
  linarith [ht, hshift]
#print axioms shape_u133_uniform
-- u134 [2-edge cycle] 4->1->(closed) | cand_progress+z_progress
--   roles: tied-1, tied+1, tied+1, tied=base; 2 instances at bases [5, 6]; all_strict=True; worst realized 41/49
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 1). -/
theorem shape_u134_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (64:ℚ) * m + (72:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have hshift : (64:ℚ) * (m - 5) + (392:ℚ) = (64:ℚ) * m + (72:ℚ) := by ring
  linarith [ht, hshift]
#print axioms shape_u134_uniform
-- u135 [2-edge cycle] 4->1->(closed) | cand_progress+z_progress
--   roles: abs=2, tied+2, tied+2, abs=3; 11 instances at bases [6, 7, 8, 9, 10]; all_strict=True; worst realized 17/25
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 1). -/
theorem shape_u135_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (64:ℚ) * m + (136:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have hshift : (64:ℚ) * (m - 5) + (456:ℚ) = (64:ℚ) * m + (136:ℚ) := by ring
  linarith [ht, hshift]
#print axioms shape_u135_uniform
-- u136 [2-edge cycle] 4->1->(closed) | cand_progress+z_progress
--   roles: abs=3, tied+2, tied+2, abs=4; 2 instances at bases [8, 9]; all_strict=True; worst realized 25/33
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 1). -/
theorem shape_u136_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (64:ℚ) * m + (136:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have hshift : (64:ℚ) * (m - 5) + (456:ℚ) = (64:ℚ) * m + (136:ℚ) := by ring
  linarith [ht, hshift]
#print axioms shape_u136_uniform
-- u137 [2-edge cycle] 4->1->(closed) | cand_progress+z_progress
--   roles: abs=4, abs=12, abs=12, abs=5; 1 instances at bases [10]; all_strict=True; worst realized 33/41
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u137_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (776:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u137_uniform
-- u138 [2-edge cycle] 4->2->(closed) | cand_entry+z_progress
--   roles: abs=12, abs=8, abs=10, abs=7; 1 instances at bases [9]; all_strict=True; worst realized 351/361
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u138_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (150:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u138_uniform
-- u139 [2-edge cycle] 4->2->(closed) | cand_progress+z_progress
--   roles: abs=2, abs=7, abs=7, abs=3; 1 instances at bases [5]; all_strict=True; worst realized 17/25
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u139_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (456:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u139_uniform
-- u140 [2-edge cycle] 4->2->(closed) | cand_progress+z_progress
--   roles: abs=3, abs=7, abs=7, abs=4; 1 instances at bases [5]; all_strict=True; worst realized 25/33
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u140_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (456:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u140_uniform
-- u141 [2-edge cycle] 4->2->(closed) | cand_progress+z_progress
--   roles: abs=4, abs=7, abs=7, abs=5; 1 instances at bases [5]; all_strict=True; worst realized 33/41
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u141_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (456:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u141_uniform
-- u142 [2-edge cycle] 4->2->(closed) | cand_progress+z_progress
--   roles: abs=7, abs=9, abs=9, abs=8; 1 instances at bases [6]; all_strict=True; worst realized 57/65
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u142_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (584:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u142_uniform
-- u143 [2-edge cycle] 4->2->(closed) | cand_progress+z_progress
--   roles: abs=5, abs=12, abs=12, abs=6; 1 instances at bases [7]; all_strict=True; worst realized 41/49
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u143_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (776:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u143_uniform
-- u144 [2-edge cycle] 4->2->(closed) | cand_progress+z_progress
--   roles: abs=7, abs=12, abs=12, abs=8; 2 instances at bases [8]; all_strict=True; worst realized 57/65
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u144_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (776:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u144_uniform
-- u145 [2-edge cycle] 4->2->(closed) | cand_progress+z_progress
--   roles: abs=10, abs=13, abs=10, abs=8; 1 instances at bases [9]; all_strict=True; worst realized 2187/2275
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u145_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (264:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u145_uniform
-- u146 [2-edge cycle] 4->2->(closed) | cand_progress+z_progress
--   roles: abs=11, abs=13, abs=13, abs=12; 1 instances at bases [9]; all_strict=True; worst realized 89/97
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u146_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (840:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u146_uniform
-- u147 [2-edge cycle] 4->3->(closed) | cand_entry+z_entry
--   roles: free+2..+6, free+1..+4, tied=base, tied=base; 169 instances at bases [5, 6, 7, 8, 9, 10]; all_strict=True; worst realized 9153/9401
/-- pattern tau=(2,1): real half-line form, mono certificate (kind ALL, strict=True, deg D = 1). -/
theorem shape_u147_pat1_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (32:ℚ) * m - (24:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have hshift : (32:ℚ) * (m - 5) + (136:ℚ) = (32:ℚ) * m - (24:ℚ) := by ring
  linarith [ht, hshift]
#print axioms shape_u147_pat1_uniform
/-- pattern tau=(3,2): real half-line form, mono certificate (kind ALL, strict=True, deg D = 1). -/
theorem shape_u147_pat2_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (32:ℚ) * m - (40:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have hshift : (32:ℚ) * (m - 5) + (120:ℚ) = (32:ℚ) * m - (40:ℚ) := by ring
  linarith [ht, hshift]
#print axioms shape_u147_pat2_uniform
/-- pattern tau=(4,3): real half-line form, mono certificate (kind ALL, strict=True, deg D = 1). -/
theorem shape_u147_pat3_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (32:ℚ) * m - (56:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have hshift : (32:ℚ) * (m - 5) + (104:ℚ) = (32:ℚ) * m - (56:ℚ) := by ring
  linarith [ht, hshift]
#print axioms shape_u147_pat3_uniform
/-- pattern tau=(5,4): real half-line form, mono certificate (kind ALL, strict=True, deg D = 1). -/
theorem shape_u147_pat4_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (32:ℚ) * m - (72:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have hshift : (32:ℚ) * (m - 5) + (88:ℚ) = (32:ℚ) * m - (72:ℚ) := by ring
  linarith [ht, hshift]
#print axioms shape_u147_pat4_uniform
/-- pattern tau=(6,4): real half-line form, mono certificate (kind ALL, strict=True, deg D = 1). -/
theorem shape_u147_pat5_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (96:ℚ) * m - (80:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have hshift : (96:ℚ) * (m - 5) + (400:ℚ) = (96:ℚ) * m - (80:ℚ) := by ring
  linarith [ht, hshift]
#print axioms shape_u147_pat5_uniform
-- u148 [2-edge cycle] 4->3->(closed) | cand_progress+z_entry
--   roles: free+1..+4, free+2..+5, tied=base, tied=base; 135 instances at bases [5, 6, 7, 8, 9, 10]; all_strict=True; worst realized 9153/9559
/-- pattern tau=(1,2): real half-line form, mono certificate (kind ALL, strict=True, deg D = 1). -/
theorem shape_u148_pat1_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (48:ℚ) * m - (26:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have hshift : (48:ℚ) * (m - 5) + (214:ℚ) = (48:ℚ) * m - (26:ℚ) := by ring
  linarith [ht, hshift]
#print axioms shape_u148_pat1_uniform
/-- pattern tau=(2,3): real half-line form, mono certificate (kind ALL, strict=True, deg D = 1). -/
theorem shape_u148_pat2_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (48:ℚ) * m - (42:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have hshift : (48:ℚ) * (m - 5) + (198:ℚ) = (48:ℚ) * m - (42:ℚ) := by ring
  linarith [ht, hshift]
#print axioms shape_u148_pat2_uniform
/-- pattern tau=(3,4): real half-line form, mono certificate (kind ALL, strict=True, deg D = 1). -/
theorem shape_u148_pat3_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (48:ℚ) * m - (58:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have hshift : (48:ℚ) * (m - 5) + (182:ℚ) = (48:ℚ) * m - (58:ℚ) := by ring
  linarith [ht, hshift]
#print axioms shape_u148_pat3_uniform
/-- pattern tau=(4,5): real half-line form, mono certificate (kind ALL, strict=True, deg D = 1). -/
theorem shape_u148_pat4_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (48:ℚ) * m - (74:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have hshift : (48:ℚ) * (m - 5) + (166:ℚ) = (48:ℚ) * m - (74:ℚ) := by ring
  linarith [ht, hshift]
#print axioms shape_u148_pat4_uniform
-- u149 [2-edge cycle] 4->6->(closed) | cand_entry+z_entry
--   roles: abs=13, abs=13, abs=12, abs=11; 1 instances at bases [7]; all_strict=True; worst realized 1869/1957
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u149_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (440:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u149_uniform
-- u150 [2-edge cycle] 5->1->(closed) | cand_progress+z_entry
--   roles: abs=1, abs=8, abs=2, abs=7; 1 instances at bases [5]; all_strict=True; worst realized 171/325
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u150_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (462:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u150_uniform
-- u151 [2-edge cycle] 5->1->(closed) | cand_progress+z_irred
--   roles: abs=1, abs=7, abs=7, abs=2; 4 instances at bases [5]; all_strict=True; worst realized 165/323
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u151_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (474:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u151_uniform
-- u152 [2-edge cycle] 5->1->(closed) | cand_progress+z_irred
--   roles: abs=1, tied+3, tied+3, abs=2; 5 instances at bases [6, 7, 8, 9]; all_strict=True; worst realized 855/1649
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 1). -/
theorem shape_u152_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (64:ℚ) * m + (218:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have hshift : (64:ℚ) * (m - 5) + (538:ℚ) = (64:ℚ) * m + (218:ℚ) := by ring
  linarith [ht, hshift]
#print axioms shape_u152_uniform
-- u153 [2-edge cycle] 5->1->(closed) | cand_progress+z_irred
--   roles: abs=2, abs=13, abs=13, abs=3; 1 instances at bases [10]; all_strict=True; worst realized 1751/2625
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u153_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (874:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u153_uniform
-- u154 [2-edge cycle] 5->1->(closed) | cand_progress+z_progress
--   roles: abs=1, tied+2, tied+2, abs=2; 9 instances at bases [5, 6]; all_strict=True; worst realized 9/17
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 1). -/
theorem shape_u154_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (64:ℚ) * m + (136:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have hshift : (64:ℚ) * (m - 5) + (456:ℚ) = (64:ℚ) * m + (136:ℚ) := by ring
  linarith [ht, hshift]
#print axioms shape_u154_uniform
-- u155 [2-edge cycle] 5->1->(closed) | cand_progress+z_progress
--   roles: abs=2, tied+2, tied+2, abs=3; 25 instances at bases [5, 6, 7, 8, 9, 10]; all_strict=True; worst realized 17/25
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 1). -/
theorem shape_u155_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (64:ℚ) * m + (136:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have hshift : (64:ℚ) * (m - 5) + (456:ℚ) = (64:ℚ) * m + (136:ℚ) := by ring
  linarith [ht, hshift]
#print axioms shape_u155_uniform
-- u156 [2-edge cycle] 5->1->(closed) | cand_progress+z_progress
--   roles: abs=3, tied+2, tied+2, abs=4; 14 instances at bases [5, 6, 7, 8, 9, 10]; all_strict=True; worst realized 25/33
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 1). -/
theorem shape_u156_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (64:ℚ) * m + (136:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have hshift : (64:ℚ) * (m - 5) + (456:ℚ) = (64:ℚ) * m + (136:ℚ) := by ring
  linarith [ht, hshift]
#print axioms shape_u156_uniform
-- u157 [2-edge cycle] 5->1->(closed) | cand_progress+z_progress
--   roles: abs=1, tied+3, tied+3, abs=2; 9 instances at bases [6, 8, 9, 10]; all_strict=True; worst realized 9/17
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 1). -/
theorem shape_u157_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (64:ℚ) * m + (200:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have hshift : (64:ℚ) * (m - 5) + (520:ℚ) = (64:ℚ) * m + (200:ℚ) := by ring
  linarith [ht, hshift]
#print axioms shape_u157_uniform
-- u158 [2-edge cycle] 5->1->(closed) | cand_progress+z_progress
--   roles: abs=4, tied+2, tied+2, abs=5; 9 instances at bases [6, 7, 8, 9, 10]; all_strict=True; worst realized 33/41
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 1). -/
theorem shape_u158_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (64:ℚ) * m + (136:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have hshift : (64:ℚ) * (m - 5) + (456:ℚ) = (64:ℚ) * m + (136:ℚ) := by ring
  linarith [ht, hshift]
#print axioms shape_u158_uniform
-- u159 [2-edge cycle] 5->1->(closed) | cand_progress+z_progress
--   roles: abs=5, tied+2, tied+2, abs=6; 8 instances at bases [7, 8, 9, 10]; all_strict=True; worst realized 41/49
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 1). -/
theorem shape_u159_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (64:ℚ) * m + (136:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have hshift : (64:ℚ) * (m - 5) + (456:ℚ) = (64:ℚ) * m + (136:ℚ) := by ring
  linarith [ht, hshift]
#print axioms shape_u159_uniform
-- u160 [2-edge cycle] 5->1->(closed) | cand_progress+z_progress
--   roles: abs=6, tied+2, tied+2, abs=7; 5 instances at bases [8, 9, 10]; all_strict=True; worst realized 49/57
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 1). -/
theorem shape_u160_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (64:ℚ) * m + (136:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have hshift : (64:ℚ) * (m - 5) + (456:ℚ) = (64:ℚ) * m + (136:ℚ) := by ring
  linarith [ht, hshift]
#print axioms shape_u160_uniform
-- u161 [2-edge cycle] 5->1->(closed) | cand_progress+z_progress
--   roles: abs=7, tied+2, tied+2, abs=8; 3 instances at bases [9, 10]; all_strict=True; worst realized 57/65
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 1). -/
theorem shape_u161_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (64:ℚ) * m + (136:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have hshift : (64:ℚ) * (m - 5) + (456:ℚ) = (64:ℚ) * m + (136:ℚ) := by ring
  linarith [ht, hshift]
#print axioms shape_u161_uniform
-- u162 [2-edge cycle] 5->1->(closed) | cand_progress+z_progress
--   roles: abs=8, abs=12, abs=12, abs=9; 1 instances at bases [10]; all_strict=True; worst realized 65/73
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u162_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (776:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u162_uniform
-- u163 [2-edge cycle] 5->2->(closed) | cand_entry+z_entry
--   roles: abs=11, abs=4, abs=3, abs=7; 1 instances at bases [6]; all_strict=True; worst realized 627/667
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u163_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (120:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u163_uniform
-- u164 [2-edge cycle] 5->2->(closed) | cand_progress+z_entry
--   roles: free+1..+2, free+3..+4, tied=base, tied+1; 13 instances at bases [5, 6, 8, 9, 10]; all_strict=True; worst realized 931/949
/-- pattern tau=(1,3): real half-line form, mono certificate (kind ALL, strict=True, deg D = 1). -/
theorem shape_u164_pat1_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (48:ℚ) * m - (106:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have hshift : (48:ℚ) * (m - 5) + (134:ℚ) = (48:ℚ) * m - (106:ℚ) := by ring
  linarith [ht, hshift]
#print axioms shape_u164_pat1_uniform
/-- pattern tau=(1,4): real half-line form, mono certificate (kind ALL, strict=True, deg D = 1). -/
theorem shape_u164_pat2_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (112:ℚ) * m - (114:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have hshift : (112:ℚ) * (m - 5) + (446:ℚ) = (112:ℚ) * m - (114:ℚ) := by ring
  linarith [ht, hshift]
#print axioms shape_u164_pat2_uniform
/-- pattern tau=(2,4): real half-line form, mono certificate (kind ALL, strict=True, deg D = 1). -/
theorem shape_u164_pat3_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (48:ℚ) * m - (186:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have hshift : (48:ℚ) * (m - 5) + (54:ℚ) = (48:ℚ) * m - (186:ℚ) := by ring
  linarith [ht, hshift]
#print axioms shape_u164_pat3_uniform
-- u165 [2-edge cycle] 5->2->(closed) | cand_progress+z_irred
--   roles: abs=1, tied+2, tied+2, abs=2; 2 instances at bases [5, 6]; all_strict=True; worst realized 567/1105
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 1). -/
theorem shape_u165_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (64:ℚ) * m + (154:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have hshift : (64:ℚ) * (m - 5) + (474:ℚ) = (64:ℚ) * m + (154:ℚ) := by ring
  linarith [ht, hshift]
#print axioms shape_u165_uniform
-- u166 [2-edge cycle] 5->2->(closed) | cand_progress+z_progress
--   roles: abs=2, abs=7, abs=7, abs=3; 1 instances at bases [5]; all_strict=True; worst realized 17/25
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u166_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (456:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u166_uniform
-- u167 [2-edge cycle] 5->2->(closed) | cand_progress+z_progress
--   roles: abs=3, abs=7, abs=7, abs=4; 5 instances at bases [5]; all_strict=True; worst realized 25/33
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u167_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (456:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u167_uniform
-- u168 [2-edge cycle] 5->2->(closed) | cand_progress+z_progress
--   roles: abs=4, abs=7, abs=7, abs=5; 5 instances at bases [5]; all_strict=True; worst realized 33/41
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u168_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (456:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u168_uniform
-- u169 [2-edge cycle] 5->2->(closed) | cand_progress+z_progress
--   roles: tied=base, tied+2, tied+2, tied+1; 6 instances at bases [5, 6]; all_strict=True; worst realized 49/57
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 1). -/
theorem shape_u169_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (64:ℚ) * m + (136:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have hshift : (64:ℚ) * (m - 5) + (456:ℚ) = (64:ℚ) * m + (136:ℚ) := by ring
  linarith [ht, hshift]
#print axioms shape_u169_uniform
-- u170 [2-edge cycle] 5->2->(closed) | cand_progress+z_progress
--   roles: tied=base, tied+4, tied+4, tied+1; 4 instances at bases [6, 7]; all_strict=True; worst realized 57/65
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 1). -/
theorem shape_u170_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (64:ℚ) * m + (264:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have hshift : (64:ℚ) * (m - 5) + (584:ℚ) = (64:ℚ) * m + (264:ℚ) := by ring
  linarith [ht, hshift]
#print axioms shape_u170_uniform
-- u171 [2-edge cycle] 5->2->(closed) | cand_progress+z_progress
--   roles: abs=11, abs=15, abs=15, abs=12; 3 instances at bases [10]; all_strict=True; worst realized 89/97
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u171_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (968:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u171_uniform
-- u172 [2-edge cycle] 5->4->(closed) | cand_entry+z_entry
--   roles: free+2..+7, free+1..+5, tied=base, tied=base; 193 instances at bases [5, 6, 7, 8, 9, 10]; all_strict=True; worst realized 9801/10033
/-- pattern tau=(2,1): real half-line form, mono certificate (kind ALL, strict=True, deg D = 1). -/
theorem shape_u172_pat1_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (32:ℚ) * m - (24:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have hshift : (32:ℚ) * (m - 5) + (136:ℚ) = (32:ℚ) * m - (24:ℚ) := by ring
  linarith [ht, hshift]
#print axioms shape_u172_pat1_uniform
/-- pattern tau=(3,2): real half-line form, mono certificate (kind ALL, strict=True, deg D = 1). -/
theorem shape_u172_pat2_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (32:ℚ) * m - (40:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have hshift : (32:ℚ) * (m - 5) + (120:ℚ) = (32:ℚ) * m - (40:ℚ) := by ring
  linarith [ht, hshift]
#print axioms shape_u172_pat2_uniform
/-- pattern tau=(4,3): real half-line form, mono certificate (kind ALL, strict=True, deg D = 1). -/
theorem shape_u172_pat3_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (32:ℚ) * m - (56:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have hshift : (32:ℚ) * (m - 5) + (104:ℚ) = (32:ℚ) * m - (56:ℚ) := by ring
  linarith [ht, hshift]
#print axioms shape_u172_pat3_uniform
/-- pattern tau=(5,4): real half-line form, mono certificate (kind ALL, strict=True, deg D = 1). -/
theorem shape_u172_pat4_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (32:ℚ) * m - (72:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have hshift : (32:ℚ) * (m - 5) + (88:ℚ) = (32:ℚ) * m - (72:ℚ) := by ring
  linarith [ht, hshift]
#print axioms shape_u172_pat4_uniform
/-- pattern tau=(6,5): real half-line form, mono certificate (kind ALL, strict=True, deg D = 1). -/
theorem shape_u172_pat5_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (32:ℚ) * m - (88:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have hshift : (32:ℚ) * (m - 5) + (72:ℚ) = (32:ℚ) * m - (88:ℚ) := by ring
  linarith [ht, hshift]
#print axioms shape_u172_pat5_uniform
/-- pattern tau=(7,5): real half-line form, mono certificate (kind ALL, strict=True, deg D = 1). -/
theorem shape_u172_pat6_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (96:ℚ) * m - (96:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have hshift : (96:ℚ) * (m - 5) + (384:ℚ) = (96:ℚ) * m - (96:ℚ) := by ring
  linarith [ht, hshift]
#print axioms shape_u172_pat6_uniform
-- u173 [2-edge cycle] 5->4->(closed) | cand_progress+z_entry
--   roles: free+1..+5, free+2..+6, tied=base, tied=base; 312 instances at bases [5, 6, 7, 8, 9, 10]; all_strict=True; worst realized 9153/9559
/-- pattern tau=(1,2): real half-line form, mono certificate (kind ALL, strict=True, deg D = 1). -/
theorem shape_u173_pat1_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (48:ℚ) * m - (26:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have hshift : (48:ℚ) * (m - 5) + (214:ℚ) = (48:ℚ) * m - (26:ℚ) := by ring
  linarith [ht, hshift]
#print axioms shape_u173_pat1_uniform
/-- pattern tau=(2,3): real half-line form, mono certificate (kind ALL, strict=True, deg D = 1). -/
theorem shape_u173_pat2_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (48:ℚ) * m - (42:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have hshift : (48:ℚ) * (m - 5) + (198:ℚ) = (48:ℚ) * m - (42:ℚ) := by ring
  linarith [ht, hshift]
#print axioms shape_u173_pat2_uniform
/-- pattern tau=(3,4): real half-line form, mono certificate (kind ALL, strict=True, deg D = 1). -/
theorem shape_u173_pat3_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (48:ℚ) * m - (58:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have hshift : (48:ℚ) * (m - 5) + (182:ℚ) = (48:ℚ) * m - (58:ℚ) := by ring
  linarith [ht, hshift]
#print axioms shape_u173_pat3_uniform
/-- pattern tau=(4,5): real half-line form, mono certificate (kind ALL, strict=True, deg D = 1). -/
theorem shape_u173_pat4_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (48:ℚ) * m - (74:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have hshift : (48:ℚ) * (m - 5) + (166:ℚ) = (48:ℚ) * m - (74:ℚ) := by ring
  linarith [ht, hshift]
#print axioms shape_u173_pat4_uniform
/-- pattern tau=(5,6): real half-line form, mono certificate (kind ALL, strict=True, deg D = 1). -/
theorem shape_u173_pat5_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (48:ℚ) * m - (90:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have hshift : (48:ℚ) * (m - 5) + (150:ℚ) = (48:ℚ) * m - (90:ℚ) := by ring
  linarith [ht, hshift]
#print axioms shape_u173_pat5_uniform
-- u174 [2-edge cycle] 6->1->(closed) | cand_progress+z_entry
--   roles: abs=1, abs=8, abs=2, abs=7; 1 instances at bases [5]; all_strict=True; worst realized 171/325
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u174_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (462:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u174_uniform
-- u175 [2-edge cycle] 6->1->(closed) | cand_progress+z_entry
--   roles: abs=2, tied+3, abs=3, tied+2; 6 instances at bases [7, 8, 9]; all_strict=True; worst realized 1513/2231
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 1). -/
theorem shape_u175_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (48:ℚ) * m + (286:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have hshift : (48:ℚ) * (m - 5) + (526:ℚ) = (48:ℚ) * m + (286:ℚ) := by ring
  linarith [ht, hshift]
#print axioms shape_u175_uniform
-- u176 [2-edge cycle] 6->1->(closed) | cand_progress+z_entry
--   roles: abs=3, tied+3, abs=4, tied+2; 5 instances at bases [9, 10]; all_strict=True; worst realized 485/651
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 1). -/
theorem shape_u176_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (48:ℚ) * m + (350:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have hshift : (48:ℚ) * (m - 5) + (590:ℚ) = (48:ℚ) * m + (350:ℚ) := by ring
  linarith [ht, hshift]
#print axioms shape_u176_uniform
-- u177 [2-edge cycle] 6->1->(closed) | cand_progress+z_irred
--   roles: tied-3, tied+2, tied+2, tied-2; 26 instances at bases [5, 6, 7, 8, 9, 10]; all_strict=True; worst realized 1083/1261
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 1). -/
theorem shape_u177_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (80:ℚ) * m + (90:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have hshift : (80:ℚ) * (m - 5) + (490:ℚ) = (80:ℚ) * m + (90:ℚ) := by ring
  linarith [ht, hshift]
#print axioms shape_u177_uniform
-- u178 [2-edge cycle] 6->1->(closed) | cand_progress+z_irred
--   roles: tied-2, tied+2, tied+2, tied-1; 23 instances at bases [5, 6, 7, 8, 9, 10]; all_strict=True; worst realized 6175/7081
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 1). -/
theorem shape_u178_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (80:ℚ) * m + (106:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have hshift : (80:ℚ) * (m - 5) + (506:ℚ) = (80:ℚ) * m + (106:ℚ) := by ring
  linarith [ht, hshift]
#print axioms shape_u178_uniform
-- u179 [2-edge cycle] 6->1->(closed) | cand_progress+z_irred
--   roles: tied-1, tied+2, tied+2, tied=base; 12 instances at bases [5, 6, 7, 8, 9, 10]; all_strict=True; worst realized 6935/7857
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 1). -/
theorem shape_u179_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (80:ℚ) * m + (122:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have hshift : (80:ℚ) * (m - 5) + (522:ℚ) = (80:ℚ) * m + (122:ℚ) := by ring
  linarith [ht, hshift]
#print axioms shape_u179_uniform
-- u180 [2-edge cycle] 6->1->(closed) | cand_progress+z_irred
--   roles: abs=1, tied+3, tied+3, abs=2; 26 instances at bases [6, 7, 8, 9]; all_strict=True; worst realized 855/1649
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 1). -/
theorem shape_u180_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (64:ℚ) * m + (218:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have hshift : (64:ℚ) * (m - 5) + (538:ℚ) = (64:ℚ) * m + (218:ℚ) := by ring
  linarith [ht, hshift]
#print axioms shape_u180_uniform
-- u181 [2-edge cycle] 6->1->(closed) | cand_progress+z_irred
--   roles: abs=2, tied+3, tied+3, abs=3; 11 instances at bases [7, 8, 9, 10]; all_strict=True; worst realized 1751/2625
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 1). -/
theorem shape_u181_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (64:ℚ) * m + (234:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have hshift : (64:ℚ) * (m - 5) + (554:ℚ) = (64:ℚ) * m + (234:ℚ) := by ring
  linarith [ht, hshift]
#print axioms shape_u181_uniform
-- u182 [2-edge cycle] 6->1->(closed) | cand_progress+z_irred
--   roles: tied-4, tied+2, tied+2, tied-3; 11 instances at bases [8, 9, 10]; all_strict=True; worst realized 245/291
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 1). -/
theorem shape_u182_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (80:ℚ) * m + (74:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have hshift : (80:ℚ) * (m - 5) + (474:ℚ) = (80:ℚ) * m + (74:ℚ) := by ring
  linarith [ht, hshift]
#print axioms shape_u182_uniform
-- u183 [2-edge cycle] 6->1->(closed) | cand_progress+z_irred
--   roles: abs=3, abs=13, abs=13, abs=4; 4 instances at bases [10]; all_strict=True; worst realized 515/693
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u183_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (890:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u183_uniform
-- u184 [2-edge cycle] 6->1->(closed) | cand_progress+z_irred
--   roles: abs=5, abs=12, abs=12, abs=6; 2 instances at bases [10]; all_strict=True; worst realized 3895/4753
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u184_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (858:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u184_uniform
-- u185 [2-edge cycle] 6->1->(closed) | cand_progress+z_progress
--   roles: abs=1, tied+3, tied+3, abs=2; 18 instances at bases [5, 6, 7, 8, 9, 10]; all_strict=True; worst realized 9/17
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 1). -/
theorem shape_u185_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (64:ℚ) * m + (200:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have hshift : (64:ℚ) * (m - 5) + (520:ℚ) = (64:ℚ) * m + (200:ℚ) := by ring
  linarith [ht, hshift]
#print axioms shape_u185_uniform
-- u186 [2-edge cycle] 6->1->(closed) | cand_progress+z_progress
--   roles: abs=2, tied+2, tied+2, abs=3; 14 instances at bases [5, 6, 7]; all_strict=True; worst realized 17/25
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 1). -/
theorem shape_u186_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (64:ℚ) * m + (136:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have hshift : (64:ℚ) * (m - 5) + (456:ℚ) = (64:ℚ) * m + (136:ℚ) := by ring
  linarith [ht, hshift]
#print axioms shape_u186_uniform
-- u187 [2-edge cycle] 6->1->(closed) | cand_progress+z_progress
--   roles: abs=3, tied+2, tied+2, abs=4; 29 instances at bases [5, 6, 7, 8, 9, 10]; all_strict=True; worst realized 25/33
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 1). -/
theorem shape_u187_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (64:ℚ) * m + (136:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have hshift : (64:ℚ) * (m - 5) + (456:ℚ) = (64:ℚ) * m + (136:ℚ) := by ring
  linarith [ht, hshift]
#print axioms shape_u187_uniform
-- u188 [2-edge cycle] 6->1->(closed) | cand_progress+z_progress
--   roles: abs=4, tied+2, tied+2, abs=5; 25 instances at bases [6, 7, 8, 9, 10]; all_strict=True; worst realized 33/41
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 1). -/
theorem shape_u188_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (64:ℚ) * m + (136:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have hshift : (64:ℚ) * (m - 5) + (456:ℚ) = (64:ℚ) * m + (136:ℚ) := by ring
  linarith [ht, hshift]
#print axioms shape_u188_uniform
-- u189 [2-edge cycle] 6->1->(closed) | cand_progress+z_progress
--   roles: abs=5, tied+2, tied+2, abs=6; 13 instances at bases [8, 9, 10]; all_strict=True; worst realized 41/49
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 1). -/
theorem shape_u189_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (64:ℚ) * m + (136:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have hshift : (64:ℚ) * (m - 5) + (456:ℚ) = (64:ℚ) * m + (136:ℚ) := by ring
  linarith [ht, hshift]
#print axioms shape_u189_uniform
-- u190 [2-edge cycle] 6->1->(closed) | cand_progress+z_progress
--   roles: abs=6, tied+2, tied+2, abs=7; 2 instances at bases [9, 10]; all_strict=True; worst realized 49/57
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 1). -/
theorem shape_u190_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (64:ℚ) * m + (136:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have hshift : (64:ℚ) * (m - 5) + (456:ℚ) = (64:ℚ) * m + (136:ℚ) := by ring
  linarith [ht, hshift]
#print axioms shape_u190_uniform
-- u191 [2-edge cycle] 6->1->(closed) | cand_progress+z_progress
--   roles: abs=2, abs=13, abs=13, abs=3; 2 instances at bases [10]; all_strict=True; worst realized 17/25
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u191_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (840:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u191_uniform
-- u192 [2-edge cycle] 6->2->(closed) | cand_progress+z_irred
--   roles: abs=3, tied+2, tied+2, abs=4; 3 instances at bases [5, 7]; all_strict=True; worst realized 1775/2409
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 1). -/
theorem shape_u192_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (64:ℚ) * m + (186:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have hshift : (64:ℚ) * (m - 5) + (506:ℚ) = (64:ℚ) * m + (186:ℚ) := by ring
  linarith [ht, hshift]
#print axioms shape_u192_uniform
-- u193 [2-edge cycle] 6->2->(closed) | cand_progress+z_irred
--   roles: tied-1, tied+2, tied+2, tied=base; 4 instances at bases [5, 6]; all_strict=True; worst realized 369/455
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 1). -/
theorem shape_u193_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (80:ℚ) * m + (122:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have hshift : (80:ℚ) * (m - 5) + (522:ℚ) = (80:ℚ) * m + (122:ℚ) := by ring
  linarith [ht, hshift]
#print axioms shape_u193_uniform
-- u194 [2-edge cycle] 6->2->(closed) | cand_progress+z_progress
--   roles: abs=3, abs=7, abs=7, abs=4; 2 instances at bases [5]; all_strict=True; worst realized 25/33
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u194_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (456:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u194_uniform
-- u195 [2-edge cycle] 6->2->(closed) | cand_progress+z_progress
--   roles: abs=4, abs=7, abs=7, abs=5; 2 instances at bases [5]; all_strict=True; worst realized 33/41
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u195_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (456:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u195_uniform
-- u196 [2-edge cycle] 6->2->(closed) | cand_progress+z_progress
--   roles: abs=5, abs=7, abs=7, abs=6; 1 instances at bases [5]; all_strict=True; worst realized 41/49
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u196_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (456:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u196_uniform
-- u197 [2-edge cycle] 6->2->(closed) | cand_progress+z_progress
--   roles: abs=6, abs=12, abs=12, abs=7; 2 instances at bases [7]; all_strict=True; worst realized 49/57
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u197_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (776:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u197_uniform
-- u198 [2-edge cycle] 6->2->(closed) | cand_progress+z_progress
--   roles: abs=8, abs=11, abs=11, abs=9; 1 instances at bases [7]; all_strict=True; worst realized 65/73
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u198_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (712:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u198_uniform
-- u199 [2-edge cycle] 6->2->(closed) | cand_progress+z_progress
--   roles: abs=11, abs=14, abs=14, abs=12; 1 instances at bases [9]; all_strict=True; worst realized 89/97
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u199_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (904:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u199_uniform
-- u200 [2-edge cycle] 6->3->(closed) | cand_progress+z_progress
--   roles: abs=7, abs=9, abs=9, abs=8; 6 instances at bases [6]; all_strict=True; worst realized 57/65
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u200_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (584:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u200_uniform
-- u201 [2-edge cycle] 6->4->(closed) | cand_progress+z_irred
--   roles: abs=10, abs=12, abs=12, abs=11; 1 instances at bases [7]; all_strict=True; worst realized 7695/8633
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u201_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (938:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u201_uniform
-- u202 [2-edge cycle] 6->5->(closed) | cand_entry+z_entry
--   roles: free+3..+8, free+2..+6, tied+1, tied+1; 454 instances at bases [5, 6, 7, 8, 9, 10]; all_strict=True; worst realized 3827/3915
/-- pattern tau=(3,2): real half-line form, mono certificate (kind ALL, strict=True, deg D = 1). -/
theorem shape_u202_pat1_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (32:ℚ) * m + (8:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have hshift : (32:ℚ) * (m - 5) + (168:ℚ) = (32:ℚ) * m + (8:ℚ) := by ring
  linarith [ht, hshift]
#print axioms shape_u202_pat1_uniform
/-- pattern tau=(4,3): real half-line form, mono certificate (kind ALL, strict=True, deg D = 1). -/
theorem shape_u202_pat2_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (32:ℚ) * m - (8:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have hshift : (32:ℚ) * (m - 5) + (152:ℚ) = (32:ℚ) * m - (8:ℚ) := by ring
  linarith [ht, hshift]
#print axioms shape_u202_pat2_uniform
/-- pattern tau=(5,4): real half-line form, mono certificate (kind ALL, strict=True, deg D = 1). -/
theorem shape_u202_pat3_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (32:ℚ) * m - (24:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have hshift : (32:ℚ) * (m - 5) + (136:ℚ) = (32:ℚ) * m - (24:ℚ) := by ring
  linarith [ht, hshift]
#print axioms shape_u202_pat3_uniform
/-- pattern tau=(6,4): real half-line form, mono certificate (kind ALL, strict=True, deg D = 1). -/
theorem shape_u202_pat4_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (96:ℚ) * m + (32:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have hshift : (96:ℚ) * (m - 5) + (512:ℚ) = (96:ℚ) * m + (32:ℚ) := by ring
  linarith [ht, hshift]
#print axioms shape_u202_pat4_uniform
/-- pattern tau=(6,5): real half-line form, mono certificate (kind ALL, strict=True, deg D = 1). -/
theorem shape_u202_pat5_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (32:ℚ) * m - (40:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have hshift : (32:ℚ) * (m - 5) + (120:ℚ) = (32:ℚ) * m - (40:ℚ) := by ring
  linarith [ht, hshift]
#print axioms shape_u202_pat5_uniform
/-- pattern tau=(7,5): real half-line form, mono certificate (kind ALL, strict=True, deg D = 1). -/
theorem shape_u202_pat6_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (96:ℚ) * m + (16:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have hshift : (96:ℚ) * (m - 5) + (496:ℚ) = (96:ℚ) * m + (16:ℚ) := by ring
  linarith [ht, hshift]
#print axioms shape_u202_pat6_uniform
/-- pattern tau=(7,6): real half-line form, mono certificate (kind ALL, strict=True, deg D = 1). -/
theorem shape_u202_pat7_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (32:ℚ) * m - (56:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have hshift : (32:ℚ) * (m - 5) + (104:ℚ) = (32:ℚ) * m - (56:ℚ) := by ring
  linarith [ht, hshift]
#print axioms shape_u202_pat7_uniform
/-- pattern tau=(8,6): real half-line form, mono certificate (kind ALL, strict=True, deg D = 1). -/
theorem shape_u202_pat8_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (96:ℚ) * m := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have hshift : (96:ℚ) * (m - 5) + (480:ℚ) = (96:ℚ) * m := by ring
  linarith [ht, hshift]
#print axioms shape_u202_pat8_uniform
-- u203 [2-edge cycle] 6->5->(closed) | cand_progress+z_entry
--   roles: free+2..+5, free+3..+6, tied+1, tied+1; 212 instances at bases [5, 6, 7, 8, 9, 10]; all_strict=True; worst realized 10769/11223
/-- pattern tau=(2,3): real half-line form, mono certificate (kind ALL, strict=True, deg D = 1). -/
theorem shape_u203_pat1_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (48:ℚ) * m + (22:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have hshift : (48:ℚ) * (m - 5) + (262:ℚ) = (48:ℚ) * m + (22:ℚ) := by ring
  linarith [ht, hshift]
#print axioms shape_u203_pat1_uniform
/-- pattern tau=(3,4): real half-line form, mono certificate (kind ALL, strict=True, deg D = 1). -/
theorem shape_u203_pat2_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (48:ℚ) * m + (6:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have hshift : (48:ℚ) * (m - 5) + (246:ℚ) = (48:ℚ) * m + (6:ℚ) := by ring
  linarith [ht, hshift]
#print axioms shape_u203_pat2_uniform
/-- pattern tau=(4,5): real half-line form, mono certificate (kind ALL, strict=True, deg D = 1). -/
theorem shape_u203_pat3_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (48:ℚ) * m - (10:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have hshift : (48:ℚ) * (m - 5) + (230:ℚ) = (48:ℚ) * m - (10:ℚ) := by ring
  linarith [ht, hshift]
#print axioms shape_u203_pat3_uniform
/-- pattern tau=(5,6): real half-line form, mono certificate (kind ALL, strict=True, deg D = 1). -/
theorem shape_u203_pat4_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (48:ℚ) * m - (26:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have hshift : (48:ℚ) * (m - 5) + (214:ℚ) = (48:ℚ) * m - (26:ℚ) := by ring
  linarith [ht, hshift]
#print axioms shape_u203_pat4_uniform
