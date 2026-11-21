import Mathlib

/-!
# UniformShapes_R3: generated uniformity lemmas for the R3-edge killing shapes

GENERATED FILE (uniform_gen_v1.py, 281 theorems; regenerate, do not edit).  The half-line
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

-- u204 [3-edge cycle] 1->2->5->(closed) | cand_entry+z_entry+z_entry
--   roles: abs=2, abs=8, abs=6, abs=8, abs=11, abs=1; 1 instances at bases [7]; all_strict=True; worst realized 845/1363
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u204_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (23310:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u204_uniform
-- u205 [3-edge cycle] 1->2->5->(closed) | cand_entry+z_entry+z_entry
--   roles: abs=2, abs=12, abs=9, abs=11, abs=15, abs=1; 1 instances at bases [10]; all_strict=True; worst realized 25899/42245
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u205_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (49038:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u205_uniform
-- u206 [3-edge cycle] 1->2->5->(closed) | cand_entry+z_entry+z_irred
--   roles: abs=2, abs=5, abs=4, abs=6, abs=1, abs=6; 1 instances at bases [5]; all_strict=True; worst realized 287/465
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u206_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (8722:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u206_uniform
-- u207 [3-edge cycle] 1->2->5->(closed) | cand_entry+z_entry+z_irred
--   roles: abs=3, abs=10, abs=9, abs=11, abs=2, abs=11; 1 instances at bases [10]; all_strict=True; worst realized 1215/1633
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u207_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (37202:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u207_uniform
-- u208 [3-edge cycle] 1->2->5->(closed) | cand_irred+z_entry+z_entry
--   roles: abs=4, abs=1, abs=3, abs=7, abs=10, abs=1; 1 instances at bases [6]; all_strict=True; worst realized 1767/1817
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u208_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (450:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u208_uniform
-- u209 [3-edge cycle] 1->2->5->(closed) | cand_irred+z_entry+z_entry
--   roles: abs=6, abs=2, abs=5, abs=8, abs=10, abs=2; 2 instances at bases [7]; all_strict=True; worst realized 235/237
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u209_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (442:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u209_uniform
-- u210 [3-edge cycle] 1->2->5->(closed) | cand_irred+z_entry+z_irred
--   roles: abs=5, abs=1, abs=4, abs=8, abs=1, abs=8; 1 instances at bases [7]; all_strict=True; worst realized 91/93
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u210_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (390:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u210_uniform
-- u211 [3-edge cycle] 1->2->5->(closed) | cand_irred+z_entry+z_irred
--   roles: abs=9, abs=2, abs=8, abs=9, abs=2, abs=9; 1 instances at bases [8]; all_strict=True; worst realized 355/357
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u211_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (438:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u211_uniform
-- u212 [3-edge cycle] 1->3->2->(closed) | cand_entry+z_entry+z_entry
--   roles: abs=3, abs=7, abs=7, abs=6, abs=6, abs=2; 1 instances at bases [5]; all_strict=True; worst realized 47481/59455
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u212_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (11974:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u212_uniform
-- u213 [3-edge cycle] 1->3->2->(closed) | cand_entry+z_entry+z_entry
--   roles: abs=4, tied+2, tied+1, tied-1, tied=base, abs=3; 2 instances at bases [8, 9]; all_strict=True; worst realized 12825/15407
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 2). -/
theorem shape_u213_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (384:ℚ) * m ^ 2 - (512:ℚ) * m + (2758:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have hshift : (384:ℚ) * (m - 5) ^ 2 + (3328:ℚ) * (m - 5) + (9798:ℚ) = (384:ℚ) * m ^ 2 - (512:ℚ) * m + (2758:ℚ) := by ring
  linarith [ht, h2, hshift]
#print axioms shape_u213_uniform
-- u214 [3-edge cycle] 1->3->2->(closed) | cand_entry+z_entry+z_entry
--   roles: abs=5, tied+2, tied+1, tied-1, tied=base, abs=4; 3 instances at bases [8, 9, 10]; all_strict=True; worst realized 5643/6461
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 2). -/
theorem shape_u214_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (384:ℚ) * m ^ 2 - (768:ℚ) * m + (3654:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have hshift : (384:ℚ) * (m - 5) ^ 2 + (3072:ℚ) * (m - 5) + (9414:ℚ) = (384:ℚ) * m ^ 2 - (768:ℚ) * m + (3654:ℚ) := by ring
  linarith [ht, h2, hshift]
#print axioms shape_u214_uniform
-- u215 [3-edge cycle] 1->3->2->(closed) | cand_entry+z_entry+z_entry
--   roles: abs=2, tied+4, tied+4, tied+3, tied+3, abs=1; 2 instances at bases [9, 10]; all_strict=True; worst realized 6111/9785
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 2). -/
theorem shape_u215_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (384:ℚ) * m ^ 2 + (2304:ℚ) * m + (3270:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have hshift : (384:ℚ) * (m - 5) ^ 2 + (6144:ℚ) * (m - 5) + (24390:ℚ) = (384:ℚ) * m ^ 2 + (2304:ℚ) * m + (3270:ℚ) := by ring
  linarith [ht, h2, hshift]
#print axioms shape_u215_uniform
-- u216 [3-edge cycle] 1->3->2->(closed) | cand_entry+z_entry+z_entry
--   roles: abs=6, tied+2, tied+1, tied-1, tied=base, abs=5; 2 instances at bases [9, 10]; all_strict=True; worst realized 237185/263623
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 2). -/
theorem shape_u216_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (384:ℚ) * m ^ 2 - (1024:ℚ) * m + (4550:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have hshift : (384:ℚ) * (m - 5) ^ 2 + (2816:ℚ) * (m - 5) + (9030:ℚ) = (384:ℚ) * m ^ 2 - (1024:ℚ) * m + (4550:ℚ) := by ring
  linarith [ht, h2, hshift]
#print axioms shape_u216_uniform
-- u217 [3-edge cycle] 1->3->2->(closed) | cand_entry+z_entry+z_entry
--   roles: abs=7, abs=12, abs=11, abs=9, abs=10, abs=6; 1 instances at bases [10]; all_strict=True; worst realized 346969/378015
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u217_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (31046:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u217_uniform
-- u218 [3-edge cycle] 1->3->2->(closed) | cand_entry+z_entry+z_irred
--   roles: abs=3, abs=10, abs=9, abs=6, abs=2, abs=6; 1 instances at bases [8]; all_strict=True; worst realized 1215/1633
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u218_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (20482:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u218_uniform
-- u219 [3-edge cycle] 1->3->2->(closed) | cand_entry+z_entry+z_irred
--   roles: abs=4, tied+2, tied+1, tied-1, abs=3, tied-1; 2 instances at bases [8, 10]; all_strict=True; worst realized 1863/2201
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 2). -/
theorem shape_u219_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (512:ℚ) * m ^ 2 - (1840:ℚ) * m + (1218:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have hshift : (512:ℚ) * (m - 5) ^ 2 + (3280:ℚ) * (m - 5) + (4818:ℚ) = (512:ℚ) * m ^ 2 - (1840:ℚ) * m + (1218:ℚ) := by ring
  linarith [ht, h2, hshift]
#print axioms shape_u219_uniform
-- u220 [3-edge cycle] 1->3->2->(closed) | cand_entry+z_entry+z_irred
--   roles: abs=2, abs=14, abs=11, abs=9, abs=1, abs=9; 1 instances at bases [10]; all_strict=True; worst realized 791/1305
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u220_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (37522:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u220_uniform
-- u221 [3-edge cycle] 1->3->2->(closed) | cand_entry+z_entry+z_irred
--   roles: abs=2, abs=14, abs=14, abs=13, abs=1, abs=10; 1 instances at bases [10]; all_strict=True; worst realized 5537/8991
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u221_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (51810:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u221_uniform
-- u222 [3-edge cycle] 1->3->2->(closed) | cand_irred+z_entry+z_irred
--   roles: abs=10, abs=2, abs=9, abs=7, abs=2, abs=7; 1 instances at bases [8]; all_strict=True; worst realized 1185/1207
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u222_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (1254:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u222_uniform
-- u223 [3-edge cycle] 1->3->2->(closed) | cand_irred+z_entry+z_irred
--   roles: abs=14, abs=1, abs=11, abs=9, abs=1, abs=9; 1 instances at bases [10]; all_strict=True; worst realized 259/261
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u223_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (438:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u223_uniform
-- u224 [3-edge cycle] 1->3->4->(closed) | cand_entry+z_entry+z_entry
--   roles: abs=3, tied+2, tied=base, tied=base, tied+2, abs=2; 6 instances at bases [5, 6]; all_strict=True; worst realized 13243/16445
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 2). -/
theorem shape_u224_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (384:ℚ) * m ^ 2 + (128:ℚ) * m - (634:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have hshift : (384:ℚ) * (m - 5) ^ 2 + (3968:ℚ) * (m - 5) + (9606:ℚ) = (384:ℚ) * m ^ 2 + (128:ℚ) * m - (634:ℚ) := by ring
  linarith [ht, h2, hshift]
#print axioms shape_u224_uniform
-- u225 [3-edge cycle] 1->3->4->(closed) | cand_entry+z_entry+z_entry
--   roles: abs=4, tied+2, tied=base, tied=base, tied+2, abs=3; 4 instances at bases [8, 9]; all_strict=True; worst realized 14625/17143
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 2). -/
theorem shape_u225_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (384:ℚ) * m ^ 2 - (128:ℚ) * m - (890:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have hshift : (384:ℚ) * (m - 5) ^ 2 + (3712:ℚ) * (m - 5) + (8070:ℚ) = (384:ℚ) * m ^ 2 - (128:ℚ) * m - (890:ℚ) := by ring
  linarith [ht, h2, hshift]
#print axioms shape_u225_uniform
-- u226 [3-edge cycle] 1->3->4->(closed) | cand_entry+z_entry+z_entry
--   roles: abs=5, tied+2, tied=base, tied=base, tied+2, abs=4; 4 instances at bases [8, 9, 10]; all_strict=True; worst realized 495/553
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 2). -/
theorem shape_u226_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (384:ℚ) * m ^ 2 - (384:ℚ) * m - (1146:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have hshift : (384:ℚ) * (m - 5) ^ 2 + (3456:ℚ) * (m - 5) + (6534:ℚ) = (384:ℚ) * m ^ 2 - (384:ℚ) * m - (1146:ℚ) := by ring
  linarith [ht, h2, hshift]
#print axioms shape_u226_uniform
-- u227 [3-edge cycle] 1->3->4->(closed) | cand_entry+z_entry+z_entry
--   roles: abs=6, tied+2, tied=base, tied=base, tied+2, abs=5; 3 instances at bases [8, 9, 10]; all_strict=True; worst realized 23985/25991
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 2). -/
theorem shape_u227_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (384:ℚ) * m ^ 2 - (640:ℚ) * m - (1402:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have hshift : (384:ℚ) * (m - 5) ^ 2 + (3200:ℚ) * (m - 5) + (4998:ℚ) = (384:ℚ) * m ^ 2 - (640:ℚ) * m - (1402:ℚ) := by ring
  linarith [ht, h2, hshift]
#print axioms shape_u227_uniform
-- u228 [3-edge cycle] 1->3->4->(closed) | cand_entry+z_entry+z_entry
--   roles: abs=7, tied+2, tied=base, tied=base, tied+2, abs=6; 3 instances at bases [8, 9, 10]; all_strict=True; worst realized 819/869
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 2). -/
theorem shape_u228_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (384:ℚ) * m ^ 2 - (896:ℚ) * m - (1658:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have hshift : (384:ℚ) * (m - 5) ^ 2 + (2944:ℚ) * (m - 5) + (3462:ℚ) = (384:ℚ) * m ^ 2 - (896:ℚ) * m - (1658:ℚ) := by ring
  linarith [ht, h2, hshift]
#print axioms shape_u228_uniform
-- u229 [3-edge cycle] 1->3->4->(closed) | cand_entry+z_entry+z_entry
--   roles: abs=8, tied+2, tied=base, tied=base, tied+2, abs=7; 3 instances at bases [8, 9, 10]; all_strict=True; worst realized 3705/3871
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 2). -/
theorem shape_u229_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (384:ℚ) * m ^ 2 - (1152:ℚ) * m - (1914:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have hshift : (384:ℚ) * (m - 5) ^ 2 + (2688:ℚ) * (m - 5) + (1926:ℚ) = (384:ℚ) * m ^ 2 - (1152:ℚ) * m - (1914:ℚ) := by ring
  linarith [ht, h2, hshift]
#print axioms shape_u229_uniform
-- u230 [3-edge cycle] 1->3->4->(closed) | cand_entry+z_entry+z_entry
--   roles: abs=2, abs=13, abs=9, abs=9, abs=13, abs=1; 3 instances at bases [9]; all_strict=True; worst realized 4599/7313
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u230_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (40710:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u230_uniform
-- u231 [3-edge cycle] 1->3->4->(closed) | cand_entry+z_entry+z_entry
--   roles: abs=9, tied+2, tied=base, tied=base, tied+2, abs=8; 2 instances at bases [9, 10]; all_strict=True; worst realized 422305/438567
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 2). -/
theorem shape_u231_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (384:ℚ) * m ^ 2 - (1408:ℚ) * m - (2170:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have hshift : (384:ℚ) * (m - 5) ^ 2 + (2432:ℚ) * (m - 5) + (390:ℚ) = (384:ℚ) * m ^ 2 - (1408:ℚ) * m - (2170:ℚ) := by ring
  linarith [ht, h2, hshift]
#print axioms shape_u231_uniform
-- u232 [3-edge cycle] 1->3->4->(closed) | cand_entry+z_entry+z_entry
--   roles: abs=10, abs=12, abs=10, abs=10, abs=12, abs=9; 1 instances at bases [10]; all_strict=True; worst realized 573561/592895
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u232_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (19334:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u232_uniform
-- u233 [3-edge cycle] 1->4->2->(closed) | cand_entry+z_entry+z_entry
--   roles: abs=3, abs=7, abs=7, abs=4, abs=4, abs=2; 1 instances at bases [5]; all_strict=True; worst realized 2907/3565
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u233_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (7238:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u233_uniform
-- u234 [3-edge cycle] 1->4->2->(closed) | cand_entry+z_entry+z_entry
--   roles: abs=3, abs=7, abs=7, abs=5, abs=5, abs=2; 1 instances at bases [5]; all_strict=True; worst realized 13243/16445
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u234_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (9606:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u234_uniform
-- u235 [3-edge cycle] 1->4->2->(closed) | cand_entry+z_entry+z_entry
--   roles: abs=3, abs=7, abs=7, abs=6, abs=6, abs=2; 1 instances at bases [5]; all_strict=True; worst realized 47481/59455
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u235_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (11974:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u235_uniform
-- u236 [3-edge cycle] 1->4->2->(closed) | cand_entry+z_entry+z_entry
--   roles: abs=3, tied+3, tied+3, tied-1, tied-1, abs=2; 2 instances at bases [6, 7]; all_strict=True; worst realized 50881/63687
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 2). -/
theorem shape_u236_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (384:ℚ) * m ^ 2 + (128:ℚ) * m - (1786:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have hshift : (384:ℚ) * (m - 5) ^ 2 + (3968:ℚ) * (m - 5) + (8454:ℚ) = (384:ℚ) * m ^ 2 + (128:ℚ) * m - (1786:ℚ) := by ring
  linarith [ht, h2, hshift]
#print axioms shape_u236_uniform
-- u237 [3-edge cycle] 1->4->2->(closed) | cand_entry+z_entry+z_irred
--   roles: abs=3, tied+3, tied+3, abs=6, abs=2, abs=5; 3 instances at bases [7, 8]; all_strict=True; worst realized 59535/74497
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 1). -/
theorem shape_u237_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (1664:ℚ) * m + (3314:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have hshift : (1664:ℚ) * (m - 5) + (11634:ℚ) = (1664:ℚ) * m + (3314:ℚ) := by ring
  linarith [ht, hshift]
#print axioms shape_u237_uniform
-- u238 [3-edge cycle] 1->4->5->(closed) | cand_entry+z_entry+z_entry
--   roles: tied-2, tied+2, tied=base, tied=base, tied+2, tied-3; 7 instances at bases [5, 6, 7, 8]; all_strict=True; worst realized 23985/25991
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 2). -/
theorem shape_u238_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (128:ℚ) * m ^ 2 + (1152:ℚ) * m + (646:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have hshift : (128:ℚ) * (m - 5) ^ 2 + (2432:ℚ) * (m - 5) + (9606:ℚ) = (128:ℚ) * m ^ 2 + (1152:ℚ) * m + (646:ℚ) := by ring
  linarith [ht, h2, hshift]
#print axioms shape_u238_uniform
-- u239 [3-edge cycle] 1->4->5->(closed) | cand_entry+z_entry+z_entry
--   roles: tied-1, tied+2, tied=base, tied=base, tied+2, tied-2; 2 instances at bases [5, 6]; all_strict=True; worst realized 385/423
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 2). -/
theorem shape_u239_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (128:ℚ) * m ^ 2 + (896:ℚ) * m + (390:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have hshift : (128:ℚ) * (m - 5) ^ 2 + (2176:ℚ) * (m - 5) + (8070:ℚ) = (128:ℚ) * m ^ 2 + (896:ℚ) * m + (390:ℚ) := by ring
  linarith [ht, h2, hshift]
#print axioms shape_u239_uniform
-- u240 [3-edge cycle] 1->4->5->(closed) | cand_entry+z_entry+z_entry
--   roles: abs=3, tied+3, tied=base, tied=base, tied+3, abs=2; 4 instances at bases [6, 7, 10]; all_strict=True; worst realized 60809/76751
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 2). -/
theorem shape_u240_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (384:ℚ) * m ^ 2 + (512:ℚ) * m - (954:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have hshift : (384:ℚ) * (m - 5) ^ 2 + (4352:ℚ) * (m - 5) + (11206:ℚ) = (384:ℚ) * m ^ 2 + (512:ℚ) * m - (954:ℚ) := by ring
  linarith [ht, h2, hshift]
#print axioms shape_u240_uniform
-- u241 [3-edge cycle] 1->4->5->(closed) | cand_entry+z_entry+z_entry
--   roles: tied-3, tied+2, tied=base, tied=base, tied+2, tied-4; 6 instances at bases [7, 8, 9, 10]; all_strict=True; worst realized 384993/412775
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 2). -/
theorem shape_u241_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (128:ℚ) * m ^ 2 + (1408:ℚ) * m + (902:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have hshift : (128:ℚ) * (m - 5) ^ 2 + (2688:ℚ) * (m - 5) + (11142:ℚ) = (128:ℚ) * m ^ 2 + (1408:ℚ) * m + (902:ℚ) := by ring
  linarith [ht, h2, hshift]
#print axioms shape_u241_uniform
-- u242 [3-edge cycle] 1->4->5->(closed) | cand_entry+z_entry+z_entry
--   roles: abs=2, abs=12, abs=8, abs=8, abs=12, abs=1; 1 instances at bases [8]; all_strict=True; worst realized 1261/1995
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u242_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (33030:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u242_uniform
-- u243 [3-edge cycle] 1->4->5->(closed) | cand_entry+z_entry+z_entry
--   roles: abs=5, tied+2, tied=base, tied=base, tied+2, abs=4; 5 instances at bases [9, 10]; all_strict=True; worst realized 71467/80301
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 2). -/
theorem shape_u243_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (384:ℚ) * m ^ 2 - (384:ℚ) * m - (1146:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have hshift : (384:ℚ) * (m - 5) ^ 2 + (3456:ℚ) * (m - 5) + (6534:ℚ) = (384:ℚ) * m ^ 2 - (384:ℚ) * m - (1146:ℚ) := by ring
  linarith [ht, h2, hshift]
#print axioms shape_u243_uniform
-- u244 [3-edge cycle] 1->4->5->(closed) | cand_entry+z_entry+z_entry
--   roles: abs=6, abs=12, abs=10, abs=10, abs=12, abs=5; 2 instances at bases [10]; all_strict=True; worst realized 322137/352735
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u244_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (30598:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u244_uniform
-- u245 [3-edge cycle] 1->4->5->(closed) | cand_entry+z_entry+z_irred
--   roles: abs=3, tied+2, tied=base, tied=base, abs=2, tied+1; 6 instances at bases [5, 6, 7, 8]; all_strict=True; worst realized 11685/14651
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 2). -/
theorem shape_u245_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (512:ℚ) * m ^ 2 - (688:ℚ) * m - (462:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have hshift : (512:ℚ) * (m - 5) ^ 2 + (4432:ℚ) * (m - 5) + (8898:ℚ) = (512:ℚ) * m ^ 2 - (688:ℚ) * m - (462:ℚ) := by ring
  linarith [ht, h2, hshift]
#print axioms shape_u245_uniform
-- u246 [3-edge cycle] 1->4->5->(closed) | cand_entry+z_entry+z_irred
--   roles: abs=2, free+3..+4, tied=base, tied=base, abs=1, tied+1; 5 instances at bases [6, 7, 10]; all_strict=True; worst realized 25039/40185
/-- pattern tau=(3): real half-line form, mono certificate (kind ALL, strict=True, deg D = 2). -/
theorem shape_u246_pat1_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (512:ℚ) * m ^ 2 - (496:ℚ) * m - (310:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have hshift : (512:ℚ) * (m - 5) ^ 2 + (4624:ℚ) * (m - 5) + (10010:ℚ) = (512:ℚ) * m ^ 2 - (496:ℚ) * m - (310:ℚ) := by ring
  linarith [ht, h2, hshift]
#print axioms shape_u246_pat1_uniform
/-- pattern tau=(4): real half-line form, mono certificate (kind ALL, strict=True, deg D = 2). -/
theorem shape_u246_pat2_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (512:ℚ) * m ^ 2 - (944:ℚ) * m - (366:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have hshift : (512:ℚ) * (m - 5) ^ 2 + (4176:ℚ) * (m - 5) + (7714:ℚ) = (512:ℚ) * m ^ 2 - (944:ℚ) * m - (366:ℚ) := by ring
  linarith [ht, h2, hshift]
#print axioms shape_u246_pat2_uniform
-- u247 [3-edge cycle] 1->4->5->(closed) | cand_entry+z_entry+z_irred
--   roles: abs=4, tied+2, tied=base, tied=base, abs=3, tied+1; 6 instances at bases [8, 9, 10]; all_strict=True; worst realized 13455/15841
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 2). -/
theorem shape_u247_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (512:ℚ) * m ^ 2 - (1328:ℚ) * m - (670:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have hshift : (512:ℚ) * (m - 5) ^ 2 + (3792:ℚ) * (m - 5) + (5490:ℚ) = (512:ℚ) * m ^ 2 - (1328:ℚ) * m - (670:ℚ) := by ring
  linarith [ht, h2, hshift]
#print axioms shape_u247_uniform
-- u248 [3-edge cycle] 1->5->2->(closed) | cand_entry+z_entry+z_entry
--   roles: abs=4, abs=7, abs=7, abs=4, abs=4, abs=3; 1 instances at bases [5]; all_strict=True; worst realized 855/961
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u248_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (5830:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u248_uniform
-- u249 [3-edge cycle] 1->5->2->(closed) | cand_entry+z_entry+z_entry
--   roles: abs=4, abs=7, abs=7, abs=5, abs=5, abs=3; 1 instances at bases [5]; all_strict=True; worst realized 3895/4433
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u249_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (8070:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u249_uniform
-- u250 [3-edge cycle] 1->5->2->(closed) | cand_entry+z_entry+z_entry
--   roles: abs=4, abs=7, abs=7, abs=6, abs=6, abs=3; 1 instances at bases [5]; all_strict=True; worst realized 13965/16027
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u250_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (10310:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u250_uniform
-- u251 [3-edge cycle] 1->5->2->(closed) | cand_entry+z_entry+z_entry
--   roles: abs=2, abs=10, abs=10, abs=4, abs=4, abs=1; 1 instances at bases [6]; all_strict=True; worst realized 8019/12245
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u251_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (12678:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u251_uniform
-- u252 [3-edge cycle] 1->5->2->(closed) | cand_entry+z_entry+z_entry
--   roles: tied-5, tied+3, tied+3, tied-1, tied-1, tied-6; 2 instances at bases [8, 10]; all_strict=True; worst realized 84315/95069
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 2). -/
theorem shape_u252_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (128:ℚ) * m ^ 2 + (1920:ℚ) * m + (262:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have hshift : (128:ℚ) * (m - 5) ^ 2 + (3200:ℚ) * (m - 5) + (13062:ℚ) = (128:ℚ) * m ^ 2 + (1920:ℚ) * m + (262:ℚ) := by ring
  linarith [ht, h2, hshift]
#print axioms shape_u252_uniform
-- u253 [3-edge cycle] 1->5->2->(closed) | cand_entry+z_entry+z_entry
--   roles: abs=2, abs=15, abs=15, abs=12, abs=12, abs=1; 1 instances at bases [10]; all_strict=True; worst realized 35211/56525
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u253_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (63942:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u253_uniform
-- u254 [3-edge cycle] 1->5->2->(closed) | cand_entry+z_entry+z_irred
--   roles: tied-3, abs=9, tied+2, abs=2, tied-4, abs=2; 2 instances at bases [5, 6]; all_strict=True; worst realized 365/483
/-- pattern tau=(): real half-line form, quad_vertex certificate (kind ALL, strict=True, deg D = 2). -/
theorem shape_u254_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (1088:ℚ) * m ^ 2 - (11288:ℚ) * m + (34578:ℚ) := by
  intro m hm
  have hsq : (0:ℚ) ≤ (m - 5 + (-3 / 16:ℚ)) ^ 2 := sq_nonneg _
  have hexp : (m - 5 + (-3 / 16:ℚ)) ^ 2 = (m - 5) ^ 2 + (-3 / 8:ℚ) * (m - 5) + (9 / 256:ℚ) := by ring
  have hshift : (1088:ℚ) * ((m - 5) ^ 2 + (-3 / 8:ℚ) * (m - 5) + (9 / 256:ℚ)) + (21199 / 4:ℚ) = (1088:ℚ) * m ^ 2 - (11288:ℚ) * m + (34578:ℚ) := by ring
  linarith [hsq, hexp, hshift]
#print axioms shape_u254_uniform
-- u255 [3-edge cycle] 1->5->2->(closed) | cand_entry+z_entry+z_irred
--   roles: abs=2, abs=10, abs=10, tied-2, abs=1, tied-3; 3 instances at bases [5, 6]; all_strict=True; worst realized 945/1343
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 1). -/
theorem shape_u255_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (4944:ℚ) * m - (18750:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have hshift : (4944:ℚ) * (m - 5) + (5970:ℚ) = (4944:ℚ) * m - (18750:ℚ) := by ring
  linarith [ht, hshift]
#print axioms shape_u255_uniform
-- u256 [3-edge cycle] 1->5->2->(closed) | cand_entry+z_entry+z_irred
--   roles: abs=3, abs=11, abs=11, abs=7, abs=2, abs=6; 1 instances at bases [8]; all_strict=True; worst realized 25365/32683
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u256_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (21954:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u256_uniform
-- u257 [3-edge cycle] 1->5->6->(closed) | cand_entry+z_entry+z_entry
--   roles: abs=2, free+4..+5, tied+1, tied+1, tied+4, abs=1; 18 instances at bases [5, 6, 7]; all_strict=True; worst realized 11907/16685
/-- pattern tau=(4): real half-line form, mono certificate (kind ALL, strict=True, deg D = 2). -/
theorem shape_u257_pat1_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (384:ℚ) * m ^ 2 + (1536:ℚ) * m + (582:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have hshift : (384:ℚ) * (m - 5) ^ 2 + (5376:ℚ) * (m - 5) + (17862:ℚ) = (384:ℚ) * m ^ 2 + (1536:ℚ) * m + (582:ℚ) := by ring
  linarith [ht, h2, hshift]
#print axioms shape_u257_pat1_uniform
/-- pattern tau=(5): real half-line form, mono certificate (kind ALL, strict=True, deg D = 2). -/
theorem shape_u257_pat2_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (384:ℚ) * m ^ 2 + (960:ℚ) * m - (66:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have hshift : (384:ℚ) * (m - 5) ^ 2 + (4800:ℚ) * (m - 5) + (14334:ℚ) = (384:ℚ) * m ^ 2 + (960:ℚ) * m - (66:ℚ) := by ring
  linarith [ht, h2, hshift]
#print axioms shape_u257_pat2_uniform
-- u258 [3-edge cycle] 1->5->6->(closed) | cand_entry+z_entry+z_entry
--   roles: abs=3, tied+3, tied+1, tied+1, tied+3, abs=2; 6 instances at bases [5, 6, 7, 8, 9]; all_strict=True; worst realized 7735/9729
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 2). -/
theorem shape_u258_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (384:ℚ) * m ^ 2 + (896:ℚ) * m - (122:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have hshift : (384:ℚ) * (m - 5) ^ 2 + (4736:ℚ) * (m - 5) + (13958:ℚ) = (384:ℚ) * m ^ 2 + (896:ℚ) * m - (122:ℚ) := by ring
  linarith [ht, h2, hshift]
#print axioms shape_u258_uniform
-- u259 [3-edge cycle] 1->5->6->(closed) | cand_entry+z_entry+z_entry
--   roles: abs=4, abs=7, abs=6, abs=6, abs=7, abs=3; 3 instances at bases [5]; all_strict=True; worst realized 13965/16027
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u259_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (10310:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u259_uniform
-- u260 [3-edge cycle] 1->5->6->(closed) | cand_entry+z_entry+z_entry
--   roles: abs=2, free+5..+6, tied+1, tied+1, tied+5, abs=1; 6 instances at bases [6, 8, 10]; all_strict=True; worst realized 24747/36565
/-- pattern tau=(5): real half-line form, mono certificate (kind ALL, strict=True, deg D = 2). -/
theorem shape_u260_pat1_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (384:ℚ) * m ^ 2 + (1920:ℚ) * m + (774:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have hshift : (384:ℚ) * (m - 5) ^ 2 + (5760:ℚ) * (m - 5) + (19974:ℚ) = (384:ℚ) * m ^ 2 + (1920:ℚ) * m + (774:ℚ) := by ring
  linarith [ht, h2, hshift]
#print axioms shape_u260_pat1_uniform
/-- pattern tau=(6): real half-line form, mono certificate (kind ALL, strict=True, deg D = 2). -/
theorem shape_u260_pat2_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (384:ℚ) * m ^ 2 + (1344:ℚ) * m + (126:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have hshift : (384:ℚ) * (m - 5) ^ 2 + (5184:ℚ) * (m - 5) + (16446:ℚ) = (384:ℚ) * m ^ 2 + (1344:ℚ) * m + (126:ℚ) := by ring
  linarith [ht, h2, hshift]
#print axioms shape_u260_pat2_uniform
-- u261 [3-edge cycle] 1->5->6->(closed) | cand_entry+z_entry+z_entry
--   roles: abs=4, tied+3, tied+1, tied+1, tied+3, abs=3; 3 instances at bases [7, 8, 9]; all_strict=True; worst realized 14625/17143
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 2). -/
theorem shape_u261_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (384:ℚ) * m ^ 2 + (640:ℚ) * m - (634:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have hshift : (384:ℚ) * (m - 5) ^ 2 + (4480:ℚ) * (m - 5) + (12166:ℚ) = (384:ℚ) * m ^ 2 + (640:ℚ) * m - (634:ℚ) := by ring
  linarith [ht, h2, hshift]
#print axioms shape_u261_uniform
-- u262 [3-edge cycle] 1->5->6->(closed) | cand_entry+z_entry+z_irred
--   roles: abs=2, abs=10, abs=6, abs=6, abs=1, abs=8; 1 instances at bases [5]; all_strict=True; worst realized 9261/15275
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u262_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (18042:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u262_uniform
-- u263 [3-edge cycle] 1->5->6->(closed) | cand_entry+z_entry+z_irred
--   roles: abs=3, abs=7, abs=6, abs=6, abs=2, abs=6; 10 instances at bases [5]; all_strict=True; worst realized 855/1081
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u263_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (11074:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u263_uniform
-- u264 [3-edge cycle] 1->5->6->(closed) | cand_irred+z_entry+z_irred
--   roles: abs=10, abs=1, abs=6, abs=6, abs=1, abs=8; 1 instances at bases [5]; all_strict=True; worst realized 27097/27495
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u264_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (398:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u264_uniform
-- u265 [3-edge cycle] 1->6->2->(closed) | cand_entry+z_entry+z_entry
--   roles: abs=5, abs=7, abs=7, abs=5, abs=5, abs=4; 1 instances at bases [5]; all_strict=True; worst realized 779/845
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u265_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (6534:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u265_uniform
-- u266 [3-edge cycle] 1->6->2->(closed) | cand_entry+z_entry+z_entry
--   roles: abs=3, tied+3, tied+3, abs=7, abs=7, abs=2; 2 instances at bases [6, 7]; all_strict=True; worst realized 70737/89815
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 1). -/
theorem shape_u266_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (2368:ℚ) * m + (4870:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have hshift : (2368:ℚ) * (m - 5) + (16710:ℚ) = (2368:ℚ) * m + (4870:ℚ) := by ring
  linarith [ht, hshift]
#print axioms shape_u266_uniform
-- u267 [3-edge cycle] 1->6->2->(closed) | cand_entry+z_entry+z_entry
--   roles: abs=3, abs=10, abs=10, abs=8, abs=8, abs=2; 1 instances at bases [7]; all_strict=True; worst realized 9945/12719
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u267_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (24966:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u267_uniform
-- u268 [3-edge cycle] 1->6->2->(closed) | cand_entry+z_entry+z_entry
--   roles: abs=4, tied+3, tied+3, tied=base, tied=base, abs=3; 2 instances at bases [9, 10]; all_strict=True; worst realized 35405/41819
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 2). -/
theorem shape_u268_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (384:ℚ) * m ^ 2 + (256:ℚ) * m - (1338:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have hshift : (384:ℚ) * (m - 5) ^ 2 + (4096:ℚ) * (m - 5) + (9542:ℚ) = (384:ℚ) * m ^ 2 + (256:ℚ) * m - (1338:ℚ) := by ring
  linarith [ht, h2, hshift]
#print axioms shape_u268_uniform
-- u269 [3-edge cycle] 1->6->2->(closed) | cand_entry+z_entry+z_irred
--   roles: tied-3, abs=9, tied+2, abs=3, tied-4, abs=3; 2 instances at bases [5, 6]; all_strict=True; worst realized 365/483
/-- pattern tau=(): real half-line form, quad_vertex certificate (kind ALL, strict=True, deg D = 2). -/
theorem shape_u269_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (1600:ℚ) * m ^ 2 - (16600:ℚ) * m + (50850:ℚ) := by
  intro m hm
  have hsq : (0:ℚ) ≤ (m - 5 + (-3 / 16:ℚ)) ^ 2 := sq_nonneg _
  have hexp : (m - 5 + (-3 / 16:ℚ)) ^ 2 = (m - 5) ^ 2 + (-3 / 8:ℚ) * (m - 5) + (9 / 256:ℚ) := by ring
  have hshift : (1600:ℚ) * ((m - 5) ^ 2 + (-3 / 8:ℚ) * (m - 5) + (9 / 256:ℚ)) + (31175 / 4:ℚ) = (1600:ℚ) * m ^ 2 - (16600:ℚ) * m + (50850:ℚ) := by ring
  linarith [hsq, hexp, hshift]
#print axioms shape_u269_uniform
-- u270 [3-edge cycle] 1->6->2->(closed) | cand_entry+z_entry+z_irred
--   roles: abs=3, tied+3, tied+3, abs=7, abs=2, abs=6; 2 instances at bases [6, 7]; all_strict=True; worst realized 62415/80017
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 1). -/
theorem shape_u270_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (2176:ℚ) * m + (4546:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have hshift : (2176:ℚ) * (m - 5) + (15426:ℚ) = (2176:ℚ) * m + (4546:ℚ) := by ring
  linarith [ht, hshift]
#print axioms shape_u270_uniform
-- u271 [3-edge cycle] 1->6->2->(closed) | cand_entry+z_entry+z_irred
--   roles: abs=3, abs=10, abs=9, abs=4, abs=2, abs=4; 1 instances at bases [7]; all_strict=True; worst realized 1215/1633
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u271_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (13794:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u271_uniform
-- u272 [3-edge cycle] 1->6->2->(closed) | cand_entry+z_entry+z_irred
--   roles: abs=3, tied+3, tied+3, abs=8, abs=2, abs=7; 2 instances at bases [7, 8]; all_strict=True; worst realized 26325/34523
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 1). -/
theorem shape_u272_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (2688:ℚ) * m + (5778:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have hshift : (2688:ℚ) * (m - 5) + (19218:ℚ) = (2688:ℚ) * m + (5778:ℚ) := by ring
  linarith [ht, hshift]
#print axioms shape_u272_uniform
-- u273 [3-edge cycle] 1->6->2->(closed) | cand_entry+z_entry+z_irred
--   roles: abs=4, tied+3, tied+3, tied=base, abs=3, tied-1; 2 instances at bases [9, 10]; all_strict=True; worst realized 162863/191425
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 2). -/
theorem shape_u273_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (512:ℚ) * m ^ 2 - (816:ℚ) * m - (5566:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have hshift : (512:ℚ) * (m - 5) ^ 2 + (4304:ℚ) * (m - 5) + (3154:ℚ) = (512:ℚ) * m ^ 2 - (816:ℚ) * m - (5566:ℚ) := by ring
  linarith [ht, h2, hshift]
#print axioms shape_u273_uniform
-- u274 [3-edge cycle] 1->6->2->(closed) | cand_entry+z_irred+z_entry
--   roles: abs=3, tied+3, tied-1, tied+1, tied=base, abs=2; 2 instances at bases [6, 7]; all_strict=True; worst realized 64719/82225
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 2). -/
theorem shape_u274_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (384:ℚ) * m ^ 2 - (704:ℚ) * m + (3618:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have hshift : (384:ℚ) * (m - 5) ^ 2 + (3136:ℚ) * (m - 5) + (9698:ℚ) = (384:ℚ) * m ^ 2 - (704:ℚ) * m + (3618:ℚ) := by ring
  linarith [ht, h2, hshift]
#print axioms shape_u274_uniform
-- u275 [3-edge cycle] 1->6->2->(closed) | cand_entry+z_irred+z_entry
--   roles: abs=4, abs=13, abs=8, abs=11, abs=9, abs=3; 1 instances at bases [10]; all_strict=True; worst realized 165375/195889
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u275_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (30514:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u275_uniform
-- u276 [3-edge cycle] 1->6->2->(closed) | cand_entry+z_irred+z_irred
--   roles: tied-1, tied+2, abs=4, tied+1, tied-2, abs=4; 2 instances at bases [5, 6]; all_strict=True; worst realized 4805/5643
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 2). -/
theorem shape_u276_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (128:ℚ) * m ^ 2 + (6286:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have hshift : (128:ℚ) * (m - 5) ^ 2 + (1280:ℚ) * (m - 5) + (9486:ℚ) = (128:ℚ) * m ^ 2 + (6286:ℚ) := by ring
  linarith [ht, h2, hshift]
#print axioms shape_u276_uniform
-- u277 [3-edge cycle] 1->6->2->(closed) | cand_entry+z_irred+z_irred
--   roles: abs=4, tied+2, tied=base, tied+1, abs=3, tied=base; 2 instances at bases [5, 6]; all_strict=True; worst realized 51129/62279
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 2). -/
theorem shape_u277_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (512:ℚ) * m ^ 2 - (464:ℚ) * m + (670:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have hshift : (512:ℚ) * (m - 5) ^ 2 + (4656:ℚ) * (m - 5) + (11150:ℚ) = (512:ℚ) * m ^ 2 - (464:ℚ) * m + (670:ℚ) := by ring
  linarith [ht, h2, hshift]
#print axioms shape_u277_uniform
-- u278 [3-edge cycle] 1->6->2->(closed) | cand_entry+z_irred+z_irred
--   roles: abs=5, tied+2, tied-1, tied+1, abs=4, tied-1; 5 instances at bases [5, 6, 7, 8, 9]; all_strict=True; worst realized 18259/21021
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 2). -/
theorem shape_u278_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (512:ℚ) * m ^ 2 - (1360:ℚ) * m + (2286:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have hshift : (512:ℚ) * (m - 5) ^ 2 + (3760:ℚ) * (m - 5) + (8286:ℚ) = (512:ℚ) * m ^ 2 - (1360:ℚ) * m + (2286:ℚ) := by ring
  linarith [ht, h2, hshift]
#print axioms shape_u278_uniform
-- u279 [3-edge cycle] 1->6->2->(closed) | cand_entry+z_irred+z_irred
--   roles: abs=5, tied+2, tied=base, tied+1, abs=4, tied=base; 5 instances at bases [5, 6, 7, 8, 9]; all_strict=True; worst realized 1767/2009
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 2). -/
theorem shape_u279_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (512:ℚ) * m ^ 2 - (848:ℚ) * m + (878:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have hshift : (512:ℚ) * (m - 5) ^ 2 + (4272:ℚ) * (m - 5) + (9438:ℚ) = (512:ℚ) * m ^ 2 - (848:ℚ) * m + (878:ℚ) := by ring
  linarith [ht, h2, hshift]
#print axioms shape_u279_uniform
-- u280 [3-edge cycle] 1->6->2->(closed) | cand_entry+z_irred+z_irred
--   roles: abs=6, tied+2, abs=5, tied+1, abs=5, abs=5; 4 instances at bases [5, 6, 7, 8]; all_strict=True; worst realized 86697/94423
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 1). -/
theorem shape_u280_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (3248:ℚ) * m - (8514:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have hshift : (3248:ℚ) * (m - 5) + (7726:ℚ) = (3248:ℚ) * m - (8514:ℚ) := by ring
  linarith [ht, hshift]
#print axioms shape_u280_uniform
-- u281 [3-edge cycle] 1->6->2->(closed) | cand_entry+z_irred+z_irred
--   roles: abs=3, tied+3, tied-1, tied+1, abs=2, tied-1; 4 instances at bases [6, 7, 9, 10]; all_strict=True; worst realized 14235/17917
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 2). -/
theorem shape_u281_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (512:ℚ) * m ^ 2 - (1552:ℚ) * m + (1926:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have hshift : (512:ℚ) * (m - 5) ^ 2 + (3568:ℚ) * (m - 5) + (6966:ℚ) = (512:ℚ) * m ^ 2 - (1552:ℚ) * m + (1926:ℚ) := by ring
  linarith [ht, h2, hshift]
#print axioms shape_u281_uniform
-- u282 [3-edge cycle] 1->6->2->(closed) | cand_entry+z_irred+z_irred
--   roles: abs=6, tied+2, abs=6, tied+1, abs=5, abs=6; 3 instances at bases [6, 7, 8]; all_strict=True; worst realized 845/931
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 1). -/
theorem shape_u282_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (3760:ℚ) * m - (10434:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have hshift : (3760:ℚ) * (m - 5) + (8366:ℚ) = (3760:ℚ) * m - (10434:ℚ) := by ring
  linarith [ht, hshift]
#print axioms shape_u282_uniform
-- u283 [3-edge cycle] 1->6->2->(closed) | cand_entry+z_irred+z_irred
--   roles: abs=7, tied+2, abs=6, tied+1, abs=6, abs=6; 3 instances at bases [6, 7, 8]; all_strict=True; worst realized 28717/30723
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 1). -/
theorem shape_u283_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (3888:ℚ) * m - (13298:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have hshift : (3888:ℚ) * (m - 5) + (6142:ℚ) = (3888:ℚ) * m - (13298:ℚ) := by ring
  linarith [ht, hshift]
#print axioms shape_u283_uniform
-- u284 [3-edge cycle] 1->6->2->(closed) | cand_entry+z_irred+z_irred
--   roles: tied-5, abs=11, tied-3, tied+1, tied-6, tied-3; 2 instances at bases [7, 8]; all_strict=True; worst realized 52065/68839
/-- pattern tau=(): real half-line form, lukas certificate (kind ALL, strict=True, deg D = 3). -/
theorem shape_u284_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (512:ℚ) * m ^ 3 - (9216:ℚ) * m ^ 2 + (55624:ℚ) * m - (100538:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have hsq1 : (0:ℚ) ≤ (m - 5 + (-45 / 16:ℚ)) ^ 2 := sq_nonneg _
  have hq1 : (0:ℚ) ≤ (512:ℚ) * (m - 5) + (1344:ℚ) := by linarith [ht]
  have hprod1 : (0:ℚ) ≤ (m - 5 + (-45 / 16:ℚ)) ^ 2 * ((512:ℚ) * (m - 5) + (1344:ℚ)) := mul_nonneg hsq1 hq1
  have hshift : (m - 5 + (-45 / 16:ℚ)) ^ 2 * ((512:ℚ) * (m - 5) + (1344:ℚ)) + (5374:ℚ) * (m - 5) + (2203 / 4:ℚ) = (512:ℚ) * m ^ 3 - (9216:ℚ) * m ^ 2 + (55624:ℚ) * m - (100538:ℚ) := by ring
  linarith [ht, hprod1, hshift]
#print axioms shape_u284_uniform
-- u285 [3-edge cycle] 1->6->2->(closed) | cand_entry+z_irred+z_irred
--   roles: tied-5, abs=11, tied-2, tied+1, tied-6, tied-2; 2 instances at bases [7, 8]; all_strict=True; worst realized 62745/82271
/-- pattern tau=(): real half-line form, lukas certificate (kind ALL, strict=True, deg D = 3). -/
theorem shape_u285_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (512:ℚ) * m ^ 3 - (8704:ℚ) * m ^ 2 + (47880:ℚ) * m - (68602:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have hsq1 : (0:ℚ) ≤ (m - 5 + (-47 / 16:ℚ)) ^ 2 := sq_nonneg _
  have hq1 : (0:ℚ) ≤ (512:ℚ) * (m - 5) + (1984:ℚ) := by linarith [ht]
  have hprod1 : (0:ℚ) ≤ (m - 5 + (-47 / 16:ℚ)) ^ 2 * ((512:ℚ) * (m - 5) + (1984:ℚ)) := mul_nonneg hsq1 hq1
  have hshift : (m - 5 + (-47 / 16:ℚ)) ^ 2 * ((512:ℚ) * (m - 5) + (1984:ℚ)) + (6478:ℚ) * (m - 5) + (313 / 4:ℚ) = (512:ℚ) * m ^ 3 - (8704:ℚ) * m ^ 2 + (47880:ℚ) * m - (68602:ℚ) := by ring
  linarith [ht, hprod1, hshift]
#print axioms shape_u285_uniform
-- u286 [3-edge cycle] 1->6->2->(closed) | cand_entry+z_irred+z_irred
--   roles: tied-2, tied+2, tied-2, tied+1, tied-3, tied-2; 3 instances at bases [7, 9, 10]; all_strict=True; worst realized 1067/1157
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 2). -/
theorem shape_u286_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (128:ℚ) * m ^ 2 + (2048:ℚ) * m - (4930:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have hshift : (128:ℚ) * (m - 5) ^ 2 + (3328:ℚ) * (m - 5) + (8510:ℚ) = (128:ℚ) * m ^ 2 + (2048:ℚ) * m - (4930:ℚ) := by ring
  linarith [ht, h2, hshift]
#print axioms shape_u286_uniform
-- u287 [3-edge cycle] 1->6->2->(closed) | cand_entry+z_irred+z_irred
--   roles: abs=6, tied+2, abs=7, tied+1, abs=5, abs=7; 3 instances at bases [7, 8, 9]; all_strict=True; worst realized 803/893
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 1). -/
theorem shape_u287_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (4272:ℚ) * m - (12354:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have hshift : (4272:ℚ) * (m - 5) + (9006:ℚ) = (4272:ℚ) * m - (12354:ℚ) := by ring
  linarith [ht, hshift]
#print axioms shape_u287_uniform
-- u288 [3-edge cycle] 1->6->2->(closed) | cand_entry+z_irred+z_irred
--   roles: abs=7, tied+2, abs=7, tied+1, abs=6, abs=7; 2 instances at bases [7, 8]; all_strict=True; worst realized 3431/3705
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 1). -/
theorem shape_u288_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (4400:ℚ) * m - (15730:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have hshift : (4400:ℚ) * (m - 5) + (6270:ℚ) = (4400:ℚ) * m - (15730:ℚ) := by ring
  linarith [ht, hshift]
#print axioms shape_u288_uniform
-- u289 [3-edge cycle] 1->6->2->(closed) | cand_entry+z_irred+z_irred
--   roles: abs=8, tied+2, abs=7, tied+1, abs=7, abs=7; 3 instances at bases [7, 8, 9]; all_strict=True; worst realized 44165/46683
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 1). -/
theorem shape_u289_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (4528:ℚ) * m - (19106:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have hshift : (4528:ℚ) * (m - 5) + (3534:ℚ) = (4528:ℚ) * m - (19106:ℚ) := by ring
  linarith [ht, hshift]
#print axioms shape_u289_uniform
-- u290 [3-edge cycle] 1->6->2->(closed) | cand_entry+z_irred+z_irred
--   roles: tied-6, abs=12, tied=base, tied+1, tied-7, tied=base; 2 instances at bases [8, 9]; all_strict=True; worst realized 34435/45333
/-- pattern tau=(): real half-line form, lukas certificate (kind ALL, strict=True, deg D = 3). -/
theorem shape_u290_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (512:ℚ) * m ^ 3 - (8704:ℚ) * m ^ 2 + (41160:ℚ) * m - (5970:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have hsq1 : (0:ℚ) ≤ (m - 5 + (-31 / 8:ℚ)) ^ 2 := sq_nonneg _
  have hq1 : (0:ℚ) ≤ (512:ℚ) * (m - 5) + (2944:ℚ) := by linarith [ht]
  have hprod1 : (0:ℚ) ≤ (m - 5 + (-31 / 8:ℚ)) ^ 2 * ((512:ℚ) * (m - 5) + (2944:ℚ)) := mul_nonneg hsq1 hq1
  have hshift : (m - 5 + (-31 / 8:ℚ)) ^ 2 * ((512:ℚ) * (m - 5) + (2944:ℚ)) + (7648:ℚ) * (m - 5) + (2024:ℚ) = (512:ℚ) * m ^ 3 - (8704:ℚ) * m ^ 2 + (41160:ℚ) * m - (5970:ℚ) := by ring
  linarith [ht, hprod1, hshift]
#print axioms shape_u290_uniform
-- u291 [3-edge cycle] 1->6->2->(closed) | cand_entry+z_irred+z_irred
--   roles: abs=6, tied+2, abs=8, tied+1, abs=5, abs=8; 3 instances at bases [8, 9, 10]; all_strict=True; worst realized 15309/17155
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 1). -/
theorem shape_u291_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (4784:ℚ) * m - (14274:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have hshift : (4784:ℚ) * (m - 5) + (9646:ℚ) = (4784:ℚ) * m - (14274:ℚ) := by ring
  linarith [ht, hshift]
#print axioms shape_u291_uniform
-- u292 [3-edge cycle] 1->6->2->(closed) | cand_entry+z_irred+z_irred
--   roles: abs=7, tied+2, abs=8, tied+1, abs=6, abs=8; 3 instances at bases [8, 9, 10]; all_strict=True; worst realized 239841/260975
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 1). -/
theorem shape_u292_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (4912:ℚ) * m - (18162:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have hshift : (4912:ℚ) * (m - 5) + (6398:ℚ) = (4912:ℚ) * m - (18162:ℚ) := by ring
  linarith [ht, hshift]
#print axioms shape_u292_uniform
-- u293 [3-edge cycle] 1->6->2->(closed) | cand_entry+z_irred+z_irred
--   roles: abs=8, tied+2, abs=8, tied+1, abs=7, abs=8; 2 instances at bases [8, 9]; all_strict=True; worst realized 891/949
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 1). -/
theorem shape_u293_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (5040:ℚ) * m - (22050:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have hshift : (5040:ℚ) * (m - 5) + (3150:ℚ) = (5040:ℚ) * m - (22050:ℚ) := by ring
  linarith [ht, hshift]
#print axioms shape_u293_uniform
-- u294 [3-edge cycle] 1->6->2->(closed) | cand_entry+z_irred+z_irred
--   roles: abs=3, tied+3, tied-2, tied+1, abs=2, tied-2; 2 instances at bases [9, 10]; all_strict=True; worst realized 26675/35397
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 2). -/
theorem shape_u294_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (512:ℚ) * m ^ 2 - (2064:ℚ) * m + (3270:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have hshift : (512:ℚ) * (m - 5) ^ 2 + (3056:ℚ) * (m - 5) + (5750:ℚ) = (512:ℚ) * m ^ 2 - (2064:ℚ) * m + (3270:ℚ) := by ring
  linarith [ht, h2, hshift]
#print axioms shape_u294_uniform
-- u295 [3-edge cycle] 1->6->2->(closed) | cand_entry+z_irred+z_irred
--   roles: abs=6, tied+2, abs=9, tied+1, abs=5, abs=9; 2 instances at bases [9, 10]; all_strict=True; worst realized 82147/92637
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 1). -/
theorem shape_u295_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (5296:ℚ) * m - (16194:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have hshift : (5296:ℚ) * (m - 5) + (10286:ℚ) = (5296:ℚ) * m - (16194:ℚ) := by ring
  linarith [ht, hshift]
#print axioms shape_u295_uniform
-- u296 [3-edge cycle] 1->6->2->(closed) | cand_entry+z_irred+z_irred
--   roles: abs=7, tied+2, abs=9, tied+1, abs=6, abs=9; 2 instances at bases [9, 10]; all_strict=True; worst realized 296993/325215
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 1). -/
theorem shape_u296_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (5424:ℚ) * m - (20594:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have hshift : (5424:ℚ) * (m - 5) + (6526:ℚ) = (5424:ℚ) * m - (20594:ℚ) := by ring
  linarith [ht, hshift]
#print axioms shape_u296_uniform
-- u297 [3-edge cycle] 1->6->2->(closed) | cand_entry+z_irred+z_irred
--   roles: abs=8, tied+2, abs=9, tied+1, abs=7, abs=9; 2 instances at bases [9, 10]; all_strict=True; worst realized 347545/372519
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 1). -/
theorem shape_u297_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (5552:ℚ) * m - (24994:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have hshift : (5552:ℚ) * (m - 5) + (2766:ℚ) = (5552:ℚ) * m - (24994:ℚ) := by ring
  linarith [ht, hshift]
#print axioms shape_u297_uniform
-- u298 [3-edge cycle] 1->6->2->(closed) | cand_entry+z_irred+z_irred
--   roles: abs=3, abs=13, abs=10, abs=11, abs=2, abs=10; 1 instances at bases [10]; all_strict=True; worst realized 13825/18423
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u298_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (41382:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u298_uniform
-- u299 [3-edge cycle] 1->6->2->(closed) | cand_entry+z_irred+z_irred
--   roles: abs=4, abs=13, abs=8, abs=11, abs=3, abs=8; 1 instances at bases [10]; all_strict=True; worst realized 30429/35867
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u299_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (27190:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u299_uniform
-- u300 [3-edge cycle] 1->6->2->(closed) | cand_entry+z_irred+z_irred
--   roles: abs=6, abs=12, abs=10, abs=11, abs=5, abs=10; 1 instances at bases [10]; all_strict=True; worst realized 99619/112941
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u300_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (39966:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u300_uniform
-- u301 [3-edge cycle] 1->6->2->(closed) | cand_entry+z_irred+z_irred
--   roles: abs=7, abs=12, abs=10, abs=11, abs=6, abs=10; 1 instances at bases [10]; all_strict=True; worst realized 360161/396495
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u301_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (36334:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u301_uniform
-- u302 [3-edge cycle] 1->6->2->(closed) | cand_entry+z_irred+z_irred
--   roles: abs=8, abs=12, abs=10, abs=11, abs=7, abs=10; 1 instances at bases [10]; all_strict=True; worst realized 421465/454167
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u302_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (32702:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u302_uniform
-- u303 [3-edge cycle] 1->6->2->(closed) | cand_entry+z_irred+z_irred
--   roles: abs=9, abs=12, abs=10, abs=11, abs=8, abs=10; 1 instances at bases [10]; all_strict=True; worst realized 53641/56871
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u303_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (29070:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u303_uniform
-- u304 [3-edge cycle] 1->6->2->(closed) | cand_entry+z_irred+z_irred
--   roles: abs=10, abs=12, abs=10, abs=11, abs=9, abs=10; 1 instances at bases [10]; all_strict=True; worst realized 6887/7209
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u304_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (25438:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u304_uniform
-- u305 [3-edge cycle] 1->6->2->(closed) | cand_entry+z_irred+z_irred
--   roles: abs=11, abs=12, abs=10, abs=11, abs=10, abs=10; 1 instances at bases [10]; all_strict=True; worst realized 605377/627183
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u305_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (21806:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u305_uniform
-- u306 [3-edge cycle] 1->6->2->(closed) | cand_irred+z_irred+z_irred
--   roles: tied+2, tied-2, abs=5, tied+1, tied-2, abs=5; 3 instances at bases [5, 6, 7]; all_strict=True; worst realized 8307/8405
/-- pattern tau=(): real half-line form, quad_vertex certificate (kind ALL, strict=True, deg D = 2). -/
theorem shape_u306_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (128:ℚ) * m ^ 2 - (1344:ℚ) * m + (4410:ℚ) := by
  intro m hm
  have hsq : (0:ℚ) ≤ (m - 5 + (-1 / 4:ℚ)) ^ 2 := sq_nonneg _
  have hexp : (m - 5 + (-1 / 4:ℚ)) ^ 2 = (m - 5) ^ 2 + (-1 / 2:ℚ) * (m - 5) + (1 / 16:ℚ) := by ring
  have hshift : (128:ℚ) * ((m - 5) ^ 2 + (-1 / 2:ℚ) * (m - 5) + (1 / 16:ℚ)) + (882:ℚ) = (128:ℚ) * m ^ 2 - (1344:ℚ) * m + (4410:ℚ) := by ring
  linarith [hsq, hexp, hshift]
#print axioms shape_u306_uniform
-- u307 [3-edge cycle] 1->6->2->(closed) | cand_irred+z_irred+z_irred
--   roles: abs=7, abs=4, abs=4, abs=6, abs=4, abs=4; 1 instances at bases [5]; all_strict=True; worst realized 4805/4851
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u307_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (506:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u307_uniform
-- u308 [3-edge cycle] 1->6->2->(closed) | cand_irred+z_irred+z_irred
--   roles: tied+2, abs=6, tied-2, tied+1, abs=6, tied-2; 2 instances at bases [8, 9]; all_strict=True; worst realized 174511/175273
/-- pattern tau=(): real half-line form, quad_vertex certificate (kind ALL, strict=True, deg D = 2). -/
theorem shape_u308_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (128:ℚ) * m ^ 2 - (1600:ℚ) * m + (5370:ℚ) := by
  intro m hm
  have hsq : (0:ℚ) ≤ (m - 5 + (-5 / 4:ℚ)) ^ 2 := sq_nonneg _
  have hexp : (m - 5 + (-5 / 4:ℚ)) ^ 2 = (m - 5) ^ 2 + (-5 / 2:ℚ) * (m - 5) + (25 / 16:ℚ) := by ring
  have hshift : (128:ℚ) * ((m - 5) ^ 2 + (-5 / 2:ℚ) * (m - 5) + (25 / 16:ℚ)) + (370:ℚ) = (128:ℚ) * m ^ 2 - (1600:ℚ) * m + (5370:ℚ) := by ring
  linarith [hsq, hexp, hshift]
#print axioms shape_u308_uniform
-- u309 [3-edge cycle] 1->6->2->(closed) | cand_irred+z_irred+z_irred
--   roles: abs=12, abs=6, abs=10, abs=11, abs=6, abs=10; 1 instances at bases [10]; all_strict=True; worst realized 352735/353241
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u309_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (506:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u309_uniform
-- u310 [3-edge cycle] 1->6->2->(closed) | cand_irred+z_irred+z_irred
--   roles: abs=12, abs=7, abs=8, abs=11, abs=7, abs=8; 1 instances at bases [10]; all_strict=True; worst realized 1155/1157
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u310_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (570:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u310_uniform
-- u311 [3-edge cycle] 1->6->2->(closed) | cand_irred+z_irred+z_irred
--   roles: abs=13, abs=2, abs=9, abs=11, abs=2, abs=9; 1 instances at bases [10]; all_strict=True; worst realized 109695/110449
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u311_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (754:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u311_uniform
-- u312 [3-edge cycle] 1->6->2->(closed) | cand_irred+z_irred+z_irred
--   roles: abs=13, abs=2, abs=10, abs=11, abs=2, abs=10; 1 instances at bases [10]; all_strict=True; worst realized 40685/40851
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u312_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (498:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u312_uniform
-- u313 [3-edge cycle] 1->6->3->(closed) | cand_entry+z_entry+z_entry
--   roles: tied+1, tied+2, tied+1, tied=base, tied+1, tied=base; 6 instances at bases [5, 6, 7, 8, 9, 10]; all_strict=True; worst realized 23571/24389
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 2). -/
theorem shape_u313_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (128:ℚ) * m ^ 2 + (896:ℚ) * m + (326:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have hshift : (128:ℚ) * (m - 5) ^ 2 + (2176:ℚ) * (m - 5) + (8006:ℚ) = (128:ℚ) * m ^ 2 + (896:ℚ) * m + (326:ℚ) := by ring
  linarith [ht, h2, hshift]
#print axioms shape_u313_uniform
-- u314 [3-edge cycle] 1->6->3->(closed) | cand_entry+z_entry+z_entry
--   roles: abs=3, tied+3, tied+1, tied=base, tied+2, abs=2; 21 instances at bases [6, 7, 8, 9]; all_strict=True; worst realized 8687/11385
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 2). -/
theorem shape_u314_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (384:ℚ) * m ^ 2 + (512:ℚ) * m + (1990:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have hshift : (384:ℚ) * (m - 5) ^ 2 + (4352:ℚ) * (m - 5) + (14150:ℚ) = (384:ℚ) * m ^ 2 + (512:ℚ) * m + (1990:ℚ) := by ring
  linarith [ht, h2, hshift]
#print axioms shape_u314_uniform
-- u315 [3-edge cycle] 1->6->3->(closed) | cand_entry+z_entry+z_entry
--   roles: abs=4, tied+3, tied+1, tied=base, tied+2, abs=3; 8 instances at bases [7, 8, 9, 10]; all_strict=True; worst realized 12825/15407
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 2). -/
theorem shape_u315_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (384:ℚ) * m ^ 2 + (256:ℚ) * m + (2630:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have hshift : (384:ℚ) * (m - 5) ^ 2 + (4096:ℚ) * (m - 5) + (13510:ℚ) = (384:ℚ) * m ^ 2 + (256:ℚ) * m + (2630:ℚ) := by ring
  linarith [ht, h2, hshift]
#print axioms shape_u315_uniform
-- u316 [3-edge cycle] 1->6->3->(closed) | cand_entry+z_entry+z_entry
--   roles: abs=5, tied+3, tied+1, tied=base, tied+2, abs=4; 4 instances at bases [9, 10]; all_strict=True; worst realized 77891/89349
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 2). -/
theorem shape_u316_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (384:ℚ) * m ^ 2 + (3270:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have hshift : (384:ℚ) * (m - 5) ^ 2 + (3840:ℚ) * (m - 5) + (12870:ℚ) = (384:ℚ) * m ^ 2 + (3270:ℚ) := by ring
  linarith [ht, h2, hshift]
#print axioms shape_u316_uniform
-- u317 [3-edge cycle] 1->6->3->(closed) | cand_entry+z_entry+z_irred
--   roles: abs=4, tied+3, tied+1, tied=base, abs=3, tied+1; 7 instances at bases [8, 9, 10]; all_strict=True; worst realized 133055/160673
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 2). -/
theorem shape_u317_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (512:ℚ) * m ^ 2 - (816:ℚ) * m + (1378:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have hshift : (512:ℚ) * (m - 5) ^ 2 + (4304:ℚ) * (m - 5) + (10098:ℚ) = (512:ℚ) * m ^ 2 - (816:ℚ) * m + (1378:ℚ) := by ring
  linarith [ht, h2, hshift]
#print axioms shape_u317_uniform
-- u318 [3-edge cycle] 1->6->3->(closed) | cand_entry+z_entry+z_irred
--   roles: abs=2, abs=14, abs=10, abs=9, abs=1, abs=10; 2 instances at bases [9]; all_strict=True; worst realized 57743/95985
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u318_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (38242:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u318_uniform
-- u319 [3-edge cycle] 1->6->3->(closed) | cand_entry+z_entry+z_irred
--   roles: abs=5, tied+3, tied+1, tied=base, abs=4, tied+1; 2 instances at bases [9, 10]; all_strict=True; worst realized 219511/249561
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 2). -/
theorem shape_u319_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (512:ℚ) * m ^ 2 - (1456:ℚ) * m + (1682:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have hshift : (512:ℚ) * (m - 5) ^ 2 + (3664:ℚ) * (m - 5) + (7202:ℚ) = (512:ℚ) * m ^ 2 - (1456:ℚ) * m + (1682:ℚ) := by ring
  linarith [ht, h2, hshift]
#print axioms shape_u319_uniform
-- u320 [3-edge cycle] 1->6->3->(closed) | cand_entry+z_entry+z_irred
--   roles: abs=6, abs=13, abs=11, abs=10, abs=5, abs=11; 1 instances at bases [10]; all_strict=True; worst realized 110565/121307
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u320_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (32226:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u320_uniform
-- u321 [3-edge cycle] 1->6->3->(closed) | cand_irred+z_entry+z_irred
--   roles: abs=9, tied-4, tied+1, tied=base, tied-4, tied+1; 4 instances at bases [5, 6]; all_strict=True; worst realized 2911/2961
/-- pattern tau=(): integer half-line form (kind ALL; Newton-ladder certificate, coefficients ['350', '760', '7424', '3072']). -/
theorem shape_u321_uniform : ∀ n : ℕ, 5 ≤ n → 0 < (512:ℚ) * (n:ℚ) ^ 3 - (5504:ℚ) * (n:ℚ) ^ 2 + (14712:ℚ) * (n:ℚ) + (390:ℚ) := by
  intro n hn
  have h3 : (0:ℚ) ≤ (3072:ℚ) := by norm_num
  have h2 : ∀ t : ℕ, (7424:ℚ) ≤ (3072:ℚ) * (t:ℚ) + (7424:ℚ) := by
    intro t
    have htn : (0:ℚ) ≤ ((t:ℚ)) := Nat.cast_nonneg _
    linarith [htn]
  have h1 : ∀ t : ℕ, (760:ℚ) ≤ (1536:ℚ) * (t:ℚ) ^ 2 + (5888:ℚ) * (t:ℚ) + (760:ℚ) := by
    intro t
    have htn : (0:ℚ) ≤ ((t:ℚ)) := Nat.cast_nonneg _
    have hp1_2 : (0:ℚ) ≤ ((t:ℚ)) ^ 2 := sq_nonneg _
    linarith [htn, hp1_2]
  have h0 : ∀ t : ℕ, (350:ℚ) ≤ (512:ℚ) * (t:ℚ) ^ 3 + (2176:ℚ) * (t:ℚ) ^ 2 - (1928:ℚ) * (t:ℚ) + (350:ℚ) := by
    intro t
    induction t with
    | zero => norm_num
    | succ k ih =>
      have hcast : ((k + 1:ℕ):ℚ) = (k:ℚ) + 1 := Nat.cast_add_one k
      have hstep : (512:ℚ) * ((k:ℚ) + 1) ^ 3 + (2176:ℚ) * ((k:ℚ) + 1) ^ 2 - (1928:ℚ) * ((k:ℚ) + 1) + (350:ℚ) = (512:ℚ) * (k:ℚ) ^ 3 + (2176:ℚ) * (k:ℚ) ^ 2 - (1928:ℚ) * (k:ℚ) + (350:ℚ) + (1536:ℚ) * (k:ℚ) ^ 2 + (5888:ℚ) * (k:ℚ) + (760:ℚ) := by ring
      have hn0 := h1 k
      rw [hcast]
      linarith
  have hsub : ((n - 5:ℕ):ℚ) = (n:ℚ) - 5 := Nat.cast_sub hn
  have h0n := h0 (n - 5)
  rw [hsub] at h0n
  have hshift : (512:ℚ) * ((n:ℚ) - 5) ^ 3 + (2176:ℚ) * ((n:ℚ) - 5) ^ 2 - (1928:ℚ) * ((n:ℚ) - 5) + (350:ℚ) = (512:ℚ) * (n:ℚ) ^ 3 - (5504:ℚ) * (n:ℚ) ^ 2 + (14712:ℚ) * (n:ℚ) + (390:ℚ) := by ring
  linarith
#print axioms shape_u321_uniform
-- u322 [3-edge cycle] 1->6->4->(closed) | cand_entry+z_entry+z_entry
--   roles: abs=2, abs=13, abs=12, abs=11, abs=11, abs=1; 1 instances at bases [7]; all_strict=True; worst realized 1869/2755
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u322_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (39870:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u322_uniform
-- u323 [3-edge cycle] 2->3->1->(closed) | cand_entry+z_entry+z_entry
--   roles: abs=3, abs=7, abs=7, abs=2, abs=2, abs=2; 1 instances at bases [5]; all_strict=True; worst realized 5491/6325
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u323_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (2502:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u323_uniform
-- u324 [3-edge cycle] 2->3->1->(closed) | cand_entry+z_entry+z_entry
--   roles: abs=4, abs=9, abs=8, abs=1, abs=1, abs=2; 1 instances at bases [5]; all_strict=True; worst realized 1241/1519
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u324_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (2502:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u324_uniform
-- u325 [3-edge cycle] 2->3->1->(closed) | cand_entry+z_entry+z_entry
--   roles: abs=10, abs=10, abs=10, abs=1, abs=1, abs=7; 1 instances at bases [7]; all_strict=True; worst realized 41553/43687
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u325_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (2134:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u325_uniform
-- u326 [3-edge cycle] 2->3->1->(closed) | cand_entry+z_entry+z_entry
--   roles: abs=14, abs=14, abs=14, abs=1, abs=1, abs=10; 1 instances at bases [10]; all_strict=True; worst realized 9153/9583
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u326_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (3870:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u326_uniform
-- u327 [3-edge cycle] 2->3->1->(closed) | cand_progress+z_entry+z_irred
--   roles: abs=8, abs=7, abs=9, abs=2, abs=7, abs=2; 1 instances at bases [7]; all_strict=True; worst realized 3575/4047
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u327_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (8024:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u327_uniform
-- u328 [3-edge cycle] 2->3->1->(closed) | cand_progress+z_irred+z_progress
--   roles: abs=10, abs=7, abs=2, abs=9, abs=7, abs=2; 1 instances at bases [8]; all_strict=True; worst realized 1215/1241
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u328_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (1482:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u328_uniform
-- u329 [3-edge cycle] 2->4->1->(closed) | cand_entry+z_entry+z_entry
--   roles: abs=4, tied+2, tied+2, abs=3, abs=3, abs=3; 2 instances at bases [5, 6]; all_strict=True; worst realized 7125/7843
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 1). -/
theorem shape_u329_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (704:ℚ) * m + (70:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have hshift : (704:ℚ) * (m - 5) + (3590:ℚ) = (704:ℚ) * m + (70:ℚ) := by ring
  linarith [ht, hshift]
#print axioms shape_u329_uniform
-- u330 [3-edge cycle] 2->4->1->(closed) | cand_entry+z_entry+z_entry
--   roles: abs=5, abs=9, abs=9, abs=3, abs=3, abs=4; 1 instances at bases [7]; all_strict=True; worst realized 20075/21229
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u330_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (3462:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u330_uniform
-- u331 [3-edge cycle] 2->4->5->(closed) | cand_entry+z_entry+z_entry
--   roles: abs=4, abs=11, abs=6, abs=6, abs=8, abs=2; 1 instances at bases [6]; all_strict=True; worst realized 10591/13113
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u331_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (17654:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u331_uniform
-- u332 [3-edge cycle] 2->5->1->(closed) | cand_entry+z_entry+z_entry
--   roles: abs=2, abs=10, abs=10, abs=1, abs=1, abs=1; 1 instances at bases [5]; all_strict=True; worst realized 2187/2765
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u332_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (1734:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u332_uniform
-- u333 [3-edge cycle] 2->5->1->(closed) | cand_entry+z_entry+z_entry
--   roles: abs=5, tied+2, tied+2, tied-2, tied-2, abs=4; 2 instances at bases [5, 6]; all_strict=True; worst realized 285/299
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 2). -/
theorem shape_u333_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (384:ℚ) * m ^ 2 - (1152:ℚ) * m - (1530:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have hshift : (384:ℚ) * (m - 5) ^ 2 + (2688:ℚ) * (m - 5) + (2310:ℚ) = (384:ℚ) * m ^ 2 - (1152:ℚ) * m - (1530:ℚ) := by ring
  linarith [ht, h2, hshift]
#print axioms shape_u333_uniform
-- u334 [3-edge cycle] 2->5->1->(closed) | cand_entry+z_entry+z_entry
--   roles: abs=11, abs=13, abs=13, abs=2, abs=2, abs=9; 1 instances at bases [10]; all_strict=True; worst realized 8687/8961
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u334_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (4110:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u334_uniform
-- u335 [3-edge cycle] 2->5->1->(closed) | cand_entry+z_irred+z_irred
--   roles: abs=10, abs=12, abs=1, abs=9, abs=9, abs=1; 2 instances at bases [8]; all_strict=True; worst realized 48209/51903
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u335_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (3694:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u335_uniform
-- u336 [3-edge cycle] 2->5->1->(closed) | cand_progress+z_entry+z_entry
--   roles: abs=10, abs=8, abs=11, abs=1, abs=1, abs=6; 1 instances at bases [7]; all_strict=True; worst realized 1701/1885
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u336_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (3864:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u336_uniform
-- u337 [3-edge cycle] 2->5->1->(closed) | cand_progress+z_entry+z_irred
--   roles: abs=14, abs=12, abs=15, abs=1, abs=12, abs=1; 1 instances at bases [10]; all_strict=True; worst realized 10735/11543
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u337_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (7272:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u337_uniform
-- u338 [3-edge cycle] 2->5->1->(closed) | cand_progress+z_irred+z_progress
--   roles: abs=7, abs=5, abs=1, abs=6, abs=5, abs=1; 1 instances at bases [5]; all_strict=True; worst realized 19/21
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u338_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (1722:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u338_uniform
-- u339 [3-edge cycle] 2->5->1->(closed) | cand_progress+z_irred+z_progress
--   roles: abs=12, abs=10, abs=2, abs=11, abs=10, abs=2; 1 instances at bases [10]; all_strict=True; worst realized 1455/1513
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u339_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (4698:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u339_uniform
-- u340 [3-edge cycle] 2->5->6->(closed) | cand_entry+z_entry+z_entry
--   roles: abs=9, abs=13, abs=9, abs=9, abs=13, abs=8; 2 instances at bases [8]; all_strict=True; worst realized 498225/519223
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u340_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (20998:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u340_uniform
-- u341 [3-edge cycle] 2->5->6->(closed) | cand_entry+z_entry+z_irred
--   roles: abs=2, free+3..+5, tied+1, tied+1, abs=1, tied+1; 15 instances at bases [5, 6]; all_strict=True; worst realized 189/235
/-- pattern tau=(3): real half-line form, mono certificate (kind ALL, strict=True, deg D = 2). -/
theorem shape_u341_pat1_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (512:ℚ) * m ^ 2 + (16:ℚ) * m - (630:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have hshift : (512:ℚ) * (m - 5) ^ 2 + (5136:ℚ) * (m - 5) + (12250:ℚ) = (512:ℚ) * m ^ 2 + (16:ℚ) * m - (630:ℚ) := by ring
  linarith [ht, h2, hshift]
#print axioms shape_u341_pat1_uniform
/-- pattern tau=(4): real half-line form, mono certificate (kind ALL, strict=True, deg D = 2). -/
theorem shape_u341_pat2_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (512:ℚ) * m ^ 2 - (432:ℚ) * m - (1134:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have hshift : (512:ℚ) * (m - 5) ^ 2 + (4688:ℚ) * (m - 5) + (9506:ℚ) = (512:ℚ) * m ^ 2 - (432:ℚ) * m - (1134:ℚ) := by ring
  linarith [ht, h2, hshift]
#print axioms shape_u341_pat2_uniform
/-- pattern tau=(5): real half-line form, mono certificate (kind ALL, strict=True, deg D = 2). -/
theorem shape_u341_pat3_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (512:ℚ) * m ^ 2 - (880:ℚ) * m - (1638:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have hshift : (512:ℚ) * (m - 5) ^ 2 + (4240:ℚ) * (m - 5) + (6762:ℚ) = (512:ℚ) * m ^ 2 - (880:ℚ) * m - (1638:ℚ) := by ring
  linarith [ht, h2, hshift]
#print axioms shape_u341_pat3_uniform
-- u342 [3-edge cycle] 2->5->6->(closed) | cand_entry+z_entry+z_irred
--   roles: abs=12, abs=12, abs=11, abs=11, abs=10, abs=11; 1 instances at bases [10]; all_strict=True; worst realized 7663/8265
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u342_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (53578:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u342_uniform
-- u343 [3-edge cycle] 2->5->6->(closed) | cand_entry+z_entry+z_irred
--   roles: abs=13, abs=15, abs=11, abs=11, abs=12, abs=15; 1 instances at bases [10]; all_strict=True; worst realized 8455/8961
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u343_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (61226:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u343_uniform
-- u344 [3-edge cycle] 2->5->6->(closed) | cand_progress+z_entry+z_irred
--   roles: free+3..+4, tied+1, tied+1, tied+1, tied+1, tied+4; 4 instances at bases [6, 7]; all_strict=True; worst realized 1
/-- pattern tau=(3): real half-line form, mono certificate (kind ALL, strict=True, deg D = 2). -/
theorem shape_u344_pat1_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (512:ℚ) * m ^ 2 + (1024:ℚ) * m + (504:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have hshift : (512:ℚ) * (m - 5) ^ 2 + (6144:ℚ) * (m - 5) + (18424:ℚ) = (512:ℚ) * m ^ 2 + (1024:ℚ) * m + (504:ℚ) := by ring
  linarith [ht, h2, hshift]
#print axioms shape_u344_pat1_uniform
/-- pattern tau=(4): D ≡ 0 identically (weak kill: P ≡ 1 with the strict candidate edge); A and B coincide as polynomials. -/
theorem shape_u344_pat2_uniform : ∀ m : ℚ, 5 ≤ m → (512:ℚ) * m ^ 3 + (3136:ℚ) * m ^ 2 + (4728:ℚ) * m + (2079:ℚ) = (512:ℚ) * m ^ 3 + (3136:ℚ) * m ^ 2 + (4728:ℚ) * m + (2079:ℚ) := fun _ _ => rfl
#print axioms shape_u344_pat2_uniform
-- u345 [3-edge cycle] 2->5->6->(closed) | cand_progress+z_entry+z_irred
--   roles: abs=11, abs=8, abs=10, abs=10, abs=7, abs=10; 1 instances at bases [9]; all_strict=True; worst realized 979/1027
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u345_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (19440:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u345_uniform
-- u346 [3-edge cycle] 2->6->1->(closed) | cand_entry+z_entry+z_entry
--   roles: abs=2, abs=12, abs=12, abs=1, abs=1, abs=1; 1 instances at bases [6]; all_strict=True; worst realized 2619/3325
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u346_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (2118:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u346_uniform
-- u347 [3-edge cycle] 2->6->1->(closed) | cand_entry+z_entry+z_entry
--   roles: abs=7, tied+2, tied+2, abs=6, abs=6, abs=6; 2 instances at bases [6, 7]; all_strict=True; worst realized 4459/4653
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 1). -/
theorem shape_u347_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (1472:ℚ) * m - (2042:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have hshift : (1472:ℚ) * (m - 5) + (5318:ℚ) = (1472:ℚ) * m - (2042:ℚ) := by ring
  linarith [ht, hshift]
#print axioms shape_u347_uniform
-- u348 [3-edge cycle] 2->6->1->(closed) | cand_entry+z_entry+z_entry
--   roles: abs=8, tied+2, tied+2, abs=7, abs=7, abs=7; 3 instances at bases [7, 8, 9]; all_strict=True; worst realized 26353/27335
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 1). -/
theorem shape_u348_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (1728:ℚ) * m - (3258:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have hshift : (1728:ℚ) * (m - 5) + (5382:ℚ) = (1728:ℚ) * m - (3258:ℚ) := by ring
  linarith [ht, hshift]
#print axioms shape_u348_uniform
-- u349 [3-edge cycle] 2->6->1->(closed) | cand_entry+z_entry+z_entry
--   roles: abs=10, tied+2, tied+2, abs=9, abs=9, abs=9; 2 instances at bases [9, 10]; all_strict=True; worst realized 474281/487983
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 1). -/
theorem shape_u349_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (2240:ℚ) * m - (6458:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have hshift : (2240:ℚ) * (m - 5) + (4742:ℚ) = (2240:ℚ) * m - (6458:ℚ) := by ring
  linarith [ht, hshift]
#print axioms shape_u349_uniform
-- u350 [3-edge cycle] 2->6->1->(closed) | cand_entry+z_entry+z_entry
--   roles: abs=11, abs=12, abs=12, abs=9, abs=9, abs=10; 1 instances at bases [10]; all_strict=True; worst realized 191187/195605
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u350_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (13254:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u350_uniform
-- u351 [3-edge cycle] 2->6->1->(closed) | cand_entry+z_entry+z_entry
--   roles: abs=11, abs=12, abs=12, abs=10, abs=10, abs=10; 1 instances at bases [10]; all_strict=True; worst realized 212139/217645
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u351_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (16518:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u351_uniform
-- u352 [3-edge cycle] 2->6->1->(closed) | cand_entry+z_irred+z_irred
--   roles: abs=5, abs=7, abs=3, abs=6, abs=4, abs=3; 1 instances at bases [5]; all_strict=True; worst realized 13547/15925
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u352_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (7134:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u352_uniform
-- u353 [3-edge cycle] 2->6->1->(closed) | cand_entry+z_irred+z_irred
--   roles: abs=6, abs=7, abs=3, abs=6, abs=5, abs=3; 1 instances at bases [5]; all_strict=True; worst realized 51129/57575
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u353_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (6446:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u353_uniform
-- u354 [3-edge cycle] 2->6->1->(closed) | cand_entry+z_irred+z_irred
--   roles: tied+1, tied+2, tied-1, tied+1, tied=base, tied-1; 2 instances at bases [5, 6]; all_strict=True; worst realized 7943/8569
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 2). -/
theorem shape_u354_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (128:ℚ) * m ^ 2 + (896:ℚ) * m - (594:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have hshift : (128:ℚ) * (m - 5) ^ 2 + (2176:ℚ) * (m - 5) + (7086:ℚ) = (128:ℚ) * m ^ 2 + (896:ℚ) * m - (594:ℚ) := by ring
  linarith [ht, h2, hshift]
#print axioms shape_u354_uniform
-- u355 [3-edge cycle] 2->6->1->(closed) | cand_irred+z_irred+z_irred
--   roles: abs=7, abs=5, abs=3, abs=6, abs=5, abs=3; 1 instances at bases [5]; all_strict=True; worst realized 9867/10045
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u355_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (890:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u355_uniform
-- u356 [3-edge cycle] 2->6->1->(closed) | cand_progress+z_entry+z_entry
--   roles: abs=9, abs=8, abs=10, abs=1, abs=1, abs=6; 1 instances at bases [6]; all_strict=True; worst realized 4599/5135
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u356_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (3752:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u356_uniform
-- u357 [3-edge cycle] 2->6->3->(closed) | cand_entry+z_entry+weak
--   roles: abs=7, abs=7, abs=6, abs=5; 2 instances at bases [5]; all_strict=False; worst realized 2337/2585
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u357_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (248:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u357_uniform
-- u358 [3-edge cycle] 2->6->3->(closed) | cand_entry+z_entry+z_entry
--   roles: tied+2, tied+3, tied+1, tied=base, tied+2, tied+1; 16 instances at bases [6, 7, 8, 9, 10]; all_strict=True; worst realized 50463/52345
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 2). -/
theorem shape_u358_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (128:ℚ) * m ^ 2 + (1408:ℚ) * m + (1350:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have hshift : (128:ℚ) * (m - 5) ^ 2 + (2688:ℚ) * (m - 5) + (11590:ℚ) = (128:ℚ) * m ^ 2 + (1408:ℚ) * m + (1350:ℚ) := by ring
  linarith [ht, h2, hshift]
#print axioms shape_u358_uniform
-- u359 [3-edge cycle] 2->6->3->(closed) | cand_entry+z_entry+z_entry
--   roles: tied+1, tied+3, tied+1, tied=base, tied+2, tied=base; 7 instances at bases [8, 9, 10]; all_strict=True; worst realized 15309/15979
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 2). -/
theorem shape_u359_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (128:ℚ) * m ^ 2 + (1664:ℚ) * m + (710:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have hshift : (128:ℚ) * (m - 5) ^ 2 + (2944:ℚ) * (m - 5) + (12230:ℚ) = (128:ℚ) * m ^ 2 + (1664:ℚ) * m + (710:ℚ) := by ring
  linarith [ht, h2, hshift]
#print axioms shape_u359_uniform
-- u360 [3-edge cycle] 2->6->3->(closed) | cand_irred+z_entry+z_entry
--   roles: abs=13, abs=6, abs=8, abs=7, abs=8, abs=4; 1 instances at bases [7]; all_strict=True; worst realized 21527/21609
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u360_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (738:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u360_uniform
-- u361 [3-edge cycle] 3->1->2->(closed) | cand_progress+z_entry+z_progress
--   roles: abs=1, abs=10, abs=2, abs=6, abs=10, abs=7; 1 instances at bases [8]; all_strict=True; worst realized 49/95
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u361_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (33534:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u361_uniform
-- u362 [3-edge cycle] 3->1->6->(closed) | cand_progress+z_entry+z_entry
--   roles: abs=1, abs=7, abs=2, abs=7, abs=6, abs=5; 3 instances at bases [5]; all_strict=True; worst realized 123/235
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u362_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (19152:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u362_uniform
-- u363 [3-edge cycle] 3->1->6->(closed) | cand_progress+z_entry+z_entry
--   roles: abs=3, abs=10, abs=4, abs=10, abs=9, abs=8; 1 instances at bases [8]; all_strict=True; worst realized 1625/2201
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u363_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (46656:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u363_uniform
-- u364 [3-edge cycle] 3->1->6->(closed) | cand_progress+z_entry+z_entry
--   roles: abs=4, abs=12, abs=5, abs=12, abs=11, abs=10; 1 instances at bases [10]; all_strict=True; worst realized 297/377
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u364_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (69840:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u364_uniform
-- u365 [3-edge cycle] 3->2->1->(closed) | cand_progress+z_irred+z_irred
--   roles: abs=7, abs=10, abs=1, abs=6, abs=10, abs=1; 1 instances at bases [7]; all_strict=True; worst realized 1501/1701
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u365_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (4200:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u365_uniform
-- u366 [3-edge cycle] 3->2->1->(closed) | cand_progress+z_irred+z_irred
--   roles: abs=10, abs=14, abs=1, abs=8, abs=14, abs=1; 1 instances at bases [10]; all_strict=True; worst realized 6993/7345
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u366_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (3168:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u366_uniform
-- u367 [3-edge cycle] 3->2->1->(closed) | cand_progress+z_irred+z_irred
--   roles: abs=11, abs=14, abs=1, abs=9, abs=14, abs=1; 1 instances at bases [10]; all_strict=True; worst realized 23051/24747
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u367_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (5088:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u367_uniform
-- u368 [3-edge cycle] 3->2->1->(closed) | cand_progress+z_irred+z_progress
--   roles: abs=10, abs=11, abs=1, abs=8, abs=11, abs=1; 1 instances at bases [8]; all_strict=True; worst realized 63/65
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u368_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (1602:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u368_uniform
-- u369 [3-edge cycle] 3->2->1->(closed) | cand_progress+z_irred+z_progress
--   roles: abs=9, abs=12, abs=2, abs=8, abs=12, abs=2; 1 instances at bases [10]; all_strict=True; worst realized 219/221
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u369_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (970:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u369_uniform
-- u370 [3-edge cycle] 3->2->1->(closed) | cand_progress+z_irred+z_progress
--   roles: abs=10, abs=12, abs=2, abs=9, abs=12, abs=2; 1 instances at bases [10]; all_strict=True; worst realized 1215/1241
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u370_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (2522:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u370_uniform
-- u371 [3-edge cycle] 3->2->1->(closed) | cand_progress+z_irred+z_progress
--   roles: abs=11, abs=12, abs=2, abs=10, abs=12, abs=2; 1 instances at bases [10]; all_strict=True; worst realized 445/459
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u371_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (4074:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u371_uniform
-- u372 [3-edge cycle] 3->5->1->(closed) | cand_entry+z_entry+z_entry
--   roles: abs=10, abs=10, abs=10, abs=2, abs=2, abs=8; 2 instances at bases [7]; all_strict=True; worst realized 5967/6241
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u372_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (4110:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u372_uniform
-- u373 [3-edge cycle] 3->5->6->(closed) | cand_entry+z_entry+z_entry
--   roles: free+2..+6, free+2..+6, tied+1, tied+1, tied+1, tied=base; 379 instances at bases [5, 6, 7, 8, 9, 10]; all_strict=True; worst realized 77697/79895
/-- pattern tau=(2,2): real half-line form, mono certificate (kind ALL, strict=True, deg D = 2). -/
theorem shape_u373_pat1_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (128:ℚ) * m ^ 2 + (640:ℚ) * m + (582:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have hshift : (128:ℚ) * (m - 5) ^ 2 + (1920:ℚ) * (m - 5) + (6982:ℚ) = (128:ℚ) * m ^ 2 + (640:ℚ) * m + (582:ℚ) := by ring
  linarith [ht, h2, hshift]
#print axioms shape_u373_pat1_uniform
/-- pattern tau=(3,3): real half-line form, mono certificate (kind ALL, strict=True, deg D = 2). -/
theorem shape_u373_pat2_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (128:ℚ) * m ^ 2 + (896:ℚ) * m + (902:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have hshift : (128:ℚ) * (m - 5) ^ 2 + (2176:ℚ) * (m - 5) + (8582:ℚ) = (128:ℚ) * m ^ 2 + (896:ℚ) * m + (902:ℚ) := by ring
  linarith [ht, h2, hshift]
#print axioms shape_u373_pat2_uniform
/-- pattern tau=(4,4): real half-line form, mono certificate (kind ALL, strict=True, deg D = 2). -/
theorem shape_u373_pat3_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (128:ℚ) * m ^ 2 + (1152:ℚ) * m + (1222:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have hshift : (128:ℚ) * (m - 5) ^ 2 + (2432:ℚ) * (m - 5) + (10182:ℚ) = (128:ℚ) * m ^ 2 + (1152:ℚ) * m + (1222:ℚ) := by ring
  linarith [ht, h2, hshift]
#print axioms shape_u373_pat3_uniform
/-- pattern tau=(5,5): real half-line form, mono certificate (kind ALL, strict=True, deg D = 2). -/
theorem shape_u373_pat4_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (128:ℚ) * m ^ 2 + (1408:ℚ) * m + (1542:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have hshift : (128:ℚ) * (m - 5) ^ 2 + (2688:ℚ) * (m - 5) + (11782:ℚ) = (128:ℚ) * m ^ 2 + (1408:ℚ) * m + (1542:ℚ) := by ring
  linarith [ht, h2, hshift]
#print axioms shape_u373_pat4_uniform
/-- pattern tau=(6,6): real half-line form, mono certificate (kind ALL, strict=True, deg D = 2). -/
theorem shape_u373_pat5_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (128:ℚ) * m ^ 2 + (1664:ℚ) * m + (1862:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have hshift : (128:ℚ) * (m - 5) ^ 2 + (2944:ℚ) * (m - 5) + (13382:ℚ) = (128:ℚ) * m ^ 2 + (1664:ℚ) * m + (1862:ℚ) := by ring
  linarith [ht, h2, hshift]
#print axioms shape_u373_pat5_uniform
-- u374 [3-edge cycle] 3->5->6->(closed) | cand_progress+z_entry+z_entry
--   roles: free+2..+4, free+2..+4, tied+1, tied+1, tied+1, tied=base; 123 instances at bases [5, 6, 7, 8, 9, 10]; all_strict=True; worst realized 801/841
/-- pattern tau=(2,2): real half-line form, mono certificate (kind ALL, strict=True, deg D = 2). -/
theorem shape_u374_pat1_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (256:ℚ) * m ^ 2 + (864:ℚ) * m + (680:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have hshift : (256:ℚ) * (m - 5) ^ 2 + (3424:ℚ) * (m - 5) + (11400:ℚ) = (256:ℚ) * m ^ 2 + (864:ℚ) * m + (680:ℚ) := by ring
  linarith [ht, h2, hshift]
#print axioms shape_u374_pat1_uniform
/-- pattern tau=(3,3): real half-line form, mono certificate (kind ALL, strict=True, deg D = 2). -/
theorem shape_u374_pat2_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (256:ℚ) * m ^ 2 + (1120:ℚ) * m + (1000:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have hshift : (256:ℚ) * (m - 5) ^ 2 + (3680:ℚ) * (m - 5) + (13000:ℚ) = (256:ℚ) * m ^ 2 + (1120:ℚ) * m + (1000:ℚ) := by ring
  linarith [ht, h2, hshift]
#print axioms shape_u374_pat2_uniform
/-- pattern tau=(4,4): real half-line form, mono certificate (kind ALL, strict=True, deg D = 2). -/
theorem shape_u374_pat3_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (256:ℚ) * m ^ 2 + (1376:ℚ) * m + (1320:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have hshift : (256:ℚ) * (m - 5) ^ 2 + (3936:ℚ) * (m - 5) + (14600:ℚ) = (256:ℚ) * m ^ 2 + (1376:ℚ) * m + (1320:ℚ) := by ring
  linarith [ht, h2, hshift]
#print axioms shape_u374_pat3_uniform
-- u375 [3-edge cycle] 3->6->2->(closed) | cand_progress+z_irred+z_progress
--   roles: abs=10, abs=10, abs=6, abs=9, abs=10, abs=7; 4 instances at bases [8]; all_strict=True; worst realized 1269/1387
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u375_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (28674:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u375_uniform
-- u376 [3-edge cycle] 4->1->3->(closed) | cand_progress+z_entry+z_entry
--   roles: abs=2, tied+2, abs=3, tied+1, tied=base, tied=base; 5 instances at bases [5, 6]; all_strict=True; worst realized 47481/70265
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 2). -/
theorem shape_u376_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (384:ℚ) * m ^ 2 + (1584:ℚ) * m - (544:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have hshift : (384:ℚ) * (m - 5) ^ 2 + (5424:ℚ) * (m - 5) + (16976:ℚ) = (384:ℚ) * m ^ 2 + (1584:ℚ) * m - (544:ℚ) := by ring
  linarith [ht, h2, hshift]
#print axioms shape_u376_uniform
-- u377 [3-edge cycle] 4->1->3->(closed) | cand_progress+z_entry+z_entry
--   roles: abs=3, tied+2, abs=4, tied+1, tied=base, tied=base; 7 instances at bases [6, 7, 8, 9]; all_strict=True; worst realized 147825/195889
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 2). -/
theorem shape_u377_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (384:ℚ) * m ^ 2 + (1968:ℚ) * m - (752:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have hshift : (384:ℚ) * (m - 5) ^ 2 + (5808:ℚ) * (m - 5) + (18688:ℚ) = (384:ℚ) * m ^ 2 + (1968:ℚ) * m - (752:ℚ) := by ring
  linarith [ht, h2, hshift]
#print axioms shape_u377_uniform
-- u378 [3-edge cycle] 4->1->3->(closed) | cand_progress+z_entry+z_entry
--   roles: abs=4, tied+2, abs=5, tied+1, tied=base, tied=base; 2 instances at bases [8, 9]; all_strict=True; worst realized 65043/82147
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 2). -/
theorem shape_u378_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (384:ℚ) * m ^ 2 + (2352:ℚ) * m - (960:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have hshift : (384:ℚ) * (m - 5) ^ 2 + (6192:ℚ) * (m - 5) + (20400:ℚ) = (384:ℚ) * m ^ 2 + (2352:ℚ) * m - (960:ℚ) := by ring
  linarith [ht, h2, hshift]
#print axioms shape_u378_uniform
-- u379 [3-edge cycle] 4->1->3->(closed) | cand_progress+z_entry+z_entry
--   roles: abs=1, abs=13, abs=2, abs=11, abs=10, abs=10; 1 instances at bases [10]; all_strict=True; worst realized 7209/13825
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u379_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (59544:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u379_uniform
-- u380 [3-edge cycle] 4->2->1->(closed) | cand_progress+weak+z_progress
--   roles: free-1..+0, tied+1, tied+1, tied=base; 4 instances at bases [5, 6]; all_strict=False; worst realized 1
/-- pattern tau=(-1): real half-line form, mono certificate (kind ALL, strict=True, deg D = 1). -/
theorem shape_u380_pat1_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (64:ℚ) * m + (72:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have hshift : (64:ℚ) * (m - 5) + (392:ℚ) = (64:ℚ) * m + (72:ℚ) := by ring
  linarith [ht, hshift]
#print axioms shape_u380_pat1_uniform
/-- pattern tau=(0): D ≡ 0 identically (weak kill: P ≡ 1 with the strict candidate edge); A and B coincide as polynomials. -/
theorem shape_u380_pat2_uniform : ∀ m : ℚ, 5 ≤ m → (64:ℚ) * m ^ 2 + (80:ℚ) * m + (9:ℚ) = (64:ℚ) * m ^ 2 + (80:ℚ) * m + (9:ℚ) := fun _ _ => rfl
#print axioms shape_u380_pat2_uniform
-- u381 [3-edge cycle] 4->2->1->(closed) | cand_progress+z_irred+z_progress
--   roles: abs=5, abs=9, abs=1, abs=4, abs=9, abs=1; 1 instances at bases [6]; all_strict=True; worst realized 287/297
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u381_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (730:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u381_uniform
-- u382 [3-edge cycle] 4->2->1->(closed) | cand_progress+z_irred+z_progress
--   roles: abs=6, abs=9, abs=1, abs=5, abs=9, abs=1; 1 instances at bases [6]; all_strict=True; worst realized 343/369
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u382_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (1898:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u382_uniform
-- u383 [3-edge cycle] 4->2->1->(closed) | cand_progress+z_irred+z_progress
--   roles: abs=7, abs=9, abs=1, abs=6, abs=9, abs=1; 1 instances at bases [6]; all_strict=True; worst realized 19/21
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u383_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (3066:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u383_uniform
-- u384 [3-edge cycle] 4->2->1->(closed) | cand_progress+z_irred+z_progress
--   roles: abs=9, abs=10, abs=2, abs=8, abs=10, abs=2; 1 instances at bases [8]; all_strict=True; worst realized 219/221
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u384_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (810:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u384_uniform
-- u385 [3-edge cycle] 4->2->1->(closed) | cand_progress+z_irred+z_progress
--   roles: abs=11, abs=14, abs=1, abs=9, abs=14, abs=1; 1 instances at bases [10]; all_strict=True; worst realized 623/657
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u385_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (3842:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u385_uniform
-- u386 [3-edge cycle] 4->2->1->(closed) | cand_progress+z_irred+z_progress
--   roles: abs=12, abs=14, abs=1, abs=10, abs=14, abs=1; 1 instances at bases [10]; all_strict=True; worst realized 679/729
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u386_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (5650:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u386_uniform
-- u387 [3-edge cycle] 4->2->3->(closed) | cand_progress+z_entry+z_entry
--   roles: abs=2, abs=7, abs=3, abs=6, abs=5, abs=5; 1 instances at bases [5]; all_strict=True; worst realized 34153/51129
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u387_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (16976:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u387_uniform
-- u388 [3-edge cycle] 4->3->2->(closed) | cand_progress+z_entry+z_progress
--   roles: abs=9, abs=10, abs=8, abs=4, abs=10, abs=5; 3 instances at bases [7]; all_strict=True; worst realized 803/861
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u388_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (14094:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u388_uniform
-- u389 [3-edge cycle] 4->3->2->(closed) | cand_progress+z_entry+z_progress
--   roles: abs=11, abs=12, abs=9, abs=6, abs=12, abs=8; 1 instances at bases [8]; all_strict=True; worst realized 4361/4615
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u389_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (24638:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u389_uniform
-- u390 [3-edge cycle] 4->5->2->(closed) | cand_progress+z_entry+z_progress
--   roles: abs=11, abs=11, abs=8, abs=2, abs=11, abs=3; 1 instances at bases [6]; all_strict=True; worst realized 1513/1575
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u390_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (5518:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u390_uniform
-- u391 [3-edge cycle] 4->5->6->(closed) | cand_entry+z_entry+z_entry
--   roles: free+4..+6, free+4..+5, abs=6, abs=6, abs=9, abs=8; 26 instances at bases [5]; all_strict=True; worst realized 232505/236927
/-- pattern tau=(4,4): real half-line form, mono certificate (kind ALL, strict=True, deg D = 1). -/
theorem shape_u391_pat1_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (1216:ℚ) * m - (1658:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have hshift : (1216:ℚ) * (m - 5) + (4422:ℚ) = (1216:ℚ) * m - (1658:ℚ) := by ring
  linarith [ht, hshift]
#print axioms shape_u391_pat1_uniform
/-- pattern tau=(5,4): real half-line form, mono certificate (kind ALL, strict=True, deg D = 1). -/
theorem shape_u391_pat2_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (1216:ℚ) * m + (25038:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have hshift : (1216:ℚ) * (m - 5) + (31118:ℚ) = (1216:ℚ) * m + (25038:ℚ) := by ring
  linarith [ht, hshift]
#print axioms shape_u391_pat2_uniform
/-- pattern tau=(5,5): real half-line form, mono certificate (kind ALL, strict=True, deg D = 1). -/
theorem shape_u391_pat3_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (1216:ℚ) * m - (442:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have hshift : (1216:ℚ) * (m - 5) + (5638:ℚ) = (1216:ℚ) * m - (442:ℚ) := by ring
  linarith [ht, hshift]
#print axioms shape_u391_pat3_uniform
/-- pattern tau=(6,5): real half-line form, mono certificate (kind ALL, strict=True, deg D = 1). -/
theorem shape_u391_pat4_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (1216:ℚ) * m + (26254:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have hshift : (1216:ℚ) * (m - 5) + (32334:ℚ) = (1216:ℚ) * m + (26254:ℚ) := by ring
  linarith [ht, hshift]
#print axioms shape_u391_pat4_uniform
-- u392 [3-edge cycle] 4->6->2->(closed) | cand_progress+z_irred+z_progress
--   roles: abs=9, abs=9, abs=6, abs=7, abs=9, abs=8; 1 instances at bases [6]; all_strict=True; worst realized 3431/3705
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u392_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (20002:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u392_uniform
-- u393 [3-edge cycle] 4->6->2->(closed) | cand_progress+z_irred+z_progress
--   roles: abs=13, abs=13, abs=9, abs=10, abs=13, abs=12; 1 instances at bases [9]; all_strict=True; worst realized 2485/2619
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u393_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (42210:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u393_uniform
-- u394 [3-edge cycle] 4->6->3->(closed) | cand_entry+z_entry+z_entry
--   roles: free+2..+6, free+2..+6, tied+1, tied=base, tied=base, tied=base; 429 instances at bases [5, 6, 7, 8, 9, 10]; all_strict=True; worst realized 212139/217645
/-- pattern tau=(2,2): real half-line form, mono certificate (kind ALL, strict=True, deg D = 2). -/
theorem shape_u394_pat1_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (128:ℚ) * m ^ 2 + (384:ℚ) * m - (122:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have hshift : (128:ℚ) * (m - 5) ^ 2 + (1664:ℚ) * (m - 5) + (4998:ℚ) = (128:ℚ) * m ^ 2 + (384:ℚ) * m - (122:ℚ) := by ring
  linarith [ht, h2, hshift]
#print axioms shape_u394_pat1_uniform
/-- pattern tau=(3,3): real half-line form, mono certificate (kind ALL, strict=True, deg D = 2). -/
theorem shape_u394_pat2_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (128:ℚ) * m ^ 2 + (640:ℚ) * m - (186:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have hshift : (128:ℚ) * (m - 5) ^ 2 + (1920:ℚ) * (m - 5) + (6214:ℚ) = (128:ℚ) * m ^ 2 + (640:ℚ) * m - (186:ℚ) := by ring
  linarith [ht, h2, hshift]
#print axioms shape_u394_pat2_uniform
/-- pattern tau=(4,4): real half-line form, mono certificate (kind ALL, strict=True, deg D = 2). -/
theorem shape_u394_pat3_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (128:ℚ) * m ^ 2 + (896:ℚ) * m - (250:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have hshift : (128:ℚ) * (m - 5) ^ 2 + (2176:ℚ) * (m - 5) + (7430:ℚ) = (128:ℚ) * m ^ 2 + (896:ℚ) * m - (250:ℚ) := by ring
  linarith [ht, h2, hshift]
#print axioms shape_u394_pat3_uniform
/-- pattern tau=(5,5): real half-line form, mono certificate (kind ALL, strict=True, deg D = 2). -/
theorem shape_u394_pat4_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (128:ℚ) * m ^ 2 + (1152:ℚ) * m - (314:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have hshift : (128:ℚ) * (m - 5) ^ 2 + (2432:ℚ) * (m - 5) + (8646:ℚ) = (128:ℚ) * m ^ 2 + (1152:ℚ) * m - (314:ℚ) := by ring
  linarith [ht, h2, hshift]
#print axioms shape_u394_pat4_uniform
/-- pattern tau=(6,6): real half-line form, mono certificate (kind ALL, strict=True, deg D = 2). -/
theorem shape_u394_pat5_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (128:ℚ) * m ^ 2 + (1408:ℚ) * m - (378:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have hshift : (128:ℚ) * (m - 5) ^ 2 + (2688:ℚ) * (m - 5) + (9862:ℚ) = (128:ℚ) * m ^ 2 + (1408:ℚ) * m - (378:ℚ) := by ring
  linarith [ht, h2, hshift]
#print axioms shape_u394_pat5_uniform
-- u395 [3-edge cycle] 4->6->3->(closed) | cand_progress+z_entry+z_entry
--   roles: free+2..+5, free+2..+5, tied+1, tied=base, tied=base, tied=base; 144 instances at bases [5, 6, 7, 8, 9, 10]; all_strict=True; worst realized 2187/2291
/-- pattern tau=(2,2): real half-line form, mono certificate (kind ALL, strict=True, deg D = 2). -/
theorem shape_u395_pat1_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (256:ℚ) * m ^ 2 + (480:ℚ) * m - (136:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have hshift : (256:ℚ) * (m - 5) ^ 2 + (3040:ℚ) * (m - 5) + (8664:ℚ) = (256:ℚ) * m ^ 2 + (480:ℚ) * m - (136:ℚ) := by ring
  linarith [ht, h2, hshift]
#print axioms shape_u395_pat1_uniform
/-- pattern tau=(3,3): real half-line form, mono certificate (kind ALL, strict=True, deg D = 2). -/
theorem shape_u395_pat2_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (256:ℚ) * m ^ 2 + (736:ℚ) * m - (200:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have hshift : (256:ℚ) * (m - 5) ^ 2 + (3296:ℚ) * (m - 5) + (9880:ℚ) = (256:ℚ) * m ^ 2 + (736:ℚ) * m - (200:ℚ) := by ring
  linarith [ht, h2, hshift]
#print axioms shape_u395_pat2_uniform
/-- pattern tau=(4,4): real half-line form, mono certificate (kind ALL, strict=True, deg D = 2). -/
theorem shape_u395_pat3_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (256:ℚ) * m ^ 2 + (992:ℚ) * m - (264:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have hshift : (256:ℚ) * (m - 5) ^ 2 + (3552:ℚ) * (m - 5) + (11096:ℚ) = (256:ℚ) * m ^ 2 + (992:ℚ) * m - (264:ℚ) := by ring
  linarith [ht, h2, hshift]
#print axioms shape_u395_pat3_uniform
/-- pattern tau=(5,5): real half-line form, mono certificate (kind ALL, strict=True, deg D = 2). -/
theorem shape_u395_pat4_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (256:ℚ) * m ^ 2 + (1248:ℚ) * m - (328:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have hshift : (256:ℚ) * (m - 5) ^ 2 + (3808:ℚ) * (m - 5) + (12312:ℚ) = (256:ℚ) * m ^ 2 + (1248:ℚ) * m - (328:ℚ) := by ring
  linarith [ht, h2, hshift]
#print axioms shape_u395_pat4_uniform
-- u396 [3-edge cycle] 5->1->2->(closed) | cand_progress+z_entry+z_entry
--   roles: abs=2, tied+2, abs=3, tied=base, tied=base, tied+1; 2 instances at bases [5, 6]; all_strict=True; worst realized 47481/70265
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 2). -/
theorem shape_u396_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (384:ℚ) * m ^ 2 + (1584:ℚ) * m - (544:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have hshift : (384:ℚ) * (m - 5) ^ 2 + (5424:ℚ) * (m - 5) + (16976:ℚ) = (384:ℚ) * m ^ 2 + (1584:ℚ) * m - (544:ℚ) := by ring
  linarith [ht, h2, hshift]
#print axioms shape_u396_uniform
-- u397 [3-edge cycle] 5->1->2->(closed) | cand_progress+z_entry+z_entry
--   roles: abs=3, tied+2, abs=4, tied-1, tied-1, tied+1; 5 instances at bases [5, 6, 7, 8, 9]; all_strict=True; worst realized 14625/19313
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 2). -/
theorem shape_u397_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (384:ℚ) * m ^ 2 + (1584:ℚ) * m - (3168:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have hshift : (384:ℚ) * (m - 5) ^ 2 + (5424:ℚ) * (m - 5) + (14352:ℚ) = (384:ℚ) * m ^ 2 + (1584:ℚ) * m - (3168:ℚ) := by ring
  linarith [ht, h2, hshift]
#print axioms shape_u397_uniform
-- u398 [3-edge cycle] 5->1->2->(closed) | cand_progress+z_entry+z_entry
--   roles: abs=3, tied+2, abs=4, tied=base, tied=base, tied+1; 3 instances at bases [6, 7, 8]; all_strict=True; worst realized 118625/158193
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 2). -/
theorem shape_u398_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (384:ℚ) * m ^ 2 + (1968:ℚ) * m - (752:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have hshift : (384:ℚ) * (m - 5) ^ 2 + (5808:ℚ) * (m - 5) + (18688:ℚ) = (384:ℚ) * m ^ 2 + (1968:ℚ) * m - (752:ℚ) := by ring
  linarith [ht, h2, hshift]
#print axioms shape_u398_uniform
-- u399 [3-edge cycle] 5->1->2->(closed) | cand_progress+z_entry+z_entry
--   roles: tied-4, tied+2, tied-3, tied-2, tied-2, tied+1; 3 instances at bases [7, 8, 9]; all_strict=True; worst realized 189297/230065
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 2). -/
theorem shape_u399_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (768:ℚ) * m ^ 2 - (2720:ℚ) * m + (3040:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have hshift : (768:ℚ) * (m - 5) ^ 2 + (4960:ℚ) * (m - 5) + (8640:ℚ) = (768:ℚ) * m ^ 2 - (2720:ℚ) * m + (3040:ℚ) := by ring
  linarith [ht, h2, hshift]
#print axioms shape_u399_uniform
-- u400 [3-edge cycle] 5->1->2->(closed) | cand_progress+z_entry+z_entry
--   roles: tied-3, tied+2, tied-2, tied-2, tied-2, tied+1; 2 instances at bases [7, 8]; all_strict=True; worst realized 146657/178929
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 2). -/
theorem shape_u400_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (768:ℚ) * m ^ 2 - (2336:ℚ) * m + (1808:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have hshift : (768:ℚ) * (m - 5) ^ 2 + (5344:ℚ) * (m - 5) + (9328:ℚ) = (768:ℚ) * m ^ 2 - (2336:ℚ) * m + (1808:ℚ) := by ring
  linarith [ht, h2, hshift]
#print axioms shape_u400_uniform
-- u401 [3-edge cycle] 5->1->2->(closed) | cand_progress+z_entry+z_entry
--   roles: abs=4, tied+2, abs=5, tied-1, tied-1, tied+1; 4 instances at bases [7, 8, 9, 10]; all_strict=True; worst realized 71467/89531
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 2). -/
theorem shape_u401_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (384:ℚ) * m ^ 2 + (1968:ℚ) * m - (3888:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have hshift : (384:ℚ) * (m - 5) ^ 2 + (5808:ℚ) * (m - 5) + (15552:ℚ) = (384:ℚ) * m ^ 2 + (1968:ℚ) * m - (3888:ℚ) := by ring
  linarith [ht, h2, hshift]
#print axioms shape_u401_uniform
-- u402 [3-edge cycle] 5->1->2->(closed) | cand_progress+z_entry+z_entry
--   roles: abs=4, tied+2, abs=5, tied=base, tied=base, tied+1; 3 instances at bases [8, 9, 10]; all_strict=True; worst realized 79299/99619
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 2). -/
theorem shape_u402_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (384:ℚ) * m ^ 2 + (2352:ℚ) * m - (960:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have hshift : (384:ℚ) * (m - 5) ^ 2 + (6192:ℚ) * (m - 5) + (20400:ℚ) = (384:ℚ) * m ^ 2 + (2352:ℚ) * m - (960:ℚ) := by ring
  linarith [ht, h2, hshift]
#print axioms shape_u402_uniform
-- u403 [3-edge cycle] 5->1->2->(closed) | cand_progress+z_entry+z_entry
--   roles: abs=1, abs=12, abs=2, abs=7, abs=7, abs=10; 1 instances at bases [9]; all_strict=True; worst realized 13851/26675
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u403_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (38472:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u403_uniform
-- u404 [3-edge cycle] 5->1->2->(closed) | cand_progress+z_entry+z_entry
--   roles: abs=4, abs=11, abs=5, abs=7, abs=7, abs=10; 1 instances at bases [9]; all_strict=True; worst realized 4617/5785
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u404_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (38544:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u404_uniform
-- u405 [3-edge cycle] 5->1->2->(closed) | cand_progress+z_entry+z_entry
--   roles: abs=5, tied+2, abs=6, tied-1, tied-1, tied+1; 2 instances at bases [9, 10]; all_strict=True; worst realized 266377/323689
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 2). -/
theorem shape_u405_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (384:ℚ) * m ^ 2 + (2352:ℚ) * m - (4608:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have hshift : (384:ℚ) * (m - 5) ^ 2 + (6192:ℚ) * (m - 5) + (16752:ℚ) = (384:ℚ) * m ^ 2 + (2352:ℚ) * m - (4608:ℚ) := by ring
  linarith [ht, h2, hshift]
#print axioms shape_u405_uniform
-- u406 [3-edge cycle] 5->1->2->(closed) | cand_progress+z_entry+z_entry
--   roles: abs=1, abs=13, abs=2, abs=9, abs=9, abs=11; 1 instances at bases [10]; all_strict=True; worst realized 6497/12425
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u406_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (53352:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u406_uniform
-- u407 [3-edge cycle] 5->1->2->(closed) | cand_progress+z_entry+z_entry
--   roles: abs=1, abs=13, abs=2, abs=10, abs=10, abs=11; 1 instances at bases [10]; all_strict=True; worst realized 7209/13825
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u407_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (59544:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u407_uniform
-- u408 [3-edge cycle] 5->1->2->(closed) | cand_progress+z_entry+z_entry
--   roles: abs=5, abs=12, abs=6, abs=10, abs=10, abs=11; 1 instances at bases [10]; all_strict=True; worst realized 295569/360161
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u408_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (64592:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u408_uniform
-- u409 [3-edge cycle] 5->1->4->(closed) | cand_progress+z_entry+z_entry
--   roles: abs=2, tied+2, abs=3, tied+1, tied=base, tied=base; 4 instances at bases [5, 6]; all_strict=True; worst realized 47481/70265
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 2). -/
theorem shape_u409_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (384:ℚ) * m ^ 2 + (1584:ℚ) * m - (544:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have hshift : (384:ℚ) * (m - 5) ^ 2 + (5424:ℚ) * (m - 5) + (16976:ℚ) = (384:ℚ) * m ^ 2 + (1584:ℚ) * m - (544:ℚ) := by ring
  linarith [ht, h2, hshift]
#print axioms shape_u409_uniform
-- u410 [3-edge cycle] 5->1->4->(closed) | cand_progress+z_entry+z_entry
--   roles: abs=3, tied+2, abs=4, tied+1, tied=base, tied=base; 10 instances at bases [6, 7, 8, 9]; all_strict=True; worst realized 147825/195889
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 2). -/
theorem shape_u410_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (384:ℚ) * m ^ 2 + (1968:ℚ) * m - (752:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have hshift : (384:ℚ) * (m - 5) ^ 2 + (5808:ℚ) * (m - 5) + (18688:ℚ) = (384:ℚ) * m ^ 2 + (1968:ℚ) * m - (752:ℚ) := by ring
  linarith [ht, h2, hshift]
#print axioms shape_u410_uniform
-- u411 [3-edge cycle] 5->1->4->(closed) | cand_progress+z_entry+z_entry
--   roles: abs=4, tied+2, abs=5, tied+1, tied=base, tied=base; 6 instances at bases [8, 9, 10]; all_strict=True; worst realized 79299/99619
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 2). -/
theorem shape_u411_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (384:ℚ) * m ^ 2 + (2352:ℚ) * m - (960:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have hshift : (384:ℚ) * (m - 5) ^ 2 + (6192:ℚ) * (m - 5) + (20400:ℚ) = (384:ℚ) * m ^ 2 + (2352:ℚ) * m - (960:ℚ) := by ring
  linarith [ht, h2, hshift]
#print axioms shape_u411_uniform
-- u412 [3-edge cycle] 5->1->4->(closed) | cand_progress+z_entry+z_entry
--   roles: abs=1, abs=13, abs=2, abs=11, abs=10, abs=10; 2 instances at bases [10]; all_strict=True; worst realized 7209/13825
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u412_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (59544:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u412_uniform
-- u413 [3-edge cycle] 5->1->4->(closed) | cand_progress+z_entry+z_entry
--   roles: abs=5, abs=12, abs=6, abs=11, abs=10, abs=10; 1 instances at bases [10]; all_strict=True; worst realized 295569/360161
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u413_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (64592:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u413_uniform
-- u414 [3-edge cycle] 5->2->1->(closed) | cand_progress+z_entry+z_entry
--   roles: abs=3, abs=7, abs=4, abs=3, abs=3, abs=6; 1 instances at bases [5]; all_strict=True; worst realized 30625/40641
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u414_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (10016:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u414_uniform
-- u415 [3-edge cycle] 5->2->1->(closed) | cand_progress+z_entry+z_entry
--   roles: abs=4, abs=7, abs=5, abs=3, abs=3, abs=6; 1 instances at bases [5]; all_strict=True; worst realized 13475/17043
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u415_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (10704:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u415_uniform
-- u416 [3-edge cycle] 5->2->1->(closed) | cand_progress+z_entry+z_entry
--   roles: abs=5, abs=7, abs=6, abs=3, abs=3, abs=6; 1 instances at bases [5]; all_strict=True; worst realized 50225/61617
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u416_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (11392:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u416_uniform
-- u417 [3-edge cycle] 5->2->1->(closed) | cand_progress+z_irred+z_progress
--   roles: abs=5, abs=8, abs=1, abs=4, abs=8, abs=1; 1 instances at bases [5]; all_strict=True; worst realized 287/297
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u417_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (650:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u417_uniform
-- u418 [3-edge cycle] 5->2->1->(closed) | cand_progress+z_irred+z_progress
--   roles: abs=6, abs=8, abs=1, abs=5, abs=8, abs=1; 1 instances at bases [5]; all_strict=True; worst realized 343/369
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u418_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (1690:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u418_uniform
-- u419 [3-edge cycle] 5->2->1->(closed) | cand_progress+z_irred+z_progress
--   roles: abs=7, abs=12, abs=1, abs=6, abs=12, abs=1; 1 instances at bases [8]; all_strict=True; worst realized 19/21
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u419_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (4074:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u419_uniform
-- u420 [3-edge cycle] 5->2->1->(closed) | cand_progress+z_irred+z_progress
--   roles: abs=11, abs=13, abs=1, abs=9, abs=13, abs=1; 1 instances at bases [9]; all_strict=True; worst realized 623/657
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u420_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (3570:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u420_uniform
-- u421 [3-edge cycle] 5->2->4->(closed) | cand_progress+z_entry+z_entry
--   roles: abs=7, abs=10, abs=8, abs=9, abs=6, abs=6; 1 instances at bases [6]; all_strict=True; worst realized 9709/11421
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u421_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (35952:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u421_uniform
-- u422 [3-edge cycle] 5->2->4->(closed) | cand_progress+z_progress+z_entry
--   roles: abs=6, abs=12, abs=9, abs=5, abs=8, abs=8; 1 instances at bases [8]; all_strict=True; worst realized 33215/35793
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u422_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (18046:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u422_uniform
-- u423 [3-edge cycle] 5->3->1->(closed) | cand_progress+z_irred+z_irred
--   roles: abs=9, abs=10, abs=2, abs=8, abs=10, abs=2; 1 instances at bases [7]; all_strict=True; worst realized 5767/5967
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u423_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (3000:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u423_uniform
-- u424 [3-edge cycle] 5->3->1->(closed) | cand_progress+z_irred+z_progress
--   roles: abs=11, abs=12, abs=2, abs=10, abs=12, abs=2; 2 instances at bases [9]; all_strict=True; worst realized 445/459
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u424_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (4074:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u424_uniform
-- u425 [3-edge cycle] 5->3->2->(closed) | cand_entry+z_entry+z_entry
--   roles: free+3..+4, abs=7, abs=7, abs=4, abs=4, abs=7; 2 instances at bases [5]; all_strict=True; worst realized 1083/1085
/-- pattern tau=(3): real half-line form, mono certificate (kind ALL, strict=True, deg D = 1). -/
theorem shape_u425_pat1_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (13640:ℚ) * m - (68002:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have hshift : (13640:ℚ) * (m - 5) + (198:ℚ) = (13640:ℚ) * m - (68002:ℚ) := by ring
  linarith [ht, hshift]
#print axioms shape_u425_pat1_uniform
/-- pattern tau=(4): real half-line form, mono certificate (kind ALL, strict=True, deg D = 1). -/
theorem shape_u425_pat2_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (13640:ℚ) * m - (54362:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have hshift : (13640:ℚ) * (m - 5) + (13838:ℚ) = (13640:ℚ) * m - (54362:ℚ) := by ring
  linarith [ht, hshift]
#print axioms shape_u425_pat2_uniform
-- u426 [3-edge cycle] 5->3->2->(closed) | cand_progress+z_entry+z_entry
--   roles: abs=11, abs=13, abs=12, abs=8, abs=6, abs=9; 2 instances at bases [8]; all_strict=True; worst realized 84461/93765
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u426_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (46520:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u426_uniform
-- u427 [3-edge cycle] 5->3->4->(closed) | cand_progress+z_entry+z_entry
--   roles: free+1..+4, free+2..+6, tied=base, tied=base, tied=base, tied=base; 342 instances at bases [5, 6, 7, 8, 9, 10]; all_strict=True; worst realized 122713/123201
/-- pattern tau=(1,2): real half-line form, mono certificate (kind ALL, strict=True, deg D = 2). -/
theorem shape_u427_pat1_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (256:ℚ) * m ^ 2 - (416:ℚ) * m + (8:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have hshift : (256:ℚ) * (m - 5) ^ 2 + (2144:ℚ) * (m - 5) + (4328:ℚ) = (256:ℚ) * m ^ 2 - (416:ℚ) * m + (8:ℚ) := by ring
  linarith [ht, h2, hshift]
#print axioms shape_u427_pat1_uniform
/-- pattern tau=(1,3): real half-line form, mono certificate (kind ALL, strict=True, deg D = 2). -/
theorem shape_u427_pat2_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (768:ℚ) * m ^ 2 - (544:ℚ) * m + (16:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have hshift : (768:ℚ) * (m - 5) ^ 2 + (7136:ℚ) * (m - 5) + (16496:ℚ) = (768:ℚ) * m ^ 2 - (544:ℚ) * m + (16:ℚ) := by ring
  linarith [ht, h2, hshift]
#print axioms shape_u427_pat2_uniform
/-- pattern tau=(2,3): real half-line form, mono certificate (kind ALL, strict=True, deg D = 2). -/
theorem shape_u427_pat3_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (256:ℚ) * m ^ 2 - (672:ℚ) * m + (8:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have hshift : (256:ℚ) * (m - 5) ^ 2 + (1888:ℚ) * (m - 5) + (3048:ℚ) = (256:ℚ) * m ^ 2 - (672:ℚ) * m + (8:ℚ) := by ring
  linarith [ht, h2, hshift]
#print axioms shape_u427_pat3_uniform
/-- pattern tau=(2,4): real half-line form, mono certificate (kind ALL, strict=True, deg D = 2). -/
theorem shape_u427_pat4_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (768:ℚ) * m ^ 2 - (800:ℚ) * m + (16:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have hshift : (768:ℚ) * (m - 5) ^ 2 + (6880:ℚ) * (m - 5) + (15216:ℚ) = (768:ℚ) * m ^ 2 - (800:ℚ) * m + (16:ℚ) := by ring
  linarith [ht, h2, hshift]
#print axioms shape_u427_pat4_uniform
/-- pattern tau=(3,4): real half-line form, mono certificate (kind ALL, strict=True, deg D = 2). -/
theorem shape_u427_pat5_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (256:ℚ) * m ^ 2 - (928:ℚ) * m + (8:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have hshift : (256:ℚ) * (m - 5) ^ 2 + (1632:ℚ) * (m - 5) + (1768:ℚ) = (256:ℚ) * m ^ 2 - (928:ℚ) * m + (8:ℚ) := by ring
  linarith [ht, h2, hshift]
#print axioms shape_u427_pat5_uniform
/-- pattern tau=(3,5): real half-line form, mono certificate (kind ALL, strict=True, deg D = 2). -/
theorem shape_u427_pat6_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (768:ℚ) * m ^ 2 - (1056:ℚ) * m + (16:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have hshift : (768:ℚ) * (m - 5) ^ 2 + (6624:ℚ) * (m - 5) + (13936:ℚ) = (768:ℚ) * m ^ 2 - (1056:ℚ) * m + (16:ℚ) := by ring
  linarith [ht, h2, hshift]
#print axioms shape_u427_pat6_uniform
/-- pattern tau=(4,5): real half-line form, mono certificate (kind ALL, strict=True, deg D = 2). -/
theorem shape_u427_pat7_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (256:ℚ) * m ^ 2 - (1184:ℚ) * m + (8:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have hshift : (256:ℚ) * (m - 5) ^ 2 + (1376:ℚ) * (m - 5) + (488:ℚ) = (256:ℚ) * m ^ 2 - (1184:ℚ) * m + (8:ℚ) := by ring
  linarith [ht, h2, hshift]
#print axioms shape_u427_pat7_uniform
/-- pattern tau=(4,6): real half-line form, mono certificate (kind ALL, strict=True, deg D = 2). -/
theorem shape_u427_pat8_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (768:ℚ) * m ^ 2 - (1312:ℚ) * m + (16:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have hshift : (768:ℚ) * (m - 5) ^ 2 + (6368:ℚ) * (m - 5) + (12656:ℚ) = (768:ℚ) * m ^ 2 - (1312:ℚ) * m + (16:ℚ) := by ring
  linarith [ht, h2, hshift]
#print axioms shape_u427_pat8_uniform
-- u428 [3-edge cycle] 5->4->2->(closed) | cand_entry+z_entry+z_entry
--   roles: abs=11, abs=10, abs=10, abs=6, abs=5, abs=8; 7 instances at bases [7]; all_strict=True; worst realized 2205/2291
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u428_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (10062:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u428_uniform
-- u429 [3-edge cycle] 5->6->2->(closed) | cand_progress+z_irred+z_irred
--   roles: abs=10, abs=10, abs=3, abs=7, abs=10, abs=4; 3 instances at bases [6]; all_strict=True; worst realized 1817/1881
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u429_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (5184:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u429_uniform
-- u430 [3-edge cycle] 5->6->4->(closed) | cand_progress+z_entry+z_entry
--   roles: abs=10, abs=10, abs=9, abs=8, abs=5, abs=5; 2 instances at bases [5]; all_strict=True; worst realized 205/213
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u430_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (8424:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u430_uniform
-- u431 [3-edge cycle] 6->1->2->(closed) | cand_progress+z_entry+z_irred
--   roles: abs=1, abs=10, abs=2, abs=7, abs=10, abs=8; 1 instances at bases [7]; all_strict=True; worst realized 1501/2925
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u431_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (38448:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u431_uniform
-- u432 [3-edge cycle] 6->1->2->(closed) | cand_progress+z_entry+z_progress
--   roles: abs=1, tied+3, abs=2, abs=6, tied+3, abs=7; 2 instances at bases [7, 8]; all_strict=True; worst realized 49/95
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 1). -/
theorem shape_u432_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (3312:ℚ) * m + (10350:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have hshift : (3312:ℚ) * (m - 5) + (26910:ℚ) = (3312:ℚ) * m + (10350:ℚ) := by ring
  linarith [ht, hshift]
#print axioms shape_u432_uniform
-- u433 [3-edge cycle] 6->2->1->(closed) | cand_progress+z_irred+z_progress
--   roles: abs=5, abs=11, abs=1, abs=4, abs=11, abs=1; 1 instances at bases [7]; all_strict=True; worst realized 287/297
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u433_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (890:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u433_uniform
-- u434 [3-edge cycle] 6->2->1->(closed) | cand_progress+z_irred+z_progress
--   roles: abs=6, abs=11, abs=1, abs=5, abs=11, abs=1; 1 instances at bases [7]; all_strict=True; worst realized 343/369
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u434_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (2314:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u434_uniform
-- u435 [3-edge cycle] 6->2->1->(closed) | cand_progress+z_irred+z_progress
--   roles: abs=9, abs=13, abs=2, abs=8, abs=13, abs=2; 1 instances at bases [10]; all_strict=True; worst realized 219/221
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u435_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (1050:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u435_uniform
-- u436 [3-edge cycle] 6->2->1->(closed) | cand_progress+z_irred+z_progress
--   roles: abs=10, abs=13, abs=2, abs=9, abs=13, abs=2; 1 instances at bases [10]; all_strict=True; worst realized 1215/1241
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u436_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (2730:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u436_uniform
-- u437 [3-edge cycle] 6->2->1->(closed) | cand_progress+z_irred+z_progress
--   roles: abs=11, abs=13, abs=2, abs=10, abs=13, abs=2; 1 instances at bases [10]; all_strict=True; worst realized 445/459
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u437_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (4410:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u437_uniform
-- u438 [3-edge cycle] 6->2->5->(closed) | cand_irred+z_entry+z_entry
--   roles: abs=5, abs=8, abs=4, abs=6, abs=6, abs=6; 1 instances at bases [5]; all_strict=True; worst realized 7203/7285
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u438_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (1066:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u438_uniform
-- u439 [3-edge cycle] 6->2->5->(closed) | cand_progress+z_entry+z_entry
--   roles: abs=5, abs=13, abs=6, abs=12, abs=8, abs=8; 1 instances at bases [7]; all_strict=True; worst realized 51701/62181
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u439_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (52400:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u439_uniform
-- u440 [3-edge cycle] 6->2->5->(closed) | cand_progress+z_entry+z_entry
--   roles: abs=11, abs=13, abs=10, abs=11, abs=11, abs=11; 1 instances at bases [10]; all_strict=True; worst realized 704969/721665
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u440_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (16696:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u440_uniform
-- u441 [3-edge cycle] 6->3->2->(closed) | cand_progress+z_entry+z_progress
--   roles: abs=10, abs=12, abs=8, abs=5, abs=12, abs=7; 1 instances at bases [7]; all_strict=True; worst realized 123/133
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u441_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (26190:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u441_uniform
-- u442 [3-edge cycle] 6->3->2->(closed) | cand_progress+z_entry+z_progress
--   roles: abs=12, abs=13, abs=11, abs=8, abs=13, abs=9; 1 instances at bases [10]; all_strict=True; worst realized 6305/6351
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u442_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (4830:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u442_uniform
-- u443 [3-edge cycle] 6->3->4->(closed) | cand_progress+z_entry+z_irred
--   roles: abs=10, abs=12, abs=7, abs=7, abs=12, abs=11; 1 instances at bases [7]; all_strict=True; worst realized 87723/94963
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u443_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (36200:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u443_uniform
-- u444 [3-edge cycle] 6->4->1->(closed) | cand_progress+z_entry+z_entry
--   roles: abs=14, abs=16, abs=15, abs=1, abs=1, abs=12; 1 instances at bases [10]; all_strict=True; worst realized 32883/35819
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u444_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (8808:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u444_uniform
-- u445 [3-edge cycle] 6->4->5->(closed) | cand_progress+z_entry+z_entry
--   roles: free+1..+5, free+2..+6, tied=base, tied=base, tied+1, tied+1; 296 instances at bases [5, 6, 7, 8, 9, 10]; all_strict=True; worst realized 248577/250745
/-- pattern tau=(1,2): real half-line form, mono certificate (kind ALL, strict=True, deg D = 2). -/
theorem shape_u445_pat1_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (256:ℚ) * m ^ 2 - (32:ℚ) * m - (200:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have hshift : (256:ℚ) * (m - 5) ^ 2 + (2528:ℚ) * (m - 5) + (6040:ℚ) = (256:ℚ) * m ^ 2 - (32:ℚ) * m - (200:ℚ) := by ring
  linarith [ht, h2, hshift]
#print axioms shape_u445_pat1_uniform
/-- pattern tau=(1,3): real half-line form, mono certificate (kind ALL, strict=True, deg D = 2). -/
theorem shape_u445_pat2_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (768:ℚ) * m ^ 2 + (352:ℚ) * m - (256:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have hshift : (768:ℚ) * (m - 5) ^ 2 + (8032:ℚ) * (m - 5) + (20704:ℚ) = (768:ℚ) * m ^ 2 + (352:ℚ) * m - (256:ℚ) := by ring
  linarith [ht, h2, hshift]
#print axioms shape_u445_pat2_uniform
/-- pattern tau=(2,3): real half-line form, mono certificate (kind ALL, strict=True, deg D = 2). -/
theorem shape_u445_pat3_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (256:ℚ) * m ^ 2 - (288:ℚ) * m - (328:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have hshift : (256:ℚ) * (m - 5) ^ 2 + (2272:ℚ) * (m - 5) + (4632:ℚ) = (256:ℚ) * m ^ 2 - (288:ℚ) * m - (328:ℚ) := by ring
  linarith [ht, h2, hshift]
#print axioms shape_u445_pat3_uniform
/-- pattern tau=(2,4): real half-line form, mono certificate (kind ALL, strict=True, deg D = 2). -/
theorem shape_u445_pat4_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (768:ℚ) * m ^ 2 + (96:ℚ) * m - (384:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have hshift : (768:ℚ) * (m - 5) ^ 2 + (7776:ℚ) * (m - 5) + (19296:ℚ) = (768:ℚ) * m ^ 2 + (96:ℚ) * m - (384:ℚ) := by ring
  linarith [ht, h2, hshift]
#print axioms shape_u445_pat4_uniform
/-- pattern tau=(3,4): real half-line form, mono certificate (kind ALL, strict=True, deg D = 2). -/
theorem shape_u445_pat5_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (256:ℚ) * m ^ 2 - (544:ℚ) * m - (456:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have hshift : (256:ℚ) * (m - 5) ^ 2 + (2016:ℚ) * (m - 5) + (3224:ℚ) = (256:ℚ) * m ^ 2 - (544:ℚ) * m - (456:ℚ) := by ring
  linarith [ht, h2, hshift]
#print axioms shape_u445_pat5_uniform
/-- pattern tau=(3,5): real half-line form, mono certificate (kind ALL, strict=True, deg D = 2). -/
theorem shape_u445_pat6_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (768:ℚ) * m ^ 2 - (160:ℚ) * m - (512:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have hshift : (768:ℚ) * (m - 5) ^ 2 + (7520:ℚ) * (m - 5) + (17888:ℚ) = (768:ℚ) * m ^ 2 - (160:ℚ) * m - (512:ℚ) := by ring
  linarith [ht, h2, hshift]
#print axioms shape_u445_pat6_uniform
/-- pattern tau=(4,5): real half-line form, mono certificate (kind ALL, strict=True, deg D = 2). -/
theorem shape_u445_pat7_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (256:ℚ) * m ^ 2 - (800:ℚ) * m - (584:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have hshift : (256:ℚ) * (m - 5) ^ 2 + (1760:ℚ) * (m - 5) + (1816:ℚ) = (256:ℚ) * m ^ 2 - (800:ℚ) * m - (584:ℚ) := by ring
  linarith [ht, h2, hshift]
#print axioms shape_u445_pat7_uniform
/-- pattern tau=(4,6): real half-line form, mono certificate (kind ALL, strict=True, deg D = 2). -/
theorem shape_u445_pat8_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (768:ℚ) * m ^ 2 - (416:ℚ) * m - (640:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have hshift : (768:ℚ) * (m - 5) ^ 2 + (7264:ℚ) * (m - 5) + (16480:ℚ) = (768:ℚ) * m ^ 2 - (416:ℚ) * m - (640:ℚ) := by ring
  linarith [ht, h2, hshift]
#print axioms shape_u445_pat8_uniform
/-- pattern tau=(5,6): real half-line form, mono certificate (kind ALL, strict=True, deg D = 2). -/
theorem shape_u445_pat9_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (256:ℚ) * m ^ 2 - (1056:ℚ) * m - (712:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have hshift : (256:ℚ) * (m - 5) ^ 2 + (1504:ℚ) * (m - 5) + (408:ℚ) = (256:ℚ) * m ^ 2 - (1056:ℚ) * m - (712:ℚ) := by ring
  linarith [ht, h2, hshift]
#print axioms shape_u445_pat9_uniform
