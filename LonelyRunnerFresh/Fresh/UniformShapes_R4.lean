import Mathlib

/-!
# UniformShapes_R4: generated uniformity lemmas for the R4-edge killing shapes

GENERATED FILE (uniform_gen_v1.py, 277 theorems; regenerate, do not edit).  The half-line
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

-- u446 [4-edge cycle] 1->2->5->6->(closed) | cand_entry+z_entry+z_entry+z_entry
--   roles: abs=2, abs=4, abs=3, abs=7, abs=7, abs=7, abs=10, abs=1; 1 instances at bases [6]; all_strict=True; worst realized 29241/45425
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u446_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (534072:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u446_uniform
-- u447 [4-edge cycle] 1->2->5->6->(closed) | cand_entry+z_entry+z_entry+z_entry
--   roles: abs=2, abs=8, abs=6, abs=7, abs=7, abs=7, abs=10, abs=1; 1 instances at bases [6]; all_strict=True; worst realized 126711/204215
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u447_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (1162560:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u447_uniform
-- u448 [4-edge cycle] 1->2->5->6->(closed) | cand_irred+z_entry+z_entry+z_entry
--   roles: abs=7, abs=2, abs=6, abs=8, abs=8, abs=8, abs=10, abs=2; 1 instances at bases [7]; all_strict=True; worst realized 232375/233919
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u448_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (26248:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u448_uniform
-- u449 [4-edge cycle] 1->2->5->6->(closed) | cand_irred+z_entry+z_entry+z_entry
--   roles: abs=7, abs=3, abs=6, abs=8, abs=8, abs=8, abs=10, abs=3; 1 instances at bases [7]; all_strict=True; worst realized 232375/233919
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u449_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (38600:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u449_uniform
-- u450 [4-edge cycle] 1->2->5->6->(closed) | cand_irred+z_entry+z_entry+z_entry
--   roles: abs=9, abs=4, abs=8, abs=11, abs=11, abs=11, abs=13, abs=4; 1 instances at bases [10]; all_strict=True; worst realized 562391/564543
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u450_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (71016:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u450_uniform
-- u451 [4-edge cycle] 1->2->6->3->(closed) | cand_entry+z_irred+z_entry+z_irred
--   roles: abs=2, abs=4, tied+2, abs=3, tied+1, tied=base, abs=1, tied+1; 2 instances at bases [5, 6]; all_strict=True; worst realized 7203/11875
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 2). -/
theorem shape_u451_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (9216:ℚ) * m ^ 2 + (18432:ℚ) * m + (20160:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have hshift : (9216:ℚ) * (m - 5) ^ 2 + (110592:ℚ) * (m - 5) + (342720:ℚ) = (9216:ℚ) * m ^ 2 + (18432:ℚ) * m + (20160:ℚ) := by ring
  linarith [ht, h2, hshift]
#print axioms shape_u451_uniform
-- u452 [4-edge cycle] 1->3->2->5->(closed) | cand_entry+z_entry+z_entry+z_entry
--   roles: abs=3, abs=7, abs=7, abs=4, abs=4, abs=7, abs=7, abs=2; 1 instances at bases [5]; all_strict=True; worst realized 165699/196075
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u452_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (334136:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u452_uniform
-- u453 [4-edge cycle] 1->3->4->5->(closed) | cand_entry+z_entry+z_entry+z_entry
--   roles: abs=3, abs=7, abs=5, abs=5, abs=5, abs=5, abs=7, abs=2; 3 instances at bases [5]; all_strict=True; worst realized 542963/641355
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u453_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (295176:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u453_uniform
-- u454 [4-edge cycle] 1->3->4->5->(closed) | cand_entry+z_entry+z_entry+z_entry
--   roles: abs=3, abs=10, abs=7, abs=7, abs=7, abs=7, abs=10, abs=2; 2 instances at bases [7]; all_strict=True; worst realized 4473873/5496425
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u454_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (1022552:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u454_uniform
-- u455 [4-edge cycle] 1->3->4->5->(closed) | cand_entry+z_entry+z_entry+z_irred
--   roles: abs=4, abs=6, abs=5, abs=5, abs=5, abs=5, abs=3, abs=6; 3 instances at bases [5]; all_strict=True; worst realized 38663/47151
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u455_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (415912:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u455_uniform
-- u456 [4-edge cycle] 1->3->4->5->(closed) | cand_entry+z_entry+z_entry+z_irred
--   roles: abs=2, free+3..+4, tied=base, tied=base, tied=base, tied=base, abs=1, tied+1; 9 instances at bases [7, 8, 10]; all_strict=True; worst realized 614061/983125
/-- pattern tau=(3): real half-line form, mono certificate (kind ALL, strict=True, deg D = 3). -/
theorem shape_u456_pat1_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (4096:ℚ) * m ^ 3 - (5376:ℚ) * m ^ 2 - (4896:ℚ) * m - (40:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have h3 : (0:ℚ) ≤ (m - 5) ^ 3 := by nlinarith
  have hshift : (4096:ℚ) * (m - 5) ^ 3 + (56064:ℚ) * (m - 5) ^ 2 + (248544:ℚ) * (m - 5) + (353080:ℚ) = (4096:ℚ) * m ^ 3 - (5376:ℚ) * m ^ 2 - (4896:ℚ) * m - (40:ℚ) := by ring
  linarith [ht, h2, h3, hshift]
#print axioms shape_u456_pat1_uniform
/-- pattern tau=(4): real half-line form, mono certificate (kind ALL, strict=True, deg D = 3). -/
theorem shape_u456_pat2_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (4096:ℚ) * m ^ 3 - (8960:ℚ) * m ^ 2 - (5792:ℚ) * m - (96:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have h3 : (0:ℚ) ≤ (m - 5) ^ 3 := by nlinarith
  have hshift : (4096:ℚ) * (m - 5) ^ 3 + (52480:ℚ) * (m - 5) ^ 2 + (211808:ℚ) * (m - 5) + (258944:ℚ) = (4096:ℚ) * m ^ 3 - (8960:ℚ) * m ^ 2 - (5792:ℚ) * m - (96:ℚ) := by ring
  linarith [ht, h2, h3, hshift]
#print axioms shape_u456_pat2_uniform
-- u457 [4-edge cycle] 1->3->4->5->(closed) | cand_entry+z_entry+z_entry+z_irred
--   roles: abs=5, abs=8, abs=7, abs=7, abs=7, abs=7, abs=4, abs=8; 4 instances at bases [7]; all_strict=True; worst realized 33573/39325
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u457_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (1121640:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u457_uniform
-- u458 [4-edge cycle] 1->3->4->5->(closed) | cand_entry+z_entry+z_entry+z_irred
--   roles: abs=3, tied+2, tied=base, tied=base, tied=base, tied=base, abs=2, tied+1; 4 instances at bases [8, 10]; all_strict=True; worst realized 63375/82271
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 3). -/
theorem shape_u458_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (4096:ℚ) * m ^ 3 - (7936:ℚ) * m ^ 2 - (7328:ℚ) * m - (48:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have h3 : (0:ℚ) ≤ (m - 5) ^ 3 := by nlinarith
  have hshift : (4096:ℚ) * (m - 5) ^ 3 + (53504:ℚ) * (m - 5) ^ 2 + (220512:ℚ) * (m - 5) + (276912:ℚ) = (4096:ℚ) * m ^ 3 - (7936:ℚ) * m ^ 2 - (7328:ℚ) * m - (48:ℚ) := by ring
  linarith [ht, h2, h3, hshift]
#print axioms shape_u458_uniform
-- u459 [4-edge cycle] 1->3->4->5->(closed) | cand_entry+z_entry+z_entry+z_irred
--   roles: abs=6, abs=10, abs=9, abs=9, abs=9, abs=9, abs=5, abs=10; 3 instances at bases [9]; all_strict=True; worst realized 207831/236927
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u459_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (2356776:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u459_uniform
-- u460 [4-edge cycle] 1->3->4->5->(closed) | cand_irred+z_entry+z_entry+z_irred
--   roles: abs=11, abs=1, abs=8, abs=8, abs=8, abs=8, abs=1, abs=9; 2 instances at bases [8]; all_strict=True; worst realized 122525/124173
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u460_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (34608:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u460_uniform
-- u461 [4-edge cycle] 1->3->4->5->(closed) | cand_irred+z_entry+z_entry+z_irred
--   roles: abs=12, abs=2, abs=10, abs=10, abs=10, abs=10, abs=2, abs=11; 1 instances at bases [10]; all_strict=True; worst realized 9349425/9442633
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u461_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (93208:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u461_uniform
-- u462 [4-edge cycle] 1->4->5->6->(closed) | cand_entry+z_entry+z_entry+z_entry
--   roles: abs=4, abs=7, abs=5, abs=5, abs=6, abs=6, abs=7, abs=3; 1 instances at bases [5]; all_strict=True; worst realized 190855/208351
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u462_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (262440:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u462_uniform
-- u463 [4-edge cycle] 1->4->5->6->(closed) | cand_entry+z_entry+z_entry+z_entry
--   roles: abs=3, abs=9, abs=6, abs=6, abs=7, abs=7, abs=9, abs=2; 1 instances at bases [6]; all_strict=True; worst realized 3466113/4221305
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u463_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (755192:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u463_uniform
-- u464 [4-edge cycle] 1->4->5->6->(closed) | cand_entry+z_entry+z_entry+z_irred
--   roles: abs=3, abs=7, abs=5, abs=5, abs=6, abs=6, abs=2, abs=6; 3 instances at bases [5]; all_strict=True; worst realized 11685/14053
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u464_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (348096:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u464_uniform
-- u465 [4-edge cycle] 1->4->5->6->(closed) | cand_entry+z_entry+z_entry+z_irred
--   roles: tied+1, tied+1, tied=base, tied=base, tied+1, tied+1, tied=base, tied+1; 2 instances at bases [5, 6]; all_strict=True; worst realized 2793/3025
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 3). -/
theorem shape_u465_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (2048:ℚ) * m ^ 3 + (4608:ℚ) * m ^ 2 + (2272:ℚ) * m - (360:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have h3 : (0:ℚ) ≤ (m - 5) ^ 3 := by nlinarith
  have hshift : (2048:ℚ) * (m - 5) ^ 3 + (35328:ℚ) * (m - 5) ^ 2 + (201952:ℚ) * (m - 5) + (382200:ℚ) = (2048:ℚ) * m ^ 3 + (4608:ℚ) * m ^ 2 + (2272:ℚ) * m - (360:ℚ) := by ring
  linarith [ht, h2, h3, hshift]
#print axioms shape_u465_uniform
-- u466 [4-edge cycle] 1->5->6->2->(closed) | cand_entry+z_entry+z_entry+z_entry
--   roles: abs=2, abs=9, abs=6, abs=6, abs=9, abs=4, abs=4, abs=1; 1 instances at bases [5]; all_strict=True; worst realized 354123/517235
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u466_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (489336:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u466_uniform
-- u467 [4-edge cycle] 1->5->6->2->(closed) | cand_entry+z_entry+z_entry+z_irred
--   roles: abs=2, tied+4, tied+1, tied+1, tied+2, abs=3, abs=1, abs=3; 4 instances at bases [5, 6]; all_strict=True; worst realized 25039/38775
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 2). -/
theorem shape_u467_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (12800:ℚ) * m ^ 2 + (7200:ℚ) * m - (12600:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have hshift : (12800:ℚ) * (m - 5) ^ 2 + (135200:ℚ) * (m - 5) + (343400:ℚ) = (12800:ℚ) * m ^ 2 + (7200:ℚ) * m - (12600:ℚ) := by ring
  linarith [ht, h2, hshift]
#print axioms shape_u467_uniform
-- u468 [4-edge cycle] 1->5->6->2->(closed) | cand_entry+z_entry+z_entry+z_irred
--   roles: abs=2, abs=10, abs=7, abs=7, abs=10, abs=8, abs=1, abs=6; 1 instances at bases [6]; all_strict=True; worst realized 20007/30415
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u468_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (1092840:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u468_uniform
-- u469 [4-edge cycle] 1->5->6->2->(closed) | cand_entry+z_entry+z_entry+z_irred
--   roles: abs=2, abs=11, abs=8, abs=8, abs=9, abs=4, abs=1, abs=4; 1 instances at bases [7]; all_strict=True; worst realized 1157/1917
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u469_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (877800:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u469_uniform
-- u470 [4-edge cycle] 1->5->6->2->(closed) | cand_entry+z_entry+z_entry+z_irred
--   roles: abs=2, abs=13, abs=9, abs=9, abs=13, abs=8, abs=1, abs=6; 1 instances at bases [8]; all_strict=True; worst realized 4745/7313
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u470_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (1887480:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u470_uniform
-- u471 [4-edge cycle] 1->5->6->2->(closed) | cand_entry+z_entry+z_irred+z_entry
--   roles: abs=2, tied+4, tied+1, tied+1, abs=3, tied+1, abs=4, abs=1; 2 instances at bases [5, 6]; all_strict=True; worst realized 5037/7285
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 2). -/
theorem shape_u471_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (16512:ℚ) * m ^ 2 - (10032:ℚ) * m - (32184:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have hshift : (16512:ℚ) * (m - 5) ^ 2 + (155088:ℚ) * (m - 5) + (330456:ℚ) = (16512:ℚ) * m ^ 2 - (10032:ℚ) * m - (32184:ℚ) := by ring
  linarith [ht, h2, hshift]
#print axioms shape_u471_uniform
-- u472 [4-edge cycle] 1->5->6->2->(closed) | cand_entry+z_entry+z_irred+z_entry
--   roles: abs=3, abs=10, abs=8, abs=8, abs=5, abs=8, abs=6, abs=2; 1 instances at bases [7]; all_strict=True; worst realized 5967/7567
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u472_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (936000:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u472_uniform
-- u473 [4-edge cycle] 1->5->6->2->(closed) | cand_entry+z_entry+z_irred+z_irred
--   roles: abs=2, free+3..+4, tied+1, tied+1, tied-1, tied+1, abs=1, tied-1; 3 instances at bases [5, 7, 9]; all_strict=True; worst realized 4183/6615
/-- pattern tau=(3): real half-line form, mono certificate (kind ALL, strict=True, deg D = 3). -/
theorem shape_u473_pat1_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (4096:ℚ) * m ^ 3 - (2560:ℚ) * m ^ 2 - (1344:ℚ) * m + (7560:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have h3 : (0:ℚ) ≤ (m - 5) ^ 3 := by nlinarith
  have hshift : (4096:ℚ) * (m - 5) ^ 3 + (58880:ℚ) * (m - 5) ^ 2 + (280256:ℚ) * (m - 5) + (448840:ℚ) = (4096:ℚ) * m ^ 3 - (2560:ℚ) * m ^ 2 - (1344:ℚ) * m + (7560:ℚ) := by ring
  linarith [ht, h2, h3, hshift]
#print axioms shape_u473_pat1_uniform
/-- pattern tau=(4): real half-line form, mono certificate (kind ALL, strict=True, deg D = 3). -/
theorem shape_u473_pat2_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (4096:ℚ) * m ^ 3 - (6144:ℚ) * m ^ 2 - (1344:ℚ) * m + (12096:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have h3 : (0:ℚ) ≤ (m - 5) ^ 3 := by nlinarith
  have hshift : (4096:ℚ) * (m - 5) ^ 3 + (55296:ℚ) * (m - 5) ^ 2 + (244416:ℚ) * (m - 5) + (363776:ℚ) = (4096:ℚ) * m ^ 3 - (6144:ℚ) * m ^ 2 - (1344:ℚ) * m + (12096:ℚ) := by ring
  linarith [ht, h2, h3, hshift]
#print axioms shape_u473_pat2_uniform
-- u474 [4-edge cycle] 1->5->6->2->(closed) | cand_entry+z_entry+z_irred+z_irred
--   roles: tied-3, abs=8, tied+1, tied+1, tied=base, tied+1, tied-4, tied=base; 2 instances at bases [5, 6]; all_strict=True; worst realized 9165/12397
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 4). -/
theorem shape_u474_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (4096:ℚ) * m ^ 4 - (37376:ℚ) * m ^ 3 + (81856:ℚ) * m ^ 2 + (126664:ℚ) * m - (20880:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have h3 : (0:ℚ) ≤ (m - 5) ^ 3 := by nlinarith
  have h4 : (0:ℚ) ≤ (m - 5) ^ 4 := by nlinarith
  have hshift : (4096:ℚ) * (m - 5) ^ 4 + (44544:ℚ) * (m - 5) ^ 3 + (135616:ℚ) * (m - 5) ^ 2 + (190024:ℚ) * (m - 5) + (546840:ℚ) = (4096:ℚ) * m ^ 4 - (37376:ℚ) * m ^ 3 + (81856:ℚ) * m ^ 2 + (126664:ℚ) * m - (20880:ℚ) := by ring
  linarith [ht, h2, h3, h4, hshift]
#print axioms shape_u474_uniform
-- u475 [4-edge cycle] 1->5->6->2->(closed) | cand_entry+z_entry+z_irred+z_irred
--   roles: abs=2, tied+4, tied+1, tied+1, abs=3, tied+1, abs=1, abs=3; 3 instances at bases [5, 6]; all_strict=True; worst realized 11753/17625
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 2). -/
theorem shape_u475_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (13696:ℚ) * m ^ 2 - (6096:ℚ) * m - (24192:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have hshift : (13696:ℚ) * (m - 5) ^ 2 + (130864:ℚ) * (m - 5) + (287728:ℚ) = (13696:ℚ) * m ^ 2 - (6096:ℚ) * m - (24192:ℚ) := by ring
  linarith [ht, h2, hshift]
#print axioms shape_u475_uniform
-- u476 [4-edge cycle] 1->5->6->2->(closed) | cand_entry+z_entry+z_irred+z_irred
--   roles: abs=2, abs=10, tied+1, tied+1, abs=2, tied+1, abs=1, abs=2; 3 instances at bases [5, 6]; all_strict=True; worst realized 567/799
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 2). -/
theorem shape_u476_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (16320:ℚ) * m ^ 2 - (35400:ℚ) * m - (60480:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have hshift : (16320:ℚ) * (m - 5) ^ 2 + (127800:ℚ) * (m - 5) + (170520:ℚ) = (16320:ℚ) * m ^ 2 - (35400:ℚ) * m - (60480:ℚ) := by ring
  linarith [ht, h2, hshift]
#print axioms shape_u476_uniform
-- u477 [4-edge cycle] 1->5->6->2->(closed) | cand_entry+z_entry+z_irred+z_irred
--   roles: tied-2, tied+2, tied+1, tied+1, abs=4, tied+1, tied-3, abs=4; 3 instances at bases [5, 6, 7]; all_strict=True; worst realized 70153/81081
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 3). -/
theorem shape_u477_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (1024:ℚ) * m ^ 3 - (4096:ℚ) * m ^ 2 + (68080:ℚ) * m + (83232:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have h3 : (0:ℚ) ≤ (m - 5) ^ 3 := by nlinarith
  have hshift : (1024:ℚ) * (m - 5) ^ 3 + (11264:ℚ) * (m - 5) ^ 2 + (103920:ℚ) * (m - 5) + (449232:ℚ) = (1024:ℚ) * m ^ 3 - (4096:ℚ) * m ^ 2 + (68080:ℚ) * m + (83232:ℚ) := by ring
  linarith [ht, h2, h3, hshift]
#print axioms shape_u477_uniform
-- u478 [4-edge cycle] 1->5->6->2->(closed) | cand_entry+z_entry+z_irred+z_irred
--   roles: abs=4, tied+2, tied+1, tied+1, abs=3, tied+1, abs=3, abs=3; 2 instances at bases [5, 6]; all_strict=True; worst realized 30153/36425
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 2). -/
theorem shape_u478_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (15744:ℚ) * m ^ 2 - (10832:ℚ) * m - (32112:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have hshift : (15744:ℚ) * (m - 5) ^ 2 + (146608:ℚ) * (m - 5) + (307328:ℚ) = (15744:ℚ) * m ^ 2 - (10832:ℚ) * m - (32112:ℚ) := by ring
  linarith [ht, h2, hshift]
#print axioms shape_u478_uniform
-- u479 [4-edge cycle] 1->5->6->2->(closed) | cand_entry+z_entry+z_irred+z_irred
--   roles: tied-3, tied+2, tied+1, tied+1, tied-3, tied+1, tied-4, tied-3; 2 instances at bases [7, 8]; all_strict=True; worst realized 2511/2911
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 2). -/
theorem shape_u479_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (25600:ℚ) * m ^ 2 - (51200:ℚ) * m - (90000:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have hshift : (25600:ℚ) * (m - 5) ^ 2 + (204800:ℚ) * (m - 5) + (294000:ℚ) = (25600:ℚ) * m ^ 2 - (51200:ℚ) * m - (90000:ℚ) := by ring
  linarith [ht, h2, hshift]
#print axioms shape_u479_uniform
-- u480 [4-edge cycle] 1->5->6->2->(closed) | cand_entry+z_entry+z_irred+z_irred
--   roles: abs=4, tied+2, tied+1, tied+1, tied-2, tied+1, abs=3, tied-2; 3 instances at bases [7, 8, 9]; all_strict=True; worst realized 21827/26691
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 3). -/
theorem shape_u480_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (4096:ℚ) * m ^ 3 - (11264:ℚ) * m ^ 2 + (9280:ℚ) * m + (30528:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have h3 : (0:ℚ) ≤ (m - 5) ^ 3 := by nlinarith
  have hshift : (4096:ℚ) * (m - 5) ^ 3 + (50176:ℚ) * (m - 5) ^ 2 + (203840:ℚ) * (m - 5) + (307328:ℚ) = (4096:ℚ) * m ^ 3 - (11264:ℚ) * m ^ 2 + (9280:ℚ) * m + (30528:ℚ) := by ring
  linarith [ht, h2, h3, hshift]
#print axioms shape_u480_uniform
-- u481 [4-edge cycle] 1->5->6->2->(closed) | cand_entry+z_entry+z_irred+z_irred
--   roles: abs=4, tied+2, tied+1, tied+1, tied-1, tied+1, abs=3, tied-1; 3 instances at bases [7, 8, 9]; all_strict=True; worst realized 78913/95697
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 3). -/
theorem shape_u481_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (4096:ℚ) * m ^ 3 - (7168:ℚ) * m ^ 2 + (2752:ℚ) * m + (18000:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have h3 : (0:ℚ) ≤ (m - 5) ^ 3 := by nlinarith
  have hshift : (4096:ℚ) * (m - 5) ^ 3 + (54272:ℚ) * (m - 5) ^ 2 + (238272:ℚ) * (m - 5) + (364560:ℚ) = (4096:ℚ) * m ^ 3 - (7168:ℚ) * m ^ 2 + (2752:ℚ) * m + (18000:ℚ) := by ring
  linarith [ht, h2, h3, hshift]
#print axioms shape_u481_uniform
-- u482 [4-edge cycle] 1->5->6->2->(closed) | cand_entry+z_entry+z_irred+z_irred
--   roles: abs=2, abs=12, abs=9, abs=9, abs=5, abs=9, abs=1, abs=5; 1 instances at bases [8]; all_strict=True; worst realized 8827/14555
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u482_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (1254432:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u482_uniform
-- u483 [4-edge cycle] 1->5->6->2->(closed) | cand_entry+z_entry+z_irred+z_irred
--   roles: abs=2, abs=12, abs=9, abs=9, abs=6, abs=9, abs=1, abs=6; 1 instances at bases [8]; all_strict=True; worst realized 4559/7455
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u483_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (1479856:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u483_uniform
-- u484 [4-edge cycle] 1->5->6->2->(closed) | cand_entry+z_entry+z_irred+z_irred
--   roles: abs=2, abs=13, abs=10, abs=10, abs=9, abs=10, abs=1, abs=9; 1 instances at bases [9]; all_strict=True; worst realized 3479/5767
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u484_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (2779920:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u484_uniform
-- u485 [4-edge cycle] 1->5->6->2->(closed) | cand_entry+z_entry+z_irred+z_irred
--   roles: abs=4, tied+2, tied+1, tied+1, tied=base, tied+1, abs=3, tied=base; 2 instances at bases [9, 10]; all_strict=True; worst realized 145337/178777
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 3). -/
theorem shape_u485_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (4096:ℚ) * m ^ 3 - (3072:ℚ) * m ^ 2 - (3776:ℚ) * m + (5472:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have h3 : (0:ℚ) ≤ (m - 5) ^ 3 := by nlinarith
  have hshift : (4096:ℚ) * (m - 5) ^ 3 + (58368:ℚ) * (m - 5) ^ 2 + (272704:ℚ) * (m - 5) + (421792:ℚ) = (4096:ℚ) * m ^ 3 - (3072:ℚ) * m ^ 2 - (3776:ℚ) * m + (5472:ℚ) := by ring
  linarith [ht, h2, h3, hshift]
#print axioms shape_u485_uniform
-- u486 [4-edge cycle] 1->5->6->2->(closed) | cand_entry+z_entry+z_irred+z_irred
--   roles: abs=5, tied+2, tied+1, tied+1, tied-2, tied+1, abs=4, tied-2; 2 instances at bases [9, 10]; all_strict=True; worst realized 151745/175617
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 3). -/
theorem shape_u486_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (4096:ℚ) * m ^ 3 - (15360:ℚ) * m ^ 2 + (16448:ℚ) * m + (43776:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have h3 : (0:ℚ) ≤ (m - 5) ^ 3 := by nlinarith
  have hshift : (4096:ℚ) * (m - 5) ^ 3 + (46080:ℚ) * (m - 5) ^ 2 + (170048:ℚ) * (m - 5) + (254016:ℚ) = (4096:ℚ) * m ^ 3 - (15360:ℚ) * m ^ 2 + (16448:ℚ) * m + (43776:ℚ) := by ring
  linarith [ht, h2, h3, hshift]
#print axioms shape_u486_uniform
-- u487 [4-edge cycle] 1->5->6->3->(closed) | cand_entry+z_entry+z_entry+z_entry
--   roles: abs=2, free+4..+5, tied+1, tied+1, tied+1, tied=base, tied+3, abs=1; 14 instances at bases [5, 6, 7]; all_strict=True; worst realized 7749/11045
/-- pattern tau=(4): real half-line form, mono certificate (kind ALL, strict=True, deg D = 3). -/
theorem shape_u487_pat1_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (3072:ℚ) * m ^ 3 + (10752:ℚ) * m ^ 2 + (20112:ℚ) * m + (14232:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have h3 : (0:ℚ) ≤ (m - 5) ^ 3 := by nlinarith
  have hshift : (3072:ℚ) * (m - 5) ^ 3 + (56832:ℚ) * (m - 5) ^ 2 + (358032:ℚ) * (m - 5) + (767592:ℚ) = (3072:ℚ) * m ^ 3 + (10752:ℚ) * m ^ 2 + (20112:ℚ) * m + (14232:ℚ) := by ring
  linarith [ht, h2, h3, hshift]
#print axioms shape_u487_pat1_uniform
/-- pattern tau=(5): real half-line form, mono certificate (kind ALL, strict=True, deg D = 3). -/
theorem shape_u487_pat2_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (3072:ℚ) * m ^ 3 + (6144:ℚ) * m ^ 2 + (14352:ℚ) * m + (13584:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have h3 : (0:ℚ) ≤ (m - 5) ^ 3 := by nlinarith
  have hshift : (3072:ℚ) * (m - 5) ^ 3 + (52224:ℚ) * (m - 5) ^ 2 + (306192:ℚ) * (m - 5) + (622944:ℚ) = (3072:ℚ) * m ^ 3 + (6144:ℚ) * m ^ 2 + (14352:ℚ) * m + (13584:ℚ) := by ring
  linarith [ht, h2, h3, hshift]
#print axioms shape_u487_pat2_uniform
-- u488 [4-edge cycle] 1->5->6->3->(closed) | cand_entry+z_entry+z_entry+z_entry
--   roles: abs=2, free+5..+6, tied+1, tied+1, tied+1, tied=base, tied+4, abs=1; 8 instances at bases [5, 6, 8, 10]; all_strict=True; worst realized 321711/478895
/-- pattern tau=(5): real half-line form, mono certificate (kind ALL, strict=True, deg D = 3). -/
theorem shape_u488_pat1_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (3072:ℚ) * m ^ 3 + (13824:ℚ) * m ^ 2 + (27792:ℚ) * m + (19464:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have h3 : (0:ℚ) ≤ (m - 5) ^ 3 := by nlinarith
  have hshift : (3072:ℚ) * (m - 5) ^ 3 + (59904:ℚ) * (m - 5) ^ 2 + (396432:ℚ) * (m - 5) + (888024:ℚ) = (3072:ℚ) * m ^ 3 + (13824:ℚ) * m ^ 2 + (27792:ℚ) * m + (19464:ℚ) := by ring
  linarith [ht, h2, h3, hshift]
#print axioms shape_u488_pat1_uniform
/-- pattern tau=(6): real half-line form, mono certificate (kind ALL, strict=True, deg D = 3). -/
theorem shape_u488_pat2_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (3072:ℚ) * m ^ 3 + (9216:ℚ) * m ^ 2 + (22032:ℚ) * m + (18816:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have h3 : (0:ℚ) ≤ (m - 5) ^ 3 := by nlinarith
  have hshift : (3072:ℚ) * (m - 5) ^ 3 + (55296:ℚ) * (m - 5) ^ 2 + (344592:ℚ) * (m - 5) + (743376:ℚ) = (3072:ℚ) * m ^ 3 + (9216:ℚ) * m ^ 2 + (22032:ℚ) * m + (18816:ℚ) := by ring
  linarith [ht, h2, h3, hshift]
#print axioms shape_u488_pat2_uniform
-- u489 [4-edge cycle] 1->5->6->3->(closed) | cand_entry+z_entry+z_entry+z_entry
--   roles: abs=3, tied+3, tied+1, tied+1, tied+1, tied=base, tied+2, abs=2; 5 instances at bases [5, 6, 7, 8]; all_strict=True; worst realized 443989/558877
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 3). -/
theorem shape_u489_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (3072:ℚ) * m ^ 3 + (4608:ℚ) * m ^ 2 + (12432:ℚ) * m + (13080:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have h3 : (0:ℚ) ≤ (m - 5) ^ 3 := by nlinarith
  have hshift : (3072:ℚ) * (m - 5) ^ 3 + (50688:ℚ) * (m - 5) ^ 2 + (288912:ℚ) * (m - 5) + (574440:ℚ) = (3072:ℚ) * m ^ 3 + (4608:ℚ) * m ^ 2 + (12432:ℚ) * m + (13080:ℚ) := by ring
  linarith [ht, h2, h3, hshift]
#print axioms shape_u489_uniform
-- u490 [4-edge cycle] 1->5->6->3->(closed) | cand_entry+z_entry+z_entry+z_entry
--   roles: abs=4, abs=7, abs=6, abs=6, abs=6, abs=5, abs=6, abs=3; 5 instances at bases [5]; all_strict=True; worst realized 2862825/3218513
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u490_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (355688:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u490_uniform
-- u491 [4-edge cycle] 1->5->6->3->(closed) | cand_entry+z_entry+z_entry+z_entry
--   roles: tied=base, tied+2, tied+1, tied+1, tied+1, tied=base, tied+1, tied-1; 5 instances at bases [5, 6]; all_strict=True; worst realized 1488669/1563925
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 2). -/
theorem shape_u491_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (8704:ℚ) * m ^ 2 + (10368:ℚ) * m + (728:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have hshift : (8704:ℚ) * (m - 5) ^ 2 + (97408:ℚ) * (m - 5) + (270168:ℚ) = (8704:ℚ) * m ^ 2 + (10368:ℚ) * m + (728:ℚ) := by ring
  linarith [ht, h2, hshift]
#print axioms shape_u491_uniform
-- u492 [4-edge cycle] 1->5->6->3->(closed) | cand_entry+z_entry+z_entry+z_entry
--   roles: abs=4, tied+3, tied+1, tied+1, tied+1, tied=base, tied+2, abs=3; 3 instances at bases [7, 8, 9]; all_strict=True; worst realized 92625/107849
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 3). -/
theorem shape_u492_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (3072:ℚ) * m ^ 3 + (1536:ℚ) * m ^ 2 + (12432:ℚ) * m + (17160:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have h3 : (0:ℚ) ≤ (m - 5) ^ 3 := by nlinarith
  have hshift : (3072:ℚ) * (m - 5) ^ 3 + (47616:ℚ) * (m - 5) ^ 2 + (258192:ℚ) * (m - 5) + (501720:ℚ) = (3072:ℚ) * m ^ 3 + (1536:ℚ) * m ^ 2 + (12432:ℚ) * m + (17160:ℚ) := by ring
  linarith [ht, h2, h3, hshift]
#print axioms shape_u492_uniform
-- u493 [4-edge cycle] 1->5->6->3->(closed) | cand_entry+z_entry+z_entry+z_entry
--   roles: abs=5, tied+3, tied+1, tied+1, tied+1, tied=base, tied+2, abs=4; 2 instances at bases [9, 10]; all_strict=True; worst realized 2103057/2352857
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 3). -/
theorem shape_u493_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (3072:ℚ) * m ^ 3 - (1536:ℚ) * m ^ 2 + (12432:ℚ) * m + (21240:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have h3 : (0:ℚ) ≤ (m - 5) ^ 3 := by nlinarith
  have hshift : (3072:ℚ) * (m - 5) ^ 3 + (44544:ℚ) * (m - 5) ^ 2 + (227472:ℚ) * (m - 5) + (429000:ℚ) = (3072:ℚ) * m ^ 3 - (1536:ℚ) * m ^ 2 + (12432:ℚ) * m + (21240:ℚ) := by ring
  linarith [ht, h2, h3, hshift]
#print axioms shape_u493_uniform
-- u494 [4-edge cycle] 1->5->6->3->(closed) | cand_entry+z_entry+z_entry+z_irred
--   roles: abs=2, free+4..+5, tied+1, tied+1, tied+1, tied=base, abs=1, tied+1; 9 instances at bases [5, 6, 8, 10]; all_strict=True; worst realized 30527/45375
/-- pattern tau=(4): real half-line form, mono certificate (kind ALL, strict=True, deg D = 3). -/
theorem shape_u494_pat1_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (4096:ℚ) * m ^ 3 + (2816:ℚ) * m ^ 2 + (2016:ℚ) * m + (4536:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have h3 : (0:ℚ) ≤ (m - 5) ^ 3 := by nlinarith
  have hshift : (4096:ℚ) * (m - 5) ^ 3 + (64256:ℚ) * (m - 5) ^ 2 + (337376:ℚ) * (m - 5) + (597016:ℚ) = (4096:ℚ) * m ^ 3 + (2816:ℚ) * m ^ 2 + (2016:ℚ) * m + (4536:ℚ) := by ring
  linarith [ht, h2, h3, hshift]
#print axioms shape_u494_pat1_uniform
/-- pattern tau=(5): real half-line form, mono certificate (kind ALL, strict=True, deg D = 3). -/
theorem shape_u494_pat2_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (4096:ℚ) * m ^ 3 - (768:ℚ) * m ^ 2 - (2464:ℚ) * m + (4032:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have h3 : (0:ℚ) ≤ (m - 5) ^ 3 := by nlinarith
  have hshift : (4096:ℚ) * (m - 5) ^ 3 + (60672:ℚ) * (m - 5) ^ 2 + (297056:ℚ) * (m - 5) + (484512:ℚ) = (4096:ℚ) * m ^ 3 - (768:ℚ) * m ^ 2 - (2464:ℚ) * m + (4032:ℚ) := by ring
  linarith [ht, h2, h3, hshift]
#print axioms shape_u494_pat2_uniform
-- u495 [4-edge cycle] 1->5->6->3->(closed) | cand_entry+z_entry+z_entry+z_irred
--   roles: abs=3, tied+3, tied+1, tied+1, tied+1, tied=base, abs=2, tied+1; 8 instances at bases [5, 6, 7, 8, 9]; all_strict=True; worst realized 39975/50807
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 3). -/
theorem shape_u495_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (4096:ℚ) * m ^ 3 + (256:ℚ) * m ^ 2 + (1120:ℚ) * m + (6768:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have h3 : (0:ℚ) ≤ (m - 5) ^ 3 := by nlinarith
  have hshift : (4096:ℚ) * (m - 5) ^ 3 + (61696:ℚ) * (m - 5) ^ 2 + (310880:ℚ) * (m - 5) + (530768:ℚ) = (4096:ℚ) * m ^ 3 + (256:ℚ) * m ^ 2 + (1120:ℚ) * m + (6768:ℚ) := by ring
  linarith [ht, h2, h3, hshift]
#print axioms shape_u495_uniform
-- u496 [4-edge cycle] 1->5->6->3->(closed) | cand_entry+z_entry+z_entry+z_irred
--   roles: tied=base, tied+2, tied+1, tied+1, tied+1, tied=base, tied-1, tied+1; 5 instances at bases [6, 7, 8, 9, 10]; all_strict=True; worst realized 61983/66439
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 3). -/
theorem shape_u496_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (2048:ℚ) * m ^ 3 + (13824:ℚ) * m ^ 2 + (13792:ℚ) * m + (936:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have h3 : (0:ℚ) ≤ (m - 5) ^ 3 := by nlinarith
  have hshift : (2048:ℚ) * (m - 5) ^ 3 + (44544:ℚ) * (m - 5) ^ 2 + (305632:ℚ) * (m - 5) + (671496:ℚ) = (2048:ℚ) * m ^ 3 + (13824:ℚ) * m ^ 2 + (13792:ℚ) * m + (936:ℚ) := by ring
  linarith [ht, h2, h3, hshift]
#print axioms shape_u496_uniform
-- u497 [4-edge cycle] 1->5->6->3->(closed) | cand_entry+z_entry+z_entry+z_irred
--   roles: abs=4, tied+3, tied+1, tied+1, tied+1, tied=base, abs=3, tied+1; 3 instances at bases [8, 9, 10]; all_strict=True; worst realized 133055/156271
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 3). -/
theorem shape_u497_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (4096:ℚ) * m ^ 3 - (5888:ℚ) * m ^ 2 - (4256:ℚ) * m + (8496:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have h3 : (0:ℚ) ≤ (m - 5) ^ 3 := by nlinarith
  have hshift : (4096:ℚ) * (m - 5) ^ 3 + (55552:ℚ) * (m - 5) ^ 2 + (244064:ℚ) * (m - 5) + (352016:ℚ) = (4096:ℚ) * m ^ 3 - (5888:ℚ) * m ^ 2 - (4256:ℚ) * m + (8496:ℚ) := by ring
  linarith [ht, h2, h3, hshift]
#print axioms shape_u497_uniform
-- u498 [4-edge cycle] 1->5->6->3->(closed) | cand_entry+z_entry+z_entry+z_irred
--   roles: tied-1, tied+2, tied+1, tied+1, tied+1, tied=base, tied-2, tied+1; 6 instances at bases [8, 9, 10]; all_strict=True; worst realized 54999/59711
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 3). -/
theorem shape_u498_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (2048:ℚ) * m ^ 3 + (15872:ℚ) * m ^ 2 + (14048:ℚ) * m - (1368:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have h3 : (0:ℚ) ≤ (m - 5) ^ 3 := by nlinarith
  have hshift : (2048:ℚ) * (m - 5) ^ 3 + (46592:ℚ) * (m - 5) ^ 2 + (326368:ℚ) * (m - 5) + (721672:ℚ) = (2048:ℚ) * m ^ 3 + (15872:ℚ) * m ^ 2 + (14048:ℚ) * m - (1368:ℚ) := by ring
  linarith [ht, h2, h3, hshift]
#print axioms shape_u498_uniform
-- u499 [4-edge cycle] 1->5->6->3->(closed) | cand_entry+z_entry+z_entry+z_irred
--   roles: abs=8, abs=12, abs=11, abs=11, abs=11, abs=10, abs=7, abs=11; 2 instances at bases [10]; all_strict=True; worst realized 5335/5887
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u499_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (3979368:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u499_uniform
-- u500 [4-edge cycle] 1->5->6->3->(closed) | cand_irred+z_entry+z_entry+z_irred
--   roles: abs=10, abs=1, abs=7, abs=7, abs=7, abs=6, abs=1, abs=7; 1 instances at bases [6]; all_strict=True; worst realized 27097/27225
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u500_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (7296:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u500_uniform
-- u501 [4-edge cycle] 1->5->6->3->(closed) | cand_irred+z_entry+z_entry+z_irred
--   roles: abs=11, abs=2, abs=9, abs=9, abs=9, abs=8, abs=2, abs=9; 1 instances at bases [8]; all_strict=True; worst realized 84825/85697
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u501_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (63656:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u501_uniform
-- u502 [4-edge cycle] 1->5->6->4->(closed) | cand_entry+z_entry+z_entry+z_entry
--   roles: abs=2, abs=12, abs=8, abs=8, abs=12, abs=11, abs=11, abs=1; 3 instances at bases [7]; all_strict=True; worst realized 112229/173565
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u502_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (2760120:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u502_uniform
-- u503 [4-edge cycle] 1->6->3->2->(closed) | cand_entry+z_entry+weak+z_entry
--   roles: abs=4, abs=7, abs=6, abs=5, abs=6, abs=3; 1 instances at bases [5]; all_strict=False; worst realized 58425/68479
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u503_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (10054:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u503_uniform
-- u504 [4-edge cycle] 1->6->3->2->(closed) | cand_entry+z_entry+weak+z_entry
--   roles: abs=5, abs=7, abs=6, abs=5, abs=6, abs=4; 1 instances at bases [5]; all_strict=False; worst realized 25707/28717
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u504_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (9030:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u504_uniform
-- u505 [4-edge cycle] 1->6->3->2->(closed) | cand_entry+z_entry+z_entry+z_entry
--   roles: abs=3, tied+3, tied+1, tied=base, tied+2, tied+1, tied+1, abs=2; 2 instances at bases [6, 7]; all_strict=True; worst realized 165053/208725
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 3). -/
theorem shape_u505_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (3072:ℚ) * m ^ 3 + (4608:ℚ) * m ^ 2 + (12432:ℚ) * m + (13080:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have h3 : (0:ℚ) ≤ (m - 5) ^ 3 := by nlinarith
  have hshift : (3072:ℚ) * (m - 5) ^ 3 + (50688:ℚ) * (m - 5) ^ 2 + (288912:ℚ) * (m - 5) + (574440:ℚ) = (3072:ℚ) * m ^ 3 + (4608:ℚ) * m ^ 2 + (12432:ℚ) * m + (13080:ℚ) := by ring
  linarith [ht, h2, h3, hshift]
#print axioms shape_u505_uniform
-- u506 [4-edge cycle] 1->6->3->2->(closed) | cand_entry+z_entry+z_entry+z_entry
--   roles: abs=2, abs=12, abs=8, abs=7, abs=8, abs=5, abs=7, abs=1; 1 instances at bases [7]; all_strict=True; worst realized 75563/121275
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u506_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (1234224:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u506_uniform
-- u507 [4-edge cycle] 1->6->3->2->(closed) | cand_entry+z_entry+z_entry+z_entry
--   roles: abs=4, tied+3, tied+1, tied=base, tied+1, tied-1, tied=base, abs=3; 2 instances at bases [8, 9]; all_strict=True; worst realized 11506625/13736441
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 3). -/
theorem shape_u507_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (3072:ℚ) * m ^ 3 - (4608:ℚ) * m ^ 2 + (40080:ℚ) * m + (2856:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have h3 : (0:ℚ) ≤ (m - 5) ^ 3 := by nlinarith
  have hshift : (3072:ℚ) * (m - 5) ^ 3 + (41472:ℚ) * (m - 5) ^ 2 + (224400:ℚ) * (m - 5) + (472056:ℚ) = (3072:ℚ) * m ^ 3 - (4608:ℚ) * m ^ 2 + (40080:ℚ) * m + (2856:ℚ) := by ring
  linarith [ht, h2, h3, hshift]
#print axioms shape_u507_uniform
-- u508 [4-edge cycle] 1->6->3->2->(closed) | cand_entry+z_entry+z_entry+z_entry
--   roles: abs=4, tied+3, tied+1, tied=base, tied+2, tied=base, tied=base, abs=3; 3 instances at bases [8, 9, 10]; all_strict=True; worst realized 9400625/10954377
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 3). -/
theorem shape_u508_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (3072:ℚ) * m ^ 3 - (1536:ℚ) * m ^ 2 + (10384:ℚ) * m - (3880:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have h3 : (0:ℚ) ≤ (m - 5) ^ 3 := by nlinarith
  have hshift : (3072:ℚ) * (m - 5) ^ 3 + (44544:ℚ) * (m - 5) ^ 2 + (225424:ℚ) * (m - 5) + (393640:ℚ) = (3072:ℚ) * m ^ 3 - (1536:ℚ) * m ^ 2 + (10384:ℚ) * m - (3880:ℚ) := by ring
  linarith [ht, h2, h3, hshift]
#print axioms shape_u508_uniform
-- u509 [4-edge cycle] 1->6->3->2->(closed) | cand_entry+z_entry+z_entry+z_entry
--   roles: abs=4, tied+3, tied+1, tied=base, tied+2, tied+1, tied+1, abs=3; 3 instances at bases [8, 9, 10]; all_strict=True; worst realized 10557625/12345409
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 3). -/
theorem shape_u509_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (3072:ℚ) * m ^ 3 + (1536:ℚ) * m ^ 2 + (12432:ℚ) * m + (17160:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have h3 : (0:ℚ) ≤ (m - 5) ^ 3 := by nlinarith
  have hshift : (3072:ℚ) * (m - 5) ^ 3 + (47616:ℚ) * (m - 5) ^ 2 + (258192:ℚ) * (m - 5) + (501720:ℚ) = (3072:ℚ) * m ^ 3 + (1536:ℚ) * m ^ 2 + (12432:ℚ) * m + (17160:ℚ) := by ring
  linarith [ht, h2, h3, hshift]
#print axioms shape_u509_uniform
-- u510 [4-edge cycle] 1->6->3->2->(closed) | cand_entry+z_entry+z_entry+z_entry
--   roles: abs=5, tied+3, tied+1, tied=base, tied+1, tied-1, tied=base, abs=4; 3 instances at bases [8, 9, 10]; all_strict=True; worst realized 389455/443111
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 3). -/
theorem shape_u510_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (3072:ℚ) * m ^ 3 - (7680:ℚ) * m ^ 2 + (52368:ℚ) * m + (3864:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have h3 : (0:ℚ) ≤ (m - 5) ^ 3 := by nlinarith
  have hshift : (3072:ℚ) * (m - 5) ^ 3 + (38400:ℚ) * (m - 5) ^ 2 + (205968:ℚ) * (m - 5) + (457704:ℚ) = (3072:ℚ) * m ^ 3 - (7680:ℚ) * m ^ 2 + (52368:ℚ) * m + (3864:ℚ) := by ring
  linarith [ht, h2, h3, hshift]
#print axioms shape_u510_uniform
-- u511 [4-edge cycle] 1->6->3->2->(closed) | cand_entry+z_entry+z_entry+z_entry
--   roles: abs=6, tied+3, tied+1, tied=base, tied+1, tied-1, tied=base, abs=5; 2 instances at bases [9, 10]; all_strict=True; worst realized 18870865/20826217
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 3). -/
theorem shape_u511_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (3072:ℚ) * m ^ 3 - (10752:ℚ) * m ^ 2 + (64656:ℚ) * m + (4872:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have h3 : (0:ℚ) ≤ (m - 5) ^ 3 := by nlinarith
  have hshift : (3072:ℚ) * (m - 5) ^ 3 + (35328:ℚ) * (m - 5) ^ 2 + (187536:ℚ) * (m - 5) + (443352:ℚ) = (3072:ℚ) * m ^ 3 - (10752:ℚ) * m ^ 2 + (64656:ℚ) * m + (4872:ℚ) := by ring
  linarith [ht, h2, h3, hshift]
#print axioms shape_u511_uniform
-- u512 [4-edge cycle] 1->6->3->2->(closed) | cand_entry+z_entry+z_entry+z_entry
--   roles: abs=5, abs=13, abs=11, abs=10, abs=11, abs=8, abs=9, abs=4; 1 instances at bases [10]; all_strict=True; worst realized 51975/59711
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u512_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (2715336:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u512_uniform
-- u513 [4-edge cycle] 1->6->3->2->(closed) | cand_entry+z_entry+z_entry+z_entry
--   roles: abs=7, abs=13, abs=11, abs=10, abs=11, abs=9, abs=10, abs=6; 1 instances at bases [10]; all_strict=True; worst realized 676053/730829
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u513_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (2464920:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u513_uniform
-- u514 [4-edge cycle] 1->6->3->2->(closed) | cand_entry+z_entry+z_entry+z_irred
--   roles: abs=3, tied+3, tied+1, tied=base, tied+2, tied+1, abs=2, tied=base; 2 instances at bases [6, 7]; all_strict=True; worst realized 1387/1771
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 3). -/
theorem shape_u514_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (4096:ℚ) * m ^ 3 + (256:ℚ) * m ^ 2 - (7712:ℚ) * m - (960:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have h3 : (0:ℚ) ≤ (m - 5) ^ 3 := by nlinarith
  have hshift : (4096:ℚ) * (m - 5) ^ 3 + (61696:ℚ) * (m - 5) ^ 2 + (302048:ℚ) * (m - 5) + (478880:ℚ) = (4096:ℚ) * m ^ 3 + (256:ℚ) * m ^ 2 - (7712:ℚ) * m - (960:ℚ) := by ring
  linarith [ht, h2, h3, hshift]
#print axioms shape_u514_uniform
-- u515 [4-edge cycle] 1->6->3->2->(closed) | cand_entry+z_entry+z_entry+z_irred
--   roles: abs=3, abs=10, abs=8, abs=7, abs=8, abs=4, abs=2, abs=4; 1 instances at bases [7]; all_strict=True; worst realized 855/1127
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u515_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (727056:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u515_uniform
-- u516 [4-edge cycle] 1->6->3->2->(closed) | cand_entry+z_entry+z_entry+z_irred
--   roles: abs=3, tied+3, tied+1, tied=base, tied+1, tied-2, abs=2, tied-2; 3 instances at bases [7, 8, 9]; all_strict=True; worst realized 855/1127
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 3). -/
theorem shape_u516_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (4096:ℚ) * m ^ 3 - (12032:ℚ) * m ^ 2 + (14176:ℚ) * m - (11280:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have h3 : (0:ℚ) ≤ (m - 5) ^ 3 := by nlinarith
  have hshift : (4096:ℚ) * (m - 5) ^ 3 + (49408:ℚ) * (m - 5) ^ 2 + (201056:ℚ) * (m - 5) + (270800:ℚ) = (4096:ℚ) * m ^ 3 - (12032:ℚ) * m ^ 2 + (14176:ℚ) * m - (11280:ℚ) := by ring
  linarith [ht, h2, h3, hshift]
#print axioms shape_u516_uniform
-- u517 [4-edge cycle] 1->6->3->2->(closed) | cand_entry+z_entry+z_entry+z_irred
--   roles: abs=3, tied+3, tied+1, tied=base, tied+1, tied-1, abs=2, tied-1; 3 instances at bases [7, 8, 9]; all_strict=True; worst realized 855/1127
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 3). -/
theorem shape_u517_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (4096:ℚ) * m ^ 3 - (7936:ℚ) * m ^ 2 + (9824:ℚ) * m - (5264:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have h3 : (0:ℚ) ≤ (m - 5) ^ 3 := by nlinarith
  have hshift : (4096:ℚ) * (m - 5) ^ 3 + (53504:ℚ) * (m - 5) ^ 2 + (237664:ℚ) * (m - 5) + (357456:ℚ) = (4096:ℚ) * m ^ 3 - (7936:ℚ) * m ^ 2 + (9824:ℚ) * m - (5264:ℚ) := by ring
  linarith [ht, h2, h3, hshift]
#print axioms shape_u517_uniform
-- u518 [4-edge cycle] 1->6->3->2->(closed) | cand_entry+z_entry+z_entry+z_irred
--   roles: tied-5, tied+3, tied+1, tied=base, abs=10, abs=8, tied-6, tied-1; 2 instances at bases [8, 9]; all_strict=True; worst realized 162863/193471
/-- pattern tau=(): real half-line form, lukas certificate (kind ALL, strict=True, deg D = 3). -/
theorem shape_u518_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (7168:ℚ) * m ^ 3 - (111616:ℚ) * m ^ 2 + (618512:ℚ) * m + (238336:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have hsq1 : (0:ℚ) ≤ (m - 5 + (-75 / 16:ℚ)) ^ 2 := sq_nonneg _
  have hq1 : (0:ℚ) ≤ (7168:ℚ) * (m - 5) + (63104:ℚ) := by linarith [ht]
  have hprod1 : (0:ℚ) ≤ (m - 5 + (-75 / 16:ℚ)) ^ 2 * ((7168:ℚ) * (m - 5) + (63104:ℚ)) := mul_nonneg hsq1 hq1
  have hshift : (m - 5 + (-75 / 16:ℚ)) ^ 2 * ((7168:ℚ) * (m - 5) + (63104:ℚ)) + (474052:ℚ) * (m - 5) + (99867 / 2:ℚ) = (7168:ℚ) * m ^ 3 - (111616:ℚ) * m ^ 2 + (618512:ℚ) * m + (238336:ℚ) := by ring
  linarith [ht, hprod1, hshift]
#print axioms shape_u518_uniform
-- u519 [4-edge cycle] 1->6->3->2->(closed) | cand_entry+z_entry+z_entry+z_irred
--   roles: abs=4, tied+3, tied+1, tied=base, tied+1, tied-1, abs=3, tied-1; 2 instances at bases [8, 10]; all_strict=True; worst realized 133055/156271
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 3). -/
theorem shape_u519_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (4096:ℚ) * m ^ 3 - (14080:ℚ) * m ^ 2 + (16736:ℚ) * m - (6608:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have h3 : (0:ℚ) ≤ (m - 5) ^ 3 := by nlinarith
  have hshift : (4096:ℚ) * (m - 5) ^ 3 + (47360:ℚ) * (m - 5) ^ 2 + (183136:ℚ) * (m - 5) + (237072:ℚ) = (4096:ℚ) * m ^ 3 - (14080:ℚ) * m ^ 2 + (16736:ℚ) * m - (6608:ℚ) := by ring
  linarith [ht, h2, h3, hshift]
#print axioms shape_u519_uniform
-- u520 [4-edge cycle] 1->6->3->2->(closed) | cand_entry+z_entry+z_entry+z_irred
--   roles: abs=4, tied+3, tied+1, tied=base, tied+2, abs=10, abs=3, abs=9; 2 instances at bases [9, 10]; all_strict=True; worst realized 60237/71021
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 2). -/
theorem shape_u520_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (25600:ℚ) * m ^ 2 + (10784:ℚ) * m + (191040:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have hshift : (25600:ℚ) * (m - 5) ^ 2 + (266784:ℚ) * (m - 5) + (884960:ℚ) = (25600:ℚ) * m ^ 2 + (10784:ℚ) * m + (191040:ℚ) := by ring
  linarith [ht, h2, hshift]
#print axioms shape_u520_uniform
-- u521 [4-edge cycle] 1->6->3->2->(closed) | cand_entry+z_entry+z_entry+z_irred
--   roles: abs=2, abs=15, abs=11, abs=10, abs=11, abs=9, abs=1, abs=9; 1 instances at bases [10]; all_strict=True; worst realized 2541/4205
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u521_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (3279744:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u521_uniform
-- u522 [4-edge cycle] 1->6->3->2->(closed) | cand_entry+z_entry+z_entry+z_irred
--   roles: abs=4, abs=13, abs=11, abs=10, abs=12, abs=11, abs=3, abs=10; 1 instances at bases [10]; all_strict=True; worst realized 14329/17081
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u522_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (3343680:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u522_uniform
-- u523 [4-edge cycle] 1->6->3->2->(closed) | cand_irred+z_entry+z_entry+z_irred
--   roles: abs=11, abs=2, abs=9, abs=8, abs=9, abs=6, abs=2, abs=6; 1 instances at bases [8]; all_strict=True; worst realized 84825/85697
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u523_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (42728:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u523_uniform
-- u524 [4-edge cycle] 1->6->3->2->(closed) | cand_irred+z_entry+z_entry+z_irred
--   roles: abs=11, abs=2, abs=9, abs=8, abs=9, abs=7, abs=2, abs=7; 2 instances at bases [8]; all_strict=True; worst realized 84825/85697
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u524_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (49704:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u524_uniform
-- u525 [4-edge cycle] 1->6->3->4->(closed) | cand_entry+z_entry+z_entry+z_entry
--   roles: abs=2, free+5..+6, tied+1, tied=base, tied=base, tied=base, tied+4, abs=1; 6 instances at bases [5, 6, 7, 8, 9]; all_strict=True; worst realized 698691/1021075
/-- pattern tau=(5): real half-line form, mono certificate (kind ALL, strict=True, deg D = 3). -/
theorem shape_u525_pat1_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (3072:ℚ) * m ^ 3 + (10752:ℚ) * m ^ 2 + (15504:ℚ) * m - (3624:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have h3 : (0:ℚ) ≤ (m - 5) ^ 3 := by nlinarith
  have hshift : (3072:ℚ) * (m - 5) ^ 3 + (56832:ℚ) * (m - 5) ^ 2 + (353424:ℚ) * (m - 5) + (726696:ℚ) = (3072:ℚ) * m ^ 3 + (10752:ℚ) * m ^ 2 + (15504:ℚ) * m - (3624:ℚ) := by ring
  linarith [ht, h2, h3, hshift]
#print axioms shape_u525_pat1_uniform
/-- pattern tau=(6): real half-line form, mono certificate (kind ALL, strict=True, deg D = 3). -/
theorem shape_u525_pat2_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (3072:ℚ) * m ^ 3 + (6144:ℚ) * m ^ 2 + (14352:ℚ) * m - (3696:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have h3 : (0:ℚ) ≤ (m - 5) ^ 3 := by nlinarith
  have hshift : (3072:ℚ) * (m - 5) ^ 3 + (52224:ℚ) * (m - 5) ^ 2 + (306192:ℚ) * (m - 5) + (605664:ℚ) = (3072:ℚ) * m ^ 3 + (6144:ℚ) * m ^ 2 + (14352:ℚ) * m - (3696:ℚ) := by ring
  linarith [ht, h2, h3, hshift]
#print axioms shape_u525_pat2_uniform
-- u526 [4-edge cycle] 1->6->3->4->(closed) | cand_entry+z_entry+z_entry+z_entry
--   roles: abs=3, tied+3, tied+1, tied=base, tied=base, tied=base, tied+2, abs=2; 5 instances at bases [5, 6]; all_strict=True; worst realized 28577/35673
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 3). -/
theorem shape_u526_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (3072:ℚ) * m ^ 3 + (1536:ℚ) * m ^ 2 + (8336:ℚ) * m - (2840:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have h3 : (0:ℚ) ≤ (m - 5) ^ 3 := by nlinarith
  have hshift : (3072:ℚ) * (m - 5) ^ 3 + (47616:ℚ) * (m - 5) ^ 2 + (254096:ℚ) * (m - 5) + (461240:ℚ) = (3072:ℚ) * m ^ 3 + (1536:ℚ) * m ^ 2 + (8336:ℚ) * m - (2840:ℚ) := by ring
  linarith [ht, h2, h3, hshift]
#print axioms shape_u526_uniform
-- u527 [4-edge cycle] 1->6->3->4->(closed) | cand_entry+z_entry+z_entry+z_entry
--   roles: abs=4, tied+3, tied+1, tied=base, tied=base, tied=base, tied+2, abs=3; 15 instances at bases [8, 9, 10]; all_strict=True; worst realized 9400625/10954377
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 3). -/
theorem shape_u527_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (3072:ℚ) * m ^ 3 - (1536:ℚ) * m ^ 2 + (10384:ℚ) * m - (3880:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have h3 : (0:ℚ) ≤ (m - 5) ^ 3 := by nlinarith
  have hshift : (3072:ℚ) * (m - 5) ^ 3 + (44544:ℚ) * (m - 5) ^ 2 + (225424:ℚ) * (m - 5) + (393640:ℚ) = (3072:ℚ) * m ^ 3 - (1536:ℚ) * m ^ 2 + (10384:ℚ) * m - (3880:ℚ) := by ring
  linarith [ht, h2, h3, hshift]
#print axioms shape_u527_uniform
-- u528 [4-edge cycle] 1->6->3->4->(closed) | cand_entry+z_entry+z_entry+z_entry
--   roles: tied-3, tied+3, tied+1, tied=base, tied=base, tied=base, tied+2, tied-4; 3 instances at bases [8, 9, 10]; all_strict=True; worst realized 2250423/2394095
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 2). -/
theorem shape_u528_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (22016:ℚ) * m ^ 2 - (4992:ℚ) * m + (3400:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have hshift : (22016:ℚ) * (m - 5) ^ 2 + (215168:ℚ) * (m - 5) + (528840:ℚ) = (22016:ℚ) * m ^ 2 - (4992:ℚ) * m + (3400:ℚ) := by ring
  linarith [ht, h2, hshift]
#print axioms shape_u528_uniform
-- u529 [4-edge cycle] 1->6->3->4->(closed) | cand_entry+z_entry+z_entry+z_entry
--   roles: tied-2, tied+3, tied+1, tied=base, tied=base, tied=base, tied+2, tied-3; 3 instances at bases [8, 9, 10]; all_strict=True; worst realized 2187/2291
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 2). -/
theorem shape_u529_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (18944:ℚ) * m ^ 2 - (2944:ℚ) * m + (2360:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have hshift : (18944:ℚ) * (m - 5) ^ 2 + (186496:ℚ) * (m - 5) + (461240:ℚ) = (18944:ℚ) * m ^ 2 - (2944:ℚ) * m + (2360:ℚ) := by ring
  linarith [ht, h2, hshift]
#print axioms shape_u529_uniform
-- u530 [4-edge cycle] 1->6->3->4->(closed) | cand_entry+z_entry+z_entry+z_entry
--   roles: tied-1, tied+3, tied+1, tied=base, tied=base, tied=base, tied+2, tied-2; 3 instances at bases [8, 9, 10]; all_strict=True; worst realized 2985255/3090559
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 2). -/
theorem shape_u530_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (15872:ℚ) * m ^ 2 - (896:ℚ) * m + (1320:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have hshift : (15872:ℚ) * (m - 5) ^ 2 + (157824:ℚ) * (m - 5) + (393640:ℚ) = (15872:ℚ) * m ^ 2 - (896:ℚ) * m + (1320:ℚ) := by ring
  linarith [ht, h2, hshift]
#print axioms shape_u530_uniform
-- u531 [4-edge cycle] 1->6->3->4->(closed) | cand_entry+z_entry+z_entry+z_entry
--   roles: tied=base, tied+3, tied+1, tied=base, tied=base, tied=base, tied+2, tied-1; 3 instances at bases [8, 9, 10]; all_strict=True; worst realized 3352671/3438791
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 2). -/
theorem shape_u531_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (12800:ℚ) * m ^ 2 + (1152:ℚ) * m + (280:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have hshift : (12800:ℚ) * (m - 5) ^ 2 + (129152:ℚ) * (m - 5) + (326040:ℚ) = (12800:ℚ) * m ^ 2 + (1152:ℚ) * m + (280:ℚ) := by ring
  linarith [ht, h2, hshift]
#print axioms shape_u531_uniform
-- u532 [4-edge cycle] 1->6->3->4->(closed) | cand_entry+z_entry+z_entry+z_entry
--   roles: abs=2, abs=16, abs=11, abs=10, abs=10, abs=10, abs=15, abs=1; 1 instances at bases [10]; all_strict=True; worst realized 846369/1363145
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u532_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (4650984:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u532_uniform
-- u533 [4-edge cycle] 1->6->3->4->(closed) | cand_entry+z_entry+z_entry+z_entry
--   roles: abs=5, abs=13, abs=11, abs=10, abs=10, abs=10, abs=12, abs=4; 2 instances at bases [10]; all_strict=True; worst realized 505197/565877
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u533_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (2730600:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u533_uniform
-- u534 [4-edge cycle] 1->6->3->4->(closed) | cand_entry+z_entry+z_entry+z_entry
--   roles: abs=6, abs=13, abs=11, abs=10, abs=10, abs=10, abs=12, abs=5; 1 instances at bases [10]; all_strict=True; worst realized 1883007/2045863
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u534_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (2442840:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u534_uniform
-- u535 [4-edge cycle] 2->1->6->3->(closed) | cand_progress+z_entry+z_entry+z_entry
--   roles: abs=2, abs=7, abs=3, abs=9, abs=8, abs=7, abs=8, abs=6; 1 instances at bases [7]; all_strict=True; worst realized 1241/1863
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u535_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (1737246:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u535_uniform
-- u536 [4-edge cycle] 2->3->4->1->(closed) | cand_entry+z_entry+z_entry+z_entry
--   roles: abs=7, tied+2, tied=base, tied=base, tied+2, abs=2, abs=2, abs=5; 2 instances at bases [5, 6]; all_strict=True; worst realized 542963/589875
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 2). -/
theorem shape_u536_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (8192:ℚ) * m ^ 2 - (7968:ℚ) * m - (24224:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have hshift : (8192:ℚ) * (m - 5) ^ 2 + (73952:ℚ) * (m - 5) + (140736:ℚ) = (8192:ℚ) * m ^ 2 - (7968:ℚ) * m - (24224:ℚ) := by ring
  linarith [ht, h2, hshift]
#print axioms shape_u536_uniform
-- u537 [4-edge cycle] 2->3->4->1->(closed) | cand_entry+z_entry+z_entry+z_entry
--   roles: abs=9, tied+2, tied=base, tied=base, tied+2, abs=3, abs=3, abs=7; 2 instances at bases [8, 9]; all_strict=True; worst realized 833625/903049
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 2). -/
theorem shape_u537_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (13312:ℚ) * m ^ 2 - (22304:ℚ) * m - (48720:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have hshift : (13312:ℚ) * (m - 5) ^ 2 + (110816:ℚ) * (m - 5) + (172560:ℚ) = (13312:ℚ) * m ^ 2 - (22304:ℚ) * m - (48720:ℚ) := by ring
  linarith [ht, h2, hshift]
#print axioms shape_u537_uniform
-- u538 [4-edge cycle] 2->3->4->1->(closed) | cand_entry+z_entry+z_entry+z_entry
--   roles: abs=13, abs=13, abs=9, abs=9, abs=13, abs=1, abs=1, abs=9; 1 instances at bases [9]; all_strict=True; worst realized 719415/753239
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u538_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (236768:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u538_uniform
-- u539 [4-edge cycle] 2->3->4->1->(closed) | cand_entry+z_entry+z_entry+z_entry
--   roles: abs=11, abs=12, abs=10, abs=10, abs=12, abs=4, abs=4, abs=9; 1 instances at bases [10]; all_strict=True; worst realized 6309171/6746995
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u539_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (1313472:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u539_uniform
-- u540 [4-edge cycle] 2->3->4->1->(closed) | cand_irred+z_entry+z_entry+z_entry
--   roles: tied+2, abs=6, tied=base, tied=base, tied+2, abs=2, abs=2, abs=5; 2 instances at bases [5, 6]; all_strict=True; worst realized 28577/28665
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 2). -/
theorem shape_u540_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (2432:ℚ) * m ^ 2 - (6896:ℚ) * m - (21480:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have hshift : (2432:ℚ) * (m - 5) ^ 2 + (17424:ℚ) * (m - 5) + (4840:ℚ) = (2432:ℚ) * m ^ 2 - (6896:ℚ) * m - (21480:ℚ) := by ring
  linarith [ht, h2, hshift]
#print axioms shape_u540_uniform
-- u541 [4-edge cycle] 2->3->4->1->(closed) | cand_irred+z_entry+z_entry+z_entry
--   roles: abs=12, abs=8, abs=8, abs=8, abs=12, abs=1, abs=1, abs=6; 1 instances at bases [8]; all_strict=True; worst realized 1
/-- pattern tau=(): D ≡ 0 identically (weak kill: P ≡ 1 with the strict candidate edge); A and B coincide as polynomials. -/
theorem shape_u541_uniform : ∀ m : ℚ, 5 ≤ m → (2723175:ℚ) = (2723175:ℚ) := fun _ _ => rfl
#print axioms shape_u541_uniform
-- u542 [4-edge cycle] 2->3->4->1->(closed) | cand_irred+z_entry+z_entry+z_entry
--   roles: abs=13, abs=12, abs=9, abs=9, abs=13, abs=1, abs=1, abs=9; 1 instances at bases [9]; all_strict=True; worst realized 47961/48209
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u542_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (25544:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u542_uniform
-- u543 [4-edge cycle] 2->3->4->5->(closed) | cand_entry+z_entry+z_entry+z_entry
--   roles: abs=3, abs=7, abs=5, abs=5, abs=5, abs=5, abs=7, abs=2; 1 instances at bases [5]; all_strict=True; worst realized 542963/641355
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u543_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (295176:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u543_uniform
-- u544 [4-edge cycle] 2->4->5->1->(closed) | cand_entry+z_entry+z_entry+z_entry
--   roles: abs=9, abs=9, abs=7, abs=7, abs=9, abs=3, abs=3, abs=7; 1 instances at bases [7]; all_strict=True; worst realized 1185885/1275373
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u544_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (447440:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u544_uniform
-- u545 [4-edge cycle] 2->4->5->1->(closed) | cand_entry+z_entry+z_entry+z_irred
--   roles: abs=4, abs=7, abs=5, abs=5, abs=7, abs=2, abs=3, abs=2; 1 instances at bases [5]; all_strict=True; worst realized 17917/22165
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u545_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (216648:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u545_uniform
-- u546 [4-edge cycle] 2->4->5->1->(closed) | cand_entry+z_entry+z_entry+z_irred
--   roles: abs=5, abs=7, abs=5, abs=5, abs=7, abs=2, abs=4, abs=2; 1 instances at bases [5]; all_strict=True; worst realized 24149/27885
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u546_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (190536:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u546_uniform
-- u547 [4-edge cycle] 2->4->5->1->(closed) | cand_entry+z_entry+z_entry+z_irred
--   roles: abs=6, abs=7, abs=5, abs=5, abs=7, abs=2, abs=5, abs=2; 1 instances at bases [5]; all_strict=True; worst realized 2337/2585
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u547_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (164424:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u547_uniform
-- u548 [4-edge cycle] 2->4->5->1->(closed) | cand_entry+z_entry+z_entry+z_irred
--   roles: abs=6, abs=9, abs=6, abs=6, abs=9, abs=2, abs=5, abs=2; 1 instances at bases [6]; all_strict=True; worst realized 139503/156839
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u548_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (294712:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u548_uniform
-- u549 [4-edge cycle] 2->4->5->1->(closed) | cand_entry+z_entry+z_irred+z_irred
--   roles: abs=8, abs=8, abs=6, abs=6, abs=2, abs=7, abs=7, abs=2; 1 instances at bases [6]; all_strict=True; worst realized 125125/136629
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u549_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (241584:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u549_uniform
-- u550 [4-edge cycle] 2->4->5->1->(closed) | cand_entry+z_entry+z_irred+z_irred
--   roles: tied+2, tied+2, tied=base, tied=base, abs=3, tied+1, tied+1, abs=3; 2 instances at bases [9, 10]; all_strict=True; worst realized 11805049/12508425
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 3). -/
theorem shape_u550_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (1024:ℚ) * m ^ 3 - (4112:ℚ) * m - (6112:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have h3 : (0:ℚ) ≤ (m - 5) ^ 3 := by nlinarith
  have hshift : (1024:ℚ) * (m - 5) ^ 3 + (15360:ℚ) * (m - 5) ^ 2 + (72688:ℚ) * (m - 5) + (101328:ℚ) = (1024:ℚ) * m ^ 3 - (4112:ℚ) * m - (6112:ℚ) := by ring
  linarith [ht, h2, h3, hshift]
#print axioms shape_u550_uniform
-- u551 [4-edge cycle] 2->4->5->1->(closed) | cand_progress+z_entry+z_entry+z_entry
--   roles: abs=10, abs=8, abs=7, abs=7, abs=11, abs=1, abs=1, abs=6; 1 instances at bases [7]; all_strict=True; worst realized 96957/103675
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u551_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (141078:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u551_uniform
-- u552 [4-edge cycle] 2->4->5->1->(closed) | cand_progress+z_entry+z_entry+z_irred
--   roles: abs=14, abs=12, abs=10, abs=10, abs=15, abs=1, abs=12, abs=1; 1 instances at bases [10]; all_strict=True; worst realized 869535/911897
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u552_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (381258:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u552_uniform
-- u553 [4-edge cycle] 2->4->5->1->(closed) | cand_progress+z_entry+z_irred+z_progress
--   roles: abs=7, abs=5, abs=5, abs=5, abs=1, abs=6, abs=5, abs=1; 1 instances at bases [5]; all_strict=True; worst realized 779/819
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u553_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (34440:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u553_uniform
-- u554 [4-edge cycle] 2->4->5->6->(closed) | cand_entry+z_entry+z_entry+z_entry
--   roles: abs=4, tied+2, tied=base, tied=base, tied+1, tied+1, tied+2, abs=3; 3 instances at bases [5, 6]; all_strict=True; worst realized 190855/208351
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 3). -/
theorem shape_u554_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (3072:ℚ) * m ^ 3 - (1536:ℚ) * m ^ 2 - (15216:ℚ) * m - (7080:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have h3 : (0:ℚ) ≤ (m - 5) ^ 3 := by nlinarith
  have hshift : (3072:ℚ) * (m - 5) ^ 3 + (44544:ℚ) * (m - 5) ^ 2 + (199824:ℚ) * (m - 5) + (262440:ℚ) = (3072:ℚ) * m ^ 3 - (1536:ℚ) * m ^ 2 - (15216:ℚ) * m - (7080:ℚ) := by ring
  linarith [ht, h2, h3, hshift]
#print axioms shape_u554_uniform
-- u555 [4-edge cycle] 2->4->5->6->(closed) | cand_entry+z_entry+z_entry+z_entry
--   roles: abs=5, abs=9, abs=7, abs=7, abs=8, abs=8, abs=9, abs=4; 2 instances at bases [7]; all_strict=True; worst realized 1387/1491
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u555_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (669240:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u555_uniform
-- u556 [4-edge cycle] 2->4->5->6->(closed) | cand_entry+z_entry+z_entry+z_irred
--   roles: abs=3, free+2..+3, tied=base, tied=base, tied+1, tied+1, abs=2, tied+1; 3 instances at bases [5, 6]; all_strict=True; worst realized 10731/11891
/-- pattern tau=(2): real half-line form, mono certificate (kind ALL, strict=True, deg D = 3). -/
theorem shape_u556_pat1_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (4096:ℚ) * m ^ 3 - (3840:ℚ) * m ^ 2 - (12832:ℚ) * m - (3744:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have h3 : (0:ℚ) ≤ (m - 5) ^ 3 := by nlinarith
  have hshift : (4096:ℚ) * (m - 5) ^ 3 + (57600:ℚ) * (m - 5) ^ 2 + (255968:ℚ) * (m - 5) + (348096:ℚ) = (4096:ℚ) * m ^ 3 - (3840:ℚ) * m ^ 2 - (12832:ℚ) * m - (3744:ℚ) := by ring
  linarith [ht, h2, h3, hshift]
#print axioms shape_u556_pat1_uniform
/-- pattern tau=(3): real half-line form, mono certificate (kind ALL, strict=True, deg D = 3). -/
theorem shape_u556_pat2_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (4096:ℚ) * m ^ 3 - (11520:ℚ) * m ^ 2 - (22432:ℚ) * m - (4824:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have h3 : (0:ℚ) ≤ (m - 5) ^ 3 := by nlinarith
  have hshift : (4096:ℚ) * (m - 5) ^ 3 + (49920:ℚ) * (m - 5) ^ 2 + (169568:ℚ) * (m - 5) + (107016:ℚ) = (4096:ℚ) * m ^ 3 - (11520:ℚ) * m ^ 2 - (22432:ℚ) * m - (4824:ℚ) := by ring
  linarith [ht, h2, h3, hshift]
#print axioms shape_u556_pat2_uniform
-- u557 [4-edge cycle] 2->4->5->6->(closed) | cand_entry+z_entry+z_entry+z_irred
--   roles: abs=4, tied+2, tied=base, tied=base, tied+1, tied+1, abs=3, tied+1; 6 instances at bases [5, 6]; all_strict=True; worst realized 17917/18941
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 3). -/
theorem shape_u557_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (4096:ℚ) * m ^ 3 - (9984:ℚ) * m ^ 2 - (21280:ℚ) * m - (5472:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have h3 : (0:ℚ) ≤ (m - 5) ^ 3 := by nlinarith
  have hshift : (4096:ℚ) * (m - 5) ^ 3 + (51456:ℚ) * (m - 5) ^ 2 + (186080:ℚ) * (m - 5) + (150528:ℚ) = (4096:ℚ) * m ^ 3 - (9984:ℚ) * m ^ 2 - (21280:ℚ) * m - (5472:ℚ) := by ring
  linarith [ht, h2, h3, hshift]
#print axioms shape_u557_uniform
-- u558 [4-edge cycle] 2->4->5->6->(closed) | cand_entry+z_entry+z_entry+z_irred
--   roles: abs=2, abs=9, abs=6, abs=6, abs=7, abs=7, abs=1, abs=7; 1 instances at bases [6]; all_strict=True; worst realized 25039/38775
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u558_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (782952:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u558_uniform
-- u559 [4-edge cycle] 2->4->5->6->(closed) | cand_entry+z_entry+z_entry+z_irred
--   roles: free+2..+4, free+2..+4, tied=base, tied=base, tied+1, tied+1, tied=base, tied+1; 25 instances at bases [8, 9, 10]; all_strict=True; worst realized 2619/2755
/-- pattern tau=(2,2): real half-line form, mono certificate (kind ALL, strict=True, deg D = 3). -/
theorem shape_u559_pat1_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (2048:ℚ) * m ^ 3 + (7680:ℚ) * m ^ 2 + (5344:ℚ) * m - (792:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have h3 : (0:ℚ) ≤ (m - 5) ^ 3 := by nlinarith
  have hshift : (2048:ℚ) * (m - 5) ^ 3 + (38400:ℚ) * (m - 5) ^ 2 + (235744:ℚ) * (m - 5) + (473928:ℚ) = (2048:ℚ) * m ^ 3 + (7680:ℚ) * m ^ 2 + (5344:ℚ) * m - (792:ℚ) := by ring
  linarith [ht, h2, h3, hshift]
#print axioms shape_u559_pat1_uniform
/-- pattern tau=(3,3): real half-line form, mono certificate (kind ALL, strict=True, deg D = 3). -/
theorem shape_u559_pat2_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (2048:ℚ) * m ^ 3 + (10752:ℚ) * m ^ 2 + (8416:ℚ) * m - (1224:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have h3 : (0:ℚ) ≤ (m - 5) ^ 3 := by nlinarith
  have hshift : (2048:ℚ) * (m - 5) ^ 3 + (41472:ℚ) * (m - 5) ^ 2 + (269536:ℚ) * (m - 5) + (565656:ℚ) = (2048:ℚ) * m ^ 3 + (10752:ℚ) * m ^ 2 + (8416:ℚ) * m - (1224:ℚ) := by ring
  linarith [ht, h2, h3, hshift]
#print axioms shape_u559_pat2_uniform
/-- pattern tau=(4,4): real half-line form, mono certificate (kind ALL, strict=True, deg D = 3). -/
theorem shape_u559_pat3_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (2048:ℚ) * m ^ 3 + (13824:ℚ) * m ^ 2 + (11488:ℚ) * m - (1656:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have h3 : (0:ℚ) ≤ (m - 5) ^ 3 := by nlinarith
  have hshift : (2048:ℚ) * (m - 5) ^ 3 + (44544:ℚ) * (m - 5) ^ 2 + (303328:ℚ) * (m - 5) + (657384:ℚ) = (2048:ℚ) * m ^ 3 + (13824:ℚ) * m ^ 2 + (11488:ℚ) * m - (1656:ℚ) := by ring
  linarith [ht, h2, h3, hshift]
#print axioms shape_u559_pat3_uniform
-- u560 [4-edge cycle] 2->4->5->6->(closed) | cand_entry+z_entry+z_entry+z_irred
--   roles: abs=11, abs=14, abs=10, abs=10, abs=11, abs=11, abs=8, abs=11; 1 instances at bases [10]; all_strict=True; worst realized 64071/66439
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u560_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (1896768:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u560_uniform
-- u561 [4-edge cycle] 2->4->5->6->(closed) | cand_progress+z_entry+z_entry+z_irred
--   roles: tied+3, tied+1, tied=base, tied=base, tied+1, tied+1, tied+1, tied+4; 2 instances at bases [6, 7]; all_strict=True; worst realized 4617/4895
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 3). -/
theorem shape_u561_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (3072:ℚ) * m ^ 3 + (2432:ℚ) * m ^ 2 - (4400:ℚ) * m - (3654:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have h3 : (0:ℚ) ≤ (m - 5) ^ 3 := by nlinarith
  have hshift : (3072:ℚ) * (m - 5) ^ 3 + (48512:ℚ) * (m - 5) ^ 2 + (250320:ℚ) * (m - 5) + (419146:ℚ) = (3072:ℚ) * m ^ 3 + (2432:ℚ) * m ^ 2 - (4400:ℚ) * m - (3654:ℚ) := by ring
  linarith [ht, h2, h3, hshift]
#print axioms shape_u561_uniform
-- u562 [4-edge cycle] 2->4->5->6->(closed) | cand_progress+z_entry+z_entry+z_irred
--   roles: abs=11, abs=8, abs=9, abs=9, abs=10, abs=10, abs=7, abs=10; 1 instances at bases [9]; all_strict=True; worst realized 71467/72917
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u562_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (587250:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u562_uniform
-- u563 [4-edge cycle] 2->5->1->3->(closed) | cand_entry+z_entry+z_entry+z_entry
--   roles: abs=7, abs=10, abs=10, abs=2, abs=2, abs=8, abs=8, abs=5; 1 instances at bases [7]; all_strict=True; worst realized 27183/30415
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u563_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (436320:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u563_uniform
-- u564 [4-edge cycle] 2->5->1->3->(closed) | cand_entry+z_entry+z_entry+z_entry
--   roles: abs=8, abs=10, abs=10, abs=2, abs=2, abs=8, abs=8, abs=6; 1 instances at bases [7]; all_strict=True; worst realized 221/237
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u564_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (317520:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u564_uniform
-- u565 [4-edge cycle] 2->5->6->1->(closed) | cand_entry+z_entry+z_entry+z_entry
--   roles: abs=9, abs=10, abs=7, abs=7, abs=10, abs=1, abs=1, abs=6; 1 instances at bases [6]; all_strict=True; worst realized 290871/308495
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u565_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (123368:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u565_uniform
-- u566 [4-edge cycle] 2->5->6->1->(closed) | cand_entry+z_entry+z_entry+z_entry
--   roles: abs=13, abs=15, abs=11, abs=11, abs=15, abs=1, abs=1, abs=9; 1 instances at bases [10]; all_strict=True; worst realized 2358411/2488171
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u566_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (389280:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u566_uniform
-- u567 [4-edge cycle] 2->5->6->1->(closed) | cand_entry+z_entry+z_entry+z_irred
--   roles: abs=5, abs=7, abs=6, abs=6, abs=7, abs=3, abs=4, abs=3; 1 instances at bases [5]; all_strict=True; worst realized 28861/33605
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u567_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (355800:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u567_uniform
-- u568 [4-edge cycle] 2->5->6->1->(closed) | cand_entry+z_entry+z_entry+z_irred
--   roles: abs=6, abs=7, abs=6, abs=6, abs=7, abs=3, abs=5, abs=3; 1 instances at bases [5]; all_strict=True; worst realized 108927/121495
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u568_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (314200:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u568_uniform
-- u569 [4-edge cycle] 2->5->6->1->(closed) | cand_entry+z_entry+z_entry+z_irred
--   roles: abs=7, abs=7, abs=6, abs=6, abs=7, abs=3, abs=6, abs=3; 1 instances at bases [5]; all_strict=True; worst realized 2793/3025
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u569_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (272600:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u569_uniform
-- u570 [4-edge cycle] 2->5->6->1->(closed) | cand_entry+z_entry+z_entry+z_irred
--   roles: abs=7, abs=9, abs=7, abs=7, abs=9, abs=2, abs=6, abs=2; 1 instances at bases [6]; all_strict=True; worst realized 195567/214775
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u570_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (326536:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u570_uniform
-- u571 [4-edge cycle] 2->5->6->1->(closed) | cand_entry+z_entry+z_entry+z_irred
--   roles: tied=base, tied+3, tied+1, tied+1, tied+3, abs=2, tied-1, abs=2; 2 instances at bases [8, 9]; all_strict=True; worst realized 494991/532855
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 2). -/
theorem shape_u571_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (4352:ℚ) * m ^ 2 + (28832:ℚ) * m + (31688:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have hshift : (4352:ℚ) * (m - 5) ^ 2 + (72352:ℚ) * (m - 5) + (284648:ℚ) = (4352:ℚ) * m ^ 2 + (28832:ℚ) * m + (31688:ℚ) := by ring
  linarith [ht, h2, hshift]
#print axioms shape_u571_uniform
-- u572 [4-edge cycle] 2->5->6->1->(closed) | cand_entry+z_entry+z_entry+z_irred
--   roles: abs=9, abs=12, abs=10, abs=10, abs=12, abs=3, abs=8, abs=3; 1 instances at bases [9]; all_strict=True; worst realized 494991/532855
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u572_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (946600:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u572_uniform
-- u573 [4-edge cycle] 2->5->6->1->(closed) | cand_entry+z_entry+z_irred+z_irred
--   roles: abs=5, abs=7, abs=6, abs=6, abs=2, abs=6, abs=4, abs=2; 2 instances at bases [5]; all_strict=True; worst realized 8835/10387
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u573_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (228144:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u573_uniform
-- u574 [4-edge cycle] 2->5->6->1->(closed) | cand_entry+z_entry+z_irred+z_irred
--   roles: abs=6, abs=7, abs=6, abs=6, abs=2, abs=6, abs=5, abs=2; 2 instances at bases [5]; all_strict=True; worst realized 33345/37553
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u574_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (206192:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u574_uniform
-- u575 [4-edge cycle] 2->5->6->1->(closed) | cand_entry+z_entry+z_irred+z_irred
--   roles: abs=7, abs=7, abs=6, abs=6, abs=2, abs=6, abs=6, abs=2; 2 instances at bases [5]; all_strict=True; worst realized 171/187
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u575_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (184240:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u575_uniform
-- u576 [4-edge cycle] 2->5->6->1->(closed) | cand_progress+z_entry+z_entry+z_entry
--   roles: abs=9, abs=8, abs=7, abs=7, abs=10, abs=1, abs=1, abs=6; 1 instances at bases [6]; all_strict=True; worst realized 262143/282425
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u576_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (141974:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u576_uniform
-- u577 [4-edge cycle] 2->5->6->3->(closed) | cand_entry+z_entry+z_entry+z_entry
--   roles: abs=2, abs=10, abs=6, abs=6, abs=6, abs=5, abs=7, abs=1; 2 instances at bases [5]; all_strict=True; worst realized 488187/607475
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u577_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (357864:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u577_uniform
-- u578 [4-edge cycle] 2->5->6->3->(closed) | cand_entry+z_entry+z_entry+z_entry
--   roles: abs=4, abs=12, abs=7, abs=7, abs=7, abs=6, abs=11, abs=3; 2 instances at bases [6]; all_strict=True; worst realized 90307/108779
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u578_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (1385400:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u578_uniform
-- u579 [4-edge cycle] 2->5->6->3->(closed) | cand_entry+z_entry+z_entry+z_entry
--   roles: abs=9, abs=10, abs=7, abs=7, abs=7, abs=6, abs=9, abs=8; 2 instances at bases [6]; all_strict=True; worst realized 2941029/3049805
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u579_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (543880:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u579_uniform
-- u580 [4-edge cycle] 2->5->6->3->(closed) | cand_entry+z_entry+z_entry+z_entry
--   roles: abs=9, abs=13, abs=9, abs=9, abs=9, abs=8, abs=12, abs=8; 2 instances at bases [8]; all_strict=True; worst realized 6476925/6800309
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u580_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (1616920:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u580_uniform
-- u581 [4-edge cycle] 2->5->6->3->(closed) | cand_entry+z_entry+z_entry+z_irred
--   roles: abs=6, abs=7, abs=6, abs=6, abs=6, abs=5, abs=5, abs=6; 2 instances at bases [5]; all_strict=True; worst realized 91143/103823
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u581_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (621320:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u581_uniform
-- u582 [4-edge cycle] 2->5->6->3->(closed) | cand_entry+z_entry+z_entry+z_irred
--   roles: tied+2, tied+2, tied+1, tied+1, tied+1, tied=base, tied+1, tied+1; 3 instances at bases [5, 6]; all_strict=True; worst realized 91/99
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 3). -/
theorem shape_u582_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (2048:ℚ) * m ^ 3 + (9728:ℚ) * m ^ 2 + (13280:ℚ) * m + (5544:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have h3 : (0:ℚ) ≤ (m - 5) ^ 3 := by nlinarith
  have hshift : (2048:ℚ) * (m - 5) ^ 3 + (40448:ℚ) * (m - 5) ^ 2 + (264160:ℚ) * (m - 5) + (571144:ℚ) = (2048:ℚ) * m ^ 3 + (9728:ℚ) * m ^ 2 + (13280:ℚ) * m + (5544:ℚ) := by ring
  linarith [ht, h2, h3, hshift]
#print axioms shape_u582_uniform
-- u583 [4-edge cycle] 2->6->3->1->(closed) | cand_progress+z_entry+z_entry+z_irred
--   roles: abs=10, abs=7, abs=8, abs=7, abs=9, abs=3, abs=7, abs=3; 1 instances at bases [7]; all_strict=True; worst realized 495/497
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u583_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (25650:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u583_uniform
-- u584 [4-edge cycle] 2->6->3->1->(closed) | cand_progress+z_entry+z_irred+z_progress
--   roles: abs=11, abs=7, abs=9, abs=8, abs=2, abs=9, abs=7, abs=2; 1 instances at bases [8]; all_strict=True; worst realized 86775/88111
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u584_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (76152:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u584_uniform
-- u585 [4-edge cycle] 3->2->1->6->(closed) | cand_irred+z_irred+z_irred+z_entry
--   roles: abs=7, tied+2, abs=2, abs=6, tied+3, abs=2, tied+1, tied=base; 2 instances at bases [7, 8]; all_strict=True; worst realized 518375/532287
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 2). -/
theorem shape_u585_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (512:ℚ) * m ^ 2 + (1536:ℚ) * m + (80152:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have hshift : (512:ℚ) * (m - 5) ^ 2 + (6656:ℚ) * (m - 5) + (100632:ℚ) = (512:ℚ) * m ^ 2 + (1536:ℚ) * m + (80152:ℚ) := by ring
  linarith [ht, h2, hshift]
#print axioms shape_u585_uniform
-- u586 [4-edge cycle] 3->2->5->6->(closed) | cand_entry+z_entry+z_entry+z_entry
--   roles: abs=10, abs=4, abs=3, abs=7, abs=7, abs=7, abs=7, abs=6; 1 instances at bases [6]; all_strict=True; worst realized 477603/499675
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u586_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (242792:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u586_uniform
-- u587 [4-edge cycle] 3->2->5->6->(closed) | cand_irred+z_entry+z_entry+z_entry
--   roles: abs=3, abs=10, abs=2, abs=7, abs=7, abs=7, abs=7, abs=6; 2 instances at bases [6]; all_strict=True; worst realized 406847/408375
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u587_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (13752:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u587_uniform
-- u588 [4-edge cycle] 3->2->5->6->(closed) | cand_irred+z_entry+z_entry+z_entry
--   roles: abs=4, abs=9, abs=3, abs=7, abs=7, abs=7, abs=7, abs=6; 2 instances at bases [6]; all_strict=True; worst realized 4935231/5078975
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u588_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (143744:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u588_uniform
-- u589 [4-edge cycle] 3->2->5->6->(closed) | cand_irred+z_entry+z_entry+z_entry
--   roles: tied=base, tied+2, tied-1, tied+1, tied+1, tied+1, tied+1, tied=base; 3 instances at bases [6, 7]; all_strict=True; worst realized 2494149/2556125
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 3). -/
theorem shape_u589_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (2048:ℚ) * m ^ 3 - (4608:ℚ) * m ^ 2 - (13856:ℚ) * m - (7416:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have h3 : (0:ℚ) ≤ (m - 5) ^ 3 := by nlinarith
  have hshift : (2048:ℚ) * (m - 5) ^ 3 + (26112:ℚ) * (m - 5) ^ 2 + (93664:ℚ) * (m - 5) + (64104:ℚ) = (2048:ℚ) * m ^ 3 - (4608:ℚ) * m ^ 2 - (13856:ℚ) * m - (7416:ℚ) := by ring
  linarith [ht, h2, h3, hshift]
#print axioms shape_u589_uniform
-- u590 [4-edge cycle] 3->2->5->6->(closed) | cand_progress+z_entry+z_entry+z_entry
--   roles: abs=2, abs=7, abs=3, abs=7, abs=6, abs=6, abs=6, abs=5; 1 instances at bases [5]; all_strict=True; worst realized 34153/50807
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u590_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (949278:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u590_uniform
-- u591 [4-edge cycle] 3->2->5->6->(closed) | cand_progress+z_entry+z_entry+z_entry
--   roles: abs=3, abs=7, abs=4, abs=7, abs=6, abs=6, abs=6, abs=5; 1 instances at bases [5]; all_strict=True; worst realized 50225/68479
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u591_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (1040478:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u591_uniform
-- u592 [4-edge cycle] 3->2->5->6->(closed) | cand_progress+z_entry+z_entry+z_entry
--   roles: abs=5, abs=10, abs=4, abs=8, abs=8, abs=8, abs=8, abs=7; 2 instances at bases [7]; all_strict=True; worst realized 3291275/3322053
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u592_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (92334:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u592_uniform
-- u593 [4-edge cycle] 3->4->5->1->(closed) | cand_progress+z_entry+z_entry+z_entry
--   roles: abs=10, abs=10, abs=7, abs=7, abs=10, abs=2, abs=2, abs=8; 2 instances at bases [7]; all_strict=True; worst realized 4199/4345
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u593_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (177390:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u593_uniform
-- u594 [4-edge cycle] 3->4->5->6->(closed) | cand_entry+z_entry+z_entry+z_entry
--   roles: free+1..+6, free+1..+5, tied=base, tied=base, tied+1, tied+1, tied+1, tied=base; 376 instances at bases [5, 6, 7, 8, 9, 10]; all_strict=True; worst realized 7800849/7819625
/-- pattern tau=(1,1): real half-line form, mono certificate (kind ALL, strict=True, deg D = 2). -/
theorem shape_u594_pat1_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (512:ℚ) * m ^ 2 + (128:ℚ) * m - (424:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have hshift : (512:ℚ) * (m - 5) ^ 2 + (5248:ℚ) * (m - 5) + (13016:ℚ) = (512:ℚ) * m ^ 2 + (128:ℚ) * m - (424:ℚ) := by ring
  linarith [ht, h2, hshift]
#print axioms shape_u594_pat1_uniform
/-- pattern tau=(2,1): real half-line form, mono certificate (kind ALL, strict=True, deg D = 3). -/
theorem shape_u594_pat2_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (4096:ℚ) * m ^ 3 + (7168:ℚ) * m ^ 2 + (2368:ℚ) * m - (816:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have h3 : (0:ℚ) ≤ (m - 5) ^ 3 := by nlinarith
  have hshift : (4096:ℚ) * (m - 5) ^ 3 + (68608:ℚ) * (m - 5) ^ 2 + (381248:ℚ) * (m - 5) + (702224:ℚ) = (4096:ℚ) * m ^ 3 + (7168:ℚ) * m ^ 2 + (2368:ℚ) * m - (816:ℚ) := by ring
  linarith [ht, h2, h3, hshift]
#print axioms shape_u594_pat2_uniform
/-- pattern tau=(2,2): real half-line form, mono certificate (kind ALL, strict=True, deg D = 2). -/
theorem shape_u594_pat3_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (1536:ℚ) * m ^ 2 + (1152:ℚ) * m - (888:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have hshift : (1536:ℚ) * (m - 5) ^ 2 + (16512:ℚ) * (m - 5) + (43272:ℚ) = (1536:ℚ) * m ^ 2 + (1152:ℚ) * m - (888:ℚ) := by ring
  linarith [ht, h2, hshift]
#print axioms shape_u594_pat3_uniform
/-- pattern tau=(3,2): real half-line form, mono certificate (kind ALL, strict=True, deg D = 3). -/
theorem shape_u594_pat4_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (4096:ℚ) * m ^ 3 + (8192:ℚ) * m ^ 2 + (3392:ℚ) * m - (1280:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have h3 : (0:ℚ) ≤ (m - 5) ^ 3 := by nlinarith
  have hshift : (4096:ℚ) * (m - 5) ^ 3 + (69632:ℚ) * (m - 5) ^ 2 + (392512:ℚ) * (m - 5) + (732480:ℚ) = (4096:ℚ) * m ^ 3 + (8192:ℚ) * m ^ 2 + (3392:ℚ) * m - (1280:ℚ) := by ring
  linarith [ht, h2, h3, hshift]
#print axioms shape_u594_pat4_uniform
/-- pattern tau=(3,3): real half-line form, mono certificate (kind ALL, strict=True, deg D = 2). -/
theorem shape_u594_pat5_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (2560:ℚ) * m ^ 2 + (2176:ℚ) * m - (1352:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have hshift : (2560:ℚ) * (m - 5) ^ 2 + (27776:ℚ) * (m - 5) + (73528:ℚ) = (2560:ℚ) * m ^ 2 + (2176:ℚ) * m - (1352:ℚ) := by ring
  linarith [ht, h2, hshift]
#print axioms shape_u594_pat5_uniform
/-- pattern tau=(4,3): real half-line form, mono certificate (kind ALL, strict=True, deg D = 3). -/
theorem shape_u594_pat6_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (4096:ℚ) * m ^ 3 + (9216:ℚ) * m ^ 2 + (4416:ℚ) * m - (1744:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have h3 : (0:ℚ) ≤ (m - 5) ^ 3 := by nlinarith
  have hshift : (4096:ℚ) * (m - 5) ^ 3 + (70656:ℚ) * (m - 5) ^ 2 + (403776:ℚ) * (m - 5) + (762736:ℚ) = (4096:ℚ) * m ^ 3 + (9216:ℚ) * m ^ 2 + (4416:ℚ) * m - (1744:ℚ) := by ring
  linarith [ht, h2, h3, hshift]
#print axioms shape_u594_pat6_uniform
/-- pattern tau=(4,4): real half-line form, mono certificate (kind ALL, strict=True, deg D = 2). -/
theorem shape_u594_pat7_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (3584:ℚ) * m ^ 2 + (3200:ℚ) * m - (1816:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have hshift : (3584:ℚ) * (m - 5) ^ 2 + (39040:ℚ) * (m - 5) + (103784:ℚ) = (3584:ℚ) * m ^ 2 + (3200:ℚ) * m - (1816:ℚ) := by ring
  linarith [ht, h2, hshift]
#print axioms shape_u594_pat7_uniform
/-- pattern tau=(5,4): real half-line form, mono certificate (kind ALL, strict=True, deg D = 3). -/
theorem shape_u594_pat8_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (4096:ℚ) * m ^ 3 + (10240:ℚ) * m ^ 2 + (5440:ℚ) * m - (2208:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have h3 : (0:ℚ) ≤ (m - 5) ^ 3 := by nlinarith
  have hshift : (4096:ℚ) * (m - 5) ^ 3 + (71680:ℚ) * (m - 5) ^ 2 + (415040:ℚ) * (m - 5) + (792992:ℚ) = (4096:ℚ) * m ^ 3 + (10240:ℚ) * m ^ 2 + (5440:ℚ) * m - (2208:ℚ) := by ring
  linarith [ht, h2, h3, hshift]
#print axioms shape_u594_pat8_uniform
/-- pattern tau=(5,5): real half-line form, mono certificate (kind ALL, strict=True, deg D = 2). -/
theorem shape_u594_pat9_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (4608:ℚ) * m ^ 2 + (4224:ℚ) * m - (2280:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have hshift : (4608:ℚ) * (m - 5) ^ 2 + (50304:ℚ) * (m - 5) + (134040:ℚ) = (4608:ℚ) * m ^ 2 + (4224:ℚ) * m - (2280:ℚ) := by ring
  linarith [ht, h2, hshift]
#print axioms shape_u594_pat9_uniform
/-- pattern tau=(6,5): real half-line form, mono certificate (kind ALL, strict=True, deg D = 3). -/
theorem shape_u594_pat10_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (4096:ℚ) * m ^ 3 + (11264:ℚ) * m ^ 2 + (6464:ℚ) * m - (2672:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have h3 : (0:ℚ) ≤ (m - 5) ^ 3 := by nlinarith
  have hshift : (4096:ℚ) * (m - 5) ^ 3 + (72704:ℚ) * (m - 5) ^ 2 + (426304:ℚ) * (m - 5) + (823248:ℚ) = (4096:ℚ) * m ^ 3 + (11264:ℚ) * m ^ 2 + (6464:ℚ) * m - (2672:ℚ) := by ring
  linarith [ht, h2, h3, hshift]
#print axioms shape_u594_pat10_uniform
-- u595 [4-edge cycle] 3->4->5->6->(closed) | cand_progress+z_entry+z_entry+z_entry
--   roles: free+1..+4, free+1..+4, tied=base, tied=base, tied+1, tied+1, tied+1, tied=base; 101 instances at bases [5, 6, 7, 8, 9, 10]; all_strict=True; worst realized 64881/66439
/-- pattern tau=(1,1): real half-line form, mono certificate (kind ALL, strict=True, deg D = 3). -/
theorem shape_u595_pat1_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (1024:ℚ) * m ^ 3 + (2176:ℚ) * m ^ 2 + (688:ℚ) * m - (522:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have h3 : (0:ℚ) ≤ (m - 5) ^ 3 := by nlinarith
  have hshift : (1024:ℚ) * (m - 5) ^ 3 + (17536:ℚ) * (m - 5) ^ 2 + (99248:ℚ) * (m - 5) + (185318:ℚ) = (1024:ℚ) * m ^ 3 + (2176:ℚ) * m ^ 2 + (688:ℚ) * m - (522:ℚ) := by ring
  linarith [ht, h2, h3, hshift]
#print axioms shape_u595_pat1_uniform
/-- pattern tau=(2,2): real half-line form, mono certificate (kind ALL, strict=True, deg D = 3). -/
theorem shape_u595_pat2_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (1024:ℚ) * m ^ 3 + (3200:ℚ) * m ^ 2 + (1712:ℚ) * m - (986:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have h3 : (0:ℚ) ≤ (m - 5) ^ 3 := by nlinarith
  have hshift : (1024:ℚ) * (m - 5) ^ 3 + (18560:ℚ) * (m - 5) ^ 2 + (110512:ℚ) * (m - 5) + (215574:ℚ) = (1024:ℚ) * m ^ 3 + (3200:ℚ) * m ^ 2 + (1712:ℚ) * m - (986:ℚ) := by ring
  linarith [ht, h2, h3, hshift]
#print axioms shape_u595_pat2_uniform
/-- pattern tau=(3,3): real half-line form, mono certificate (kind ALL, strict=True, deg D = 3). -/
theorem shape_u595_pat3_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (1024:ℚ) * m ^ 3 + (4224:ℚ) * m ^ 2 + (2736:ℚ) * m - (1450:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have h3 : (0:ℚ) ≤ (m - 5) ^ 3 := by nlinarith
  have hshift : (1024:ℚ) * (m - 5) ^ 3 + (19584:ℚ) * (m - 5) ^ 2 + (121776:ℚ) * (m - 5) + (245830:ℚ) = (1024:ℚ) * m ^ 3 + (4224:ℚ) * m ^ 2 + (2736:ℚ) * m - (1450:ℚ) := by ring
  linarith [ht, h2, h3, hshift]
#print axioms shape_u595_pat3_uniform
/-- pattern tau=(4,4): real half-line form, mono certificate (kind ALL, strict=True, deg D = 3). -/
theorem shape_u595_pat4_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (1024:ℚ) * m ^ 3 + (5248:ℚ) * m ^ 2 + (3760:ℚ) * m - (1914:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have h3 : (0:ℚ) ≤ (m - 5) ^ 3 := by nlinarith
  have hshift : (1024:ℚ) * (m - 5) ^ 3 + (20608:ℚ) * (m - 5) ^ 2 + (133040:ℚ) * (m - 5) + (276086:ℚ) = (1024:ℚ) * m ^ 3 + (5248:ℚ) * m ^ 2 + (3760:ℚ) * m - (1914:ℚ) := by ring
  linarith [ht, h2, h3, hshift]
#print axioms shape_u595_pat4_uniform
-- u596 [4-edge cycle] 3->5->1->2->(closed) | cand_progress+z_irred+z_irred+z_irred
--   roles: abs=14, abs=14, abs=1, abs=11, abs=13, abs=1, abs=14, abs=13; 1 instances at bases [10]; all_strict=True; worst realized 3811/4005
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u596_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (460362:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u596_uniform
-- u597 [4-edge cycle] 3->5->6->2->(closed) | cand_progress+z_entry+z_irred+z_progress
--   roles: abs=10, abs=10, abs=9, abs=9, abs=6, abs=9, abs=10, abs=7; 4 instances at bases [8]; all_strict=True; worst realized 1269/1349
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u597_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (1419120:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u597_uniform
-- u598 [4-edge cycle] 3->6->2->1->(closed) | cand_progress+z_irred+z_irred+z_progress
--   roles: abs=9, abs=8, abs=2, abs=7, abs=2, abs=2, abs=8, abs=2; 1 instances at bases [6]; all_strict=True; worst realized 5475/5491
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u598_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (3120:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u598_uniform
-- u599 [4-edge cycle] 4->1->6->3->(closed) | cand_progress+z_entry+z_entry+z_entry
--   roles: tied-3, tied+2, tied-2, tied+2, tied+1, tied=base, tied=base, tied=base; 10 instances at bases [5, 6, 7, 8, 9, 10]; all_strict=True; worst realized 13851/16037
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 3). -/
theorem shape_u599_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (5120:ℚ) * m ^ 3 + (6784:ℚ) * m ^ 2 - (7568:ℚ) * m + (2414:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have h3 : (0:ℚ) ≤ (m - 5) ^ 3 := by nlinarith
  have hshift : (5120:ℚ) * (m - 5) ^ 3 + (83584:ℚ) * (m - 5) ^ 2 + (444272:ℚ) * (m - 5) + (774174:ℚ) = (5120:ℚ) * m ^ 3 + (6784:ℚ) * m ^ 2 - (7568:ℚ) * m + (2414:ℚ) := by ring
  linarith [ht, h2, h3, hshift]
#print axioms shape_u599_uniform
-- u600 [4-edge cycle] 4->1->6->3->(closed) | cand_progress+z_entry+z_entry+z_entry
--   roles: tied-2, tied+2, tied-1, tied+2, tied+1, tied=base, tied=base, tied=base; 3 instances at bases [5, 6, 7]; all_strict=True; worst realized 14801/18095
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 3). -/
theorem shape_u600_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (5120:ℚ) * m ^ 3 + (8832:ℚ) * m ^ 2 - (3728:ℚ) * m + (1326:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have h3 : (0:ℚ) ≤ (m - 5) ^ 3 := by nlinarith
  have hshift : (5120:ℚ) * (m - 5) ^ 3 + (85632:ℚ) * (m - 5) ^ 2 + (468592:ℚ) * (m - 5) + (843486:ℚ) = (5120:ℚ) * m ^ 3 + (8832:ℚ) * m ^ 2 - (3728:ℚ) * m + (1326:ℚ) := by ring
  linarith [ht, h2, h3, hshift]
#print axioms shape_u600_uniform
-- u601 [4-edge cycle] 4->1->6->3->(closed) | cand_progress+z_entry+z_entry+z_entry
--   roles: tied-4, tied+2, tied-3, tied+2, tied+1, tied=base, tied=base, tied=base; 7 instances at bases [7, 8, 9, 10]; all_strict=True; worst realized 107163/126005
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 3). -/
theorem shape_u601_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (5120:ℚ) * m ^ 3 + (4736:ℚ) * m ^ 2 - (11408:ℚ) * m + (3502:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have h3 : (0:ℚ) ≤ (m - 5) ^ 3 := by nlinarith
  have hshift : (5120:ℚ) * (m - 5) ^ 3 + (81536:ℚ) * (m - 5) ^ 2 + (419952:ℚ) * (m - 5) + (704862:ℚ) = (5120:ℚ) * m ^ 3 + (4736:ℚ) * m ^ 2 - (11408:ℚ) * m + (3502:ℚ) := by ring
  linarith [ht, h2, h3, hshift]
#print axioms shape_u601_uniform
-- u602 [4-edge cycle] 4->1->6->3->(closed) | cand_progress+z_entry+z_entry+z_entry
--   roles: abs=1, tied+3, abs=2, tied+2, tied+1, tied=base, tied=base, tied=base; 4 instances at bases [9, 10]; all_strict=True; worst realized 212139/400925
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 3). -/
theorem shape_u602_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (3072:ℚ) * m ^ 3 + (18816:ℚ) * m ^ 2 + (14640:ℚ) * m - (2778:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have h3 : (0:ℚ) ≤ (m - 5) ^ 3 := by nlinarith
  have hshift : (3072:ℚ) * (m - 5) ^ 3 + (64896:ℚ) * (m - 5) ^ 2 + (433200:ℚ) * (m - 5) + (924822:ℚ) = (3072:ℚ) * m ^ 3 + (18816:ℚ) * m ^ 2 + (14640:ℚ) * m - (2778:ℚ) := by ring
  linarith [ht, h2, h3, hshift]
#print axioms shape_u602_uniform
-- u603 [4-edge cycle] 4->1->6->3->(closed) | cand_progress+z_entry+z_entry+z_entry
--   roles: tied-5, tied+2, tied-4, tied+2, tied+1, tied=base, tied=base, tied=base; 2 instances at bases [9, 10]; all_strict=True; worst realized 89667/107677
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 3). -/
theorem shape_u603_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (5120:ℚ) * m ^ 3 + (2688:ℚ) * m ^ 2 - (15248:ℚ) * m + (4590:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have h3 : (0:ℚ) ≤ (m - 5) ^ 3 := by nlinarith
  have hshift : (5120:ℚ) * (m - 5) ^ 3 + (79488:ℚ) * (m - 5) ^ 2 + (395632:ℚ) * (m - 5) + (635550:ℚ) = (5120:ℚ) * m ^ 3 + (2688:ℚ) * m ^ 2 - (15248:ℚ) * m + (4590:ℚ) := by ring
  linarith [ht, h2, h3, hshift]
#print axioms shape_u603_uniform
-- u604 [4-edge cycle] 4->2->6->3->(closed) | cand_progress+z_entry+z_entry+z_entry
--   roles: abs=2, abs=7, abs=3, abs=7, abs=6, abs=5, abs=5, abs=5; 1 instances at bases [5]; all_strict=True; worst realized 28577/42159
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u604_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (774174:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u604_uniform
-- u605 [4-edge cycle] 4->2->6->3->(closed) | cand_progress+z_entry+z_entry+z_entry
--   roles: abs=3, abs=7, abs=4, abs=7, abs=6, abs=5, abs=5, abs=5; 3 instances at bases [5]; all_strict=True; worst realized 42025/56823
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u605_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (843486:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u605_uniform
-- u606 [4-edge cycle] 4->5->6->1->(closed) | cand_entry+z_entry+z_entry+z_entry
--   roles: free+4..+6, free+4..+5, abs=7, abs=7, abs=10, abs=1, abs=1, abs=7; 8 instances at bases [6]; all_strict=True; worst realized 2368521/2402785
/-- pattern tau=(4,4): real half-line form, mono certificate (kind ALL, strict=True, deg D = 1). -/
theorem shape_u606_pat1_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (9392:ℚ) * m - (22088:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have hshift : (9392:ℚ) * (m - 5) + (24872:ℚ) = (9392:ℚ) * m - (22088:ℚ) := by ring
  linarith [ht, hshift]
#print axioms shape_u606_pat1_uniform
/-- pattern tau=(5,4): real half-line form, mono certificate (kind ALL, strict=True, deg D = 1). -/
theorem shape_u606_pat2_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (9392:ℚ) * m + (221232:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have hshift : (9392:ℚ) * (m - 5) + (268192:ℚ) = (9392:ℚ) * m + (221232:ℚ) := by ring
  linarith [ht, hshift]
#print axioms shape_u606_pat2_uniform
/-- pattern tau=(5,5): real half-line form, mono certificate (kind ALL, strict=True, deg D = 1). -/
theorem shape_u606_pat3_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (9392:ℚ) * m - (12696:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have hshift : (9392:ℚ) * (m - 5) + (34264:ℚ) = (9392:ℚ) * m - (12696:ℚ) := by ring
  linarith [ht, hshift]
#print axioms shape_u606_pat3_uniform
/-- pattern tau=(6,5): real half-line form, mono certificate (kind ALL, strict=True, deg D = 1). -/
theorem shape_u606_pat4_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (9392:ℚ) * m + (230624:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have hshift : (9392:ℚ) * (m - 5) + (277584:ℚ) = (9392:ℚ) * m + (230624:ℚ) := by ring
  linarith [ht, hshift]
#print axioms shape_u606_pat4_uniform
-- u607 [4-edge cycle] 4->5->6->2->(closed) | cand_progress+z_entry+z_irred+z_progress
--   roles: abs=9, abs=9, abs=7, abs=7, abs=6, abs=7, abs=9, abs=8; 1 instances at bases [6]; all_strict=True; worst realized 3431/3575
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u607_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (599184:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u607_uniform
-- u608 [4-edge cycle] 4->5->6->2->(closed) | cand_progress+z_entry+z_irred+z_progress
--   roles: abs=13, abs=13, abs=10, abs=10, abs=9, abs=10, abs=13, abs=12; 1 instances at bases [9]; all_strict=True; worst realized 7455/7663
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u608_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (1769040:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u608_uniform
-- u609 [4-edge cycle] 4->5->6->3->(closed) | cand_entry+z_entry+z_entry+z_entry
--   roles: free+2..+7, free+2..+6, tied+1, tied+1, tied+1, tied=base, tied=base, tied=base; 716 instances at bases [5, 6, 7, 8, 9, 10]; all_strict=True; worst realized 6293457/6311705
/-- pattern tau=(2,2): real half-line form, mono certificate (kind ALL, strict=True, deg D = 2). -/
theorem shape_u609_pat1_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (1536:ℚ) * m ^ 2 + (1152:ℚ) * m - (888:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have hshift : (1536:ℚ) * (m - 5) ^ 2 + (16512:ℚ) * (m - 5) + (43272:ℚ) = (1536:ℚ) * m ^ 2 + (1152:ℚ) * m - (888:ℚ) := by ring
  linarith [ht, h2, hshift]
#print axioms shape_u609_pat1_uniform
/-- pattern tau=(3,2): real half-line form, mono certificate (kind ALL, strict=True, deg D = 3). -/
theorem shape_u609_pat2_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (4096:ℚ) * m ^ 3 + (8192:ℚ) * m ^ 2 + (3392:ℚ) * m - (1280:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have h3 : (0:ℚ) ≤ (m - 5) ^ 3 := by nlinarith
  have hshift : (4096:ℚ) * (m - 5) ^ 3 + (69632:ℚ) * (m - 5) ^ 2 + (392512:ℚ) * (m - 5) + (732480:ℚ) = (4096:ℚ) * m ^ 3 + (8192:ℚ) * m ^ 2 + (3392:ℚ) * m - (1280:ℚ) := by ring
  linarith [ht, h2, h3, hshift]
#print axioms shape_u609_pat2_uniform
/-- pattern tau=(3,3): real half-line form, mono certificate (kind ALL, strict=True, deg D = 2). -/
theorem shape_u609_pat3_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (2560:ℚ) * m ^ 2 + (2176:ℚ) * m - (1352:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have hshift : (2560:ℚ) * (m - 5) ^ 2 + (27776:ℚ) * (m - 5) + (73528:ℚ) = (2560:ℚ) * m ^ 2 + (2176:ℚ) * m - (1352:ℚ) := by ring
  linarith [ht, h2, hshift]
#print axioms shape_u609_pat3_uniform
/-- pattern tau=(4,3): real half-line form, mono certificate (kind ALL, strict=True, deg D = 3). -/
theorem shape_u609_pat4_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (4096:ℚ) * m ^ 3 + (9216:ℚ) * m ^ 2 + (4416:ℚ) * m - (1744:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have h3 : (0:ℚ) ≤ (m - 5) ^ 3 := by nlinarith
  have hshift : (4096:ℚ) * (m - 5) ^ 3 + (70656:ℚ) * (m - 5) ^ 2 + (403776:ℚ) * (m - 5) + (762736:ℚ) = (4096:ℚ) * m ^ 3 + (9216:ℚ) * m ^ 2 + (4416:ℚ) * m - (1744:ℚ) := by ring
  linarith [ht, h2, h3, hshift]
#print axioms shape_u609_pat4_uniform
/-- pattern tau=(4,4): real half-line form, mono certificate (kind ALL, strict=True, deg D = 2). -/
theorem shape_u609_pat5_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (3584:ℚ) * m ^ 2 + (3200:ℚ) * m - (1816:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have hshift : (3584:ℚ) * (m - 5) ^ 2 + (39040:ℚ) * (m - 5) + (103784:ℚ) = (3584:ℚ) * m ^ 2 + (3200:ℚ) * m - (1816:ℚ) := by ring
  linarith [ht, h2, hshift]
#print axioms shape_u609_pat5_uniform
/-- pattern tau=(5,4): real half-line form, mono certificate (kind ALL, strict=True, deg D = 3). -/
theorem shape_u609_pat6_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (4096:ℚ) * m ^ 3 + (10240:ℚ) * m ^ 2 + (5440:ℚ) * m - (2208:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have h3 : (0:ℚ) ≤ (m - 5) ^ 3 := by nlinarith
  have hshift : (4096:ℚ) * (m - 5) ^ 3 + (71680:ℚ) * (m - 5) ^ 2 + (415040:ℚ) * (m - 5) + (792992:ℚ) = (4096:ℚ) * m ^ 3 + (10240:ℚ) * m ^ 2 + (5440:ℚ) * m - (2208:ℚ) := by ring
  linarith [ht, h2, h3, hshift]
#print axioms shape_u609_pat6_uniform
/-- pattern tau=(5,5): real half-line form, mono certificate (kind ALL, strict=True, deg D = 2). -/
theorem shape_u609_pat7_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (4608:ℚ) * m ^ 2 + (4224:ℚ) * m - (2280:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have hshift : (4608:ℚ) * (m - 5) ^ 2 + (50304:ℚ) * (m - 5) + (134040:ℚ) = (4608:ℚ) * m ^ 2 + (4224:ℚ) * m - (2280:ℚ) := by ring
  linarith [ht, h2, hshift]
#print axioms shape_u609_pat7_uniform
/-- pattern tau=(6,5): real half-line form, mono certificate (kind ALL, strict=True, deg D = 3). -/
theorem shape_u609_pat8_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (4096:ℚ) * m ^ 3 + (11264:ℚ) * m ^ 2 + (6464:ℚ) * m - (2672:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have h3 : (0:ℚ) ≤ (m - 5) ^ 3 := by nlinarith
  have hshift : (4096:ℚ) * (m - 5) ^ 3 + (72704:ℚ) * (m - 5) ^ 2 + (426304:ℚ) * (m - 5) + (823248:ℚ) = (4096:ℚ) * m ^ 3 + (11264:ℚ) * m ^ 2 + (6464:ℚ) * m - (2672:ℚ) := by ring
  linarith [ht, h2, h3, hshift]
#print axioms shape_u609_pat8_uniform
/-- pattern tau=(6,6): real half-line form, mono certificate (kind ALL, strict=True, deg D = 2). -/
theorem shape_u609_pat9_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (5632:ℚ) * m ^ 2 + (5248:ℚ) * m - (2744:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have hshift : (5632:ℚ) * (m - 5) ^ 2 + (61568:ℚ) * (m - 5) + (164296:ℚ) = (5632:ℚ) * m ^ 2 + (5248:ℚ) * m - (2744:ℚ) := by ring
  linarith [ht, h2, hshift]
#print axioms shape_u609_pat9_uniform
/-- pattern tau=(7,6): real half-line form, mono certificate (kind ALL, strict=True, deg D = 3). -/
theorem shape_u609_pat10_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (4096:ℚ) * m ^ 3 + (12288:ℚ) * m ^ 2 + (7488:ℚ) * m - (3136:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have h3 : (0:ℚ) ≤ (m - 5) ^ 3 := by nlinarith
  have hshift : (4096:ℚ) * (m - 5) ^ 3 + (73728:ℚ) * (m - 5) ^ 2 + (437568:ℚ) * (m - 5) + (853504:ℚ) = (4096:ℚ) * m ^ 3 + (12288:ℚ) * m ^ 2 + (7488:ℚ) * m - (3136:ℚ) := by ring
  linarith [ht, h2, h3, hshift]
#print axioms shape_u609_pat10_uniform
-- u610 [4-edge cycle] 4->5->6->3->(closed) | cand_progress+z_entry+z_entry+z_entry
--   roles: free+2..+5, free+2..+5, tied+1, tied+1, tied+1, tied=base, tied=base, tied=base; 153 instances at bases [5, 6, 7, 8, 9, 10]; all_strict=True; worst realized 64881/66439
/-- pattern tau=(2,2): real half-line form, mono certificate (kind ALL, strict=True, deg D = 3). -/
theorem shape_u610_pat1_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (1024:ℚ) * m ^ 3 + (3200:ℚ) * m ^ 2 + (1712:ℚ) * m - (986:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have h3 : (0:ℚ) ≤ (m - 5) ^ 3 := by nlinarith
  have hshift : (1024:ℚ) * (m - 5) ^ 3 + (18560:ℚ) * (m - 5) ^ 2 + (110512:ℚ) * (m - 5) + (215574:ℚ) = (1024:ℚ) * m ^ 3 + (3200:ℚ) * m ^ 2 + (1712:ℚ) * m - (986:ℚ) := by ring
  linarith [ht, h2, h3, hshift]
#print axioms shape_u610_pat1_uniform
/-- pattern tau=(3,3): real half-line form, mono certificate (kind ALL, strict=True, deg D = 3). -/
theorem shape_u610_pat2_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (1024:ℚ) * m ^ 3 + (4224:ℚ) * m ^ 2 + (2736:ℚ) * m - (1450:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have h3 : (0:ℚ) ≤ (m - 5) ^ 3 := by nlinarith
  have hshift : (1024:ℚ) * (m - 5) ^ 3 + (19584:ℚ) * (m - 5) ^ 2 + (121776:ℚ) * (m - 5) + (245830:ℚ) = (1024:ℚ) * m ^ 3 + (4224:ℚ) * m ^ 2 + (2736:ℚ) * m - (1450:ℚ) := by ring
  linarith [ht, h2, h3, hshift]
#print axioms shape_u610_pat2_uniform
/-- pattern tau=(4,4): real half-line form, mono certificate (kind ALL, strict=True, deg D = 3). -/
theorem shape_u610_pat3_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (1024:ℚ) * m ^ 3 + (5248:ℚ) * m ^ 2 + (3760:ℚ) * m - (1914:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have h3 : (0:ℚ) ≤ (m - 5) ^ 3 := by nlinarith
  have hshift : (1024:ℚ) * (m - 5) ^ 3 + (20608:ℚ) * (m - 5) ^ 2 + (133040:ℚ) * (m - 5) + (276086:ℚ) = (1024:ℚ) * m ^ 3 + (5248:ℚ) * m ^ 2 + (3760:ℚ) * m - (1914:ℚ) := by ring
  linarith [ht, h2, h3, hshift]
#print axioms shape_u610_pat3_uniform
/-- pattern tau=(5,5): real half-line form, mono certificate (kind ALL, strict=True, deg D = 3). -/
theorem shape_u610_pat4_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (1024:ℚ) * m ^ 3 + (6272:ℚ) * m ^ 2 + (4784:ℚ) * m - (2378:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have h3 : (0:ℚ) ≤ (m - 5) ^ 3 := by nlinarith
  have hshift : (1024:ℚ) * (m - 5) ^ 3 + (21632:ℚ) * (m - 5) ^ 2 + (144304:ℚ) * (m - 5) + (306342:ℚ) = (1024:ℚ) * m ^ 3 + (6272:ℚ) * m ^ 2 + (4784:ℚ) * m - (2378:ℚ) := by ring
  linarith [ht, h2, h3, hshift]
#print axioms shape_u610_pat4_uniform
-- u611 [4-edge cycle] 4->6->2->1->(closed) | cand_entry+z_irred+z_entry+z_entry
--   roles: abs=12, abs=12, abs=7, abs=10, abs=8, abs=3, abs=3, abs=10; 1 instances at bases [9]; all_strict=True; worst realized 26675/27531
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u611_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (346680:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u611_uniform
-- u612 [4-edge cycle] 4->6->2->1->(closed) | cand_progress+z_irred+z_irred+z_progress
--   roles: abs=8, abs=8, abs=3, abs=7, abs=2, abs=3, abs=8, abs=2; 1 instances at bases [6]; all_strict=True; worst realized 299/323
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u612_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (117000:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u612_uniform
-- u613 [4-edge cycle] 4->6->3->2->(closed) | cand_progress+z_entry+z_entry+z_progress
--   roles: abs=10, abs=10, abs=8, abs=7, abs=8, abs=4, abs=10, abs=5; 3 instances at bases [7]; all_strict=True; worst realized 1881/2009
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u613_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (839808:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u613_uniform
-- u614 [4-edge cycle] 4->6->3->2->(closed) | cand_progress+z_entry+z_entry+z_progress
--   roles: abs=12, abs=12, abs=9, abs=8, abs=9, abs=6, abs=12, abs=8; 1 instances at bases [8]; all_strict=True; worst realized 4753/5041
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u614_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (1815840:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u614_uniform
-- u615 [4-edge cycle] 5->1->3->4->(closed) | cand_progress+z_entry+z_entry+z_entry
--   roles: abs=1, tied+3, abs=2, tied+1, tied=base, tied=base, tied=base, tied=base; 4 instances at bases [7, 8]; all_strict=True; worst realized 61685/117747
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 3). -/
theorem shape_u615_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (3072:ℚ) * m ^ 3 + (15744:ℚ) * m ^ 2 - (7248:ℚ) * m + (294:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have h3 : (0:ℚ) ≤ (m - 5) ^ 3 := by nlinarith
  have hshift : (3072:ℚ) * (m - 5) ^ 3 + (61824:ℚ) * (m - 5) ^ 2 + (380592:ℚ) * (m - 5) + (741654:ℚ) = (3072:ℚ) * m ^ 3 + (15744:ℚ) * m ^ 2 - (7248:ℚ) * m + (294:ℚ) := by ring
  linarith [ht, h2, h3, hshift]
#print axioms shape_u615_uniform
-- u616 [4-edge cycle] 5->1->3->4->(closed) | cand_progress+z_entry+z_entry+z_entry
--   roles: tied-2, tied+2, tied-1, tied+1, tied=base, tied=base, tied=base, tied=base; 4 instances at bases [7, 8, 9, 10]; all_strict=True; worst realized 37955385/42981767
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 3). -/
theorem shape_u616_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (5120:ℚ) * m ^ 3 - (1408:ℚ) * m ^ 2 + (4720:ℚ) * m - (18:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have h3 : (0:ℚ) ≤ (m - 5) ^ 3 := by nlinarith
  have hshift : (5120:ℚ) * (m - 5) ^ 3 + (75392:ℚ) * (m - 5) ^ 2 + (374640:ℚ) * (m - 5) + (628382:ℚ) = (5120:ℚ) * m ^ 3 - (1408:ℚ) * m ^ 2 + (4720:ℚ) * m - (18:ℚ) := by ring
  linarith [ht, h2, h3, hshift]
#print axioms shape_u616_uniform
-- u617 [4-edge cycle] 5->1->3->4->(closed) | cand_progress+z_entry+z_entry+z_entry
--   roles: abs=6, tied+2, abs=7, tied+1, tied=base, tied=base, tied=base, tied=base; 3 instances at bases [9, 10]; all_strict=True; worst realized 28612521/33295735
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 3). -/
theorem shape_u617_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (3072:ℚ) * m ^ 3 + (18304:ℚ) * m ^ 2 - (21968:ℚ) * m + (494:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have h3 : (0:ℚ) ≤ (m - 5) ^ 3 := by nlinarith
  have hshift : (3072:ℚ) * (m - 5) ^ 3 + (64384:ℚ) * (m - 5) ^ 2 + (391472:ℚ) * (m - 5) + (732254:ℚ) = (3072:ℚ) * m ^ 3 + (18304:ℚ) * m ^ 2 - (21968:ℚ) * m + (494:ℚ) := by ring
  linarith [ht, h2, h3, hshift]
#print axioms shape_u617_uniform
-- u618 [4-edge cycle] 5->1->3->4->(closed) | cand_progress+z_entry+z_entry+z_entry
--   roles: abs=7, abs=12, abs=8, abs=11, abs=10, abs=10, abs=10, abs=10; 1 instances at bases [10]; all_strict=True; worst realized 3698217/4237639
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u618_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (4854798:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u618_uniform
-- u619 [4-edge cycle] 5->2->1->4->(closed) | cand_progress+z_entry+z_entry+z_entry
--   roles: abs=11, abs=15, abs=12, abs=1, abs=1, abs=11, abs=10, abs=10; 1 instances at bases [10]; all_strict=True; worst realized 5774409/6356735
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u619_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (582326:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u619_uniform
-- u620 [4-edge cycle] 5->2->1->4->(closed) | cand_progress+z_irred+z_progress+z_entry
--   roles: abs=4, abs=9, abs=1, abs=3, abs=8, abs=1, abs=5, abs=5; 2 instances at bases [5]; all_strict=True; worst realized 3157/3285
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u620_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (24960:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u620_uniform
-- u621 [4-edge cycle] 5->2->3->4->(closed) | cand_entry+z_entry+z_entry+z_entry
--   roles: tied+5, tied+1, tied+1, tied+3, tied=base, tied=base, tied=base, tied=base; 2 instances at bases [6, 7]; all_strict=True; worst realized 3330187/3523355
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 3). -/
theorem shape_u621_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (4096:ℚ) * m ^ 3 - (7168:ℚ) * m ^ 2 - (7872:ℚ) * m + (48:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have h3 : (0:ℚ) ≤ (m - 5) ^ 3 := by nlinarith
  have hshift : (4096:ℚ) * (m - 5) ^ 3 + (54272:ℚ) * (m - 5) ^ 2 + (227648:ℚ) * (m - 5) + (293488:ℚ) = (4096:ℚ) * m ^ 3 - (7168:ℚ) * m ^ 2 - (7872:ℚ) * m + (48:ℚ) := by ring
  linarith [ht, h2, h3, hshift]
#print axioms shape_u621_uniform
-- u622 [4-edge cycle] 5->2->3->4->(closed) | cand_progress+z_entry+z_entry+z_entry
--   roles: abs=4, abs=7, abs=5, abs=6, abs=5, abs=5, abs=5, abs=5; 3 instances at bases [5]; all_strict=True; worst realized 906059/1127061
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u622_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (663006:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u622_uniform
-- u623 [4-edge cycle] 5->2->3->4->(closed) | cand_progress+z_entry+z_entry+z_entry
--   roles: abs=5, abs=7, abs=6, abs=6, abs=5, abs=5, abs=5, abs=5; 3 instances at bases [5]; all_strict=True; worst realized 3377129/4074759
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u623_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (697630:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u623_uniform
-- u624 [4-edge cycle] 5->3->1->2->(closed) | cand_entry+z_entry+z_entry+z_entry
--   roles: abs=11, abs=9, abs=8, abs=1, abs=1, abs=2, abs=3, abs=9; 1 instances at bases [5]; all_strict=True; worst realized 90593/98049
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u624_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (67104:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u624_uniform
-- u625 [4-edge cycle] 5->3->1->2->(closed) | cand_progress+z_entry+z_entry+z_entry
--   roles: abs=9, abs=10, abs=8, abs=1, abs=1, abs=2, abs=3, abs=9; 1 instances at bases [5]; all_strict=True; worst realized 90593/91287
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u625_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (6246:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u625_uniform
-- u626 [4-edge cycle] 5->4->1->2->(closed) | cand_entry+z_entry+z_entry+z_entry
--   roles: abs=12, abs=11, abs=11, abs=4, abs=4, abs=7, abs=7, abs=10; 1 instances at bases [9]; all_strict=True; worst realized 21627/22475
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u626_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (531696:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u626_uniform
-- u627 [4-edge cycle] 5->6->2->1->(closed) | cand_progress+z_irred+z_irred+z_progress
--   roles: tied+2, tied+2, tied-3, tied+1, abs=3, tied-3, tied+2, abs=3; 2 instances at bases [6, 7]; all_strict=True; worst realized 52049/53625
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 3). -/
theorem shape_u627_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (1024:ℚ) * m ^ 3 - (8448:ℚ) * m ^ 2 + (14224:ℚ) * m + (78200:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have h3 : (0:ℚ) ≤ (m - 5) ^ 3 := by nlinarith
  have hshift : (1024:ℚ) * (m - 5) ^ 3 + (6912:ℚ) * (m - 5) ^ 2 + (6544:ℚ) * (m - 5) + (66120:ℚ) = (1024:ℚ) * m ^ 3 - (8448:ℚ) * m ^ 2 + (14224:ℚ) * m + (78200:ℚ) := by ring
  linarith [ht, h2, h3, hshift]
#print axioms shape_u627_uniform
-- u628 [4-edge cycle] 5->6->2->1->(closed) | cand_progress+z_irred+z_irred+z_progress
--   roles: abs=8, abs=8, abs=6, abs=7, abs=2, abs=6, abs=8, abs=2; 1 instances at bases [6]; all_strict=True; worst realized 15275/15827
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u628_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (107640:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u628_uniform
-- u629 [4-edge cycle] 5->6->2->1->(closed) | cand_progress+z_irred+z_irred+z_progress
--   roles: abs=11, abs=11, abs=7, abs=10, abs=3, abs=7, abs=11, abs=3; 1 instances at bases [9]; all_strict=True; worst realized 22517/23085
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u629_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (252760:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u629_uniform
-- u630 [4-edge cycle] 5->6->2->1->(closed) | cand_progress+z_irred+z_irred+z_progress
--   roles: abs=12, abs=12, abs=10, abs=11, abs=3, abs=10, abs=12, abs=3; 1 instances at bases [10]; all_strict=True; worst realized 176249/180225
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u630_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (385672:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u630_uniform
-- u631 [4-edge cycle] 5->6->3->1->(closed) | cand_progress+z_entry+z_irred+z_irred
--   roles: abs=10, abs=10, abs=8, abs=7, abs=2, abs=8, abs=10, abs=2; 1 instances at bases [7]; all_strict=True; worst realized 1501/1547
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u631_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (167670:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u631_uniform
-- u632 [4-edge cycle] 5->6->3->1->(closed) | cand_progress+z_entry+z_irred+z_progress
--   roles: abs=12, abs=12, abs=10, abs=9, abs=2, abs=10, abs=12, abs=2; 2 instances at bases [9]; all_strict=True; worst realized 35405/36261
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u632_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (249096:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u632_uniform
-- u633 [4-edge cycle] 5->6->3->2->(closed) | cand_progress+z_entry+z_entry+z_entry
--   roles: abs=13, abs=13, abs=9, abs=8, abs=12, abs=8, abs=6, abs=9; 2 instances at bases [8]; all_strict=True; worst realized 61685/63403
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u633_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (901950:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u633_uniform
-- u634 [4-edge cycle] 5->6->3->4->(closed) | cand_entry+z_entry+z_entry+z_entry
--   roles: free+2..+7, free+2..+6, tied+1, tied=base, tied=base, tied=base, tied=base, tied=base; 856 instances at bases [5, 6, 7, 8, 9, 10]; all_strict=True; worst realized 17183259/17193955
/-- pattern tau=(2,2): real half-line form, mono certificate (kind ALL, strict=True, deg D = 2). -/
theorem shape_u634_pat1_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (512:ℚ) * m ^ 2 - (1920:ℚ) * m + (88:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have hshift : (512:ℚ) * (m - 5) ^ 2 + (3200:ℚ) * (m - 5) + (3288:ℚ) = (512:ℚ) * m ^ 2 - (1920:ℚ) * m + (88:ℚ) := by ring
  linarith [ht, h2, hshift]
#print axioms shape_u634_pat1_uniform
/-- pattern tau=(3,2): real half-line form, mono certificate (kind ALL, strict=True, deg D = 3). -/
theorem shape_u634_pat2_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (4096:ℚ) * m ^ 3 + (3072:ℚ) * m ^ 2 - (2752:ℚ) * m + (144:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have h3 : (0:ℚ) ≤ (m - 5) ^ 3 := by nlinarith
  have hshift : (4096:ℚ) * (m - 5) ^ 3 + (64512:ℚ) * (m - 5) ^ 2 + (335168:ℚ) * (m - 5) + (575184:ℚ) = (4096:ℚ) * m ^ 3 + (3072:ℚ) * m ^ 2 - (2752:ℚ) * m + (144:ℚ) := by ring
  linarith [ht, h2, h3, hshift]
#print axioms shape_u634_pat2_uniform
/-- pattern tau=(3,3): real half-line form, mono certificate (kind ALL, strict=True, deg D = 2). -/
theorem shape_u634_pat3_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (1536:ℚ) * m ^ 2 - (2944:ℚ) * m + (136:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have hshift : (1536:ℚ) * (m - 5) ^ 2 + (12416:ℚ) * (m - 5) + (23816:ℚ) = (1536:ℚ) * m ^ 2 - (2944:ℚ) * m + (136:ℚ) := by ring
  linarith [ht, h2, hshift]
#print axioms shape_u634_pat3_uniform
/-- pattern tau=(4,3): real half-line form, mono certificate (kind ALL, strict=True, deg D = 3). -/
theorem shape_u634_pat4_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (4096:ℚ) * m ^ 3 + (4096:ℚ) * m ^ 2 - (3776:ℚ) * m + (192:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have h3 : (0:ℚ) ≤ (m - 5) ^ 3 := by nlinarith
  have hshift : (4096:ℚ) * (m - 5) ^ 3 + (65536:ℚ) * (m - 5) ^ 2 + (344384:ℚ) * (m - 5) + (595712:ℚ) = (4096:ℚ) * m ^ 3 + (4096:ℚ) * m ^ 2 - (3776:ℚ) * m + (192:ℚ) := by ring
  linarith [ht, h2, h3, hshift]
#print axioms shape_u634_pat4_uniform
/-- pattern tau=(4,4): real half-line form, mono certificate (kind ALL, strict=True, deg D = 2). -/
theorem shape_u634_pat5_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (2560:ℚ) * m ^ 2 - (3968:ℚ) * m + (184:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have hshift : (2560:ℚ) * (m - 5) ^ 2 + (21632:ℚ) * (m - 5) + (44344:ℚ) = (2560:ℚ) * m ^ 2 - (3968:ℚ) * m + (184:ℚ) := by ring
  linarith [ht, h2, hshift]
#print axioms shape_u634_pat5_uniform
/-- pattern tau=(5,4): real half-line form, mono certificate (kind ALL, strict=True, deg D = 3). -/
theorem shape_u634_pat6_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (4096:ℚ) * m ^ 3 + (5120:ℚ) * m ^ 2 - (4800:ℚ) * m + (240:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have h3 : (0:ℚ) ≤ (m - 5) ^ 3 := by nlinarith
  have hshift : (4096:ℚ) * (m - 5) ^ 3 + (66560:ℚ) * (m - 5) ^ 2 + (353600:ℚ) * (m - 5) + (616240:ℚ) = (4096:ℚ) * m ^ 3 + (5120:ℚ) * m ^ 2 - (4800:ℚ) * m + (240:ℚ) := by ring
  linarith [ht, h2, h3, hshift]
#print axioms shape_u634_pat6_uniform
/-- pattern tau=(5,5): real half-line form, mono certificate (kind ALL, strict=True, deg D = 2). -/
theorem shape_u634_pat7_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (3584:ℚ) * m ^ 2 - (4992:ℚ) * m + (232:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have hshift : (3584:ℚ) * (m - 5) ^ 2 + (30848:ℚ) * (m - 5) + (64872:ℚ) = (3584:ℚ) * m ^ 2 - (4992:ℚ) * m + (232:ℚ) := by ring
  linarith [ht, h2, hshift]
#print axioms shape_u634_pat7_uniform
/-- pattern tau=(6,5): real half-line form, mono certificate (kind ALL, strict=True, deg D = 3). -/
theorem shape_u634_pat8_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (4096:ℚ) * m ^ 3 + (6144:ℚ) * m ^ 2 - (5824:ℚ) * m + (288:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have h3 : (0:ℚ) ≤ (m - 5) ^ 3 := by nlinarith
  have hshift : (4096:ℚ) * (m - 5) ^ 3 + (67584:ℚ) * (m - 5) ^ 2 + (362816:ℚ) * (m - 5) + (636768:ℚ) = (4096:ℚ) * m ^ 3 + (6144:ℚ) * m ^ 2 - (5824:ℚ) * m + (288:ℚ) := by ring
  linarith [ht, h2, h3, hshift]
#print axioms shape_u634_pat8_uniform
/-- pattern tau=(6,6): real half-line form, mono certificate (kind ALL, strict=True, deg D = 2). -/
theorem shape_u634_pat9_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (4608:ℚ) * m ^ 2 - (6016:ℚ) * m + (280:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have hshift : (4608:ℚ) * (m - 5) ^ 2 + (40064:ℚ) * (m - 5) + (85400:ℚ) = (4608:ℚ) * m ^ 2 - (6016:ℚ) * m + (280:ℚ) := by ring
  linarith [ht, h2, hshift]
#print axioms shape_u634_pat9_uniform
/-- pattern tau=(7,6): real half-line form, mono certificate (kind ALL, strict=True, deg D = 3). -/
theorem shape_u634_pat10_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (4096:ℚ) * m ^ 3 + (7168:ℚ) * m ^ 2 - (6848:ℚ) * m + (336:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have h3 : (0:ℚ) ≤ (m - 5) ^ 3 := by nlinarith
  have hshift : (4096:ℚ) * (m - 5) ^ 3 + (68608:ℚ) * (m - 5) ^ 2 + (372032:ℚ) * (m - 5) + (657296:ℚ) = (4096:ℚ) * m ^ 3 + (7168:ℚ) * m ^ 2 - (6848:ℚ) * m + (336:ℚ) := by ring
  linarith [ht, h2, h3, hshift]
#print axioms shape_u634_pat10_uniform
-- u635 [4-edge cycle] 5->6->3->4->(closed) | cand_progress+z_entry+z_entry+z_entry
--   roles: free+2..+6, free+2..+6, tied+1, tied=base, tied=base, tied=base, tied=base, tied=base; 270 instances at bases [5, 6, 7, 8, 9, 10]; all_strict=True; worst realized 177147/180989
/-- pattern tau=(2,2): real half-line form, mono certificate (kind ALL, strict=True, deg D = 3). -/
theorem shape_u635_pat1_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (1024:ℚ) * m ^ 3 + (1152:ℚ) * m ^ 2 - (2128:ℚ) * m + (102:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have h3 : (0:ℚ) ≤ (m - 5) ^ 3 := by nlinarith
  have hshift : (1024:ℚ) * (m - 5) ^ 3 + (16512:ℚ) * (m - 5) ^ 2 + (86192:ℚ) * (m - 5) + (146262:ℚ) = (1024:ℚ) * m ^ 3 + (1152:ℚ) * m ^ 2 - (2128:ℚ) * m + (102:ℚ) := by ring
  linarith [ht, h2, h3, hshift]
#print axioms shape_u635_pat1_uniform
/-- pattern tau=(3,3): real half-line form, mono certificate (kind ALL, strict=True, deg D = 3). -/
theorem shape_u635_pat2_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (1024:ℚ) * m ^ 3 + (2176:ℚ) * m ^ 2 - (3152:ℚ) * m + (150:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have h3 : (0:ℚ) ≤ (m - 5) ^ 3 := by nlinarith
  have hshift : (1024:ℚ) * (m - 5) ^ 3 + (17536:ℚ) * (m - 5) ^ 2 + (95408:ℚ) * (m - 5) + (166790:ℚ) = (1024:ℚ) * m ^ 3 + (2176:ℚ) * m ^ 2 - (3152:ℚ) * m + (150:ℚ) := by ring
  linarith [ht, h2, h3, hshift]
#print axioms shape_u635_pat2_uniform
/-- pattern tau=(4,4): real half-line form, mono certificate (kind ALL, strict=True, deg D = 3). -/
theorem shape_u635_pat3_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (1024:ℚ) * m ^ 3 + (3200:ℚ) * m ^ 2 - (4176:ℚ) * m + (198:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have h3 : (0:ℚ) ≤ (m - 5) ^ 3 := by nlinarith
  have hshift : (1024:ℚ) * (m - 5) ^ 3 + (18560:ℚ) * (m - 5) ^ 2 + (104624:ℚ) * (m - 5) + (187318:ℚ) = (1024:ℚ) * m ^ 3 + (3200:ℚ) * m ^ 2 - (4176:ℚ) * m + (198:ℚ) := by ring
  linarith [ht, h2, h3, hshift]
#print axioms shape_u635_pat3_uniform
/-- pattern tau=(5,5): real half-line form, mono certificate (kind ALL, strict=True, deg D = 3). -/
theorem shape_u635_pat4_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (1024:ℚ) * m ^ 3 + (4224:ℚ) * m ^ 2 - (5200:ℚ) * m + (246:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have h3 : (0:ℚ) ≤ (m - 5) ^ 3 := by nlinarith
  have hshift : (1024:ℚ) * (m - 5) ^ 3 + (19584:ℚ) * (m - 5) ^ 2 + (113840:ℚ) * (m - 5) + (207846:ℚ) = (1024:ℚ) * m ^ 3 + (4224:ℚ) * m ^ 2 - (5200:ℚ) * m + (246:ℚ) := by ring
  linarith [ht, h2, h3, hshift]
#print axioms shape_u635_pat4_uniform
/-- pattern tau=(6,6): real half-line form, mono certificate (kind ALL, strict=True, deg D = 3). -/
theorem shape_u635_pat5_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (1024:ℚ) * m ^ 3 + (5248:ℚ) * m ^ 2 - (6224:ℚ) * m + (294:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have h3 : (0:ℚ) ≤ (m - 5) ^ 3 := by nlinarith
  have hshift : (1024:ℚ) * (m - 5) ^ 3 + (20608:ℚ) * (m - 5) ^ 2 + (123056:ℚ) * (m - 5) + (228374:ℚ) = (1024:ℚ) * m ^ 3 + (5248:ℚ) * m ^ 2 - (6224:ℚ) * m + (294:ℚ) := by ring
  linarith [ht, h2, h3, hshift]
#print axioms shape_u635_pat5_uniform
-- u636 [4-edge cycle] 6->1->2->5->(closed) | cand_progress+z_entry+z_entry+z_entry
--   roles: abs=4, tied+2, abs=5, tied=base, tied=base, tied+1, tied+1, tied+1; 2 instances at bases [5, 6]; all_strict=True; worst realized 159201/198575
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 3). -/
theorem shape_u636_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (3072:ℚ) * m ^ 3 + (17280:ℚ) * m ^ 2 + (3504:ℚ) * m - (7314:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have h3 : (0:ℚ) ≤ (m - 5) ^ 3 := by nlinarith
  have hshift : (3072:ℚ) * (m - 5) ^ 3 + (63360:ℚ) * (m - 5) ^ 2 + (406704:ℚ) * (m - 5) + (826206:ℚ) = (3072:ℚ) * m ^ 3 + (17280:ℚ) * m ^ 2 + (3504:ℚ) * m - (7314:ℚ) := by ring
  linarith [ht, h2, h3, hshift]
#print axioms shape_u636_uniform
-- u637 [4-edge cycle] 6->1->2->5->(closed) | cand_progress+z_entry+z_entry+z_entry
--   roles: abs=1, tied+3, abs=2, tied-3, tied-3, tied+1, tied+1, tied+1; 2 instances at bases [6, 7]; all_strict=True; worst realized 9295/17577
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 3). -/
theorem shape_u637_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (3072:ℚ) * m ^ 3 + (9600:ℚ) * m ^ 2 - (51024:ℚ) * m - (48858:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have h3 : (0:ℚ) ≤ (m - 5) ^ 3 := by nlinarith
  have hshift : (3072:ℚ) * (m - 5) ^ 3 + (55680:ℚ) * (m - 5) ^ 2 + (275376:ℚ) * (m - 5) + (320022:ℚ) = (3072:ℚ) * m ^ 3 + (9600:ℚ) * m ^ 2 - (51024:ℚ) * m - (48858:ℚ) := by ring
  linarith [ht, h2, h3, hshift]
#print axioms shape_u637_uniform
-- u638 [4-edge cycle] 6->1->2->5->(closed) | cand_progress+z_entry+z_entry+z_entry
--   roles: abs=1, abs=9, abs=2, abs=4, abs=4, abs=7, abs=7, abs=7; 1 instances at bases [6]; all_strict=True; worst realized 29241/56575
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u638_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (902022:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u638_uniform
-- u639 [4-edge cycle] 6->1->2->5->(closed) | cand_progress+z_entry+z_entry+z_entry
--   roles: abs=5, tied+2, abs=6, abs=6, abs=6, tied+1, tied+1, tied+1; 2 instances at bases [6, 7]; all_strict=True; worst realized 1212575/1451313
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 2). -/
theorem shape_u639_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (12800:ℚ) * m ^ 2 + (134832:ℚ) * m + (100142:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have hshift : (12800:ℚ) * (m - 5) ^ 2 + (262832:ℚ) * (m - 5) + (1094302:ℚ) = (12800:ℚ) * m ^ 2 + (134832:ℚ) * m + (100142:ℚ) := by ring
  linarith [ht, h2, hshift]
#print axioms shape_u639_uniform
-- u640 [4-edge cycle] 6->1->2->5->(closed) | cand_progress+z_entry+z_entry+z_entry
--   roles: abs=1, tied+3, abs=2, tied-1, tied-1, tied+1, tied+1, tied+1; 2 instances at bases [7, 8]; all_strict=True; worst realized 911259/1737725
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 3). -/
theorem shape_u640_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (3072:ℚ) * m ^ 3 + (15744:ℚ) * m ^ 2 - (10320:ℚ) * m - (18522:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have h3 : (0:ℚ) ≤ (m - 5) ^ 3 := by nlinarith
  have hshift : (3072:ℚ) * (m - 5) ^ 3 + (61824:ℚ) * (m - 5) ^ 2 + (377520:ℚ) * (m - 5) + (707478:ℚ) = (3072:ℚ) * m ^ 3 + (15744:ℚ) * m ^ 2 - (10320:ℚ) * m - (18522:ℚ) := by ring
  linarith [ht, h2, h3, hshift]
#print axioms shape_u640_uniform
-- u641 [4-edge cycle] 6->1->2->5->(closed) | cand_progress+z_entry+z_entry+z_entry
--   roles: abs=1, tied+3, abs=2, tied=base, tied=base, tied+1, tied+1, tied+1; 4 instances at bases [7, 8, 9]; all_strict=True; worst realized 1436859/2720365
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 3). -/
theorem shape_u641_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (3072:ℚ) * m ^ 3 + (18816:ℚ) * m ^ 2 + (10032:ℚ) * m - (3354:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have h3 : (0:ℚ) ≤ (m - 5) ^ 3 := by nlinarith
  have hshift : (3072:ℚ) * (m - 5) ^ 3 + (64896:ℚ) * (m - 5) ^ 2 + (428592:ℚ) * (m - 5) + (901206:ℚ) = (3072:ℚ) * m ^ 3 + (18816:ℚ) * m ^ 2 + (10032:ℚ) * m - (3354:ℚ) := by ring
  linarith [ht, h2, h3, hshift]
#print axioms shape_u641_uniform
-- u642 [4-edge cycle] 6->1->2->5->(closed) | cand_progress+z_entry+z_entry+z_entry
--   roles: abs=5, tied+2, abs=6, tied=base, tied=base, tied+1, tied+1, tied+1; 2 instances at bases [7, 8]; all_strict=True; worst realized 14201785/17028711
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 3). -/
theorem shape_u642_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (3072:ℚ) * m ^ 3 + (19328:ℚ) * m ^ 2 + (3248:ℚ) * m - (8914:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have h3 : (0:ℚ) ≤ (m - 5) ^ 3 := by nlinarith
  have hshift : (3072:ℚ) * (m - 5) ^ 3 + (65408:ℚ) * (m - 5) ^ 2 + (426928:ℚ) * (m - 5) + (874526:ℚ) = (3072:ℚ) * m ^ 3 + (19328:ℚ) * m ^ 2 + (3248:ℚ) * m - (8914:ℚ) := by ring
  linarith [ht, h2, h3, hshift]
#print axioms shape_u642_uniform
-- u643 [4-edge cycle] 6->1->2->5->(closed) | cand_progress+z_entry+z_entry+z_entry
--   roles: abs=6, tied+2, abs=7, abs=7, abs=7, tied+1, tied+1, tied+1; 2 instances at bases [7, 8]; all_strict=True; worst realized 4961299/5798925
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 2). -/
theorem shape_u643_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (14848:ℚ) * m ^ 2 + (178608:ℚ) * m + (133742:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have hshift : (14848:ℚ) * (m - 5) ^ 2 + (327088:ℚ) * (m - 5) + (1397982:ℚ) = (14848:ℚ) * m ^ 2 + (178608:ℚ) * m + (133742:ℚ) := by ring
  linarith [ht, h2, hshift]
#print axioms shape_u643_uniform
-- u644 [4-edge cycle] 6->1->2->5->(closed) | cand_progress+z_entry+z_entry+z_entry
--   roles: abs=6, tied+2, abs=7, abs=8, abs=8, tied+1, tied+1, tied+1; 2 instances at bases [8, 9]; all_strict=True; worst realized 66339/77341
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 2). -/
theorem shape_u644_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (17920:ℚ) * m ^ 2 + (206640:ℚ) * m + (154350:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have hshift : (17920:ℚ) * (m - 5) ^ 2 + (385840:ℚ) * (m - 5) + (1635550:ℚ) = (17920:ℚ) * m ^ 2 + (206640:ℚ) * m + (154350:ℚ) := by ring
  linarith [ht, h2, hshift]
#print axioms shape_u644_uniform
-- u645 [4-edge cycle] 6->1->2->5->(closed) | cand_progress+z_entry+z_entry+z_entry
--   roles: abs=7, tied+2, abs=8, abs=8, abs=8, tied+1, tied+1, tied+1; 2 instances at bases [8, 9]; all_strict=True; worst realized 300105/344519
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 2). -/
theorem shape_u645_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (16896:ℚ) * m ^ 2 + (228528:ℚ) * m + (172206:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have hshift : (16896:ℚ) * (m - 5) ^ 2 + (397488:ℚ) * (m - 5) + (1737246:ℚ) = (16896:ℚ) * m ^ 2 + (228528:ℚ) * m + (172206:ℚ) := by ring
  linarith [ht, h2, hshift]
#print axioms shape_u645_uniform
-- u646 [4-edge cycle] 6->1->2->5->(closed) | cand_progress+z_entry+z_entry+z_entry
--   roles: abs=6, tied+2, abs=7, tied=base, tied=base, tied+1, tied+1, tied+1; 2 instances at bases [9, 10]; all_strict=True; worst realized 10479483/12222485
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 3). -/
theorem shape_u646_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (3072:ℚ) * m ^ 3 + (21376:ℚ) * m ^ 2 + (2992:ℚ) * m - (10514:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have h3 : (0:ℚ) ≤ (m - 5) ^ 3 := by nlinarith
  have hshift : (3072:ℚ) * (m - 5) ^ 3 + (67456:ℚ) * (m - 5) ^ 2 + (447152:ℚ) * (m - 5) + (922846:ℚ) = (3072:ℚ) * m ^ 3 + (21376:ℚ) * m ^ 2 + (2992:ℚ) * m - (10514:ℚ) := by ring
  linarith [ht, h2, h3, hshift]
#print axioms shape_u646_uniform
-- u647 [4-edge cycle] 6->1->2->5->(closed) | cand_progress+z_entry+z_entry+z_entry
--   roles: abs=7, tied+2, abs=8, abs=9, abs=9, tied+1, tied+1, tied+1; 2 instances at bases [9, 10]; all_strict=True; worst realized 10986427/12582549
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 2). -/
theorem shape_u647_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (19968:ℚ) * m ^ 2 + (259632:ℚ) * m + (195246:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have hshift : (19968:ℚ) * (m - 5) ^ 2 + (459312:ℚ) * (m - 5) + (1992606:ℚ) = (19968:ℚ) * m ^ 2 + (259632:ℚ) * m + (195246:ℚ) := by ring
  linarith [ht, h2, hshift]
#print axioms shape_u647_uniform
-- u648 [4-edge cycle] 6->1->2->5->(closed) | cand_progress+z_entry+z_entry+z_entry
--   roles: abs=8, tied+2, abs=9, abs=9, abs=9, tied+1, tied+1, tied+1; 2 instances at bases [9, 10]; all_strict=True; worst realized 37585145/42540999
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 2). -/
theorem shape_u648_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (18944:ℚ) * m ^ 2 + (284592:ℚ) * m + (215534:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have hshift : (18944:ℚ) * (m - 5) ^ 2 + (474032:ℚ) * (m - 5) + (2112094:ℚ) = (18944:ℚ) * m ^ 2 + (284592:ℚ) * m + (215534:ℚ) := by ring
  linarith [ht, h2, hshift]
#print axioms shape_u648_uniform
-- u649 [4-edge cycle] 6->1->2->5->(closed) | cand_progress+z_entry+z_entry+z_entry
--   roles: abs=7, abs=12, abs=8, abs=10, abs=10, abs=11, abs=11, abs=11; 1 instances at bases [10]; all_strict=True; worst realized 1354491/1555589
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u649_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (5429646:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u649_uniform
-- u650 [4-edge cycle] 6->1->2->5->(closed) | cand_progress+z_entry+z_entry+z_entry
--   roles: abs=8, abs=12, abs=9, abs=10, abs=10, abs=11, abs=11, abs=11; 1 instances at bases [10]; all_strict=True; worst realized 13901355/15778117
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u650_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (5630286:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u650_uniform
-- u651 [4-edge cycle] 6->1->2->5->(closed) | cand_progress+z_entry+z_entry+z_entry
--   roles: abs=9, abs=12, abs=10, abs=10, abs=10, abs=11, abs=11, abs=11; 1 instances at bases [10]; all_strict=True; worst realized 15612291/17555933
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u651_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (5830926:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u651_uniform
-- u652 [4-edge cycle] 6->1->4->5->(closed) | cand_progress+z_entry+z_entry+z_entry
--   roles: abs=4, tied+2, abs=5, tied+1, tied=base, tied=base, tied+1, tied+1; 3 instances at bases [5, 6]; all_strict=True; worst realized 159201/198575
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 3). -/
theorem shape_u652_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (3072:ℚ) * m ^ 3 + (17280:ℚ) * m ^ 2 + (3504:ℚ) * m - (7314:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have h3 : (0:ℚ) ≤ (m - 5) ^ 3 := by nlinarith
  have hshift : (3072:ℚ) * (m - 5) ^ 3 + (63360:ℚ) * (m - 5) ^ 2 + (406704:ℚ) * (m - 5) + (826206:ℚ) = (3072:ℚ) * m ^ 3 + (17280:ℚ) * m ^ 2 + (3504:ℚ) * m - (7314:ℚ) := by ring
  linarith [ht, h2, h3, hshift]
#print axioms shape_u652_uniform
-- u653 [4-edge cycle] 6->1->4->5->(closed) | cand_progress+z_entry+z_entry+z_entry
--   roles: abs=5, tied+2, abs=6, tied+1, tied=base, tied=base, tied+1, tied+1; 6 instances at bases [6, 7, 8]; all_strict=True; worst realized 14201785/17028711
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 3). -/
theorem shape_u653_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (3072:ℚ) * m ^ 3 + (19328:ℚ) * m ^ 2 + (3248:ℚ) * m - (8914:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have h3 : (0:ℚ) ≤ (m - 5) ^ 3 := by nlinarith
  have hshift : (3072:ℚ) * (m - 5) ^ 3 + (65408:ℚ) * (m - 5) ^ 2 + (426928:ℚ) * (m - 5) + (874526:ℚ) = (3072:ℚ) * m ^ 3 + (19328:ℚ) * m ^ 2 + (3248:ℚ) * m - (8914:ℚ) := by ring
  linarith [ht, h2, h3, hshift]
#print axioms shape_u653_uniform
-- u654 [4-edge cycle] 6->1->4->5->(closed) | cand_progress+z_entry+z_entry+z_entry
--   roles: abs=1, tied+3, abs=2, tied+1, tied=base, tied=base, tied+1, tied+1; 12 instances at bases [7, 8, 9]; all_strict=True; worst realized 1436859/2720365
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 3). -/
theorem shape_u654_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (3072:ℚ) * m ^ 3 + (18816:ℚ) * m ^ 2 + (10032:ℚ) * m - (3354:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have h3 : (0:ℚ) ≤ (m - 5) ^ 3 := by nlinarith
  have hshift : (3072:ℚ) * (m - 5) ^ 3 + (64896:ℚ) * (m - 5) ^ 2 + (428592:ℚ) * (m - 5) + (901206:ℚ) = (3072:ℚ) * m ^ 3 + (18816:ℚ) * m ^ 2 + (10032:ℚ) * m - (3354:ℚ) := by ring
  linarith [ht, h2, h3, hshift]
#print axioms shape_u654_uniform
-- u655 [4-edge cycle] 6->1->4->5->(closed) | cand_progress+z_entry+z_entry+z_entry
--   roles: abs=6, tied+2, abs=7, tied+1, tied=base, tied=base, tied+1, tied+1; 9 instances at bases [7, 8, 9, 10]; all_strict=True; worst realized 10479483/12222485
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 3). -/
theorem shape_u655_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (3072:ℚ) * m ^ 3 + (21376:ℚ) * m ^ 2 + (2992:ℚ) * m - (10514:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have h3 : (0:ℚ) ≤ (m - 5) ^ 3 := by nlinarith
  have hshift : (3072:ℚ) * (m - 5) ^ 3 + (67456:ℚ) * (m - 5) ^ 2 + (447152:ℚ) * (m - 5) + (922846:ℚ) = (3072:ℚ) * m ^ 3 + (21376:ℚ) * m ^ 2 + (2992:ℚ) * m - (10514:ℚ) := by ring
  linarith [ht, h2, h3, hshift]
#print axioms shape_u655_uniform
-- u656 [4-edge cycle] 6->1->4->5->(closed) | cand_progress+z_entry+z_entry+z_entry
--   roles: abs=7, tied+2, abs=8, tied+1, tied=base, tied=base, tied+1, tied+1; 6 instances at bases [8, 9, 10]; all_strict=True; worst realized 1354491/1555589
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 3). -/
theorem shape_u656_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (3072:ℚ) * m ^ 3 + (23424:ℚ) * m ^ 2 + (2736:ℚ) * m - (12114:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have h3 : (0:ℚ) ≤ (m - 5) ^ 3 := by nlinarith
  have hshift : (3072:ℚ) * (m - 5) ^ 3 + (69504:ℚ) * (m - 5) ^ 2 + (467376:ℚ) * (m - 5) + (971166:ℚ) = (3072:ℚ) * m ^ 3 + (23424:ℚ) * m ^ 2 + (2736:ℚ) * m - (12114:ℚ) := by ring
  linarith [ht, h2, h3, hshift]
#print axioms shape_u656_uniform
-- u657 [4-edge cycle] 6->1->4->5->(closed) | cand_progress+z_entry+z_entry+z_entry
--   roles: abs=8, tied+2, abs=9, tied+1, tied=base, tied=base, tied+1, tied+1; 3 instances at bases [9, 10]; all_strict=True; worst realized 13901355/15778117
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 3). -/
theorem shape_u657_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (3072:ℚ) * m ^ 3 + (25472:ℚ) * m ^ 2 + (2480:ℚ) * m - (13714:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have h3 : (0:ℚ) ≤ (m - 5) ^ 3 := by nlinarith
  have hshift : (3072:ℚ) * (m - 5) ^ 3 + (71552:ℚ) * (m - 5) ^ 2 + (487600:ℚ) * (m - 5) + (1019486:ℚ) = (3072:ℚ) * m ^ 3 + (25472:ℚ) * m ^ 2 + (2480:ℚ) * m - (13714:ℚ) := by ring
  linarith [ht, h2, h3, hshift]
#print axioms shape_u657_uniform
-- u658 [4-edge cycle] 6->1->4->5->(closed) | cand_progress+z_entry+z_entry+z_entry
--   roles: abs=9, abs=12, abs=10, abs=11, abs=10, abs=10, abs=11, abs=11; 1 instances at bases [10]; all_strict=True; worst realized 15612291/17555933
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u658_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (5830926:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u658_uniform
-- u659 [4-edge cycle] 6->2->1->5->(closed) | cand_progress+z_entry+z_entry+z_entry
--   roles: abs=5, abs=7, abs=6, abs=4, abs=4, abs=6, abs=6, abs=6; 1 instances at bases [5]; all_strict=True; worst realized 1082851/1301101
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u659_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (654750:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u659_uniform
-- u660 [4-edge cycle] 6->2->4->5->(closed) | cand_entry+z_progress+z_entry+z_entry
--   roles: abs=13, abs=8, abs=10, abs=7, abs=9, abs=9, abs=10, abs=10; 1 instances at bases [9]; all_strict=True; worst realized 10377315/10976813
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u660_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (1798494:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u660_uniform
-- u661 [4-edge cycle] 6->2->4->5->(closed) | cand_progress+z_entry+z_entry+z_entry
--   roles: tied-1, tied+2, tied=base, tied+1, tied=base, tied=base, tied+1, tied+1; 3 instances at bases [5, 6]; all_strict=True; worst realized 6527241/7897175
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 3). -/
theorem shape_u661_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (5120:ℚ) * m ^ 3 + (6784:ℚ) * m ^ 2 + (3184:ℚ) * m + (686:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have h3 : (0:ℚ) ≤ (m - 5) ^ 3 := by nlinarith
  have hshift : (5120:ℚ) * (m - 5) ^ 3 + (83584:ℚ) * (m - 5) ^ 2 + (455024:ℚ) * (m - 5) + (826206:ℚ) = (5120:ℚ) * m ^ 3 + (6784:ℚ) * m ^ 2 + (3184:ℚ) * m + (686:ℚ) := by ring
  linarith [ht, h2, h3, hshift]
#print axioms shape_u661_uniform
-- u662 [4-edge cycle] 6->3->2->1->(closed) | cand_entry+z_entry+z_entry+z_entry
--   roles: abs=14, abs=12, abs=11, abs=9, abs=10, abs=6, abs=6, abs=12; 1 instances at bases [10]; all_strict=True; worst realized 33655993/35856441
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u662_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (2200448:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u662_uniform
-- u663 [4-edge cycle] 6->3->2->1->(closed) | cand_progress+z_entry+z_entry+z_entry
--   roles: abs=12, abs=13, abs=11, abs=9, abs=10, abs=6, abs=6, abs=12; 1 instances at bases [10]; all_strict=True; worst realized 4807999/4845465
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u663_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (262262:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u663_uniform
-- u664 [4-edge cycle] 6->3->2->1->(closed) | cand_progress+z_entry+z_irred+z_progress
--   roles: abs=11, abs=12, abs=10, abs=7, abs=2, abs=7, abs=12, abs=2; 1 instances at bases [9]; all_strict=True; worst realized 1335/1343
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u664_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (44232:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u664_uniform
-- u665 [4-edge cycle] 6->3->2->1->(closed) | cand_progress+z_entry+z_irred+z_progress
--   roles: abs=11, abs=12, abs=10, abs=8, abs=2, abs=8, abs=12, abs=2; 1 instances at bases [9]; all_strict=True; worst realized 1335/1343
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u665_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (50440:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u665_uniform
-- u666 [4-edge cycle] 6->3->2->5->(closed) | cand_entry+z_entry+z_entry+z_entry
--   roles: abs=9, abs=7, abs=7, abs=4, abs=4, abs=7, abs=6, abs=6; 1 instances at bases [5]; all_strict=True; worst realized 477603/517235
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u666_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (435952:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u666_uniform
-- u667 [4-edge cycle] 6->3->4->1->(closed) | cand_progress+z_entry+z_entry+z_entry
--   roles: abs=14, abs=16, abs=10, abs=10, abs=15, abs=1, abs=1, abs=12; 1 instances at bases [10]; all_strict=True; worst realized 2663523/2829701
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u667_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (498534:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u667_uniform
-- u668 [4-edge cycle] 6->3->4->5->(closed) | cand_entry+z_entry+z_entry+z_entry
--   roles: free+3..+7, free+1..+4, tied=base, tied=base, tied=base, tied=base, tied+1, tied+1; 165 instances at bases [5, 6, 7, 8, 9, 10]; all_strict=True; worst realized 6012937/6219369
/-- pattern tau=(3,1): real half-line form, mono certificate (kind ALL, strict=True, deg D = 3). -/
theorem shape_u668_pat1_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (4096:ℚ) * m ^ 3 - (1024:ℚ) * m ^ 2 - (3776:ℚ) * m + (80:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have h3 : (0:ℚ) ≤ (m - 5) ^ 3 := by nlinarith
  have hshift : (4096:ℚ) * (m - 5) ^ 3 + (60416:ℚ) * (m - 5) ^ 2 + (293184:ℚ) * (m - 5) + (467600:ℚ) = (4096:ℚ) * m ^ 3 - (1024:ℚ) * m ^ 2 - (3776:ℚ) * m + (80:ℚ) := by ring
  linarith [ht, h2, h3, hshift]
#print axioms shape_u668_pat1_uniform
/-- pattern tau=(4,2): real half-line form, mono certificate (kind ALL, strict=True, deg D = 3). -/
theorem shape_u668_pat2_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (4096:ℚ) * m ^ 3 - (4096:ℚ) * m ^ 2 - (5824:ℚ) * m + (64:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have h3 : (0:ℚ) ≤ (m - 5) ^ 3 := by nlinarith
  have hshift : (4096:ℚ) * (m - 5) ^ 3 + (57344:ℚ) * (m - 5) ^ 2 + (260416:ℚ) * (m - 5) + (380544:ℚ) = (4096:ℚ) * m ^ 3 - (4096:ℚ) * m ^ 2 - (5824:ℚ) * m + (64:ℚ) := by ring
  linarith [ht, h2, h3, hshift]
#print axioms shape_u668_pat2_uniform
/-- pattern tau=(5,3): real half-line form, mono certificate (kind ALL, strict=True, deg D = 3). -/
theorem shape_u668_pat3_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (4096:ℚ) * m ^ 3 - (7168:ℚ) * m ^ 2 - (7872:ℚ) * m + (48:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have h3 : (0:ℚ) ≤ (m - 5) ^ 3 := by nlinarith
  have hshift : (4096:ℚ) * (m - 5) ^ 3 + (54272:ℚ) * (m - 5) ^ 2 + (227648:ℚ) * (m - 5) + (293488:ℚ) = (4096:ℚ) * m ^ 3 - (7168:ℚ) * m ^ 2 - (7872:ℚ) * m + (48:ℚ) := by ring
  linarith [ht, h2, h3, hshift]
#print axioms shape_u668_pat3_uniform
/-- pattern tau=(6,4): real half-line form, mono certificate (kind ALL, strict=True, deg D = 3). -/
theorem shape_u668_pat4_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (4096:ℚ) * m ^ 3 - (10240:ℚ) * m ^ 2 - (9920:ℚ) * m + (32:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have h3 : (0:ℚ) ≤ (m - 5) ^ 3 := by nlinarith
  have hshift : (4096:ℚ) * (m - 5) ^ 3 + (51200:ℚ) * (m - 5) ^ 2 + (194880:ℚ) * (m - 5) + (206432:ℚ) = (4096:ℚ) * m ^ 3 - (10240:ℚ) * m ^ 2 - (9920:ℚ) * m + (32:ℚ) := by ring
  linarith [ht, h2, h3, hshift]
#print axioms shape_u668_pat4_uniform
/-- pattern tau=(7,4): real half-line form, mono certificate (kind ALL, strict=True, deg D = 3). -/
theorem shape_u668_pat5_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (8192:ℚ) * m ^ 3 - (7680:ℚ) * m ^ 2 - (10752:ℚ) * m + (88:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have h3 : (0:ℚ) ≤ (m - 5) ^ 3 := by nlinarith
  have hshift : (8192:ℚ) * (m - 5) ^ 3 + (115200:ℚ) * (m - 5) ^ 2 + (526848:ℚ) * (m - 5) + (778328:ℚ) = (8192:ℚ) * m ^ 3 - (7680:ℚ) * m ^ 2 - (10752:ℚ) * m + (88:ℚ) := by ring
  linarith [ht, h2, h3, hshift]
#print axioms shape_u668_pat5_uniform
-- u669 [4-edge cycle] 6->3->4->5->(closed) | cand_irred+z_entry+z_entry+z_entry
--   roles: abs=9, abs=10, abs=6, abs=6, abs=6, abs=6, abs=7, abs=7; 1 instances at bases [6]; all_strict=True; worst realized 3238949/3280365
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u669_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (124248:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u669_uniform
