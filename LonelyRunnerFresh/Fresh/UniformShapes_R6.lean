import Mathlib

/-!
# UniformShapes_R6: generated uniformity lemmas for the R6-edge killing shapes

GENERATED FILE (uniform_gen_v1.py, 76 theorems; regenerate, do not edit).  The half-line
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

-- u833 [6-edge cycle] 1->2->3->4->5->6->(closed) | cand_entry+z_entry+z_entry+z_entry+z_entry+z_entry
--   roles: abs=2, tied+1, tied+1, tied+3, tied=base, tied=base, tied=base, tied=base, tied+1, tied+1, tied+4, abs=1; 2 instances at bases [6, 7]; all_strict=True; worst realized 1708385931/2639478875
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 5). -/
theorem shape_u833_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (196608:ℚ) * m ^ 5 + (983040:ℚ) * m ^ 4 + (178176:ℚ) * m ^ 3 - (1228800:ℚ) * m ^ 2 - (636432:ℚ) * m + (4560:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have h3 : (0:ℚ) ≤ (m - 5) ^ 3 := by nlinarith
  have h4 : (0:ℚ) ≤ (m - 5) ^ 4 := by nlinarith
  have h5 : (0:ℚ) ≤ (m - 5) ^ 5 := by nlinarith
  have hshift : (196608:ℚ) * (m - 5) ^ 5 + (5898240:ℚ) * (m - 5) ^ 4 + (68990976:ℚ) * (m - 5) ^ 3 + (394659840:ℚ) * (m - 5) ^ 2 + (1106358768:ℚ) * (m - 5) + (1217174400:ℚ) = (196608:ℚ) * m ^ 5 + (983040:ℚ) * m ^ 4 + (178176:ℚ) * m ^ 3 - (1228800:ℚ) * m ^ 2 - (636432:ℚ) * m + (4560:ℚ) := by ring
  linarith [ht, h2, h3, h4, h5, hshift]
#print axioms shape_u833_uniform
-- u834 [6-edge cycle] 1->3->4->5->6->2->(closed) | cand_entry+z_entry+z_entry+z_entry+z_entry+z_entry
--   roles: abs=3, abs=7, abs=5, abs=5, abs=5, abs=5, abs=6, abs=6, abs=8, abs=6, abs=6, abs=2; 1 instances at bases [5]; all_strict=True; worst realized 186236309/231832341
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u834_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (957516672:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u834_uniform
-- u835 [6-edge cycle] 1->3->4->5->6->2->(closed) | cand_entry+z_entry+z_entry+z_entry+z_entry+z_entry
--   roles: abs=2, abs=13, abs=9, abs=9, abs=9, abs=9, abs=10, abs=10, abs=14, abs=12, abs=12, abs=1; 1 instances at bases [9]; all_strict=True; worst realized 879269013/1399810085
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u835_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (23424348240:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u835_uniform
-- u836 [6-edge cycle] 1->3->4->5->6->2->(closed) | cand_entry+z_entry+z_entry+z_entry+z_entry+z_irred
--   roles: abs=3, tied+2, tied=base, tied=base, tied=base, tied=base, tied+1, tied+1, tied+2, tied-3, abs=2, tied-3; 2 instances at bases [6, 7]; all_strict=True; worst realized 423605/558877
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 5). -/
theorem shape_u836_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (262144:ℚ) * m ^ 5 - (589824:ℚ) * m ^ 4 - (1323008:ℚ) * m ^ 3 + (1853952:ℚ) * m ^ 2 + (1712896:ℚ) * m - (2760:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have h3 : (0:ℚ) ≤ (m - 5) ^ 3 := by nlinarith
  have h4 : (0:ℚ) ≤ (m - 5) ^ 4 := by nlinarith
  have h5 : (0:ℚ) ≤ (m - 5) ^ 5 := by nlinarith
  have hshift : (262144:ℚ) * (m - 5) ^ 5 + (5963776:ℚ) * (m - 5) ^ 4 + (52416512:ℚ) * (m - 5) ^ 3 + (221215232:ℚ) * (m - 5) ^ 2 + (445314816:ℚ) * (m - 5) + (340094520:ℚ) = (262144:ℚ) * m ^ 5 - (589824:ℚ) * m ^ 4 - (1323008:ℚ) * m ^ 3 + (1853952:ℚ) * m ^ 2 + (1712896:ℚ) * m - (2760:ℚ) := by ring
  linarith [ht, h2, h3, h4, h5, hshift]
#print axioms shape_u836_uniform
-- u837 [6-edge cycle] 1->3->4->5->6->2->(closed) | cand_entry+z_entry+z_entry+z_entry+z_entry+z_irred
--   roles: abs=2, abs=14, abs=10, abs=10, abs=10, abs=10, abs=11, abs=11, abs=15, abs=13, abs=1, abs=10; 1 instances at bases [10]; all_strict=True; worst realized 1900773/3076813
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u837_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (30006660600:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u837_uniform
-- u838 [6-edge cycle] 1->3->4->5->6->2->(closed) | cand_entry+z_entry+z_entry+z_entry+z_irred+z_entry
--   roles: abs=3, abs=8, abs=6, abs=6, abs=6, abs=6, abs=7, abs=7, abs=5, abs=7, abs=6, abs=2; 1 instances at bases [6]; all_strict=True; worst realized 20694219/26267219
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u838_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (1588305000:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u838_uniform
-- u839 [6-edge cycle] 1->3->4->5->6->2->(closed) | cand_entry+z_entry+z_entry+z_entry+z_irred+z_entry
--   roles: tied-5, tied+2, tied=base, tied=base, tied=base, tied=base, tied+1, tied+1, tied-2, tied+1, tied-1, tied-6; 2 instances at bases [8, 9]; all_strict=True; worst realized 652136375/777760767
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 4). -/
theorem shape_u839_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (1998848:ℚ) * m ^ 4 - (3104768:ℚ) * m ^ 3 - (8072192:ℚ) * m ^ 2 - (2393728:ℚ) * m - (99000:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have h3 : (0:ℚ) ≤ (m - 5) ^ 3 := by nlinarith
  have h4 : (0:ℚ) ≤ (m - 5) ^ 4 := by nlinarith
  have hshift : (1998848:ℚ) * (m - 5) ^ 4 + (36872192:ℚ) * (m - 5) ^ 3 + (245183488:ℚ) * (m - 5) ^ 2 + (683450752:ℚ) * (m - 5) + (647311560:ℚ) = (1998848:ℚ) * m ^ 4 - (3104768:ℚ) * m ^ 3 - (8072192:ℚ) * m ^ 2 - (2393728:ℚ) * m - (99000:ℚ) := by ring
  linarith [ht, h2, h3, h4, hshift]
#print axioms shape_u839_uniform
-- u840 [6-edge cycle] 1->3->4->5->6->2->(closed) | cand_entry+z_entry+z_entry+z_entry+z_irred+z_entry
--   roles: abs=4, abs=12, abs=10, abs=10, abs=10, abs=10, abs=11, abs=11, abs=8, abs=11, abs=9, abs=3; 1 instances at bases [10]; all_strict=True; worst realized 334118925/398356789
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u840_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (17151509688:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u840_uniform
-- u841 [6-edge cycle] 1->3->4->5->6->2->(closed) | cand_entry+z_entry+z_entry+z_entry+z_irred+z_irred
--   roles: tied-1, tied+1, tied=base, tied=base, tied=base, tied=base, tied+1, tied+1, abs=5, tied+1, tied-2, abs=5; 3 instances at bases [5, 6, 7]; all_strict=True; worst realized 7138053/8160845
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 5). -/
theorem shape_u841_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (65536:ℚ) * m ^ 5 + (360448:ℚ) * m ^ 4 + (2459648:ℚ) * m ^ 3 + (3513344:ℚ) * m ^ 2 + (1274832:ℚ) * m + (30456:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have h3 : (0:ℚ) ≤ (m - 5) ^ 3 := by nlinarith
  have h4 : (0:ℚ) ≤ (m - 5) ^ 4 := by nlinarith
  have h5 : (0:ℚ) ≤ (m - 5) ^ 5 := by nlinarith
  have hshift : (65536:ℚ) * (m - 5) ^ 5 + (1998848:ℚ) * (m - 5) ^ 4 + (26052608:ℚ) * (m - 5) ^ 3 + (176395264:ℚ) * (m - 5) ^ 2 + (605905872:ℚ) * (m - 5) + (831774216:ℚ) = (65536:ℚ) * m ^ 5 + (360448:ℚ) * m ^ 4 + (2459648:ℚ) * m ^ 3 + (3513344:ℚ) * m ^ 2 + (1274832:ℚ) * m + (30456:ℚ) := by ring
  linarith [ht, h2, h3, h4, h5, hshift]
#print axioms shape_u841_uniform
-- u842 [6-edge cycle] 1->3->4->5->6->2->(closed) | cand_entry+z_entry+z_entry+z_entry+z_irred+z_irred
--   roles: abs=5, abs=6, abs=5, abs=5, abs=5, abs=5, abs=6, abs=6, abs=4, abs=6, abs=4, abs=4; 1 instances at bases [5]; all_strict=True; worst realized 79156609/92003769
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u842_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (629510840:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u842_uniform
-- u843 [6-edge cycle] 1->3->4->5->6->2->(closed) | cand_entry+z_entry+z_entry+z_entry+z_irred+z_irred
--   roles: abs=3, abs=8, abs=6, abs=6, abs=6, abs=6, abs=7, abs=7, abs=2, abs=7, abs=2, abs=2; 1 instances at bases [6]; all_strict=True; worst realized 7022925/9500909
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u843_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (706225440:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u843_uniform
-- u844 [6-edge cycle] 1->3->4->5->6->2->(closed) | cand_entry+z_entry+z_entry+z_entry+z_irred+z_irred
--   roles: abs=5, tied+1, tied=base, tied=base, tied=base, tied=base, tied+1, tied+1, tied=base, tied+1, abs=4, tied=base; 2 instances at bases [6, 7]; all_strict=True; worst realized 28861/33605
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 5). -/
theorem shape_u844_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (262144:ℚ) * m ^ 5 - (16384:ℚ) * m ^ 4 - (636928:ℚ) * m ^ 3 - (317696:ℚ) * m ^ 2 + (9888:ℚ) * m + (4968:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have h3 : (0:ℚ) ≤ (m - 5) ^ 3 := by nlinarith
  have h4 : (0:ℚ) ≤ (m - 5) ^ 4 := by nlinarith
  have h5 : (0:ℚ) ≤ (m - 5) ^ 5 := by nlinarith
  have hshift : (262144:ℚ) * (m - 5) ^ 5 + (6537216:ℚ) * (m - 5) ^ 4 + (64571392:ℚ) * (m - 5) ^ 3 + (315350784:ℚ) * (m - 5) ^ 2 + (760071328:ℚ) * (m - 5) + (721456008:ℚ) = (262144:ℚ) * m ^ 5 - (16384:ℚ) * m ^ 4 - (636928:ℚ) * m ^ 3 - (317696:ℚ) * m ^ 2 + (9888:ℚ) * m + (4968:ℚ) := by ring
  linarith [ht, h2, h3, h4, h5, hshift]
#print axioms shape_u844_uniform
-- u845 [6-edge cycle] 1->3->4->5->6->2->(closed) | cand_entry+z_entry+z_entry+z_entry+z_irred+z_irred
--   roles: abs=2, abs=10, abs=7, abs=7, abs=7, abs=7, abs=8, abs=8, abs=4, abs=8, abs=1, abs=4; 1 instances at bases [7]; all_strict=True; worst realized 100719/166375
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u845_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (2419751880:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u845_uniform
-- u846 [6-edge cycle] 1->3->4->5->6->2->(closed) | cand_entry+z_entry+z_entry+z_entry+z_irred+z_irred
--   roles: tied-5, abs=10, tied=base, tied=base, tied=base, tied=base, tied+1, tied+1, tied-2, tied+1, tied-6, tied-2; 2 instances at bases [7, 8]; all_strict=True; worst realized 2978625/3920833
/-- pattern tau=(): real half-line form, lukas certificate (kind ALL, strict=True, deg D = 6). -/
theorem shape_u846_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (262144:ℚ) * m ^ 6 - (4030464:ℚ) * m ^ 5 + (17686528:ℚ) * m ^ 4 - (1790976:ℚ) * m ^ 3 - (39389120:ℚ) * m ^ 2 - (10440408:ℚ) * m - (568512:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have hsq1 : (0:ℚ) ≤ (m - 5 + (39 / 16:ℚ)) ^ 2 := sq_nonneg _
  have hsq2 : (0:ℚ) ≤ (m - 5 + (-19 / 8:ℚ)) ^ 2 := sq_nonneg _
  have hq2_2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have hq2 : (0:ℚ) ≤ (262144:ℚ) * (m - 5) ^ 2 + (3801088:ℚ) * (m - 5) + (17787904:ℚ) := by linarith [ht, hq2_2]
  have hprod2 : (0:ℚ) ≤ (m - 5 + (-19 / 8:ℚ)) ^ 2 * ((262144:ℚ) * (m - 5) ^ 2 + (3801088:ℚ) * (m - 5) + (17787904:ℚ)) := mul_nonneg hsq2 hq2
  have hq1 : (0:ℚ) ≤ (m - 5 + (-19 / 8:ℚ)) ^ 2 * ((262144:ℚ) * (m - 5) ^ 2 + (3801088:ℚ) * (m - 5) + (17787904:ℚ)) + (41644416:ℚ) * (m - 5) + (3075300:ℚ) := by linarith [ht, hprod2]
  have hprod1 : (0:ℚ) ≤ (m - 5 + (39 / 16:ℚ)) ^ 2 * ((m - 5 + (-19 / 8:ℚ)) ^ 2 * ((262144:ℚ) * (m - 5) ^ 2 + (3801088:ℚ) * (m - 5) + (17787904:ℚ)) + (41644416:ℚ) * (m - 5) + (3075300:ℚ)) := mul_nonneg hsq1 hq1
  have hshift : (m - 5 + (39 / 16:ℚ)) ^ 2 * ((m - 5 + (-19 / 8:ℚ)) ^ 2 * ((262144:ℚ) * (m - 5) ^ 2 + (3801088:ℚ) * (m - 5) + (17787904:ℚ)) + (41644416:ℚ) * (m - 5) + (3075300:ℚ)) + (247675830:ℚ) * (m - 5) + (43462877643 / 64:ℚ) = (262144:ℚ) * m ^ 6 - (4030464:ℚ) * m ^ 5 + (17686528:ℚ) * m ^ 4 - (1790976:ℚ) * m ^ 3 - (39389120:ℚ) * m ^ 2 - (10440408:ℚ) * m - (568512:ℚ) := by ring
  linarith [ht, hprod1, hshift]
#print axioms shape_u846_uniform
-- u847 [6-edge cycle] 1->3->4->5->6->2->(closed) | cand_entry+z_entry+z_entry+z_entry+z_irred+z_irred
--   roles: abs=2, tied+3, tied=base, tied=base, tied=base, tied=base, tied+1, tied+1, tied-1, tied+1, abs=1, tied-1; 2 instances at bases [7, 8]; all_strict=True; worst realized 458109/741125
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 5). -/
theorem shape_u847_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (262144:ℚ) * m ^ 5 - (344064:ℚ) * m ^ 4 - (399360:ℚ) * m ^ 3 + (647936:ℚ) * m ^ 2 + (331296:ℚ) * m + (7560:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have h3 : (0:ℚ) ≤ (m - 5) ^ 3 := by nlinarith
  have h4 : (0:ℚ) ≤ (m - 5) ^ 4 := by nlinarith
  have h5 : (0:ℚ) ≤ (m - 5) ^ 5 := by nlinarith
  have hshift : (262144:ℚ) * (m - 5) ^ 5 + (6209536:ℚ) * (m - 5) ^ 4 + (58255360:ℚ) * (m - 5) ^ 3 + (270727936:ℚ) * (m - 5) ^ 2 + (624026656:ℚ) * (m - 5) + (572102440:ℚ) = (262144:ℚ) * m ^ 5 - (344064:ℚ) * m ^ 4 - (399360:ℚ) * m ^ 3 + (647936:ℚ) * m ^ 2 + (331296:ℚ) * m + (7560:ℚ) := by ring
  linarith [ht, h2, h3, h4, h5, hshift]
#print axioms shape_u847_uniform
-- u848 [6-edge cycle] 1->3->4->5->6->2->(closed) | cand_entry+z_entry+z_entry+z_entry+z_irred+z_irred
--   roles: abs=6, tied+1, tied=base, tied=base, tied=base, tied=base, tied+1, tied+1, tied-1, tied+1, abs=5, tied-1; 2 instances at bases [7, 8]; all_strict=True; worst realized 183027/207515
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 5). -/
theorem shape_u848_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (262144:ℚ) * m ^ 5 - (409600:ℚ) * m ^ 4 - (350208:ℚ) * m ^ 3 + (1196800:ℚ) * m ^ 2 + (793376:ℚ) * m + (7704:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have h3 : (0:ℚ) ≤ (m - 5) ^ 3 := by nlinarith
  have h4 : (0:ℚ) ≤ (m - 5) ^ 4 := by nlinarith
  have h5 : (0:ℚ) ≤ (m - 5) ^ 5 := by nlinarith
  have hshift : (262144:ℚ) * (m - 5) ^ 5 + (6144000:ℚ) * (m - 5) ^ 4 + (56993792:ℚ) * (m - 5) ^ 3 + (262183680:ℚ) * (m - 5) ^ 2 + (600895776:ℚ) * (m - 5) + (553318584:ℚ) = (262144:ℚ) * m ^ 5 - (409600:ℚ) * m ^ 4 - (350208:ℚ) * m ^ 3 + (1196800:ℚ) * m ^ 2 + (793376:ℚ) * m + (7704:ℚ) := by ring
  linarith [ht, h2, h3, h4, h5, hshift]
#print axioms shape_u848_uniform
-- u849 [6-edge cycle] 1->3->4->5->6->2->(closed) | cand_entry+z_entry+z_entry+z_entry+z_irred+z_irred
--   roles: abs=6, tied+1, tied=base, tied=base, tied=base, tied=base, tied+1, tied+1, tied=base, tied+1, abs=5, tied=base; 2 instances at bases [8, 9]; all_strict=True; worst realized 61685/70077
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 5). -/
theorem shape_u849_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (262144:ℚ) * m ^ 5 - (147456:ℚ) * m ^ 4 - (849920:ℚ) * m ^ 3 - (389376:ℚ) * m ^ 2 + (13216:ℚ) * m + (6120:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have h3 : (0:ℚ) ≤ (m - 5) ^ 3 := by nlinarith
  have h4 : (0:ℚ) ≤ (m - 5) ^ 4 := by nlinarith
  have h5 : (0:ℚ) ≤ (m - 5) ^ 5 := by nlinarith
  have hshift : (262144:ℚ) * (m - 5) ^ 5 + (6406144:ℚ) * (m - 5) ^ 4 + (61736960:ℚ) * (m - 5) ^ 3 + (292423424:ℚ) * (m - 5) ^ 2 + (677847456:ℚ) * (m - 5) + (611137800:ℚ) = (262144:ℚ) * m ^ 5 - (147456:ℚ) * m ^ 4 - (849920:ℚ) * m ^ 3 - (389376:ℚ) * m ^ 2 + (13216:ℚ) * m + (6120:ℚ) := by ring
  linarith [ht, h2, h3, h4, h5, hshift]
#print axioms shape_u849_uniform
-- u850 [6-edge cycle] 1->3->4->5->6->2->(closed) | cand_entry+z_entry+z_entry+z_entry+z_irred+z_irred
--   roles: abs=7, tied+1, tied=base, tied=base, tied=base, tied=base, tied+1, tied+1, tied-2, tied+1, abs=6, tied-2; 2 instances at bases [8, 9]; all_strict=True; worst realized 136262165/151889661
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 5). -/
theorem shape_u850_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (262144:ℚ) * m ^ 5 - (802816:ℚ) * m ^ 4 + (329728:ℚ) * m ^ 3 + (3415808:ℚ) * m ^ 2 + (1873824:ℚ) * m + (12744:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have h3 : (0:ℚ) ≤ (m - 5) ^ 3 := by nlinarith
  have h4 : (0:ℚ) ≤ (m - 5) ^ 4 := by nlinarith
  have h5 : (0:ℚ) ≤ (m - 5) ^ 5 := by nlinarith
  have hshift : (262144:ℚ) * (m - 5) ^ 5 + (5750784:ℚ) * (m - 5) ^ 4 + (49809408:ℚ) * (m - 5) ^ 3 + (215619328:ℚ) * (m - 5) ^ 2 + (478553504:ℚ) * (m - 5) + (453433064:ℚ) = (262144:ℚ) * m ^ 5 - (802816:ℚ) * m ^ 4 + (329728:ℚ) * m ^ 3 + (3415808:ℚ) * m ^ 2 + (1873824:ℚ) * m + (12744:ℚ) := by ring
  linarith [ht, h2, h3, h4, h5, hshift]
#print axioms shape_u850_uniform
-- u851 [6-edge cycle] 1->3->4->5->6->2->(closed) | cand_entry+z_entry+z_entry+z_entry+z_irred+z_irred
--   roles: abs=3, tied+2, tied=base, tied=base, tied=base, tied=base, tied+1, tied+1, tied-2, tied+1, abs=2, tied-2; 2 instances at bases [9, 10]; all_strict=True; worst realized 130427275/174030443
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 5). -/
theorem shape_u851_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (262144:ℚ) * m ^ 5 - (770048:ℚ) * m ^ 4 - (22528:ℚ) * m ^ 3 + (2174720:ℚ) * m ^ 2 + (974112:ℚ) * m + (17280:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have h3 : (0:ℚ) ≤ (m - 5) ^ 3 := by nlinarith
  have h4 : (0:ℚ) ≤ (m - 5) ^ 4 := by nlinarith
  have h5 : (0:ℚ) ≤ (m - 5) ^ 5 := by nlinarith
  have hshift : (262144:ℚ) * (m - 5) ^ 5 + (5783552:ℚ) * (m - 5) ^ 4 + (50112512:ℚ) * (m - 5) ^ 3 + (214009600:ℚ) * (m - 5) ^ 2 + (455207712:ℚ) * (m - 5) + (394359840:ℚ) = (262144:ℚ) * m ^ 5 - (770048:ℚ) * m ^ 4 - (22528:ℚ) * m ^ 3 + (2174720:ℚ) * m ^ 2 + (974112:ℚ) * m + (17280:ℚ) := by ring
  linarith [ht, h2, h3, h4, h5, hshift]
#print axioms shape_u851_uniform
-- u852 [6-edge cycle] 1->3->4->5->6->2->(closed) | cand_entry+z_entry+z_entry+z_entry+z_irred+z_irred
--   roles: abs=7, tied+1, tied=base, tied=base, tied=base, tied=base, tied+1, tied+1, tied-1, tied+1, abs=6, tied-1; 2 instances at bases [9, 10]; all_strict=True; worst realized 1278112689/1423704425
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 5). -/
theorem shape_u852_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (262144:ℚ) * m ^ 5 - (540672:ℚ) * m ^ 4 - (366592:ℚ) * m ^ 3 + (1477376:ℚ) * m ^ 2 + (945184:ℚ) * m + (10008:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have h3 : (0:ℚ) ≤ (m - 5) ^ 3 := by nlinarith
  have h4 : (0:ℚ) ≤ (m - 5) ^ 4 := by nlinarith
  have h5 : (0:ℚ) ≤ (m - 5) ^ 5 := by nlinarith
  have hshift : (262144:ℚ) * (m - 5) ^ 5 + (6012928:ℚ) * (m - 5) ^ 4 + (54355968:ℚ) * (m - 5) ^ 3 + (242557696:ℚ) * (m - 5) ^ 2 + (537088544:ℚ) * (m - 5) + (477126328:ℚ) = (262144:ℚ) * m ^ 5 - (540672:ℚ) * m ^ 4 - (366592:ℚ) * m ^ 3 + (1477376:ℚ) * m ^ 2 + (945184:ℚ) * m + (10008:ℚ) := by ring
  linarith [ht, h2, h3, h4, h5, hshift]
#print axioms shape_u852_uniform
-- u853 [6-edge cycle] 1->3->4->5->6->2->(closed) | cand_entry+z_entry+z_entry+z_entry+z_irred+z_irred
--   roles: abs=3, abs=12, abs=10, abs=10, abs=10, abs=10, abs=11, abs=11, abs=9, abs=11, abs=2, abs=9; 1 instances at bases [10]; all_strict=True; worst realized 225928035/303880531
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u853_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (20813316432:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u853_uniform
-- u854 [6-edge cycle] 1->3->4->5->6->2->(closed) | cand_entry+z_entry+z_entry+z_entry+z_irred+z_irred
--   roles: abs=3, abs=12, abs=10, abs=10, abs=10, abs=10, abs=11, abs=11, abs=10, abs=11, abs=2, abs=10; 1 instances at bases [10]; all_strict=True; worst realized 39285/52693
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u854_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (22908010464:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u854_uniform
-- u855 [6-edge cycle] 1->3->4->5->6->2->(closed) | cand_entry+z_entry+z_entry+z_entry+z_irred+z_irred
--   roles: abs=7, abs=11, abs=10, abs=10, abs=10, abs=10, abs=11, abs=11, abs=10, abs=11, abs=6, abs=10; 1 instances at bases [10]; all_strict=True; worst realized 112941/126005
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u855_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (22320275112:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u855_uniform
-- u856 [6-edge cycle] 1->3->4->5->6->2->(closed) | cand_entry+z_entry+z_entry+z_entry+z_irred+z_irred
--   roles: abs=8, abs=11, abs=10, abs=10, abs=10, abs=10, abs=11, abs=11, abs=8, abs=11, abs=7, abs=8; 1 instances at bases [10]; all_strict=True; worst realized 2141073/2352857
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u856_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (17812093320:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u856_uniform
-- u857 [6-edge cycle] 1->3->4->5->6->2->(closed) | cand_irred+z_entry+z_entry+z_entry+z_entry+z_irred
--   roles: abs=8, abs=2, abs=6, abs=6, abs=6, abs=6, abs=7, abs=7, abs=8, abs=3, abs=2, abs=3; 1 instances at bases [6]; all_strict=True; worst realized 410571/413083
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u857_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (19782000:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u857_uniform
-- u858 [6-edge cycle] 1->3->4->5->6->2->(closed) | cand_irred+z_entry+z_entry+z_entry+z_irred+z_irred
--   roles: abs=10, abs=1, abs=7, abs=7, abs=7, abs=7, abs=8, abs=8, abs=4, abs=8, abs=1, abs=4; 1 instances at bases [7]; all_strict=True; worst realized 884089/898425
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u858_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (58705920:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u858_uniform
-- u859 [6-edge cycle] 1->3->4->5->6->2->(closed) | cand_irred+z_entry+z_entry+z_entry+z_irred+z_irred
--   roles: abs=10, abs=1, abs=7, abs=7, abs=7, abs=7, abs=8, abs=8, abs=5, abs=8, abs=1, abs=5; 1 instances at bases [7]; all_strict=True; worst realized 370747/372075
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u859_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (16314480:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u859_uniform
-- u860 [6-edge cycle] 1->3->4->5->6->2->(closed) | cand_irred+z_entry+z_entry+z_entry+z_irred+z_irred
--   roles: abs=11, abs=1, abs=8, abs=8, abs=8, abs=8, abs=9, abs=9, abs=8, abs=9, abs=1, abs=8; 1 instances at bases [8]; all_strict=True; worst realized 1885/1917
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u860_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (200884320:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u860_uniform
-- u861 [6-edge cycle] 1->3->4->5->6->2->(closed) | cand_irred+z_entry+z_entry+z_entry+z_irred+z_irred
--   roles: abs=11, abs=2, abs=9, abs=9, abs=9, abs=9, abs=10, abs=10, abs=7, abs=10, abs=2, abs=7; 1 instances at bases [9]; all_strict=True; worst realized 127496325/128631197
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u861_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (275773896:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u861_uniform
-- u862 [6-edge cycle] 1->4->2->5->6->3->(closed) | cand_entry+z_entry+z_entry+z_entry+z_entry+z_entry
--   roles: abs=3, abs=10, abs=10, abs=6, abs=5, abs=8, abs=8, abs=8, abs=8, abs=7, abs=9, abs=2; 1 instances at bases [7]; all_strict=True; worst realized 104975/129007
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u862_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (3719937312:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u862_uniform
-- u863 [6-edge cycle] 1->4->2->5->6->3->(closed) | cand_entry+z_entry+z_entry+z_entry+z_entry+z_entry
--   roles: abs=4, abs=10, abs=10, abs=6, abs=5, abs=8, abs=8, abs=8, abs=8, abs=7, abs=9, abs=3; 1 instances at bases [7]; all_strict=True; worst realized 154375/173879
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u863_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (3019043664:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u863_uniform
-- u864 [6-edge cycle] 1->4->2->5->6->3->(closed) | cand_entry+z_entry+z_entry+z_entry+z_entry+z_irred
--   roles: abs=3, abs=10, abs=10, abs=6, abs=5, abs=8, abs=8, abs=8, abs=8, abs=7, abs=2, abs=8; 1 instances at bases [7]; all_strict=True; worst realized 1425/1817
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u864_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (3944074680:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u864_uniform
-- u865 [6-edge cycle] 1->4->5->6->3->2->(closed) | cand_entry+z_entry+z_entry+z_entry+z_entry+z_entry
--   roles: abs=3, abs=10, abs=7, abs=7, abs=8, abs=8, abs=8, abs=7, abs=8, abs=4, abs=5, abs=2; 1 instances at bases [7]; all_strict=True; worst realized 6137/7889
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u865_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (2739611160:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u865_uniform
-- u866 [6-edge cycle] 1->4->5->6->3->2->(closed) | cand_entry+z_entry+z_entry+z_entry+z_entry+z_irred
--   roles: abs=3, tied+2, tied=base, tied=base, tied+1, tied+1, tied+1, tied=base, tied+1, tied-2, abs=2, tied-2; 2 instances at bases [5, 6]; all_strict=True; worst realized 23475165/31043077
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 5). -/
theorem shape_u866_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (262144:ℚ) * m ^ 5 - (327680:ℚ) * m ^ 4 - (405504:ℚ) * m ^ 3 + (154112:ℚ) * m ^ 2 - (24832:ℚ) * m + (152760:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have h3 : (0:ℚ) ≤ (m - 5) ^ 3 := by nlinarith
  have h4 : (0:ℚ) ≤ (m - 5) ^ 4 := by nlinarith
  have h5 : (0:ℚ) ≤ (m - 5) ^ 5 := by nlinarith
  have hshift : (262144:ℚ) * (m - 5) ^ 5 + (6225920:ℚ) * (m - 5) ^ 4 + (58576896:ℚ) * (m - 5) ^ 3 + (272599552:ℚ) * (m - 5) ^ 2 + (626463488:ℚ) * (m - 5) + (567593400:ℚ) = (262144:ℚ) * m ^ 5 - (327680:ℚ) * m ^ 4 - (405504:ℚ) * m ^ 3 + (154112:ℚ) * m ^ 2 - (24832:ℚ) * m + (152760:ℚ) := by ring
  linarith [ht, h2, h3, h4, h5, hshift]
#print axioms shape_u866_uniform
-- u867 [6-edge cycle] 1->4->5->6->3->2->(closed) | cand_entry+z_entry+z_entry+z_entry+z_entry+z_irred
--   roles: abs=3, tied+2, tied=base, tied=base, tied+1, tied+1, tied+1, tied=base, tied+1, tied-1, abs=2, tied-1; 2 instances at bases [5, 6]; all_strict=True; worst realized 23475165/31043077
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 5). -/
theorem shape_u867_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (262144:ℚ) * m ^ 5 - (65536:ℚ) * m ^ 4 - (241664:ℚ) * m ^ 3 + (55808:ℚ) * m ^ 2 - (55040:ℚ) * m + (71288:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have h3 : (0:ℚ) ≤ (m - 5) ^ 3 := by nlinarith
  have h4 : (0:ℚ) ≤ (m - 5) ^ 4 := by nlinarith
  have h5 : (0:ℚ) ≤ (m - 5) ^ 5 := by nlinarith
  have hshift : (262144:ℚ) * (m - 5) ^ 5 + (6488064:ℚ) * (m - 5) ^ 4 + (63983616:ℚ) * (m - 5) ^ 3 + (314280448:ℚ) * (m - 5) ^ 2 + (768810240:ℚ) * (m - 5) + (749223288:ℚ) = (262144:ℚ) * m ^ 5 - (65536:ℚ) * m ^ 4 - (241664:ℚ) * m ^ 3 + (55808:ℚ) * m ^ 2 - (55040:ℚ) * m + (71288:ℚ) := by ring
  linarith [ht, h2, h3, h4, h5, hshift]
#print axioms shape_u867_uniform
-- u868 [6-edge cycle] 1->4->5->6->3->2->(closed) | cand_entry+z_entry+z_entry+z_entry+z_entry+z_irred
--   roles: abs=2, tied+4, tied=base, tied=base, tied+1, tied+1, tied+1, tied=base, tied+1, tied-2, abs=1, tied-2; 2 instances at bases [8, 9]; all_strict=True; worst realized 5983445/9663597
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 5). -/
theorem shape_u868_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (262144:ℚ) * m ^ 5 - (524288:ℚ) * m ^ 4 - (339968:ℚ) * m ^ 3 + (655872:ℚ) * m ^ 2 + (123648:ℚ) * m + (108360:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have h3 : (0:ℚ) ≤ (m - 5) ^ 3 := by nlinarith
  have h4 : (0:ℚ) ≤ (m - 5) ^ 4 := by nlinarith
  have h5 : (0:ℚ) ≤ (m - 5) ^ 5 := by nlinarith
  have hshift : (262144:ℚ) * (m - 5) ^ 5 + (6029312:ℚ) * (m - 5) ^ 4 + (54710272:ℚ) * (m - 5) ^ 3 + (244593152:ℚ) * (m - 5) ^ 2 + (538240768:ℚ) * (m - 5) + (466147400:ℚ) = (262144:ℚ) * m ^ 5 - (524288:ℚ) * m ^ 4 - (339968:ℚ) * m ^ 3 + (655872:ℚ) * m ^ 2 + (123648:ℚ) * m + (108360:ℚ) := by ring
  linarith [ht, h2, h3, h4, h5, hshift]
#print axioms shape_u868_uniform
-- u869 [6-edge cycle] 1->4->5->6->3->2->(closed) | cand_entry+z_entry+z_entry+z_entry+z_entry+z_irred
--   roles: abs=4, tied+2, tied=base, tied=base, tied+1, tied+1, tied+1, tied=base, tied+1, tied-2, abs=3, tied-2; 2 instances at bases [8, 9]; all_strict=True; worst realized 63843975/77666687
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 5). -/
theorem shape_u869_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (262144:ℚ) * m ^ 5 - (589824:ℚ) * m ^ 4 - (241664:ℚ) * m ^ 3 + (698880:ℚ) * m ^ 2 + (73984:ℚ) * m + (212280:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have h3 : (0:ℚ) ≤ (m - 5) ^ 3 := by nlinarith
  have h4 : (0:ℚ) ≤ (m - 5) ^ 4 := by nlinarith
  have h5 : (0:ℚ) ≤ (m - 5) ^ 5 := by nlinarith
  have hshift : (262144:ℚ) * (m - 5) ^ 5 + (5963776:ℚ) * (m - 5) ^ 4 + (53497856:ℚ) * (m - 5) ^ 3 + (236280320:ℚ) * (m - 5) ^ 2 + (513225984:ℚ) * (m - 5) + (438406200:ℚ) = (262144:ℚ) * m ^ 5 - (589824:ℚ) * m ^ 4 - (241664:ℚ) * m ^ 3 + (698880:ℚ) * m ^ 2 + (73984:ℚ) * m + (212280:ℚ) := by ring
  linarith [ht, h2, h3, h4, h5, hshift]
#print axioms shape_u869_uniform
-- u870 [6-edge cycle] 1->4->5->6->3->2->(closed) | cand_entry+z_entry+z_entry+z_entry+z_entry+z_irred
--   roles: abs=2, abs=13, abs=9, abs=9, abs=10, abs=10, abs=10, abs=9, abs=10, abs=8, abs=1, abs=8; 1 instances at bases [9]; all_strict=True; worst realized 21150801/35005769
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u870_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (13508593800:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u870_uniform
-- u871 [6-edge cycle] 1->4->5->6->3->2->(closed) | cand_entry+z_entry+z_entry+z_entry+z_entry+z_irred
--   roles: abs=4, abs=12, abs=10, abs=10, abs=11, abs=11, abs=11, abs=10, abs=11, abs=9, abs=3, abs=9; 1 instances at bases [10]; all_strict=True; worst realized 48249837/59728661
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u871_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (22624762104:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u871_uniform
-- u872 [6-edge cycle] 1->6->3->4->5->2->(closed) | cand_entry+z_entry+z_entry+z_entry+z_entry+z_irred
--   roles: abs=3, abs=8, abs=6, abs=5, abs=5, abs=5, abs=5, abs=5, abs=7, abs=2, abs=2, abs=2; 1 instances at bases [5]; all_strict=True; worst realized 344605/463749
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u872_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (394962360:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u872_uniform
-- u873 [6-edge cycle] 1->6->3->4->5->2->(closed) | cand_entry+z_entry+z_entry+z_entry+z_entry+z_irred
--   roles: abs=2, abs=12, abs=7, abs=6, abs=6, abs=6, abs=6, abs=6, abs=9, abs=1, abs=1, abs=1; 1 instances at bases [6]; all_strict=True; worst realized 79883671/129392175
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u873_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (445576536:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u873_uniform
-- u874 [6-edge cycle] 2->3->4->5->6->1->(closed) | cand_entry+z_entry+z_entry+z_entry+z_entry+z_entry
--   roles: abs=3, abs=7, abs=5, abs=5, abs=5, abs=5, abs=6, abs=6, abs=8, abs=2, abs=2, abs=2; 1 instances at bases [5]; all_strict=True; worst realized 64612597/73989045
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u874_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (196905408:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u874_uniform
-- u875 [6-edge cycle] 2->3->4->5->6->1->(closed) | cand_entry+z_entry+z_entry+z_entry+z_entry+z_entry
--   roles: abs=10, abs=10, abs=7, abs=7, abs=7, abs=7, abs=8, abs=8, abs=11, abs=1, abs=1, abs=7; 1 instances at bases [7]; all_strict=True; worst realized 65002743/67916695
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u875_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (393383520:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u875_uniform
-- u876 [6-edge cycle] 2->3->4->5->6->1->(closed) | cand_entry+z_entry+z_entry+z_entry+z_entry+z_entry
--   roles: abs=14, abs=14, abs=10, abs=10, abs=10, abs=10, abs=11, abs=11, abs=15, abs=1, abs=1, abs=10; 1 instances at bases [10]; all_strict=True; worst realized 5344702137/5578261969
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u876_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (2102038488:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u876_uniform
-- u877 [6-edge cycle] 2->3->4->5->6->1->(closed) | cand_entry+z_entry+z_entry+z_entry+z_irred+z_irred
--   roles: abs=6, abs=6, abs=5, abs=5, abs=5, abs=5, abs=6, abs=6, abs=3, abs=6, abs=5, abs=3; 1 instances at bases [5]; all_strict=True; worst realized 1894487/2153775
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u877_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (495499368:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u877_uniform
-- u878 [6-edge cycle] 2->3->4->5->6->1->(closed) | cand_progress+z_entry+z_entry+z_entry+z_entry+z_entry
--   roles: abs=8, abs=8, abs=6, abs=6, abs=6, abs=6, abs=7, abs=7, abs=10, abs=1, abs=1, abs=6; 1 instances at bases [6]; all_strict=True; worst realized 8621991/9598105
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u878_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (444131870:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u878_uniform
-- u879 [6-edge cycle] 2->4->5->6->3->1->(closed) | cand_progress+z_entry+z_entry+z_entry+z_entry+z_irred
--   roles: abs=9, abs=7, abs=7, abs=7, abs=8, abs=8, abs=8, abs=7, abs=9, abs=2, abs=7, abs=2; 1 instances at bases [7]; all_strict=True; worst realized 90155/93933
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u879_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (604045530:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u879_uniform
-- u880 [6-edge cycle] 2->4->5->6->3->1->(closed) | cand_progress+z_entry+z_entry+z_entry+z_entry+z_irred
--   roles: abs=9, abs=7, abs=7, abs=7, abs=8, abs=8, abs=8, abs=7, abs=9, abs=3, abs=7, abs=3; 1 instances at bases [7]; all_strict=True; worst realized 90155/93933
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u880_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (888302250:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u880_uniform
-- u881 [6-edge cycle] 2->4->5->6->3->1->(closed) | cand_progress+z_entry+z_entry+z_entry+z_irred+z_progress
--   roles: free+2..+3, abs=4, tied=base, tied=base, tied+1, tied+1, tied+1, tied=base, abs=1, tied+1, abs=4, abs=1; 3 instances at bases [5, 6]; all_strict=True; worst realized 58835/59643
/-- pattern tau=(2): real half-line form, mono certificate (kind ALL, strict=True, deg D = 4). -/
theorem shape_u881_pat1_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (270336:ℚ) * m ^ 4 + (33792:ℚ) * m ^ 3 - (156288:ℚ) * m ^ 2 + (18480:ℚ) * m - (166320:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have h3 : (0:ℚ) ≤ (m - 5) ^ 3 := by nlinarith
  have h4 : (0:ℚ) ≤ (m - 5) ^ 4 := by nlinarith
  have hshift : (270336:ℚ) * (m - 5) ^ 4 + (5440512:ℚ) * (m - 5) ^ 3 + (40900992:ℚ) * (m - 5) ^ 2 + (136158000:ℚ) * (m - 5) + (169202880:ℚ) = (270336:ℚ) * m ^ 4 + (33792:ℚ) * m ^ 3 - (156288:ℚ) * m ^ 2 + (18480:ℚ) * m - (166320:ℚ) := by ring
  linarith [ht, h2, h3, h4, hshift]
#print axioms shape_u881_pat1_uniform
/-- pattern tau=(3): real half-line form, mono certificate (kind ALL, strict=True, deg D = 4). -/
theorem shape_u881_pat2_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (270336:ℚ) * m ^ 4 - (912384:ℚ) * m ^ 3 - (1457280:ℚ) * m ^ 2 - (262416:ℚ) * m - (182952:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have h3 : (0:ℚ) ≤ (m - 5) ^ 3 := by nlinarith
  have h4 : (0:ℚ) ≤ (m - 5) ^ 4 := by nlinarith
  have hshift : (270336:ℚ) * (m - 5) ^ 4 + (4494336:ℚ) * (m - 5) ^ 3 + (25407360:ℚ) * (m - 5) ^ 2 + (51903984:ℚ) * (m - 5) + (16984968:ℚ) = (270336:ℚ) * m ^ 4 - (912384:ℚ) * m ^ 3 - (1457280:ℚ) * m ^ 2 - (262416:ℚ) * m - (182952:ℚ) := by ring
  linarith [ht, h2, h3, h4, hshift]
#print axioms shape_u881_pat2_uniform
-- u882 [6-edge cycle] 2->4->5->6->3->1->(closed) | cand_progress+z_entry+z_entry+z_entry+z_irred+z_progress
--   roles: abs=10, abs=7, abs=8, abs=8, abs=9, abs=9, abs=9, abs=8, abs=2, abs=9, abs=7, abs=2; 1 instances at bases [8]; all_strict=True; worst realized 570375/599879
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u882_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (1104895296:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u882_uniform
-- u883 [6-edge cycle] 2->5->6->3->4->1->(closed) | cand_entry+z_entry+z_entry+z_entry+z_entry+z_entry
--   roles: abs=4, abs=11, abs=7, abs=7, abs=7, abs=6, abs=6, abs=6, abs=10, abs=1, abs=1, abs=2; 1 instances at bases [6]; all_strict=True; worst realized 266225967/348186575
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u883_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (573724256:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u883_uniform
-- u884 [6-edge cycle] 2->5->6->3->4->1->(closed) | cand_entry+z_entry+z_entry+z_entry+z_entry+z_entry
--   roles: abs=9, abs=13, abs=9, abs=9, abs=9, abs=8, abs=8, abs=8, abs=12, abs=1, abs=1, abs=6; 1 instances at bases [8]; all_strict=True; worst realized 6476925/6800309
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u884_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (713061720:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u884_uniform
-- u885 [6-edge cycle] 2->5->6->3->4->1->(closed) | cand_entry+z_entry+z_entry+z_entry+z_entry+z_irred
--   roles: abs=5, abs=9, abs=6, abs=6, abs=6, abs=5, abs=5, abs=5, abs=8, abs=1, abs=4, abs=1; 1 instances at bases [5]; all_strict=True; worst realized 26628721/30239001
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u885_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (227447640:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u885_uniform
-- u886 [6-edge cycle] 2->6->3->4->5->1->(closed) | cand_entry+z_entry+z_entry+z_entry+z_irred+z_irred
--   roles: abs=10, abs=11, abs=8, abs=7, abs=7, abs=7, abs=7, abs=7, abs=1, abs=8, abs=9, abs=1; 1 instances at bases [7]; all_strict=True; worst realized 43342021/46600125
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u886_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (615781656:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u886_uniform
-- u887 [6-edge cycle] 2->6->3->4->5->1->(closed) | cand_entry+z_entry+z_entry+z_entry+z_irred+z_irred
--   roles: abs=9, abs=11, abs=9, abs=8, abs=8, abs=8, abs=8, abs=8, abs=2, abs=9, abs=8, abs=2; 1 instances at bases [8]; all_strict=True; worst realized 122208125/131373501
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u887_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (1732256064:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u887_uniform
-- u888 [6-edge cycle] 2->6->3->4->5->1->(closed) | cand_irred+z_entry+z_entry+z_entry+z_irred+z_irred
--   roles: abs=11, abs=8, abs=9, abs=8, abs=8, abs=8, abs=8, abs=8, abs=2, abs=9, abs=8, abs=2; 1 instances at bases [8]; all_strict=True; worst realized 612625/616777
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u888_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (153021960:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u888_uniform
-- u889 [6-edge cycle] 2->6->3->4->5->1->(closed) | cand_progress+z_entry+z_entry+z_entry+z_entry+z_entry
--   roles: abs=11, abs=8, abs=8, abs=7, abs=7, abs=7, abs=7, abs=7, abs=11, abs=1, abs=1, abs=6; 1 instances at bases [7]; all_strict=True; worst realized 5494059/5702125
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u889_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (275271318:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u889_uniform
-- u890 [6-edge cycle] 2->6->3->4->5->1->(closed) | cand_progress+z_entry+z_entry+z_entry+z_irred+z_progress
--   roles: abs=12, abs=10, abs=11, abs=10, abs=10, abs=10, abs=10, abs=10, abs=2, abs=11, abs=10, abs=2; 1 instances at bases [10]; all_strict=True; worst realized 257748885/273836357
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u890_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (3909255696:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u890_uniform
-- u891 [6-edge cycle] 3->2->1->4->5->6->(closed) | cand_progress+z_entry+z_entry+z_entry+z_entry+z_entry
--   roles: abs=11, abs=13, abs=12, abs=1, abs=1, abs=10, abs=9, abs=9, abs=10, abs=10, abs=10, abs=9; 1 instances at bases [9]; all_strict=True; worst realized 9335272923/10313408525
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u891_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (2934406806:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u891_uniform
-- u892 [6-edge cycle] 3->4->5->6->2->1->(closed) | cand_progress+z_entry+z_entry+z_irred+z_irred+z_progress
--   roles: abs=8, abs=8, abs=6, abs=6, abs=7, abs=7, abs=2, abs=7, abs=2, abs=2, abs=8, abs=2; 1 instances at bases [6]; all_strict=True; worst realized 143325/149413
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u892_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (112780200:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u892_uniform
-- u893 [6-edge cycle] 3->4->5->6->2->1->(closed) | cand_progress+z_entry+z_entry+z_irred+z_irred+z_progress
--   roles: abs=11, abs=11, abs=8, abs=8, abs=9, abs=9, abs=7, abs=9, abs=1, abs=7, abs=11, abs=1; 1 instances at bases [8]; all_strict=True; worst realized 318175/327807
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u893_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (438053728:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u893_uniform
-- u894 [6-edge cycle] 4->1->2->5->6->3->(closed) | cand_progress+z_entry+z_entry+z_entry+z_entry+z_entry
--   roles: abs=2, tied+2, abs=3, abs=3, abs=3, tied+1, tied+1, tied+1, tied+1, tied=base, tied=base, tied=base; 2 instances at bases [5, 6]; all_strict=True; worst realized 132614433/195547495
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 4). -/
theorem shape_u894_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (425984:ℚ) * m ^ 4 + (3773440:ℚ) * m ^ 3 + (5457536:ℚ) * m ^ 2 + (1698672:ℚ) * m - (475082:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have h3 : (0:ℚ) ≤ (m - 5) ^ 3 := by nlinarith
  have h4 : (0:ℚ) ≤ (m - 5) ^ 4 := by nlinarith
  have hshift : (425984:ℚ) * (m - 5) ^ 4 + (12293120:ℚ) * (m - 5) ^ 3 + (125956736:ℚ) * (m - 5) ^ 2 + (552274032:ℚ) * (m - 5) + (882376678:ℚ) = (425984:ℚ) * m ^ 4 + (3773440:ℚ) * m ^ 3 + (5457536:ℚ) * m ^ 2 + (1698672:ℚ) * m - (475082:ℚ) := by ring
  linarith [ht, h2, h3, h4, hshift]
#print axioms shape_u894_uniform
-- u895 [6-edge cycle] 4->1->2->5->6->3->(closed) | cand_progress+z_entry+z_entry+z_entry+z_entry+z_entry
--   roles: abs=2, abs=9, abs=3, abs=4, abs=4, abs=8, abs=8, abs=8, abs=8, abs=7, abs=7, abs=7; 1 instances at bases [7]; all_strict=True; worst realized 5185765/7651203
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u895_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (3661175430:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u895_uniform
-- u896 [6-edge cycle] 4->1->2->5->6->3->(closed) | cand_progress+z_entry+z_entry+z_entry+z_entry+z_entry
--   roles: abs=2, tied+2, abs=3, tied-2, tied-2, tied+1, tied+1, tied+1, tied+1, tied=base, tied=base, tied=base; 2 instances at bases [7, 8]; all_strict=True; worst realized 2679287975/3972555009
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 5). -/
theorem shape_u896_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (196608:ℚ) * m ^ 5 + (876544:ℚ) * m ^ 4 - (1406976:ℚ) * m ^ 3 - (3872512:ℚ) * m ^ 2 - (1504976:ℚ) * m + (346358:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have h3 : (0:ℚ) ≤ (m - 5) ^ 3 := by nlinarith
  have h4 : (0:ℚ) ≤ (m - 5) ^ 4 := by nlinarith
  have h5 : (0:ℚ) ≤ (m - 5) ^ 5 := by nlinarith
  have hshift : (196608:ℚ) * (m - 5) ^ 5 + (5791744:ℚ) * (m - 5) ^ 4 + (65275904:ℚ) * (m - 5) ^ 3 + (352264448:ℚ) * (m - 5) ^ 2 + (906918704:ℚ) * (m - 5) + (882376678:ℚ) = (196608:ℚ) * m ^ 5 + (876544:ℚ) * m ^ 4 - (1406976:ℚ) * m ^ 3 - (3872512:ℚ) * m ^ 2 - (1504976:ℚ) * m + (346358:ℚ) := by ring
  linarith [ht, h2, h3, h4, h5, hshift]
#print axioms shape_u896_uniform
-- u897 [6-edge cycle] 4->1->2->5->6->3->(closed) | cand_progress+z_entry+z_entry+z_entry+z_entry+z_entry
--   roles: abs=2, abs=9, abs=3, abs=6, abs=6, abs=8, abs=8, abs=8, abs=8, abs=7, abs=7, abs=7; 1 instances at bases [7]; all_strict=True; worst realized 5185765/7812387
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u897_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (5791701510:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u897_uniform
-- u898 [6-edge cycle] 4->1->2->5->6->3->(closed) | cand_progress+z_entry+z_entry+z_entry+z_entry+z_entry
--   roles: abs=3, abs=11, abs=4, abs=7, abs=7, abs=10, abs=10, abs=10, abs=10, abs=9, abs=9, abs=9; 1 instances at bases [9]; all_strict=True; worst realized 9964617165/13447975739
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u898_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (17416792870:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u898_uniform
-- u899 [6-edge cycle] 4->2->1->5->6->3->(closed) | cand_progress+z_entry+z_entry+z_entry+z_entry+z_entry
--   roles: abs=3, abs=7, abs=4, abs=2, abs=2, abs=6, abs=6, abs=6, abs=6, abs=5, abs=5, abs=5; 1 instances at bases [5]; all_strict=True; worst realized 343066885/456686451
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u899_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (568097830:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u899_uniform
-- u900 [6-edge cycle] 4->2->1->5->6->3->(closed) | cand_progress+z_entry+z_entry+z_entry+z_entry+z_entry
--   roles: abs=4, abs=7, abs=5, abs=2, abs=2, abs=6, abs=6, abs=6, abs=6, abs=5, abs=5, abs=5; 1 instances at bases [5]; all_strict=True; worst realized 754747147/957568365
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u900_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (608463654:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u900_uniform
-- u901 [6-edge cycle] 4->2->1->5->6->3->(closed) | cand_progress+z_entry+z_entry+z_entry+z_entry+z_entry
--   roles: abs=5, abs=7, abs=6, abs=2, abs=2, abs=6, abs=6, abs=6, abs=6, abs=5, abs=5, abs=5; 1 instances at bases [5]; all_strict=True; worst realized 2813148457/3461977935
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u901_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (648829478:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u901_uniform
-- u902 [6-edge cycle] 5->2->1->6->3->4->(closed) | cand_progress+z_entry+z_entry+z_entry+z_entry+z_entry
--   roles: abs=6, abs=12, abs=7, abs=1, abs=1, abs=9, abs=8, abs=7, abs=7, abs=7, abs=7, abs=7; 1 instances at bases [7]; all_strict=True; worst realized 13519089/16138375
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u902_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (1155105126:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u902_uniform
-- u903 [6-edge cycle] 5->6->3->4->1->2->(closed) | cand_progress+z_entry+z_entry+z_entry+z_entry+z_entry
--   roles: abs=13, abs=13, abs=9, abs=8, abs=8, abs=8, abs=12, abs=1, abs=1, abs=6, abs=6, abs=9; 1 instances at bases [8]; all_strict=True; worst realized 61685/63403
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u903_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (397759950:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u903_uniform
-- u904 [6-edge cycle] 5->6->3->4->1->2->(closed) | cand_progress+z_entry+z_entry+z_entry+z_irred+z_entry
--   roles: abs=9, abs=9, abs=6, abs=5, abs=5, abs=5, abs=8, abs=1, abs=4, abs=1, abs=3, abs=6; 1 instances at bases [5]; all_strict=True; worst realized 364777/379431
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u904_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (67393746:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u904_uniform
-- u905 [6-edge cycle] 6->2->1->3->4->5->(closed) | cand_irred+z_irred+z_irred+z_entry+z_entry+z_entry
--   roles: abs=8, abs=11, abs=1, abs=6, abs=10, abs=1, abs=7, abs=7, abs=7, abs=7, abs=8, abs=8; 1 instances at bases [7]; all_strict=True; worst realized 370747/376915
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u905_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (122403960:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u905_uniform
-- u906 [6-edge cycle] 6->2->1->3->4->5->(closed) | cand_irred+z_irred+z_irred+z_entry+z_entry+z_entry
--   roles: abs=12, abs=15, abs=1, abs=9, abs=14, abs=1, abs=10, abs=10, abs=10, abs=10, abs=11, abs=11; 1 instances at bases [10]; all_strict=True; worst realized 1596397005/1598675837
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u906_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (61528464:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u906_uniform
-- u907 [6-edge cycle] 6->3->4->1->2->5->(closed) | cand_progress+z_entry+z_entry+z_entry+z_entry+z_entry
--   roles: abs=11, abs=13, abs=8, abs=8, abs=12, abs=1, abs=1, abs=6, abs=6, abs=9, abs=9, abs=9; 1 instances at bases [8]; all_strict=True; worst realized 6165653/6657315
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u907_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (1084114710:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u907_uniform
