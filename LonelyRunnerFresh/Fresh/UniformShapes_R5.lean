import Mathlib

/-!
# UniformShapes_R5: generated uniformity lemmas for the R5-edge killing shapes

GENERATED FILE (uniform_gen_v1.py, 180 theorems; regenerate, do not edit).  The half-line
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

-- u670 [5-edge cycle] 1->2->5->6->3->(closed) | cand_entry+z_entry+z_entry+z_entry+z_entry
--   roles: abs=3, abs=7, abs=6, abs=8, abs=8, abs=8, abs=8, abs=7, abs=9, abs=2; 1 instances at bases [7]; all_strict=True; worst realized 25928825/33847191
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u670_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (71265294:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u670_uniform
-- u671 [5-edge cycle] 1->2->5->6->3->(closed) | cand_entry+z_entry+z_entry+z_entry+z_entry
--   roles: abs=4, abs=7, abs=6, abs=8, abs=8, abs=8, abs=8, abs=7, abs=9, abs=3; 1 instances at bases [7]; all_strict=True; worst realized 38130625/45620127
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u671_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (67405518:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u671_uniform
-- u672 [5-edge cycle] 1->2->5->6->3->(closed) | cand_entry+z_entry+z_entry+z_entry+z_irred
--   roles: abs=4, abs=9, abs=8, abs=10, abs=10, abs=10, abs=10, abs=9, abs=3, abs=10; 1 instances at bases [9]; all_strict=True; worst realized 1103103/1354297
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u672_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (183120426:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u672_uniform
-- u673 [5-edge cycle] 1->2->5->6->3->(closed) | cand_entry+z_entry+z_entry+z_entry+z_irred
--   roles: abs=2, abs=12, abs=9, abs=11, abs=11, abs=11, abs=11, abs=10, abs=1, abs=11; 1 instances at bases [10]; all_strict=True; worst realized 181293/298555
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u673_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (281780586:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u673_uniform
-- u674 [5-edge cycle] 1->2->5->6->3->(closed) | cand_irred+z_entry+z_entry+z_entry+z_irred
--   roles: abs=6, abs=2, abs=5, abs=7, abs=7, abs=7, abs=7, abs=6, abs=2, abs=7; 2 instances at bases [6]; all_strict=True; worst realized 131271/133705
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u674_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (2081070:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u674_uniform
-- u675 [5-edge cycle] 1->2->5->6->3->(closed) | cand_irred+z_entry+z_entry+z_entry+z_irred
--   roles: abs=8, abs=3, abs=7, abs=10, abs=10, abs=10, abs=10, abs=9, abs=3, abs=10; 2 instances at bases [9]; all_strict=True; worst realized 8567937/8581375
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u675_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (1088478:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u675_uniform
-- u676 [5-edge cycle] 1->2->5->6->3->(closed) | cand_irred+z_entry+z_entry+z_entry+z_irred
--   roles: abs=12, abs=1, abs=9, abs=11, abs=11, abs=11, abs=11, abs=10, abs=1, abs=11; 1 instances at bases [10]; all_strict=True; worst realized 59185/59711
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u676_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (3791934:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u676_uniform
-- u677 [5-edge cycle] 1->3->4->5->2->(closed) | cand_entry+z_entry+z_entry+z_entry+z_irred
--   roles: abs=3, abs=7, abs=5, abs=5, abs=5, abs=5, abs=7, abs=2, abs=2, abs=2; 1 instances at bases [5]; all_strict=True; worst realized 31939/42757
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u677_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (8275770:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u677_uniform
-- u678 [5-edge cycle] 1->3->4->5->2->(closed) | cand_irred+z_entry+z_entry+z_entry+z_irred
--   roles: abs=7, abs=2, abs=5, abs=5, abs=5, abs=5, abs=7, abs=2, abs=2, abs=2; 1 instances at bases [5]; all_strict=True; worst realized 8405/8619
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u678_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (600270:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u678_uniform
-- u679 [5-edge cycle] 1->3->4->5->6->(closed) | cand_entry+z_entry+z_entry+z_entry+z_entry
--   roles: abs=3, abs=7, abs=5, abs=5, abs=5, abs=5, abs=6, abs=6, abs=8, abs=2; 6 instances at bases [5]; all_strict=True; worst realized 3800741/4932603
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u679_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (23769102:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u679_uniform
-- u680 [5-edge cycle] 1->3->4->5->6->(closed) | cand_entry+z_entry+z_entry+z_entry+z_entry
--   roles: abs=2, abs=10, abs=7, abs=7, abs=7, abs=7, abs=8, abs=8, abs=11, abs=1; 4 instances at bases [7]; all_strict=True; worst realized 380133/614075
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u680_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (94746510:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u680_uniform
-- u681 [5-edge cycle] 1->3->4->5->6->(closed) | cand_entry+z_entry+z_entry+z_entry+z_entry
--   roles: abs=2, tied+4, tied=base, tied=base, tied=base, tied=base, tied+1, tied+1, tied+5, abs=1; 6 instances at bases [9, 10]; all_strict=True; worst realized 9064629/14734843
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 4). -/
theorem shape_u681_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (24576:ℚ) * m ^ 4 + (135168:ℚ) * m ^ 3 - (45312:ℚ) * m ^ 2 - (105792:ℚ) * m + (1422:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have h3 : (0:ℚ) ≤ (m - 5) ^ 3 := by nlinarith
  have h4 : (0:ℚ) ≤ (m - 5) ^ 4 := by nlinarith
  have hshift : (24576:ℚ) * (m - 5) ^ 4 + (626688:ℚ) * (m - 5) ^ 3 + (5668608:ℚ) * (m - 5) ^ 2 + (21866688:ℚ) * (m - 5) + (30595662:ℚ) = (24576:ℚ) * m ^ 4 + (135168:ℚ) * m ^ 3 - (45312:ℚ) * m ^ 2 - (105792:ℚ) * m + (1422:ℚ) := by ring
  linarith [ht, h2, h3, h4, hshift]
#print axioms shape_u681_uniform
-- u682 [5-edge cycle] 1->3->4->5->6->(closed) | cand_entry+z_entry+z_entry+z_entry+z_irred
--   roles: abs=2, abs=9, abs=5, abs=5, abs=5, abs=5, abs=6, abs=6, abs=1, abs=8; 1 instances at bases [5]; all_strict=True; worst realized 42090559/69699825
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u682_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (27609266:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u682_uniform
-- u683 [5-edge cycle] 1->3->4->5->6->(closed) | cand_entry+z_entry+z_entry+z_entry+z_irred
--   roles: abs=4, abs=6, abs=5, abs=5, abs=5, abs=5, abs=6, abs=6, abs=3, abs=6; 1 instances at bases [5]; all_strict=True; worst realized 1894487/2216097
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u683_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (15758890:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u683_uniform
-- u684 [5-edge cycle] 1->3->4->5->6->(closed) | cand_irred+z_entry+z_entry+z_entry+z_entry
--   roles: abs=8, abs=2, abs=6, abs=6, abs=6, abs=6, abs=7, abs=7, abs=9, abs=2; 4 instances at bases [6]; all_strict=True; worst realized 8621991/8626145
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u684_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (70618:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u684_uniform
-- u685 [5-edge cycle] 1->4->2->5->6->(closed) | cand_entry+z_entry+z_entry+z_entry+z_entry
--   roles: abs=3, abs=10, abs=10, abs=6, abs=5, abs=8, abs=8, abs=8, abs=10, abs=2; 1 instances at bases [7]; all_strict=True; worst realized 116025/143543
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u685_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (67611726:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u685_uniform
-- u686 [5-edge cycle] 1->4->2->5->6->(closed) | cand_entry+z_entry+z_entry+z_entry+z_entry
--   roles: abs=4, abs=10, abs=10, abs=6, abs=5, abs=8, abs=8, abs=8, abs=10, abs=3; 1 instances at bases [7]; all_strict=True; worst realized 170625/193471
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u686_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (56132622:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u686_uniform
-- u687 [5-edge cycle] 1->4->5->6->2->(closed) | cand_entry+z_entry+z_entry+z_entry+z_irred
--   roles: tied-2, tied+2, tied=base, tied=base, tied+1, tied+1, tied+2, abs=3, tied-3, abs=3; 2 instances at bases [5, 6]; all_strict=True; worst realized 39767/48081
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 3). -/
theorem shape_u687_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (25600:ℚ) * m ^ 3 + (355200:ℚ) * m ^ 2 + (561200:ℚ) * m + (140250:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have h3 : (0:ℚ) ≤ (m - 5) ^ 3 := by nlinarith
  have hshift : (25600:ℚ) * (m - 5) ^ 3 + (739200:ℚ) * (m - 5) ^ 2 + (6033200:ℚ) * (m - 5) + (15026250:ℚ) = (25600:ℚ) * m ^ 3 + (355200:ℚ) * m ^ 2 + (561200:ℚ) * m + (140250:ℚ) := by ring
  linarith [ht, h2, h3, hshift]
#print axioms shape_u687_uniform
-- u688 [5-edge cycle] 1->4->5->6->2->(closed) | cand_entry+z_entry+z_entry+z_entry+z_irred
--   roles: abs=4, abs=9, abs=7, abs=7, abs=8, abs=8, abs=9, abs=4, abs=3, abs=4; 1 instances at bases [7]; all_strict=True; worst realized 414713/508431
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u688_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (46390410:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u688_uniform
-- u689 [5-edge cycle] 1->4->5->6->2->(closed) | cand_entry+z_entry+z_entry+z_irred+z_entry
--   roles: tied-2, tied+2, tied=base, tied=base, tied+1, tied+1, tied=base, tied+1, tied+1, tied-3; 2 instances at bases [5, 6]; all_strict=True; worst realized 3185/3751
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 4). -/
theorem shape_u689_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (8192:ℚ) * m ^ 4 + (114688:ℚ) * m ^ 3 + (77056:ℚ) * m ^ 2 - (43264:ℚ) * m + (3978:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have h3 : (0:ℚ) ≤ (m - 5) ^ 3 := by nlinarith
  have h4 : (0:ℚ) ≤ (m - 5) ^ 4 := by nlinarith
  have hshift : (8192:ℚ) * (m - 5) ^ 4 + (278528:ℚ) * (m - 5) ^ 3 + (3026176:ℚ) * (m - 5) ^ 2 + (13424896:ℚ) * (m - 5) + (21170058:ℚ) = (8192:ℚ) * m ^ 4 + (114688:ℚ) * m ^ 3 + (77056:ℚ) * m ^ 2 - (43264:ℚ) * m + (3978:ℚ) := by ring
  linarith [ht, h2, h3, h4, hshift]
#print axioms shape_u689_uniform
-- u690 [5-edge cycle] 1->4->5->6->2->(closed) | cand_entry+z_entry+z_entry+z_irred+z_entry
--   roles: abs=4, tied+2, tied=base, tied=base, tied+1, tied+1, tied=base, tied+1, tied+1, abs=3; 2 instances at bases [7, 8]; all_strict=True; worst realized 34675/41013
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 4). -/
theorem shape_u690_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (24576:ℚ) * m ^ 4 + (16384:ℚ) * m ^ 3 + (58368:ℚ) * m ^ 2 + (71168:ℚ) * m - (9846:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have h3 : (0:ℚ) ≤ (m - 5) ^ 3 := by nlinarith
  have h4 : (0:ℚ) ≤ (m - 5) ^ 4 := by nlinarith
  have hshift : (24576:ℚ) * (m - 5) ^ 4 + (507904:ℚ) * (m - 5) ^ 3 + (3990528:ℚ) * (m - 5) ^ 2 + (14171648:ℚ) * (m - 5) + (19213194:ℚ) = (24576:ℚ) * m ^ 4 + (16384:ℚ) * m ^ 3 + (58368:ℚ) * m ^ 2 + (71168:ℚ) * m - (9846:ℚ) := by ring
  linarith [ht, h2, h3, h4, hshift]
#print axioms shape_u690_uniform
-- u691 [5-edge cycle] 1->4->5->6->2->(closed) | cand_entry+z_entry+z_entry+z_irred+z_entry
--   roles: abs=5, tied+2, tied=base, tied=base, tied+1, tied+1, tied=base, tied+1, tied+1, abs=4; 3 instances at bases [8, 9, 10]; all_strict=True; worst realized 4455/5041
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 4). -/
theorem shape_u691_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (24576:ℚ) * m ^ 4 + (58368:ℚ) * m ^ 2 + (89856:ℚ) * m - (12150:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have h3 : (0:ℚ) ≤ (m - 5) ^ 3 := by nlinarith
  have h4 : (0:ℚ) ≤ (m - 5) ^ 4 := by nlinarith
  have hshift : (24576:ℚ) * (m - 5) ^ 4 + (491520:ℚ) * (m - 5) ^ 3 + (3744768:ℚ) * (m - 5) ^ 2 + (12961536:ℚ) * (m - 5) + (17256330:ℚ) = (24576:ℚ) * m ^ 4 + (58368:ℚ) * m ^ 2 + (89856:ℚ) * m - (12150:ℚ) := by ring
  linarith [ht, h2, h3, h4, hshift]
#print axioms shape_u691_uniform
-- u692 [5-edge cycle] 1->4->5->6->2->(closed) | cand_entry+z_entry+z_entry+z_irred+z_entry
--   roles: abs=2, abs=13, abs=9, abs=9, abs=10, abs=10, abs=9, abs=10, abs=12, abs=1; 1 instances at bases [9]; all_strict=True; worst realized 4599/7505
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u692_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (250686090:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u692_uniform
-- u693 [5-edge cycle] 1->4->5->6->2->(closed) | cand_entry+z_entry+z_entry+z_irred+z_entry
--   roles: abs=4, abs=12, abs=10, abs=10, abs=11, abs=11, abs=9, abs=11, abs=10, abs=3; 1 instances at bases [10]; all_strict=True; worst realized 4648725/5610659
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u693_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (256836378:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u693_uniform
-- u694 [5-edge cycle] 1->4->5->6->2->(closed) | cand_entry+z_entry+z_entry+z_irred+z_entry
--   roles: abs=5, abs=12, abs=10, abs=10, abs=11, abs=11, abs=9, abs=11, abs=10, abs=4; 1 instances at bases [10]; all_strict=True; worst realized 2045439/2352857
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u694_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (246241818:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u694_uniform
-- u695 [5-edge cycle] 1->4->5->6->2->(closed) | cand_entry+z_entry+z_entry+z_irred+z_entry
--   roles: abs=6, abs=12, abs=10, abs=10, abs=11, abs=11, abs=10, abs=11, abs=11, abs=5; 1 instances at bases [10]; all_strict=True; worst realized 35793/39527
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u695_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (236283786:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u695_uniform
-- u696 [5-edge cycle] 1->4->5->6->2->(closed) | cand_entry+z_entry+z_entry+z_irred+z_irred
--   roles: abs=3, tied+2, tied=base, tied=base, tied+1, tied+1, abs=3, tied+1, abs=2, abs=3; 2 instances at bases [5, 6]; all_strict=True; worst realized 2337/3055
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 3). -/
theorem shape_u696_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (117760:ℚ) * m ^ 3 - (44160:ℚ) * m ^ 2 - (277840:ℚ) * m - (89010:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have h3 : (0:ℚ) ≤ (m - 5) ^ 3 := by nlinarith
  have hshift : (117760:ℚ) * (m - 5) ^ 3 + (1722240:ℚ) * (m - 5) ^ 2 + (8112560:ℚ) * (m - 5) + (12137790:ℚ) = (117760:ℚ) * m ^ 3 - (44160:ℚ) * m ^ 2 - (277840:ℚ) * m - (89010:ℚ) := by ring
  linarith [ht, h2, h3, hshift]
#print axioms shape_u696_uniform
-- u697 [5-edge cycle] 1->4->5->6->2->(closed) | cand_entry+z_entry+z_entry+z_irred+z_irred
--   roles: abs=3, tied+2, tied=base, tied=base, tied+1, tied+1, tied=base, tied+1, abs=2, tied=base; 4 instances at bases [5, 6, 7, 8]; all_strict=True; worst realized 855/1081
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 4). -/
theorem shape_u697_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (32768:ℚ) * m ^ 4 - (11264:ℚ) * m ^ 3 - (54656:ℚ) * m ^ 2 + (176:ℚ) * m + (846:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have h3 : (0:ℚ) ≤ (m - 5) ^ 3 := by nlinarith
  have h4 : (0:ℚ) ≤ (m - 5) ^ 4 := by nlinarith
  have hshift : (32768:ℚ) * (m - 5) ^ 4 + (644096:ℚ) * (m - 5) ^ 3 + (4691584:ℚ) * (m - 5) ^ 2 + (14992816:ℚ) * (m - 5) + (17707326:ℚ) = (32768:ℚ) * m ^ 4 - (11264:ℚ) * m ^ 3 - (54656:ℚ) * m ^ 2 + (176:ℚ) * m + (846:ℚ) := by ring
  linarith [ht, h2, h3, h4, hshift]
#print axioms shape_u697_uniform
-- u698 [5-edge cycle] 1->4->5->6->2->(closed) | cand_entry+z_entry+z_entry+z_irred+z_irred
--   roles: tied-4, abs=9, tied=base, tied=base, tied+1, tied+1, tied-2, tied+1, tied-5, tied-2; 2 instances at bases [6, 7]; all_strict=True; worst realized 54093/72611
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 5). -/
theorem shape_u698_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (32768:ℚ) * m ^ 5 - (434176:ℚ) * m ^ 4 + (1702912:ℚ) * m ^ 3 - (261888:ℚ) * m ^ 2 - (3555320:ℚ) * m - (489114:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have h3 : (0:ℚ) ≤ (m - 5) ^ 3 := by nlinarith
  have h4 : (0:ℚ) ≤ (m - 5) ^ 4 := by nlinarith
  have h5 : (0:ℚ) ≤ (m - 5) ^ 5 := by nlinarith
  have hshift : (32768:ℚ) * (m - 5) ^ 5 + (385024:ℚ) * (m - 5) ^ 4 + (1211392:ℚ) * (m - 5) ^ 3 + (1115392:ℚ) * (m - 5) ^ 2 + (6856200:ℚ) * (m - 5) + (19091086:ℚ) = (32768:ℚ) * m ^ 5 - (434176:ℚ) * m ^ 4 + (1702912:ℚ) * m ^ 3 - (261888:ℚ) * m ^ 2 - (3555320:ℚ) * m - (489114:ℚ) := by ring
  linarith [ht, h2, h3, h4, h5, hshift]
#print axioms shape_u698_uniform
-- u699 [5-edge cycle] 1->4->5->6->2->(closed) | cand_entry+z_entry+z_entry+z_irred+z_irred
--   roles: tied-4, abs=9, tied=base, tied=base, tied+1, tied+1, tied-1, tied+1, tied-5, tied-1; 2 instances at bases [6, 7]; all_strict=True; worst realized 65189/86779
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 5). -/
theorem shape_u699_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (32768:ℚ) * m ^ 5 - (401408:ℚ) * m ^ 4 + (1330176:ℚ) * m ^ 3 + (667392:ℚ) * m ^ 2 - (1785144:ℚ) * m - (256986:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have h3 : (0:ℚ) ≤ (m - 5) ^ 3 := by nlinarith
  have h4 : (0:ℚ) ≤ (m - 5) ^ 4 := by nlinarith
  have h5 : (0:ℚ) ≤ (m - 5) ^ 5 := by nlinarith
  have hshift : (32768:ℚ) * (m - 5) ^ 5 + (417792:ℚ) * (m - 5) ^ 4 + (1494016:ℚ) * (m - 5) ^ 3 + (1368832:ℚ) * (m - 5) ^ 2 + (6347976:ℚ) * (m - 5) + (25294094:ℚ) = (32768:ℚ) * m ^ 5 - (401408:ℚ) * m ^ 4 + (1330176:ℚ) * m ^ 3 + (667392:ℚ) * m ^ 2 - (1785144:ℚ) * m - (256986:ℚ) := by ring
  linarith [ht, h2, h3, h4, h5, hshift]
#print axioms shape_u699_uniform
-- u700 [5-edge cycle] 1->4->5->6->2->(closed) | cand_entry+z_entry+z_entry+z_irred+z_irred
--   roles: abs=2, free+3..+4, tied=base, tied=base, tied+1, tied+1, abs=6, tied+1, abs=1, abs=6; 2 instances at bases [6, 8]; all_strict=True; worst realized 59267/93933
/-- pattern tau=(3): real half-line form, mono certificate (kind ALL, strict=True, deg D = 3). -/
theorem shape_u700_pat1_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (207872:ℚ) * m ^ 3 - (31360:ℚ) * m ^ 2 - (405328:ℚ) * m - (120330:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have h3 : (0:ℚ) ≤ (m - 5) ^ 3 := by nlinarith
  have hshift : (207872:ℚ) * (m - 5) ^ 3 + (3086720:ℚ) * (m - 5) ^ 2 + (14871472:ℚ) * (m - 5) + (23053030:ℚ) = (207872:ℚ) * m ^ 3 - (31360:ℚ) * m ^ 2 - (405328:ℚ) * m - (120330:ℚ) := by ring
  linarith [ht, h2, h3, hshift]
#print axioms shape_u700_pat1_uniform
/-- pattern tau=(4): real half-line form, mono certificate (kind ALL, strict=True, deg D = 3). -/
theorem shape_u700_pat2_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (207872:ℚ) * m ^ 3 - (199808:ℚ) * m ^ 2 - (615888:ℚ) * m - (144018:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have h3 : (0:ℚ) ≤ (m - 5) ^ 3 := by nlinarith
  have hshift : (207872:ℚ) * (m - 5) ^ 3 + (2918272:ℚ) * (m - 5) ^ 2 + (12976432:ℚ) * (m - 5) + (17765342:ℚ) = (207872:ℚ) * m ^ 3 - (199808:ℚ) * m ^ 2 - (615888:ℚ) * m - (144018:ℚ) := by ring
  linarith [ht, h2, h3, hshift]
#print axioms shape_u700_pat2_uniform
-- u701 [5-edge cycle] 1->4->5->6->2->(closed) | cand_entry+z_entry+z_entry+z_irred+z_irred
--   roles: abs=3, abs=8, abs=6, abs=6, abs=7, abs=7, abs=4, abs=7, abs=2, abs=4; 1 instances at bases [6]; all_strict=True; worst realized 98735/130801
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u701_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (27416430:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u701_uniform
-- u702 [5-edge cycle] 1->4->5->6->2->(closed) | cand_entry+z_entry+z_entry+z_irred+z_irred
--   roles: abs=4, tied+2, tied=base, tied=base, tied+1, tied+1, tied=base, tied+1, abs=3, tied=base; 3 instances at bases [8, 9, 10]; all_strict=True; worst realized 1863/2201
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 4). -/
theorem shape_u702_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (32768:ℚ) * m ^ 4 - (52224:ℚ) * m ^ 3 - (100736:ℚ) * m ^ 2 + (816:ℚ) * m + (1566:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have h3 : (0:ℚ) ≤ (m - 5) ^ 3 := by nlinarith
  have h4 : (0:ℚ) ≤ (m - 5) ^ 4 := by nlinarith
  have hshift : (32768:ℚ) * (m - 5) ^ 4 + (603136:ℚ) * (m - 5) ^ 3 + (4031104:ℚ) * (m - 5) ^ 2 + (11460656:ℚ) * (m - 5) + (11439246:ℚ) = (32768:ℚ) * m ^ 4 - (52224:ℚ) * m ^ 3 - (100736:ℚ) * m ^ 2 + (816:ℚ) * m + (1566:ℚ) := by ring
  linarith [ht, h2, h3, h4, hshift]
#print axioms shape_u702_uniform
-- u703 [5-edge cycle] 1->4->5->6->2->(closed) | cand_entry+z_entry+z_entry+z_irred+z_irred
--   roles: abs=2, abs=14, abs=10, abs=10, abs=11, abs=11, abs=8, abs=11, abs=1, abs=8; 1 instances at bases [10]; all_strict=True; worst realized 448497/744575
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u703_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (237158478:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u703_uniform
-- u704 [5-edge cycle] 1->4->5->6->2->(closed) | cand_entry+z_entry+z_entry+z_irred+z_irred
--   roles: abs=2, abs=14, abs=10, abs=10, abs=11, abs=11, abs=9, abs=11, abs=1, abs=9; 1 instances at bases [10]; all_strict=True; worst realized 505449/836215
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u704_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (264943566:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u704_uniform
-- u705 [5-edge cycle] 1->4->5->6->2->(closed) | cand_entry+z_entry+z_entry+z_irred+z_irred
--   roles: abs=2, abs=14, abs=10, abs=10, abs=11, abs=11, abs=10, abs=11, abs=1, abs=10; 1 instances at bases [10]; all_strict=True; worst realized 791/1305
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u705_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (292728654:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u705_uniform
-- u706 [5-edge cycle] 1->4->5->6->2->(closed) | cand_entry+z_entry+z_entry+z_irred+z_irred
--   roles: abs=4, abs=12, abs=10, abs=10, abs=11, abs=11, abs=9, abs=11, abs=3, abs=9; 1 instances at bases [10]; all_strict=True; worst realized 4276827/5184533
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u706_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (242357502:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u706_uniform
-- u707 [5-edge cycle] 1->4->5->6->3->(closed) | cand_entry+z_entry+z_entry+z_entry+z_entry
--   roles: abs=4, abs=7, abs=5, abs=5, abs=6, abs=6, abs=6, abs=5, abs=6, abs=3; 1 instances at bases [5]; all_strict=True; worst realized 39125275/41840669
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u707_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (8146182:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u707_uniform
-- u708 [5-edge cycle] 1->4->5->6->3->(closed) | cand_entry+z_entry+z_entry+z_entry+z_entry
--   roles: abs=3, abs=9, abs=6, abs=6, abs=7, abs=7, abs=7, abs=6, abs=8, abs=2; 1 instances at bases [6]; all_strict=True; worst realized 8087597/9810075
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u708_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (36172038:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u708_uniform
-- u709 [5-edge cycle] 1->4->5->6->3->(closed) | cand_entry+z_entry+z_entry+z_entry+z_irred
--   roles: abs=4, tied+2, tied=base, tied=base, tied+1, tied+1, tied+1, tied=base, abs=3, tied+1; 5 instances at bases [5, 6]; all_strict=True; worst realized 734597/890227
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 4). -/
theorem shape_u709_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (32768:ℚ) * m ^ 4 + (19456:ℚ) * m ^ 3 - (1664:ℚ) * m ^ 2 + (4880:ℚ) * m - (17190:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have h3 : (0:ℚ) ≤ (m - 5) ^ 3 := by nlinarith
  have h4 : (0:ℚ) ≤ (m - 5) ^ 4 := by nlinarith
  have hshift : (32768:ℚ) * (m - 5) ^ 4 + (674816:ℚ) * (m - 5) ^ 3 + (5205376:ℚ) * (m - 5) ^ 2 + (17831440:ℚ) * (m - 5) + (22877610:ℚ) = (32768:ℚ) * m ^ 4 + (19456:ℚ) * m ^ 3 - (1664:ℚ) * m ^ 2 + (4880:ℚ) * m - (17190:ℚ) := by ring
  linarith [ht, h2, h3, h4, hshift]
#print axioms shape_u709_uniform
-- u710 [5-edge cycle] 1->4->5->6->3->(closed) | cand_entry+z_entry+z_entry+z_entry+z_irred
--   roles: abs=5, tied+2, tied=base, tied=base, tied+1, tied+1, tied+1, tied=base, abs=4, tied+1; 6 instances at bases [6, 7, 9]; all_strict=True; worst realized 74431/85305
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 4). -/
theorem shape_u710_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (32768:ℚ) * m ^ 4 - (5120:ℚ) * m ^ 3 - (29312:ℚ) * m ^ 2 + (656:ℚ) * m - (21942:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have h3 : (0:ℚ) ≤ (m - 5) ^ 3 := by nlinarith
  have h4 : (0:ℚ) ≤ (m - 5) ^ 4 := by nlinarith
  have hshift : (32768:ℚ) * (m - 5) ^ 4 + (650240:ℚ) * (m - 5) ^ 3 + (4809088:ℚ) * (m - 5) ^ 2 + (15707536:ℚ) * (m - 5) + (19088538:ℚ) = (32768:ℚ) * m ^ 4 - (5120:ℚ) * m ^ 3 - (29312:ℚ) * m ^ 2 + (656:ℚ) * m - (21942:ℚ) := by ring
  linarith [ht, h2, h3, h4, hshift]
#print axioms shape_u710_uniform
-- u711 [5-edge cycle] 1->4->5->6->3->(closed) | cand_entry+z_entry+z_entry+z_entry+z_irred
--   roles: abs=2, abs=12, abs=8, abs=8, abs=9, abs=9, abs=9, abs=8, abs=1, abs=9; 2 instances at bases [8]; all_strict=True; worst realized 81965/136107
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u711_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (138332810:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u711_uniform
-- u712 [5-edge cycle] 1->4->5->6->3->(closed) | cand_entry+z_entry+z_entry+z_entry+z_irred
--   roles: abs=6, tied+2, tied=base, tied=base, tied+1, tied+1, tied+1, tied=base, abs=5, tied+1; 2 instances at bases [8, 10]; all_strict=True; worst realized 1482975/1658489
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 4). -/
theorem shape_u712_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (32768:ℚ) * m ^ 4 - (29696:ℚ) * m ^ 3 - (56960:ℚ) * m ^ 2 - (3568:ℚ) * m - (26694:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have h3 : (0:ℚ) ≤ (m - 5) ^ 3 := by nlinarith
  have h4 : (0:ℚ) ≤ (m - 5) ^ 4 := by nlinarith
  have hshift : (32768:ℚ) * (m - 5) ^ 4 + (625664:ℚ) * (m - 5) ^ 3 + (4412800:ℚ) * (m - 5) ^ 2 + (13583632:ℚ) * (m - 5) + (15299466:ℚ) = (32768:ℚ) * m ^ 4 - (29696:ℚ) * m ^ 3 - (56960:ℚ) * m ^ 2 - (3568:ℚ) * m - (26694:ℚ) := by ring
  linarith [ht, h2, h3, h4, hshift]
#print axioms shape_u712_uniform
-- u713 [5-edge cycle] 1->4->5->6->3->(closed) | cand_entry+z_entry+z_entry+z_entry+z_irred
--   roles: abs=3, abs=13, abs=10, abs=10, abs=11, abs=11, abs=11, abs=10, abs=2, abs=11; 2 instances at bases [10]; all_strict=True; worst realized 1148175/1528097
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u713_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (304317522:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u713_uniform
-- u714 [5-edge cycle] 1->5->6->3->2->(closed) | cand_entry+z_entry+z_entry+z_entry+z_entry
--   roles: abs=2, abs=9, abs=6, abs=6, abs=6, abs=5, abs=8, abs=4, abs=4, abs=1; 1 instances at bases [5]; all_strict=True; worst realized 230461/342395
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u714_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (21155526:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u714_uniform
-- u715 [5-edge cycle] 1->5->6->3->2->(closed) | cand_entry+z_entry+z_entry+z_entry+z_entry
--   roles: abs=3, tied+3, tied+1, tied+1, tied+1, tied=base, tied+1, tied-1, tied=base, abs=2; 2 instances at bases [5, 6]; all_strict=True; worst realized 142110633/179851375
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 4). -/
theorem shape_u715_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (24576:ℚ) * m ^ 4 - (8192:ℚ) * m ^ 3 + (170240:ℚ) * m ^ 2 + (252032:ℚ) * m + (18886:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have h3 : (0:ℚ) ≤ (m - 5) ^ 3 := by nlinarith
  have h4 : (0:ℚ) ≤ (m - 5) ^ 4 := by nlinarith
  have hshift : (24576:ℚ) * (m - 5) ^ 4 + (483328:ℚ) * (m - 5) ^ 3 + (3733760:ℚ) * (m - 5) ^ 2 + (13628032:ℚ) * (m - 5) + (19871046:ℚ) = (24576:ℚ) * m ^ 4 - (8192:ℚ) * m ^ 3 + (170240:ℚ) * m ^ 2 + (252032:ℚ) * m + (18886:ℚ) := by ring
  linarith [ht, h2, h3, h4, hshift]
#print axioms shape_u715_uniform
-- u716 [5-edge cycle] 1->5->6->3->2->(closed) | cand_entry+z_entry+z_entry+z_entry+z_entry
--   roles: abs=2, tied+5, tied+1, tied+1, tied+1, tied=base, tied+1, abs=5, abs=7, abs=1; 2 instances at bases [6, 7]; all_strict=True; worst realized 30574971/45753125
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 3). -/
theorem shape_u716_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (233472:ℚ) * m ^ 3 - (95616:ℚ) * m ^ 2 - (266688:ℚ) * m + (146814:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have h3 : (0:ℚ) ≤ (m - 5) ^ 3 := by nlinarith
  have hshift : (233472:ℚ) * (m - 5) ^ 3 + (3406464:ℚ) * (m - 5) ^ 2 + (16287552:ℚ) * (m - 5) + (25606974:ℚ) = (233472:ℚ) * m ^ 3 - (95616:ℚ) * m ^ 2 - (266688:ℚ) * m + (146814:ℚ) := by ring
  linarith [ht, h2, h3, hshift]
#print axioms shape_u716_uniform
-- u717 [5-edge cycle] 1->5->6->3->2->(closed) | cand_entry+z_entry+z_entry+z_entry+z_entry
--   roles: abs=4, abs=12, abs=10, abs=10, abs=10, abs=9, abs=10, abs=7, abs=8, abs=3; 1 instances at bases [9]; all_strict=True; worst realized 90813825/106989463
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u717_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (145580742:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u717_uniform
-- u718 [5-edge cycle] 1->5->6->3->2->(closed) | cand_entry+z_entry+z_entry+z_entry+z_irred
--   roles: abs=2, tied+4, tied+1, tied+1, tied+1, tied=base, tied+1, tied-2, abs=1, tied-2; 4 instances at bases [5, 6, 8]; all_strict=True; worst realized 1026599/1557345
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 4). -/
theorem shape_u718_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (32768:ℚ) * m ^ 4 - (54272:ℚ) * m ^ 3 - (24192:ℚ) * m ^ 2 + (44688:ℚ) * m - (45990:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have h3 : (0:ℚ) ≤ (m - 5) ^ 3 := by nlinarith
  have h4 : (0:ℚ) ≤ (m - 5) ^ 4 := by nlinarith
  have hshift : (32768:ℚ) * (m - 5) ^ 4 + (601088:ℚ) * (m - 5) ^ 3 + (4076928:ℚ) * (m - 5) ^ 2 + (12116368:ℚ) * (m - 5) + (13268650:ℚ) = (32768:ℚ) * m ^ 4 - (54272:ℚ) * m ^ 3 - (24192:ℚ) * m ^ 2 + (44688:ℚ) * m - (45990:ℚ) := by ring
  linarith [ht, h2, h3, h4, hshift]
#print axioms shape_u718_uniform
-- u719 [5-edge cycle] 1->5->6->3->2->(closed) | cand_entry+z_entry+z_entry+z_entry+z_irred
--   roles: abs=2, free+4..+5, tied+1, tied+1, tied+1, tied=base, tied+1, tied-1, abs=1, tied-1; 3 instances at bases [5, 6, 8]; all_strict=True; worst realized 580013/831875
/-- pattern tau=(4): real half-line form, mono certificate (kind ALL, strict=True, deg D = 4). -/
theorem shape_u719_pat1_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (32768:ℚ) * m ^ 4 - (21504:ℚ) * m ^ 3 - (17024:ℚ) * m ^ 2 + (33936:ℚ) * m - (21462:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have h3 : (0:ℚ) ≤ (m - 5) ^ 3 := by nlinarith
  have h4 : (0:ℚ) ≤ (m - 5) ^ 4 := by nlinarith
  have hshift : (32768:ℚ) * (m - 5) ^ 4 + (633856:ℚ) * (m - 5) ^ 3 + (4575616:ℚ) * (m - 5) ^ 2 + (14634896:ℚ) * (m - 5) + (17514618:ℚ) = (32768:ℚ) * m ^ 4 - (21504:ℚ) * m ^ 3 - (17024:ℚ) * m ^ 2 + (33936:ℚ) * m - (21462:ℚ) := by ring
  linarith [ht, h2, h3, h4, hshift]
#print axioms shape_u719_pat1_uniform
/-- pattern tau=(5): real half-line form, mono certificate (kind ALL, strict=True, deg D = 4). -/
theorem shape_u719_pat2_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (32768:ℚ) * m ^ 4 - (50176:ℚ) * m ^ 3 - (27776:ℚ) * m ^ 2 + (61264:ℚ) * m - (17934:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have h3 : (0:ℚ) ≤ (m - 5) ^ 3 := by nlinarith
  have h4 : (0:ℚ) ≤ (m - 5) ^ 4 := by nlinarith
  have hshift : (32768:ℚ) * (m - 5) ^ 4 + (605184:ℚ) * (m - 5) ^ 3 + (4134784:ℚ) * (m - 5) ^ 2 + (12404304:ℚ) * (m - 5) + (13801986:ℚ) = (32768:ℚ) * m ^ 4 - (50176:ℚ) * m ^ 3 - (27776:ℚ) * m ^ 2 + (61264:ℚ) * m - (17934:ℚ) := by ring
  linarith [ht, h2, h3, h4, hshift]
#print axioms shape_u719_pat2_uniform
-- u720 [5-edge cycle] 1->5->6->3->2->(closed) | cand_entry+z_entry+z_entry+z_entry+z_irred
--   roles: abs=2, abs=9, abs=6, abs=6, abs=6, abs=5, abs=8, abs=4, abs=1, abs=3; 1 instances at bases [5]; all_strict=True; worst realized 1613227/2485125
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u720_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (18309858:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u720_uniform
-- u721 [5-edge cycle] 1->5->6->3->2->(closed) | cand_entry+z_entry+z_entry+z_entry+z_irred
--   roles: abs=4, tied+2, tied+1, tied+1, tied+1, tied=base, tied+1, tied-2, abs=3, tied-2; 2 instances at bases [5, 6]; all_strict=True; worst realized 2633799/3218513
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 4). -/
theorem shape_u721_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (32768:ℚ) * m ^ 4 - (46080:ℚ) * m ^ 3 - (640:ℚ) * m ^ 2 + (4112:ℚ) * m - (106710:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have h3 : (0:ℚ) ≤ (m - 5) ^ 3 := by nlinarith
  have h4 : (0:ℚ) ≤ (m - 5) ^ 4 := by nlinarith
  have hshift : (32768:ℚ) * (m - 5) ^ 4 + (609280:ℚ) * (m - 5) ^ 3 + (4223360:ℚ) * (m - 5) ^ 2 + (12925712:ℚ) * (m - 5) + (14617850:ℚ) = (32768:ℚ) * m ^ 4 - (46080:ℚ) * m ^ 3 - (640:ℚ) * m ^ 2 + (4112:ℚ) * m - (106710:ℚ) := by ring
  linarith [ht, h2, h3, h4, hshift]
#print axioms shape_u721_uniform
-- u722 [5-edge cycle] 1->5->6->3->2->(closed) | cand_entry+z_entry+z_entry+z_entry+z_irred
--   roles: abs=4, tied+2, tied+1, tied+1, tied+1, tied=base, tied+1, tied-1, abs=3, tied-1; 2 instances at bases [5, 6]; all_strict=True; worst realized 2633799/3218513
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 4). -/
theorem shape_u722_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (32768:ℚ) * m ^ 4 - (13312:ℚ) * m ^ 3 + (14720:ℚ) * m ^ 2 + (32272:ℚ) * m - (49798:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have h3 : (0:ℚ) ≤ (m - 5) ^ 3 := by nlinarith
  have h4 : (0:ℚ) ≤ (m - 5) ^ 4 := by nlinarith
  have hshift : (32768:ℚ) * (m - 5) ^ 4 + (642048:ℚ) * (m - 5) ^ 3 + (4730240:ℚ) * (m - 5) ^ 2 + (15565072:ℚ) * (m - 5) + (19295562:ℚ) = (32768:ℚ) * m ^ 4 - (13312:ℚ) * m ^ 3 + (14720:ℚ) * m ^ 2 + (32272:ℚ) * m - (49798:ℚ) := by ring
  linarith [ht, h2, h3, h4, hshift]
#print axioms shape_u722_uniform
-- u723 [5-edge cycle] 1->5->6->3->2->(closed) | cand_entry+z_entry+z_entry+z_entry+z_irred
--   roles: abs=5, tied+2, tied+1, tied+1, tied+1, tied=base, tied+1, abs=4, abs=4, abs=4; 3 instances at bases [5, 6, 7]; all_strict=True; worst realized 1183301/1349699
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 3). -/
theorem shape_u723_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (135168:ℚ) * m ^ 3 - (38016:ℚ) * m ^ 2 + (48576:ℚ) * m + (284922:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have h3 : (0:ℚ) ≤ (m - 5) ^ 3 := by nlinarith
  have hshift : (135168:ℚ) * (m - 5) ^ 3 + (1989504:ℚ) * (m - 5) ^ 2 + (9806016:ℚ) * (m - 5) + (16473402:ℚ) = (135168:ℚ) * m ^ 3 - (38016:ℚ) * m ^ 2 + (48576:ℚ) * m + (284922:ℚ) := by ring
  linarith [ht, h2, h3, hshift]
#print axioms shape_u723_uniform
-- u724 [5-edge cycle] 1->5->6->3->2->(closed) | cand_entry+z_entry+z_entry+z_entry+z_irred
--   roles: abs=2, abs=10, abs=7, abs=7, abs=7, abs=6, abs=9, abs=8, abs=1, abs=6; 1 instances at bases [6]; all_strict=True; worst realized 140049/214775
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u724_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (54923610:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u724_uniform
-- u725 [5-edge cycle] 1->5->6->3->2->(closed) | cand_entry+z_entry+z_entry+z_entry+z_irred
--   roles: abs=2, abs=12, abs=7, abs=7, abs=7, abs=6, abs=11, abs=3, abs=1, abs=2; 1 instances at bases [6]; all_strict=True; worst realized 632149/894795
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u725_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (19698450:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u725_uniform
-- u726 [5-edge cycle] 1->5->6->3->2->(closed) | cand_entry+z_entry+z_entry+z_entry+z_irred
--   roles: abs=5, tied+2, tied+1, tied+1, tied+1, tied=base, tied+1, abs=5, abs=4, abs=5; 2 instances at bases [6, 7]; all_strict=True; worst realized 28861/33275
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 3). -/
theorem shape_u726_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (167936:ℚ) * m ^ 3 - (47232:ℚ) * m ^ 2 + (60352:ℚ) * m + (353994:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have h3 : (0:ℚ) ≤ (m - 5) ^ 3 := by nlinarith
  have hshift : (167936:ℚ) * (m - 5) ^ 3 + (2471808:ℚ) * (m - 5) ^ 2 + (12183232:ℚ) * (m - 5) + (20466954:ℚ) = (167936:ℚ) * m ^ 3 - (47232:ℚ) * m ^ 2 + (60352:ℚ) * m + (353994:ℚ) := by ring
  linarith [ht, h2, h3, hshift]
#print axioms shape_u726_uniform
-- u727 [5-edge cycle] 1->5->6->3->2->(closed) | cand_entry+z_entry+z_entry+z_entry+z_irred
--   roles: abs=3, tied+3, tied+1, tied+1, tied+1, tied=base, tied+1, tied-2, abs=2, tied-2; 3 instances at bases [7, 8, 9]; all_strict=True; worst realized 6175/7889
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 4). -/
theorem shape_u727_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (32768:ℚ) * m ^ 4 - (82944:ℚ) * m ^ 3 + (8064:ℚ) * m ^ 2 + (96592:ℚ) * m - (67710:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have h3 : (0:ℚ) ≤ (m - 5) ^ 3 := by nlinarith
  have h4 : (0:ℚ) ≤ (m - 5) ^ 4 := by nlinarith
  have hshift : (32768:ℚ) * (m - 5) ^ 4 + (572416:ℚ) * (m - 5) ^ 3 + (3679104:ℚ) * (m - 5) ^ 2 + (10340432:ℚ) * (m - 5) + (10728850:ℚ) = (32768:ℚ) * m ^ 4 - (82944:ℚ) * m ^ 3 + (8064:ℚ) * m ^ 2 + (96592:ℚ) * m - (67710:ℚ) := by ring
  linarith [ht, h2, h3, h4, hshift]
#print axioms shape_u727_uniform
-- u728 [5-edge cycle] 1->5->6->3->2->(closed) | cand_entry+z_entry+z_entry+z_entry+z_irred
--   roles: abs=5, tied+2, tied+1, tied+1, tied+1, tied=base, tied+1, abs=6, abs=4, abs=6; 2 instances at bases [7, 8]; all_strict=True; worst realized 214985/250047
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 3). -/
theorem shape_u728_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (200704:ℚ) * m ^ 3 - (56448:ℚ) * m ^ 2 + (72128:ℚ) * m + (423066:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have h3 : (0:ℚ) ≤ (m - 5) ^ 3 := by nlinarith
  have hshift : (200704:ℚ) * (m - 5) ^ 3 + (2954112:ℚ) * (m - 5) ^ 2 + (14560448:ℚ) * (m - 5) + (24460506:ℚ) = (200704:ℚ) * m ^ 3 - (56448:ℚ) * m ^ 2 + (72128:ℚ) * m + (423066:ℚ) := by ring
  linarith [ht, h2, h3, hshift]
#print axioms shape_u728_uniform
-- u729 [5-edge cycle] 1->5->6->3->2->(closed) | cand_entry+z_entry+z_entry+z_entry+z_irred
--   roles: abs=2, abs=13, abs=9, abs=9, abs=9, abs=8, abs=12, abs=8, abs=1, abs=6; 1 instances at bases [8]; all_strict=True; worst realized 61685/95779
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u729_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (125295450:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u729_uniform
-- u730 [5-edge cycle] 1->5->6->3->2->(closed) | cand_entry+z_entry+z_entry+z_entry+z_irred
--   roles: abs=5, tied+2, tied+1, tied+1, tied+1, tied=base, tied+1, abs=7, abs=4, abs=7; 2 instances at bases [8, 9]; all_strict=True; worst realized 305505/357911
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 3). -/
theorem shape_u730_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (233472:ℚ) * m ^ 3 - (65664:ℚ) * m ^ 2 + (83904:ℚ) * m + (492138:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have h3 : (0:ℚ) ≤ (m - 5) ^ 3 := by nlinarith
  have hshift : (233472:ℚ) * (m - 5) ^ 3 + (3436416:ℚ) * (m - 5) ^ 2 + (16937664:ℚ) * (m - 5) + (28454058:ℚ) = (233472:ℚ) * m ^ 3 - (65664:ℚ) * m ^ 2 + (83904:ℚ) * m + (492138:ℚ) := by ring
  linarith [ht, h2, h3, hshift]
#print axioms shape_u730_uniform
-- u731 [5-edge cycle] 1->5->6->3->2->(closed) | cand_entry+z_entry+z_entry+z_entry+z_irred
--   roles: abs=6, tied+2, tied+1, tied+1, tied+1, tied=base, tied+1, tied-2, abs=5, tied-2; 2 instances at bases [8, 9]; all_strict=True; worst realized 14989455/16821817
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 4). -/
theorem shape_u731_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (32768:ℚ) * m ^ 4 - (95232:ℚ) * m ^ 3 + (58752:ℚ) * m ^ 2 + (89872:ℚ) * m - (152310:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have h3 : (0:ℚ) ≤ (m - 5) ^ 3 := by nlinarith
  have h4 : (0:ℚ) ≤ (m - 5) ^ 4 := by nlinarith
  have hshift : (32768:ℚ) * (m - 5) ^ 4 + (560128:ℚ) * (m - 5) ^ 3 + (3545472:ℚ) * (m - 5) ^ 2 + (9918992:ℚ) * (m - 5) + (10341850:ℚ) = (32768:ℚ) * m ^ 4 - (95232:ℚ) * m ^ 3 + (58752:ℚ) * m ^ 2 + (89872:ℚ) * m - (152310:ℚ) := by ring
  linarith [ht, h2, h3, h4, hshift]
#print axioms shape_u731_uniform
-- u732 [5-edge cycle] 1->5->6->3->2->(closed) | cand_entry+z_entry+z_entry+z_entry+z_irred
--   roles: abs=6, tied+2, tied+1, tied+1, tied+1, tied=base, tied+1, tied-1, abs=5, tied-1; 3 instances at bases [8, 9, 10]; all_strict=True; worst realized 14989455/16821817
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 4). -/
theorem shape_u732_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (32768:ℚ) * m ^ 4 - (62464:ℚ) * m ^ 3 + (24960:ℚ) * m ^ 2 + (85264:ℚ) * m - (71078:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have h3 : (0:ℚ) ≤ (m - 5) ^ 3 := by nlinarith
  have h4 : (0:ℚ) ≤ (m - 5) ^ 4 := by nlinarith
  have hshift : (32768:ℚ) * (m - 5) ^ 4 + (592896:ℚ) * (m - 5) ^ 3 + (4003200:ℚ) * (m - 5) ^ 2 + (12034064:ℚ) * (m - 5) + (13651242:ℚ) = (32768:ℚ) * m ^ 4 - (62464:ℚ) * m ^ 3 + (24960:ℚ) * m ^ 2 + (85264:ℚ) * m - (71078:ℚ) := by ring
  linarith [ht, h2, h3, h4, hshift]
#print axioms shape_u732_uniform
-- u733 [5-edge cycle] 1->5->6->3->2->(closed) | cand_entry+z_entry+z_entry+z_entry+z_irred
--   roles: abs=5, abs=11, abs=10, abs=10, abs=10, abs=9, abs=10, abs=8, abs=4, abs=8; 1 instances at bases [9]; all_strict=True; worst realized 5437989/6409507
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u733_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (189446010:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u733_uniform
-- u734 [5-edge cycle] 1->5->6->3->2->(closed) | cand_entry+z_entry+z_entry+z_entry+z_irred
--   roles: abs=3, abs=13, abs=11, abs=11, abs=11, abs=10, abs=11, abs=9, abs=2, abs=9; 1 instances at bases [10]; all_strict=True; worst realized 420525/560947
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u734_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (276771762:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u734_uniform
-- u735 [5-edge cycle] 1->5->6->3->2->(closed) | cand_entry+z_entry+z_entry+z_entry+z_irred
--   roles: abs=7, abs=12, abs=11, abs=11, abs=11, abs=10, abs=11, abs=9, abs=6, abs=9; 1 instances at bases [10]; all_strict=True; worst realized 1217253/1341395
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u735_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (244683882:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u735_uniform
-- u736 [5-edge cycle] 1->5->6->3->4->(closed) | cand_entry+z_entry+z_entry+z_entry+z_entry
--   roles: abs=2, tied+4, tied+1, tied+1, tied+1, tied=base, tied=base, tied=base, tied+3, abs=1; 5 instances at bases [5, 6]; all_strict=True; worst realized 858991/1292265
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 4). -/
theorem shape_u736_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (24576:ℚ) * m ^ 4 + (73728:ℚ) * m ^ 3 + (100608:ℚ) * m ^ 2 + (44928:ℚ) * m - (19578:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have h3 : (0:ℚ) ≤ (m - 5) ^ 3 := by nlinarith
  have h4 : (0:ℚ) ≤ (m - 5) ^ 4 := by nlinarith
  have hshift : (24576:ℚ) * (m - 5) ^ 4 + (565248:ℚ) * (m - 5) ^ 3 + (4892928:ℚ) * (m - 5) ^ 2 + (18868608:ℚ) * (m - 5) + (27296262:ℚ) = (24576:ℚ) * m ^ 4 + (73728:ℚ) * m ^ 3 + (100608:ℚ) * m ^ 2 + (44928:ℚ) * m - (19578:ℚ) := by ring
  linarith [ht, h2, h3, h4, hshift]
#print axioms shape_u736_uniform
-- u737 [5-edge cycle] 1->5->6->3->4->(closed) | cand_entry+z_entry+z_entry+z_entry+z_entry
--   roles: abs=2, free+5..+6, tied+1, tied+1, tied+1, tied=base, tied=base, tied=base, tied+4, abs=1; 6 instances at bases [6, 7, 8]; all_strict=True; worst realized 39825387/56159125
/-- pattern tau=(5): real half-line form, mono certificate (kind ALL, strict=True, deg D = 4). -/
theorem shape_u737_pat1_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (24576:ℚ) * m ^ 4 + (98304:ℚ) * m ^ 3 + (149760:ℚ) * m ^ 2 + (67584:ℚ) * m - (26106:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have h3 : (0:ℚ) ≤ (m - 5) ^ 3 := by nlinarith
  have h4 : (0:ℚ) ≤ (m - 5) ^ 4 := by nlinarith
  have hshift : (24576:ℚ) * (m - 5) ^ 4 + (589824:ℚ) * (m - 5) ^ 3 + (5310720:ℚ) * (m - 5) ^ 2 + (21225984:ℚ) * (m - 5) + (31703814:ℚ) = (24576:ℚ) * m ^ 4 + (98304:ℚ) * m ^ 3 + (149760:ℚ) * m ^ 2 + (67584:ℚ) * m - (26106:ℚ) := by ring
  linarith [ht, h2, h3, h4, hshift]
#print axioms shape_u737_pat1_uniform
/-- pattern tau=(6): real half-line form, mono certificate (kind ALL, strict=True, deg D = 4). -/
theorem shape_u737_pat2_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (24576:ℚ) * m ^ 4 + (61440:ℚ) * m ^ 3 + (99072:ℚ) * m ^ 2 + (56640:ℚ) * m - (26754:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have h3 : (0:ℚ) ≤ (m - 5) ^ 3 := by nlinarith
  have h4 : (0:ℚ) ≤ (m - 5) ^ 4 := by nlinarith
  have hshift : (24576:ℚ) * (m - 5) ^ 4 + (552960:ℚ) * (m - 5) ^ 3 + (4707072:ℚ) * (m - 5) ^ 2 + (17943360:ℚ) * (m - 5) + (25773246:ℚ) = (24576:ℚ) * m ^ 4 + (61440:ℚ) * m ^ 3 + (99072:ℚ) * m ^ 2 + (56640:ℚ) * m - (26754:ℚ) := by ring
  linarith [ht, h2, h3, h4, hshift]
#print axioms shape_u737_pat2_uniform
-- u738 [5-edge cycle] 1->5->6->3->4->(closed) | cand_entry+z_entry+z_entry+z_entry+z_entry
--   roles: abs=2, abs=16, abs=11, abs=11, abs=11, abs=10, abs=10, abs=10, abs=15, abs=1; 1 instances at bases [10]; all_strict=True; worst realized 25108947/39531205
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u738_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (389400966:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u738_uniform
-- u739 [5-edge cycle] 1->6->3->4->5->(closed) | cand_entry+z_entry+z_entry+z_entry+z_irred
--   roles: abs=4, tied+2, tied+1, tied=base, tied=base, tied=base, tied=base, tied=base, abs=3, tied+1; 11 instances at bases [5, 6, 7]; all_strict=True; worst realized 30118477/36196251
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 4). -/
theorem shape_u739_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (32768:ℚ) * m ^ 4 - (13312:ℚ) * m ^ 3 - (16000:ℚ) * m ^ 2 - (36848:ℚ) * m + (1562:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have h3 : (0:ℚ) ≤ (m - 5) ^ 3 := by nlinarith
  have h4 : (0:ℚ) ≤ (m - 5) ^ 4 := by nlinarith
  have hshift : (32768:ℚ) * (m - 5) ^ 4 + (642048:ℚ) * (m - 5) ^ 3 + (4699520:ℚ) * (m - 5) ^ 2 + (15188752:ℚ) * (m - 5) + (18233322:ℚ) = (32768:ℚ) * m ^ 4 - (13312:ℚ) * m ^ 3 - (16000:ℚ) * m ^ 2 - (36848:ℚ) * m + (1562:ℚ) := by ring
  linarith [ht, h2, h3, h4, hshift]
#print axioms shape_u739_uniform
-- u740 [5-edge cycle] 1->6->3->4->5->(closed) | cand_entry+z_entry+z_entry+z_entry+z_irred
--   roles: abs=5, tied+2, tied+1, tied=base, tied=base, tied=base, tied=base, tied=base, abs=4, tied+1; 17 instances at bases [5, 6, 7, 8, 9, 10]; all_strict=True; worst realized 40594469/45537219
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 4). -/
theorem shape_u740_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (32768:ℚ) * m ^ 4 - (37888:ℚ) * m ^ 3 - (27264:ℚ) * m ^ 2 - (47216:ℚ) * m + (1930:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have h3 : (0:ℚ) ≤ (m - 5) ^ 3 := by nlinarith
  have h4 : (0:ℚ) ≤ (m - 5) ^ 4 := by nlinarith
  have hshift : (32768:ℚ) * (m - 5) ^ 4 + (617472:ℚ) * (m - 5) ^ 3 + (4319616:ℚ) * (m - 5) ^ 2 + (13222544:ℚ) * (m - 5) + (14828250:ℚ) = (32768:ℚ) * m ^ 4 - (37888:ℚ) * m ^ 3 - (27264:ℚ) * m ^ 2 - (47216:ℚ) * m + (1930:ℚ) := by ring
  linarith [ht, h2, h3, h4, hshift]
#print axioms shape_u740_uniform
-- u741 [5-edge cycle] 1->6->3->4->5->(closed) | cand_entry+z_entry+z_entry+z_entry+z_irred
--   roles: abs=6, tied+2, tied+1, tied=base, tied=base, tied=base, tied=base, tied=base, abs=5, tied+1; 13 instances at bases [6, 7, 8, 9, 10]; all_strict=True; worst realized 19882681/21699007
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 4). -/
theorem shape_u741_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (32768:ℚ) * m ^ 4 - (62464:ℚ) * m ^ 3 - (38528:ℚ) * m ^ 2 - (57584:ℚ) * m + (2298:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have h3 : (0:ℚ) ≤ (m - 5) ^ 3 := by nlinarith
  have h4 : (0:ℚ) ≤ (m - 5) ^ 4 := by nlinarith
  have hshift : (32768:ℚ) * (m - 5) ^ 4 + (592896:ℚ) * (m - 5) ^ 3 + (3939712:ℚ) * (m - 5) ^ 2 + (11256336:ℚ) * (m - 5) + (11423178:ℚ) = (32768:ℚ) * m ^ 4 - (62464:ℚ) * m ^ 3 - (38528:ℚ) * m ^ 2 - (57584:ℚ) * m + (2298:ℚ) := by ring
  linarith [ht, h2, h3, h4, hshift]
#print axioms shape_u741_uniform
-- u742 [5-edge cycle] 1->6->3->4->5->(closed) | cand_entry+z_entry+z_entry+z_entry+z_irred
--   roles: abs=2, tied+4, tied+1, tied=base, tied=base, tied=base, tied=base, tied=base, abs=1, tied+1; 3 instances at bases [7, 8]; all_strict=True; worst realized 610451/983125
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 4). -/
theorem shape_u742_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (32768:ℚ) * m ^ 4 - (21504:ℚ) * m ^ 3 - (14976:ℚ) * m ^ 2 - (18800:ℚ) * m + (714:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have h3 : (0:ℚ) ≤ (m - 5) ^ 3 := by nlinarith
  have h4 : (0:ℚ) ≤ (m - 5) ^ 4 := by nlinarith
  have hshift : (32768:ℚ) * (m - 5) ^ 4 + (633856:ℚ) * (m - 5) ^ 3 + (4577664:ℚ) * (m - 5) ^ 2 + (14602640:ℚ) * (m - 5) + (17324314:ℚ) = (32768:ℚ) * m ^ 4 - (21504:ℚ) * m ^ 3 - (14976:ℚ) * m ^ 2 - (18800:ℚ) * m + (714:ℚ) := by ring
  linarith [ht, h2, h3, h4, hshift]
#print axioms shape_u742_uniform
-- u743 [5-edge cycle] 1->6->3->4->5->(closed) | cand_entry+z_entry+z_entry+z_entry+z_irred
--   roles: abs=3, tied+3, tied+1, tied=base, tied=base, tied=base, tied=base, tied=base, abs=2, tied+1; 14 instances at bases [7, 8, 9, 10]; all_strict=True; worst realized 5000211/6331325
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 4). -/
theorem shape_u743_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (32768:ℚ) * m ^ 4 - (50176:ℚ) * m ^ 3 - (27776:ℚ) * m ^ 2 - (29360:ℚ) * m + (1074:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have h3 : (0:ℚ) ≤ (m - 5) ^ 3 := by nlinarith
  have h4 : (0:ℚ) ≤ (m - 5) ^ 4 := by nlinarith
  have hshift : (32768:ℚ) * (m - 5) ^ 4 + (605184:ℚ) * (m - 5) ^ 3 + (4134784:ℚ) * (m - 5) ^ 2 + (12313680:ℚ) * (m - 5) + (13367874:ℚ) = (32768:ℚ) * m ^ 4 - (50176:ℚ) * m ^ 3 - (27776:ℚ) * m ^ 2 - (29360:ℚ) * m + (1074:ℚ) := by ring
  linarith [ht, h2, h3, h4, hshift]
#print axioms shape_u743_uniform
-- u744 [5-edge cycle] 1->6->3->4->5->(closed) | cand_entry+z_entry+z_entry+z_entry+z_irred
--   roles: abs=7, tied+2, tied+1, tied=base, tied=base, tied=base, tied=base, tied=base, abs=6, tied+1; 10 instances at bases [7, 8, 9, 10]; all_strict=True; worst realized 70599687/75700625
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 4). -/
theorem shape_u744_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (32768:ℚ) * m ^ 4 - (87040:ℚ) * m ^ 3 - (49792:ℚ) * m ^ 2 - (67952:ℚ) * m + (2666:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have h3 : (0:ℚ) ≤ (m - 5) ^ 3 := by nlinarith
  have h4 : (0:ℚ) ≤ (m - 5) ^ 4 := by nlinarith
  have hshift : (32768:ℚ) * (m - 5) ^ 4 + (568320:ℚ) * (m - 5) ^ 3 + (3559808:ℚ) * (m - 5) ^ 2 + (9290128:ℚ) * (m - 5) + (8018106:ℚ) = (32768:ℚ) * m ^ 4 - (87040:ℚ) * m ^ 3 - (49792:ℚ) * m ^ 2 - (67952:ℚ) * m + (2666:ℚ) := by ring
  linarith [ht, h2, h3, h4, hshift]
#print axioms shape_u744_uniform
-- u745 [5-edge cycle] 1->6->3->4->5->(closed) | cand_entry+z_entry+z_entry+z_entry+z_irred
--   roles: abs=8, tied+2, tied+1, tied=base, tied=base, tied=base, tied=base, tied=base, abs=7, tied+1; 7 instances at bases [8, 9, 10]; all_strict=True; worst realized 15104375/15999921
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 4). -/
theorem shape_u745_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (32768:ℚ) * m ^ 4 - (111616:ℚ) * m ^ 3 - (61056:ℚ) * m ^ 2 - (78320:ℚ) * m + (3034:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have h3 : (0:ℚ) ≤ (m - 5) ^ 3 := by nlinarith
  have h4 : (0:ℚ) ≤ (m - 5) ^ 4 := by nlinarith
  have hshift : (32768:ℚ) * (m - 5) ^ 4 + (543744:ℚ) * (m - 5) ^ 3 + (3179904:ℚ) * (m - 5) ^ 2 + (7323920:ℚ) * (m - 5) + (4613034:ℚ) = (32768:ℚ) * m ^ 4 - (111616:ℚ) * m ^ 3 - (61056:ℚ) * m ^ 2 - (78320:ℚ) * m + (3034:ℚ) := by ring
  linarith [ht, h2, h3, h4, hshift]
#print axioms shape_u745_uniform
-- u746 [5-edge cycle] 1->6->3->4->5->(closed) | cand_entry+z_entry+z_entry+z_entry+z_irred
--   roles: abs=9, tied+2, tied+1, tied=base, tied=base, tied=base, tied=base, tied=base, abs=8, tied+1; 4 instances at bases [9, 10]; all_strict=True; worst realized 242357591/254474721
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 4). -/
theorem shape_u746_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (32768:ℚ) * m ^ 4 - (136192:ℚ) * m ^ 3 - (72320:ℚ) * m ^ 2 - (88688:ℚ) * m + (3402:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have h3 : (0:ℚ) ≤ (m - 5) ^ 3 := by nlinarith
  have h4 : (0:ℚ) ≤ (m - 5) ^ 4 := by nlinarith
  have hshift : (32768:ℚ) * (m - 5) ^ 4 + (519168:ℚ) * (m - 5) ^ 3 + (2800000:ℚ) * (m - 5) ^ 2 + (5357712:ℚ) * (m - 5) + (1207962:ℚ) = (32768:ℚ) * m ^ 4 - (136192:ℚ) * m ^ 3 - (72320:ℚ) * m ^ 2 - (88688:ℚ) * m + (3402:ℚ) := by ring
  linarith [ht, h2, h3, h4, hshift]
#print axioms shape_u746_uniform
-- u747 [5-edge cycle] 1->6->3->4->5->(closed) | cand_entry+z_entry+z_entry+z_entry+z_irred
--   roles: abs=10, abs=12, abs=11, abs=10, abs=10, abs=10, abs=10, abs=10, abs=9, abs=11; 2 instances at bases [10]; all_strict=True; worst realized 1220011389/1272533659
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u747_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (157566810:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u747_uniform
-- u748 [5-edge cycle] 1->6->3->4->5->(closed) | cand_irred+z_entry+z_entry+z_entry+z_irred
--   roles: abs=7, abs=3, abs=6, abs=5, abs=5, abs=5, abs=5, abs=5, abs=3, abs=6; 3 instances at bases [5]; all_strict=True; worst realized 17437013/17514315
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u748_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (386510:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u748_uniform
-- u749 [5-edge cycle] 1->6->3->4->5->(closed) | cand_irred+z_entry+z_entry+z_entry+z_irred
--   roles: abs=9, abs=4, abs=8, abs=7, abs=7, abs=7, abs=7, abs=7, abs=4, abs=8; 4 instances at bases [7]; all_strict=True; worst realized 15096659/15140125
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u749_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (1173582:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u749_uniform
-- u750 [5-edge cycle] 1->6->3->4->5->(closed) | cand_irred+z_entry+z_entry+z_entry+z_irred
--   roles: abs=11, abs=5, abs=10, abs=9, abs=9, abs=9, abs=9, abs=9, abs=5, abs=10; 3 instances at bases [9]; all_strict=True; worst realized 146659409/146950191
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u750_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (2617038:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u750_uniform
-- u751 [5-edge cycle] 1->6->3->4->5->(closed) | cand_irred+z_entry+z_entry+z_entry+z_irred
--   roles: abs=13, abs=2, abs=11, abs=10, abs=10, abs=10, abs=10, abs=10, abs=2, abs=11; 3 instances at bases [10]; all_strict=True; worst realized 273692115/273836357
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u751_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (432726:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u751_uniform
-- u752 [5-edge cycle] 2->3->4->5->1->(closed) | cand_entry+z_entry+z_entry+z_irred+z_irred
--   roles: abs=10, abs=10, abs=7, abs=7, abs=7, abs=7, abs=1, abs=8, abs=9, abs=1; 1 instances at bases [7]; all_strict=True; worst realized 14532777/15533375
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u752_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (9005382:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u752_uniform
-- u753 [5-edge cycle] 2->3->4->5->1->(closed) | cand_entry+z_entry+z_entry+z_irred+z_irred
--   roles: abs=9, abs=10, abs=8, abs=8, abs=8, abs=8, abs=2, abs=9, abs=8, abs=2; 1 instances at bases [8]; all_strict=True; worst realized 570375/616777
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u753_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (26309934:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u753_uniform
-- u754 [5-edge cycle] 2->3->4->5->1->(closed) | cand_entry+z_entry+z_entry+z_irred+z_irred
--   roles: abs=14, abs=14, abs=10, abs=10, abs=10, abs=10, abs=1, abs=11, abs=13, abs=1; 1 instances at bases [10]; all_strict=True; worst realized 19797939/20551613
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u754_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (20349198:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u754_uniform
-- u755 [5-edge cycle] 2->3->4->5->1->(closed) | cand_irred+z_entry+z_entry+z_irred+z_irred
--   roles: abs=10, abs=9, abs=7, abs=7, abs=7, abs=7, abs=1, abs=8, abs=9, abs=1; 1 instances at bases [7]; all_strict=True; worst realized 14173943/14353625
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u755_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (1617138:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u755_uniform
-- u756 [5-edge cycle] 2->3->4->5->1->(closed) | cand_progress+z_entry+z_entry+z_entry+z_entry
--   roles: abs=10, abs=8, abs=7, abs=7, abs=7, abs=7, abs=11, abs=1, abs=1, abs=6; 1 instances at bases [7]; all_strict=True; worst realized 5526549/5702125
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u756_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (3687096:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u756_uniform
-- u757 [5-edge cycle] 2->3->4->5->1->(closed) | cand_progress+z_entry+z_entry+z_irred+z_progress
--   roles: abs=11, abs=10, abs=10, abs=10, abs=10, abs=10, abs=2, abs=11, abs=10, abs=2; 1 instances at bases [10]; all_strict=True; worst realized 98415/106097
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u757_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (55379538:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u757_uniform
-- u758 [5-edge cycle] 2->3->4->5->6->(closed) | cand_entry+z_entry+z_entry+z_entry+z_entry
--   roles: abs=4, abs=7, abs=5, abs=5, abs=5, abs=5, abs=6, abs=6, abs=8, abs=3; 1 instances at bases [5]; all_strict=True; worst realized 5589325/6648291
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u758_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (22238286:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u758_uniform
-- u759 [5-edge cycle] 2->3->4->5->6->(closed) | cand_entry+z_entry+z_entry+z_entry+z_entry
--   roles: abs=5, abs=7, abs=5, abs=5, abs=5, abs=5, abs=6, abs=6, abs=8, abs=4; 1 instances at bases [5]; all_strict=True; worst realized 2459303/2787993
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u759_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (20707470:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u759_uniform
-- u760 [5-edge cycle] 2->3->4->5->6->(closed) | cand_entry+z_entry+z_entry+z_entry+z_entry
--   roles: abs=7, abs=7, abs=5, abs=5, abs=5, abs=5, abs=6, abs=6, abs=8, abs=6; 2 instances at bases [5]; all_strict=True; worst realized 10955077/11795355
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u760_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (17645838:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u760_uniform
-- u761 [5-edge cycle] 2->3->4->5->6->(closed) | cand_entry+z_entry+z_entry+z_entry+z_entry
--   roles: abs=5, abs=9, abs=7, abs=7, abs=7, abs=7, abs=8, abs=8, abs=9, abs=4; 1 instances at bases [7]; all_strict=True; worst realized 26353/27335
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u761_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (18957510:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u761_uniform
-- u762 [5-edge cycle] 2->3->4->5->6->(closed) | cand_entry+z_entry+z_entry+z_entry+z_entry
--   roles: abs=6, abs=10, abs=7, abs=7, abs=7, abs=7, abs=8, abs=8, abs=11, abs=5; 3 instances at bases [7]; all_strict=True; worst realized 5195151/5772305
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u762_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (77915790:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u762_uniform
-- u763 [5-edge cycle] 2->3->4->5->6->(closed) | cand_entry+z_entry+z_entry+z_entry+z_entry
--   roles: abs=10, abs=10, abs=7, abs=7, abs=7, abs=7, abs=8, abs=8, abs=11, abs=9; 1 instances at bases [7]; all_strict=True; worst realized 9249903/9702385
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u763_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (61085070:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u763_uniform
-- u764 [5-edge cycle] 2->3->4->5->6->(closed) | cand_entry+z_entry+z_entry+z_entry+z_entry
--   roles: tied+4, tied+4, tied=base, tied=base, tied=base, tied=base, tied+1, tied+1, tied+5, tied+3; 4 instances at bases [9, 10]; all_strict=True; worst realized 109973295/113842081
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 4). -/
theorem shape_u764_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (24576:ℚ) * m ^ 4 + (32768:ℚ) * m ^ 3 - (322816:ℚ) * m ^ 2 - (251392:ℚ) * m + (1038:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have h3 : (0:ℚ) ≤ (m - 5) ^ 3 := by nlinarith
  have h4 : (0:ℚ) ≤ (m - 5) ^ 4 := by nlinarith
  have hshift : (24576:ℚ) * (m - 5) ^ 4 + (524288:ℚ) * (m - 5) ^ 3 + (3855104:ℚ) * (m - 5) ^ 2 + (11266048:ℚ) * (m - 5) + (10129678:ℚ) = (24576:ℚ) * m ^ 4 + (32768:ℚ) * m ^ 3 - (322816:ℚ) * m ^ 2 - (251392:ℚ) * m + (1038:ℚ) := by ring
  linarith [ht, h2, h3, h4, hshift]
#print axioms shape_u764_uniform
-- u765 [5-edge cycle] 2->3->4->5->6->(closed) | cand_entry+z_entry+z_entry+z_entry+z_irred
--   roles: free+0..+3, free+1..+4, tied=base, tied=base, tied=base, tied=base, tied+1, tied+1, tied-1, tied+1; 18 instances at bases [5, 6, 7, 8, 9, 10]; all_strict=True; worst realized 13819653/14298131
/-- pattern tau=(0,1): real half-line form, mono certificate (kind ALL, strict=True, deg D = 4). -/
theorem shape_u765_pat1_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (8192:ℚ) * m ^ 4 + (40960:ℚ) * m ^ 3 + (47360:ℚ) * m ^ 2 + (13696:ℚ) * m + (666:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have h3 : (0:ℚ) ≤ (m - 5) ^ 3 := by nlinarith
  have h4 : (0:ℚ) ≤ (m - 5) ^ 4 := by nlinarith
  have hshift : (8192:ℚ) * (m - 5) ^ 4 + (204800:ℚ) * (m - 5) ^ 3 + (1890560:ℚ) * (m - 5) ^ 2 + (7655296:ℚ) * (m - 5) + (11493146:ℚ) = (8192:ℚ) * m ^ 4 + (40960:ℚ) * m ^ 3 + (47360:ℚ) * m ^ 2 + (13696:ℚ) * m + (666:ℚ) := by ring
  linarith [ht, h2, h3, h4, hshift]
#print axioms shape_u765_pat1_uniform
/-- pattern tau=(1,2): real half-line form, mono certificate (kind ALL, strict=True, deg D = 4). -/
theorem shape_u765_pat2_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (8192:ℚ) * m ^ 4 + (90112:ℚ) * m ^ 3 + (104704:ℚ) * m ^ 2 + (17024:ℚ) * m + (1818:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have h3 : (0:ℚ) ≤ (m - 5) ^ 3 := by nlinarith
  have h4 : (0:ℚ) ≤ (m - 5) ^ 4 := by nlinarith
  have hshift : (8192:ℚ) * (m - 5) ^ 4 + (253952:ℚ) * (m - 5) ^ 3 + (2685184:ℚ) * (m - 5) ^ 2 + (11918464:ℚ) * (m - 5) + (19088538:ℚ) = (8192:ℚ) * m ^ 4 + (90112:ℚ) * m ^ 3 + (104704:ℚ) * m ^ 2 + (17024:ℚ) * m + (1818:ℚ) := by ring
  linarith [ht, h2, h3, h4, hshift]
#print axioms shape_u765_pat2_uniform
/-- pattern tau=(2,3): real half-line form, mono certificate (kind ALL, strict=True, deg D = 4). -/
theorem shape_u765_pat3_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (8192:ℚ) * m ^ 4 + (139264:ℚ) * m ^ 3 + (162048:ℚ) * m ^ 2 + (20352:ℚ) * m + (2970:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have h3 : (0:ℚ) ≤ (m - 5) ^ 3 := by nlinarith
  have h4 : (0:ℚ) ≤ (m - 5) ^ 4 := by nlinarith
  have hshift : (8192:ℚ) * (m - 5) ^ 4 + (303104:ℚ) * (m - 5) ^ 3 + (3479808:ℚ) * (m - 5) ^ 2 + (16181632:ℚ) * (m - 5) + (26683930:ℚ) = (8192:ℚ) * m ^ 4 + (139264:ℚ) * m ^ 3 + (162048:ℚ) * m ^ 2 + (20352:ℚ) * m + (2970:ℚ) := by ring
  linarith [ht, h2, h3, h4, hshift]
#print axioms shape_u765_pat3_uniform
/-- pattern tau=(3,4): real half-line form, mono certificate (kind ALL, strict=True, deg D = 4). -/
theorem shape_u765_pat4_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (8192:ℚ) * m ^ 4 + (188416:ℚ) * m ^ 3 + (219392:ℚ) * m ^ 2 + (23680:ℚ) * m + (4122:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have h3 : (0:ℚ) ≤ (m - 5) ^ 3 := by nlinarith
  have h4 : (0:ℚ) ≤ (m - 5) ^ 4 := by nlinarith
  have hshift : (8192:ℚ) * (m - 5) ^ 4 + (352256:ℚ) * (m - 5) ^ 3 + (4274432:ℚ) * (m - 5) ^ 2 + (20444800:ℚ) * (m - 5) + (34279322:ℚ) = (8192:ℚ) * m ^ 4 + (188416:ℚ) * m ^ 3 + (219392:ℚ) * m ^ 2 + (23680:ℚ) * m + (4122:ℚ) := by ring
  linarith [ht, h2, h3, h4, hshift]
#print axioms shape_u765_pat4_uniform
-- u766 [5-edge cycle] 2->3->4->5->6->(closed) | cand_entry+z_entry+z_entry+z_entry+z_irred
--   roles: free+1..+4, free+1..+4, tied=base, tied=base, tied=base, tied=base, tied+1, tied+1, tied=base, tied+1; 17 instances at bases [5, 6, 7, 8, 9, 10]; all_strict=True; worst realized 64881/66439
/-- pattern tau=(1,1): real half-line form, mono certificate (kind ALL, strict=True, deg D = 4). -/
theorem shape_u766_pat1_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (8192:ℚ) * m ^ 4 + (16384:ℚ) * m ^ 3 + (3328:ℚ) * m ^ 2 - (4864:ℚ) * m + (522:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have h3 : (0:ℚ) ≤ (m - 5) ^ 3 := by nlinarith
  have h4 : (0:ℚ) ≤ (m - 5) ^ 4 := by nlinarith
  have hshift : (8192:ℚ) * (m - 5) ^ 4 + (180224:ℚ) * (m - 5) ^ 3 + (1477888:ℚ) * (m - 5) ^ 2 + (5353216:ℚ) * (m - 5) + (7227402:ℚ) = (8192:ℚ) * m ^ 4 + (16384:ℚ) * m ^ 3 + (3328:ℚ) * m ^ 2 - (4864:ℚ) * m + (522:ℚ) := by ring
  linarith [ht, h2, h3, h4, hshift]
#print axioms shape_u766_pat1_uniform
/-- pattern tau=(2,2): real half-line form, mono certificate (kind ALL, strict=True, deg D = 4). -/
theorem shape_u766_pat2_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (8192:ℚ) * m ^ 4 + (32768:ℚ) * m ^ 3 + (15616:ℚ) * m ^ 2 - (11264:ℚ) * m + (1098:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have h3 : (0:ℚ) ≤ (m - 5) ^ 3 := by nlinarith
  have h4 : (0:ℚ) ≤ (m - 5) ^ 4 := by nlinarith
  have hshift : (8192:ℚ) * (m - 5) ^ 4 + (196608:ℚ) * (m - 5) ^ 3 + (1735936:ℚ) * (m - 5) ^ 2 + (6698496:ℚ) * (m - 5) + (9551178:ℚ) = (8192:ℚ) * m ^ 4 + (32768:ℚ) * m ^ 3 + (15616:ℚ) * m ^ 2 - (11264:ℚ) * m + (1098:ℚ) := by ring
  linarith [ht, h2, h3, h4, hshift]
#print axioms shape_u766_pat2_uniform
/-- pattern tau=(3,3): real half-line form, mono certificate (kind ALL, strict=True, deg D = 4). -/
theorem shape_u766_pat3_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (8192:ℚ) * m ^ 4 + (49152:ℚ) * m ^ 3 + (27904:ℚ) * m ^ 2 - (17664:ℚ) * m + (1674:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have h3 : (0:ℚ) ≤ (m - 5) ^ 3 := by nlinarith
  have h4 : (0:ℚ) ≤ (m - 5) ^ 4 := by nlinarith
  have hshift : (8192:ℚ) * (m - 5) ^ 4 + (212992:ℚ) * (m - 5) ^ 3 + (1993984:ℚ) * (m - 5) ^ 2 + (8043776:ℚ) * (m - 5) + (11874954:ℚ) = (8192:ℚ) * m ^ 4 + (49152:ℚ) * m ^ 3 + (27904:ℚ) * m ^ 2 - (17664:ℚ) * m + (1674:ℚ) := by ring
  linarith [ht, h2, h3, h4, hshift]
#print axioms shape_u766_pat3_uniform
/-- pattern tau=(4,4): real half-line form, mono certificate (kind ALL, strict=True, deg D = 4). -/
theorem shape_u766_pat4_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (8192:ℚ) * m ^ 4 + (65536:ℚ) * m ^ 3 + (40192:ℚ) * m ^ 2 - (24064:ℚ) * m + (2250:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have h3 : (0:ℚ) ≤ (m - 5) ^ 3 := by nlinarith
  have h4 : (0:ℚ) ≤ (m - 5) ^ 4 := by nlinarith
  have hshift : (8192:ℚ) * (m - 5) ^ 4 + (229376:ℚ) * (m - 5) ^ 3 + (2252032:ℚ) * (m - 5) ^ 2 + (9389056:ℚ) * (m - 5) + (14198730:ℚ) = (8192:ℚ) * m ^ 4 + (65536:ℚ) * m ^ 3 + (40192:ℚ) * m ^ 2 - (24064:ℚ) * m + (2250:ℚ) := by ring
  linarith [ht, h2, h3, h4, hshift]
#print axioms shape_u766_pat4_uniform
-- u767 [5-edge cycle] 2->3->4->5->6->(closed) | cand_irred+z_entry+z_entry+z_entry+z_entry
--   roles: abs=8, abs=4, abs=5, abs=5, abs=5, abs=5, abs=6, abs=6, abs=7, abs=3; 1 instances at bases [5]; all_strict=True; worst realized 2882915/2883309
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u767_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (17730:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u767_uniform
-- u768 [5-edge cycle] 2->3->4->5->6->(closed) | cand_irred+z_entry+z_entry+z_entry+z_entry
--   roles: abs=8, abs=7, abs=6, abs=6, abs=6, abs=6, abs=7, abs=7, abs=9, abs=7; 3 instances at bases [6]; all_strict=True; worst realized 8621991/8626145
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u768_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (236778:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u768_uniform
-- u769 [5-edge cycle] 2->3->4->5->6->(closed) | cand_progress+z_entry+z_entry+z_entry+z_irred
--   roles: tied+2, tied+1, tied=base, tied=base, tied=base, tied=base, tied+1, tied+1, tied+1, tied+4; 2 instances at bases [6, 7]; all_strict=True; worst realized 237177/269225
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 4). -/
theorem shape_u769_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (49152:ℚ) * m ^ 4 + (47104:ℚ) * m ^ 3 - (52992:ℚ) * m ^ 2 - (48352:ℚ) * m + (1008:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have h3 : (0:ℚ) ≤ (m - 5) ^ 3 := by nlinarith
  have h4 : (0:ℚ) ≤ (m - 5) ^ 4 := by nlinarith
  have hshift : (49152:ℚ) * (m - 5) ^ 4 + (1030144:ℚ) * (m - 5) ^ 3 + (8026368:ℚ) * (m - 5) ^ 2 + (27530528:ℚ) * (m - 5) + (35042448:ℚ) = (49152:ℚ) * m ^ 4 + (47104:ℚ) * m ^ 3 - (52992:ℚ) * m ^ 2 - (48352:ℚ) * m + (1008:ℚ) := by ring
  linarith [ht, h2, h3, h4, hshift]
#print axioms shape_u769_uniform
-- u770 [5-edge cycle] 2->3->4->5->6->(closed) | cand_progress+z_entry+z_entry+z_entry+z_irred
--   roles: abs=10, abs=8, abs=9, abs=9, abs=9, abs=9, abs=10, abs=10, abs=7, abs=10; 1 instances at bases [9]; all_strict=True; worst realized 4748139/5177107
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u770_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (173732040:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u770_uniform
-- u771 [5-edge cycle] 2->4->1->6->3->(closed) | cand_entry+z_entry+z_entry+z_entry+z_entry
--   roles: abs=13, abs=15, abs=15, abs=1, abs=1, abs=12, abs=11, abs=10, abs=11, abs=9; 1 instances at bases [10]; all_strict=True; worst realized 69400881/72156959
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u771_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (24804702:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u771_uniform
-- u772 [5-edge cycle] 2->4->5->1->3->(closed) | cand_entry+z_entry+z_entry+z_entry+z_entry
--   roles: abs=6, abs=10, abs=7, abs=7, abs=10, abs=2, abs=2, abs=8, abs=8, abs=4; 1 instances at bases [7]; all_strict=True; worst realized 113373/129955
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u772_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (24624270:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u772_uniform
-- u773 [5-edge cycle] 2->4->5->6->1->(closed) | cand_entry+z_entry+z_entry+z_irred+z_irred
--   roles: abs=4, abs=7, abs=5, abs=5, abs=6, abs=6, abs=2, abs=6, abs=3, abs=2; 2 instances at bases [5]; all_strict=True; worst realized 268755/321997
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u773_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (7826574:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u773_uniform
-- u774 [5-edge cycle] 2->4->5->6->1->(closed) | cand_progress+z_entry+z_entry+z_entry+z_irred
--   roles: abs=9, abs=4, abs=6, abs=6, abs=7, abs=7, abs=10, abs=1, abs=4, abs=1; 1 instances at bases [6]; all_strict=True; worst realized 2106853/2246365
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u774_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (3766824:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u774_uniform
-- u775 [5-edge cycle] 2->4->5->6->3->(closed) | cand_entry+z_entry+z_entry+z_entry+weak
--   roles: free+1..+2, tied+1, tied=base, tied=base, tied+1, tied+1, tied+1, tied=base; 4 instances at bases [5, 6]; all_strict=False; worst realized 7800849/7819625
/-- pattern tau=(1): real half-line form, mono certificate (kind ALL, strict=True, deg D = 2). -/
theorem shape_u775_pat1_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (512:ℚ) * m ^ 2 + (128:ℚ) * m - (424:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have hshift : (512:ℚ) * (m - 5) ^ 2 + (5248:ℚ) * (m - 5) + (13016:ℚ) = (512:ℚ) * m ^ 2 + (128:ℚ) * m - (424:ℚ) := by ring
  linarith [ht, h2, hshift]
#print axioms shape_u775_pat1_uniform
/-- pattern tau=(2): real half-line form, mono certificate (kind ALL, strict=True, deg D = 3). -/
theorem shape_u775_pat2_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (4096:ℚ) * m ^ 3 + (7168:ℚ) * m ^ 2 + (2368:ℚ) * m - (816:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have h3 : (0:ℚ) ≤ (m - 5) ^ 3 := by nlinarith
  have hshift : (4096:ℚ) * (m - 5) ^ 3 + (68608:ℚ) * (m - 5) ^ 2 + (381248:ℚ) * (m - 5) + (702224:ℚ) = (4096:ℚ) * m ^ 3 + (7168:ℚ) * m ^ 2 + (2368:ℚ) * m - (816:ℚ) := by ring
  linarith [ht, h2, h3, hshift]
#print axioms shape_u775_pat2_uniform
-- u776 [5-edge cycle] 2->4->5->6->3->(closed) | cand_progress+z_entry+z_entry+z_entry+z_entry
--   roles: free+1..+4, free+0..+2, tied=base, tied=base, tied+1, tied+1, tied+1, tied=base, tied+1, tied-1; 9 instances at bases [7, 8, 9, 10]; all_strict=True; worst realized 34206705/35005769
/-- pattern tau=(1,0): real half-line form, mono certificate (kind ALL, strict=True, deg D = 4). -/
theorem shape_u776_pat1_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (32768:ℚ) * m ^ 4 + (86016:ℚ) * m ^ 3 + (61952:ℚ) * m ^ 2 + (8256:ℚ) * m + (224:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have h3 : (0:ℚ) ≤ (m - 5) ^ 3 := by nlinarith
  have h4 : (0:ℚ) ≤ (m - 5) ^ 4 := by nlinarith
  have hshift : (32768:ℚ) * (m - 5) ^ 4 + (741376:ℚ) * (m - 5) ^ 3 + (6267392:ℚ) * (m - 5) ^ 2 + (23462976:ℚ) * (m - 5) + (32822304:ℚ) = (32768:ℚ) * m ^ 4 + (86016:ℚ) * m ^ 3 + (61952:ℚ) * m ^ 2 + (8256:ℚ) * m + (224:ℚ) := by ring
  linarith [ht, h2, h3, h4, hshift]
#print axioms shape_u776_pat1_uniform
/-- pattern tau=(2,0): real half-line form, mono certificate (kind ALL, strict=True, deg D = 3). -/
theorem shape_u776_pat2_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (69632:ℚ) * m ^ 3 + (91648:ℚ) * m ^ 2 + (16192:ℚ) * m + (728:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have h3 : (0:ℚ) ≤ (m - 5) ^ 3 := by nlinarith
  have hshift : (69632:ℚ) * (m - 5) ^ 3 + (1136128:ℚ) * (m - 5) ^ 2 + (6155072:ℚ) * (m - 5) + (11076888:ℚ) = (69632:ℚ) * m ^ 3 + (91648:ℚ) * m ^ 2 + (16192:ℚ) * m + (728:ℚ) := by ring
  linarith [ht, h2, h3, hshift]
#print axioms shape_u776_pat2_uniform
/-- pattern tau=(3,1): real half-line form, mono certificate (kind ALL, strict=True, deg D = 3). -/
theorem shape_u776_pat3_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (135168:ℚ) * m ^ 3 + (185856:ℚ) * m ^ 2 + (36672:ℚ) * m - (1512:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have h3 : (0:ℚ) ≤ (m - 5) ^ 3 := by nlinarith
  have hshift : (135168:ℚ) * (m - 5) ^ 3 + (2213376:ℚ) * (m - 5) ^ 2 + (12032832:ℚ) * (m - 5) + (21724248:ℚ) = (135168:ℚ) * m ^ 3 + (185856:ℚ) * m ^ 2 + (36672:ℚ) * m - (1512:ℚ) := by ring
  linarith [ht, h2, h3, hshift]
#print axioms shape_u776_pat3_uniform
/-- pattern tau=(4,2): real half-line form, mono certificate (kind ALL, strict=True, deg D = 3). -/
theorem shape_u776_pat4_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (200704:ℚ) * m ^ 3 + (280064:ℚ) * m ^ 2 + (57152:ℚ) * m - (3752:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have h3 : (0:ℚ) ≤ (m - 5) ^ 3 := by nlinarith
  have hshift : (200704:ℚ) * (m - 5) ^ 3 + (3290624:ℚ) * (m - 5) ^ 2 + (17910592:ℚ) * (m - 5) + (32371608:ℚ) = (200704:ℚ) * m ^ 3 + (280064:ℚ) * m ^ 2 + (57152:ℚ) * m - (3752:ℚ) := by ring
  linarith [ht, h2, h3, hshift]
#print axioms shape_u776_pat4_uniform
-- u777 [5-edge cycle] 2->5->6->3->1->(closed) | cand_entry+z_entry+z_entry+z_entry+z_entry
--   roles: abs=2, abs=10, abs=6, abs=6, abs=6, abs=5, abs=9, abs=1, abs=1, abs=1; 1 instances at bases [5]; all_strict=True; worst realized 627669/784195
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u777_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (3287046:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u777_uniform
-- u778 [5-edge cycle] 2->5->6->3->1->(closed) | cand_entry+z_entry+z_entry+z_entry+z_entry
--   roles: tied-1, abs=10, tied+1, tied+1, tied+1, tied=base, tied+3, abs=1, abs=1, tied-3; 2 instances at bases [5, 6]; all_strict=True; worst realized 96957/111683
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 4). -/
theorem shape_u778_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (28672:ℚ) * m ^ 4 - (272896:ℚ) * m ^ 3 + (623552:ℚ) * m ^ 2 + (1165000:ℚ) * m + (79902:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have h3 : (0:ℚ) ≤ (m - 5) ^ 3 := by nlinarith
  have h4 : (0:ℚ) ≤ (m - 5) ^ 4 := by nlinarith
  have hshift : (28672:ℚ) * (m - 5) ^ 4 + (300544:ℚ) * (m - 5) ^ 3 + (830912:ℚ) * (m - 5) ^ 2 + (1269320:ℚ) * (m - 5) + (5301702:ℚ) = (28672:ℚ) * m ^ 4 - (272896:ℚ) * m ^ 3 + (623552:ℚ) * m ^ 2 + (1165000:ℚ) * m + (79902:ℚ) := by ring
  linarith [ht, h2, h3, h4, hshift]
#print axioms shape_u778_uniform
-- u779 [5-edge cycle] 2->5->6->3->1->(closed) | cand_entry+z_entry+z_entry+z_entry+z_entry
--   roles: free+2..+3, abs=11, tied+1, tied+1, tied+1, tied=base, tied+3, abs=1, abs=1, tied-1; 3 instances at bases [6, 7]; all_strict=True; worst realized 207993/214775
/-- pattern tau=(2): real half-line form, mono certificate (kind ALL, strict=True, deg D = 4). -/
theorem shape_u779_pat1_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (28672:ℚ) * m ^ 4 - (223744:ℚ) * m ^ 3 + (261056:ℚ) * m ^ 2 + (765640:ℚ) * m + (168798:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have h3 : (0:ℚ) ≤ (m - 5) ^ 3 := by nlinarith
  have h4 : (0:ℚ) ≤ (m - 5) ^ 4 := by nlinarith
  have hshift : (28672:ℚ) * (m - 5) ^ 4 + (349696:ℚ) * (m - 5) ^ 3 + (1205696:ℚ) * (m - 5) ^ 2 + (931400:ℚ) * (m - 5) + (475398:ℚ) = (28672:ℚ) * m ^ 4 - (223744:ℚ) * m ^ 3 + (261056:ℚ) * m ^ 2 + (765640:ℚ) * m + (168798:ℚ) := by ring
  linarith [ht, h2, h3, h4, hshift]
#print axioms shape_u779_pat1_uniform
/-- pattern tau=(3): real half-line form, mono certificate (kind ALL, strict=True, deg D = 4). -/
theorem shape_u779_pat2_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (28672:ℚ) * m ^ 4 - (195072:ℚ) * m ^ 3 + (393664:ℚ) * m ^ 2 + (931848:ℚ) * m + (231910:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have h3 : (0:ℚ) ≤ (m - 5) ^ 3 := by nlinarith
  have h4 : (0:ℚ) ≤ (m - 5) ^ 4 := by nlinarith
  have hshift : (28672:ℚ) * (m - 5) ^ 4 + (378368:ℚ) * (m - 5) ^ 3 + (1768384:ℚ) * (m - 5) ^ 2 + (4574088:ℚ) * (m - 5) + (8268750:ℚ) = (28672:ℚ) * m ^ 4 - (195072:ℚ) * m ^ 3 + (393664:ℚ) * m ^ 2 + (931848:ℚ) * m + (231910:ℚ) := by ring
  linarith [ht, h2, h3, h4, hshift]
#print axioms shape_u779_pat2_uniform
-- u780 [5-edge cycle] 2->5->6->3->1->(closed) | cand_entry+z_entry+z_entry+z_entry+z_entry
--   roles: abs=13, abs=15, abs=11, abs=11, abs=11, abs=10, abs=14, abs=1, abs=1, abs=9; 1 instances at bases [10]; all_strict=True; worst realized 21225699/22435357
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u780_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (32660766:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u780_uniform
-- u781 [5-edge cycle] 2->5->6->3->1->(closed) | cand_entry+z_entry+z_entry+z_entry+z_irred
--   roles: abs=5, abs=7, abs=6, abs=6, abs=6, abs=5, abs=6, abs=3, abs=4, abs=3; 1 instances at bases [5]; all_strict=True; worst realized 1183301/1349699
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u781_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (12479850:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u781_uniform
-- u782 [5-edge cycle] 2->5->6->3->1->(closed) | cand_entry+z_entry+z_entry+z_entry+z_irred
--   roles: abs=7, abs=10, abs=8, abs=8, abs=8, abs=7, abs=9, abs=2, abs=6, abs=2; 1 instances at bases [7]; all_strict=True; worst realized 34827/38269
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u782_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (23698170:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u782_uniform
-- u783 [5-edge cycle] 2->5->6->3->1->(closed) | cand_irred+z_entry+z_entry+z_entry+z_entry
--   roles: abs=10, abs=3, abs=6, abs=6, abs=6, abs=5, abs=8, abs=1, abs=1, abs=2; 1 instances at bases [5]; all_strict=True; worst realized 55063/55225
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u783_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (71442:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u783_uniform
-- u784 [5-edge cycle] 2->5->6->3->1->(closed) | cand_progress+z_entry+z_entry+z_entry+z_irred
--   roles: abs=9, abs=7, abs=8, abs=8, abs=8, abs=7, abs=9, abs=2, abs=7, abs=2; 1 instances at bases [7]; all_strict=True; worst realized 260975/281799
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u784_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (20178456:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u784_uniform
-- u785 [5-edge cycle] 2->5->6->3->1->(closed) | cand_progress+z_entry+z_entry+z_entry+z_irred
--   roles: abs=9, abs=7, abs=8, abs=8, abs=8, abs=7, abs=9, abs=3, abs=7, abs=3; 1 instances at bases [7]; all_strict=True; worst realized 260975/281799
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u785_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (29674200:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u785_uniform
-- u786 [5-edge cycle] 2->5->6->3->1->(closed) | cand_progress+z_entry+z_entry+z_irred+z_progress
--   roles: tied+3, abs=4, tied+1, tied+1, tied+1, tied=base, abs=1, tied+1, abs=4, abs=1; 2 instances at bases [5, 6]; all_strict=True; worst realized 18655/19881
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 3). -/
theorem shape_u786_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (33792:ℚ) * m ^ 3 - (80256:ℚ) * m ^ 2 - (62832:ℚ) * m + (79002:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have h3 : (0:ℚ) ≤ (m - 5) ^ 3 := by nlinarith
  have hshift : (33792:ℚ) * (m - 5) ^ 3 + (426624:ℚ) * (m - 5) ^ 2 + (1669008:ℚ) * (m - 5) + (1982442:ℚ) = (33792:ℚ) * m ^ 3 - (80256:ℚ) * m ^ 2 - (62832:ℚ) * m + (79002:ℚ) := by ring
  linarith [ht, h2, h3, hshift]
#print axioms shape_u786_uniform
-- u787 [5-edge cycle] 2->5->6->3->1->(closed) | cand_progress+z_entry+z_entry+z_irred+z_progress
--   roles: abs=10, abs=7, abs=9, abs=9, abs=9, abs=8, abs=2, abs=9, abs=7, abs=2; 1 instances at bases [8]; all_strict=True; worst realized 78975/85697
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u787_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (27970242:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u787_uniform
-- u788 [5-edge cycle] 2->5->6->4->1->(closed) | cand_entry+z_entry+z_entry+z_entry+z_entry
--   roles: abs=5, abs=9, abs=6, abs=6, abs=9, abs=8, abs=8, abs=1, abs=1, abs=3; 1 instances at bases [5]; all_strict=True; worst realized 9125/10011
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u788_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (5079438:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u788_uniform
-- u789 [5-edge cycle] 2->5->6->4->1->(closed) | cand_entry+z_entry+z_entry+z_entry+z_entry
--   roles: free+1..+2, abs=9, abs=6, abs=6, abs=9, abs=8, abs=8, abs=1, abs=1, abs=4; 2 instances at bases [5]; all_strict=True; worst realized 156585/156839
/-- pattern tau=(1): real half-line form, mono certificate (kind ALL, strict=True, deg D = 1). -/
theorem shape_u789_pat1_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (11772936:ℚ) * m - (58752666:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have hshift : (11772936:ℚ) * (m - 5) + (112014:ℚ) = (11772936:ℚ) * m - (58752666:ℚ) := by ring
  linarith [ht, hshift]
#print axioms shape_u789_pat1_uniform
/-- pattern tau=(2): real half-line form, mono certificate (kind ALL, strict=True, deg D = 1). -/
theorem shape_u789_pat2_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (11772936:ℚ) * m - (46979730:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have hshift : (11772936:ℚ) * (m - 5) + (11884950:ℚ) = (11772936:ℚ) * m - (46979730:ℚ) := by ring
  linarith [ht, hshift]
#print axioms shape_u789_pat2_uniform
-- u790 [5-edge cycle] 2->5->6->4->1->(closed) | cand_entry+z_entry+z_entry+z_entry+z_entry
--   roles: abs=8, abs=9, abs=6, abs=6, abs=9, abs=8, abs=8, abs=1, abs=1, abs=5; 2 instances at bases [5]; all_strict=True; worst realized 194545/210231
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u790_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (6917526:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u790_uniform
-- u791 [5-edge cycle] 2->6->3->4->1->(closed) | cand_entry+z_entry+z_entry+z_entry+z_entry
--   roles: abs=7, abs=8, abs=6, abs=5, abs=5, abs=5, abs=7, abs=2, abs=2, abs=5; 1 instances at bases [5]; all_strict=True; worst realized 1171657/1279575
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u791_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (7014670:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u791_uniform
-- u792 [5-edge cycle] 2->6->3->4->1->(closed) | cand_entry+z_entry+z_entry+z_entry+z_entry
--   roles: abs=9, tied+3, tied+1, tied=base, tied=base, tied=base, tied+2, abs=3, abs=3, abs=7; 2 instances at bases [8, 9]; all_strict=True; worst realized 178611875/192349437
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 3). -/
theorem shape_u792_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (106496:ℚ) * m ^ 3 - (267648:ℚ) * m ^ 2 + (502912:ℚ) * m - (207090:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have h3 : (0:ℚ) ≤ (m - 5) ^ 3 := by nlinarith
  have hshift : (106496:ℚ) * (m - 5) ^ 3 + (1329792:ℚ) * (m - 5) ^ 2 + (5813632:ℚ) * (m - 5) + (8928270:ℚ) = (106496:ℚ) * m ^ 3 - (267648:ℚ) * m ^ 2 + (502912:ℚ) * m - (207090:ℚ) := by ring
  linarith [ht, h2, h3, hshift]
#print axioms shape_u792_uniform
-- u793 [5-edge cycle] 2->6->3->4->1->(closed) | cand_entry+z_entry+z_entry+z_entry+z_entry
--   roles: abs=9, abs=13, abs=9, abs=8, abs=8, abs=8, abs=12, abs=1, abs=1, abs=6; 1 instances at bases [8]; all_strict=True; worst realized 88725/95779
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u793_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (15554070:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u793_uniform
-- u794 [5-edge cycle] 2->6->3->4->1->(closed) | cand_entry+z_entry+z_entry+z_entry+z_entry
--   roles: abs=10, tied+3, tied+1, tied=base, tied=base, tied=base, tied+2, abs=3, abs=3, abs=8; 2 instances at bases [8, 9]; all_strict=True; worst realized 611040625/642067839
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 3). -/
theorem shape_u794_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (98304:ℚ) * m ^ 3 - (365952:ℚ) * m ^ 2 + (543488:ℚ) * m - (231410:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have h3 : (0:ℚ) ≤ (m - 5) ^ 3 := by nlinarith
  have hshift : (98304:ℚ) * (m - 5) ^ 3 + (1108608:ℚ) * (m - 5) ^ 2 + (4256768:ℚ) * (m - 5) + (5625230:ℚ) = (98304:ℚ) * m ^ 3 - (365952:ℚ) * m ^ 2 + (543488:ℚ) * m - (231410:ℚ) := by ring
  linarith [ht, h2, h3, hshift]
#print axioms shape_u794_uniform
-- u795 [5-edge cycle] 2->6->3->4->1->(closed) | cand_entry+z_entry+z_entry+z_entry+z_entry
--   roles: abs=13, abs=14, abs=10, abs=9, abs=9, abs=9, abs=13, abs=1, abs=1, abs=9; 1 instances at bases [9]; all_strict=True; worst realized 395630289/416541167
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u795_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (20910878:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u795_uniform
-- u796 [5-edge cycle] 2->6->3->4->1->(closed) | cand_entry+z_entry+z_entry+z_entry+z_entry
--   roles: abs=11, abs=13, abs=11, abs=10, abs=10, abs=10, abs=12, abs=4, abs=4, abs=9; 1 instances at bases [10]; all_strict=True; worst realized 36879381/39132571
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u796_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (101393550:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u796_uniform
-- u797 [5-edge cycle] 2->6->3->4->1->(closed) | cand_entry+z_entry+z_entry+z_entry+z_irred
--   roles: tied+1, tied+3, tied+1, tied=base, tied=base, tied=base, tied+2, abs=3, tied=base, abs=3; 3 instances at bases [8, 9, 10]; all_strict=True; worst realized 15309/15979
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 3). -/
theorem shape_u797_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (25600:ℚ) * m ^ 3 + (329600:ℚ) * m ^ 2 + (100400:ℚ) * m - (17750:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have h3 : (0:ℚ) ≤ (m - 5) ^ 3 := by nlinarith
  have hshift : (25600:ℚ) * (m - 5) ^ 3 + (713600:ℚ) * (m - 5) ^ 2 + (5316400:ℚ) * (m - 5) + (11924250:ℚ) = (25600:ℚ) * m ^ 3 + (329600:ℚ) * m ^ 2 + (100400:ℚ) * m - (17750:ℚ) := by ring
  linarith [ht, h2, h3, hshift]
#print axioms shape_u797_uniform
-- u798 [5-edge cycle] 2->6->3->4->1->(closed) | cand_irred+z_entry+z_entry+z_entry+z_entry
--   roles: abs=13, abs=10, abs=11, abs=10, abs=10, abs=10, abs=12, abs=4, abs=4, abs=9; 1 instances at bases [10]; all_strict=True; worst realized 6699429/6746995
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u798_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (11558538:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u798_uniform
-- u799 [5-edge cycle] 2->6->3->4->5->(closed) | cand_entry+z_entry+z_entry+z_entry+z_entry
--   roles: abs=2, abs=12, abs=7, abs=6, abs=6, abs=6, abs=6, abs=6, abs=9, abs=1; 2 instances at bases [6]; all_strict=True; worst realized 34235859/43130725
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u799_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (26684598:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u799_uniform
-- u800 [5-edge cycle] 2->6->3->4->5->(closed) | cand_entry+z_entry+z_entry+z_entry+z_irred
--   roles: abs=5, abs=7, abs=6, abs=5, abs=5, abs=5, abs=5, abs=5, abs=4, abs=6; 1 instances at bases [5]; all_strict=True; worst realized 40594469/45537219
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u800_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (14828250:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u800_uniform
-- u801 [5-edge cycle] 2->6->3->4->5->(closed) | cand_irred+z_entry+z_entry+z_entry+z_entry
--   roles: abs=12, abs=3, abs=7, abs=6, abs=6, abs=6, abs=6, abs=6, abs=8, abs=2; 1 instances at bases [6]; all_strict=True; worst realized 5428661/5467275
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u801_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (1351490:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u801_uniform
-- u802 [5-edge cycle] 3->2->1->5->6->(closed) | cand_irred+z_irred+z_irred+z_entry+z_entry
--   roles: abs=4, abs=9, abs=1, abs=3, abs=10, abs=1, abs=7, abs=7, abs=7, abs=6; 2 instances at bases [6]; all_strict=True; worst realized 15960133/16561875
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u802_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (1805226:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u802_uniform
-- u803 [5-edge cycle] 3->2->4->5->6->(closed) | cand_entry+z_progress+z_entry+z_entry+z_entry
--   roles: abs=12, abs=8, abs=10, abs=7, abs=9, abs=9, abs=10, abs=10, abs=10, abs=9; 1 instances at bases [9]; all_strict=True; worst realized 151508799/159963071
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u803_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (126814080:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u803_uniform
-- u804 [5-edge cycle] 3->2->4->5->6->(closed) | cand_irred+z_progress+z_entry+z_entry+z_entry
--   roles: abs=6, abs=9, abs=8, abs=5, abs=7, abs=7, abs=8, abs=8, abs=8, abs=7; 1 instances at bases [7]; all_strict=True; worst realized 14337115/14519043
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u804_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (8186760:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u804_uniform
-- u805 [5-edge cycle] 3->2->4->5->6->(closed) | cand_progress+z_entry+z_entry+z_entry+z_entry
--   roles: tied+2, tied+4, tied+3, tied+4, tied=base, tied=base, tied+1, tied+1, tied+1, tied=base; 3 instances at bases [9, 10]; all_strict=True; worst realized 6293457/6843217
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 4). -/
theorem shape_u805_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (32768:ℚ) * m ^ 4 + (200704:ℚ) * m ^ 3 + (297472:ℚ) * m ^ 2 + (101696:ℚ) * m - (42240:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have h3 : (0:ℚ) ≤ (m - 5) ^ 3 := by nlinarith
  have h4 : (0:ℚ) ≤ (m - 5) ^ 4 := by nlinarith
  have hshift : (32768:ℚ) * (m - 5) ^ 4 + (856064:ℚ) * (m - 5) ^ 3 + (8223232:ℚ) * (m - 5) ^ 2 + (34513216:ℚ) * (m - 5) + (53471040:ℚ) = (32768:ℚ) * m ^ 4 + (200704:ℚ) * m ^ 3 + (297472:ℚ) * m ^ 2 + (101696:ℚ) * m - (42240:ℚ) := by ring
  linarith [ht, h2, h3, h4, hshift]
#print axioms shape_u805_uniform
-- u806 [5-edge cycle] 3->2->4->5->6->(closed) | cand_progress+z_progress+z_entry+z_entry+z_entry
--   roles: abs=5, abs=10, abs=8, abs=4, abs=7, abs=7, abs=8, abs=8, abs=8, abs=7; 1 instances at bases [7]; all_strict=True; worst realized 12506845/12966723
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u806_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (20694510:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u806_uniform
-- u807 [5-edge cycle] 3->2->4->5->6->(closed) | cand_progress+z_progress+z_entry+z_entry+z_entry
--   roles: abs=7, abs=10, abs=8, abs=6, abs=7, abs=7, abs=8, abs=8, abs=8, abs=7; 1 instances at bases [7]; all_strict=True; worst realized 5795855/6417873
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u807_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (83972430:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u807_uniform
-- u808 [5-edge cycle] 3->4->5->6->2->(closed) | cand_progress+z_entry+z_entry+z_irred+z_progress
--   roles: abs=10, abs=10, abs=8, abs=8, abs=9, abs=9, abs=6, abs=9, abs=10, abs=7; 2 instances at bases [8]; all_strict=True; worst realized 9165/9443
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u808_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (44382978:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u808_uniform
-- u809 [5-edge cycle] 3->5->6->2->1->(closed) | cand_progress+z_entry+z_irred+z_irred+z_progress
--   roles: abs=8, abs=8, abs=7, abs=7, abs=2, abs=7, abs=2, abs=2, abs=8, abs=2; 1 instances at bases [6]; all_strict=True; worst realized 2925/3179
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u809_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (4705350:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u809_uniform
-- u810 [5-edge cycle] 3->5->6->2->1->(closed) | cand_progress+z_entry+z_irred+z_irred+z_progress
--   roles: abs=11, abs=11, abs=9, abs=9, abs=7, abs=9, abs=1, abs=7, abs=11, abs=1; 1 instances at bases [8]; all_strict=True; worst realized 34265/36423
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u810_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (14020526:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u810_uniform
-- u811 [5-edge cycle] 4->2->5->6->3->(closed) | cand_progress+z_entry+z_entry+z_entry+z_entry
--   roles: abs=5, abs=7, abs=6, abs=7, abs=6, abs=6, abs=6, abs=5, abs=5, abs=5; 1 instances at bases [5]; all_strict=True; worst realized 3377129/4049097
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u811_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (38302176:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u811_uniform
-- u812 [5-edge cycle] 4->2->5->6->3->(closed) | cand_progress+z_entry+z_entry+z_entry+z_entry
--   roles: abs=11, abs=13, abs=12, abs=13, abs=11, abs=11, abs=11, abs=10, abs=10, abs=10; 1 instances at bases [10]; all_strict=True; worst realized 5774409/6311705
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u812_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (507744720:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u812_uniform
-- u813 [5-edge cycle] 4->5->6->2->1->(closed) | cand_progress+z_entry+z_entry+z_irred+z_progress
--   roles: abs=7, abs=7, abs=6, abs=6, abs=7, abs=3, abs=2, abs=3, abs=7, abs=2; 1 instances at bases [5]; all_strict=True; worst realized 8379/8789
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u813_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (2921250:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u813_uniform
-- u814 [5-edge cycle] 4->5->6->2->1->(closed) | cand_progress+z_entry+z_irred+z_irred+z_progress
--   roles: abs=8, abs=8, abs=7, abs=7, abs=3, abs=7, abs=2, abs=3, abs=8, abs=2; 1 instances at bases [6]; all_strict=True; worst realized 897/935
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u814_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (3519750:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u814_uniform
-- u815 [5-edge cycle] 4->5->6->3->2->(closed) | cand_progress+z_entry+z_entry+z_entry+z_progress
--   roles: abs=10, abs=10, abs=8, abs=8, abs=8, abs=7, abs=8, abs=4, abs=10, abs=5; 1 instances at bases [7]; all_strict=True; worst realized 13585/14063
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u815_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (28225422:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u815_uniform
-- u816 [5-edge cycle] 4->5->6->3->2->(closed) | cand_progress+z_entry+z_entry+z_entry+z_progress
--   roles: abs=12, abs=12, abs=9, abs=9, abs=9, abs=8, abs=9, abs=6, abs=12, abs=8; 1 instances at bases [8]; all_strict=True; worst realized 346969/357911
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u816_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (68989310:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u816_uniform
-- u817 [5-edge cycle] 5->1->6->3->4->(closed) | cand_progress+z_entry+z_entry+z_entry+z_entry
--   roles: abs=1, tied+3, abs=2, tied+2, tied+1, tied=base, tied=base, tied=base, tied=base, tied=base; 7 instances at bases [6, 7]; all_strict=True; worst realized 500707/952875
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 4). -/
theorem shape_u817_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (24576:ℚ) * m ^ 4 + (138240:ℚ) * m ^ 3 + (76416:ℚ) * m ^ 2 - (41904:ℚ) * m + (2472:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have h3 : (0:ℚ) ≤ (m - 5) ^ 3 := by nlinarith
  have h4 : (0:ℚ) ≤ (m - 5) ^ 4 := by nlinarith
  have hshift : (24576:ℚ) * (m - 5) ^ 4 + (629760:ℚ) * (m - 5) ^ 3 + (5836416:ℚ) * (m - 5) ^ 2 + (23378256:ℚ) * (m - 5) + (34343352:ℚ) = (24576:ℚ) * m ^ 4 + (138240:ℚ) * m ^ 3 + (76416:ℚ) * m ^ 2 - (41904:ℚ) * m + (2472:ℚ) := by ring
  linarith [ht, h2, h3, h4, hshift]
#print axioms shape_u817_uniform
-- u818 [5-edge cycle] 5->1->6->3->4->(closed) | cand_progress+z_entry+z_entry+z_entry+z_entry
--   roles: abs=2, abs=13, abs=3, abs=12, abs=11, abs=10, abs=10, abs=10, abs=10, abs=10; 2 instances at bases [10]; all_strict=True; worst realized 97371801/145696145
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u818_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (434919096:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u818_uniform
-- u819 [5-edge cycle] 5->2->1->3->4->(closed) | cand_progress+z_irred+z_irred+z_entry+z_entry
--   roles: abs=4, abs=10, abs=1, abs=3, abs=9, abs=1, abs=6, abs=6, abs=6, abs=6; 1 instances at bases [6]; all_strict=True; worst realized 13126267/13419675
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u819_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (880224:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u819_uniform
-- u820 [5-edge cycle] 5->2->1->3->4->(closed) | cand_progress+z_irred+z_irred+z_entry+z_entry
--   roles: abs=5, abs=10, abs=1, abs=4, abs=9, abs=1, abs=6, abs=6, abs=6, abs=6; 1 instances at bases [6]; all_strict=True; worst realized 48925177/53141913
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u820_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (4216736:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u820_uniform
-- u821 [5-edge cycle] 5->2->6->3->4->(closed) | cand_progress+z_entry+z_entry+z_entry+z_entry
--   roles: abs=11, abs=15, abs=12, abs=15, abs=11, abs=10, abs=10, abs=10, abs=10, abs=10; 2 instances at bases [10]; all_strict=True; worst realized 15766083/17193955
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u821_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (518317536:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u821_uniform
-- u822 [5-edge cycle] 5->3->4->1->2->(closed) | cand_progress+z_entry+z_entry+z_entry+z_entry
--   roles: abs=11, abs=13, abs=8, abs=8, abs=12, abs=1, abs=1, abs=6, abs=6, abs=9; 1 instances at bases [8]; all_strict=True; worst realized 84461/93765
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u822_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (20515320:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u822_uniform
-- u823 [5-edge cycle] 5->3->4->1->2->(closed) | cand_progress+z_entry+z_entry+z_irred+z_entry
--   roles: abs=7, abs=9, abs=5, abs=5, abs=8, abs=1, abs=4, abs=1, abs=3, abs=6; 1 instances at bases [5]; all_strict=True; worst realized 169043/196443
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u823_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (5178600:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u823_uniform
-- u824 [5-edge cycle] 5->6->3->1->2->(closed) | cand_progress+z_entry+z_entry+z_entry+z_entry
--   roles: abs=10, abs=10, abs=6, abs=5, abs=8, abs=1, abs=1, abs=2, abs=3, abs=9; 1 instances at bases [5]; all_strict=True; worst realized 50881/52969
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u824_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (1522152:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u824_uniform
-- u825 [5-edge cycle] 5->6->3->2->1->(closed) | cand_progress+z_entry+z_entry+z_irred+z_progress
--   roles: abs=12, abs=12, abs=9, abs=8, abs=9, abs=6, abs=1, abs=6, abs=12, abs=1; 1 instances at bases [8]; all_strict=True; worst realized 44135/45369
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u825_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (5865202:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u825_uniform
-- u826 [5-edge cycle] 5->6->3->2->1->(closed) | cand_progress+z_entry+z_entry+z_irred+z_progress
--   roles: abs=12, abs=12, abs=9, abs=8, abs=9, abs=7, abs=1, abs=7, abs=12, abs=1; 1 instances at bases [8]; all_strict=True; worst realized 44135/45369
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u826_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (6822786:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u826_uniform
-- u827 [5-edge cycle] 6->1->3->4->5->(closed) | cand_progress+z_entry+z_entry+z_entry+z_entry
--   roles: abs=1, abs=9, abs=2, abs=7, abs=6, abs=6, abs=6, abs=6, abs=7, abs=7; 1 instances at bases [6]; all_strict=True; worst realized 23402547/44345675
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u827_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (62829384:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u827_uniform
-- u828 [5-edge cycle] 6->1->3->4->5->(closed) | cand_progress+z_entry+z_entry+z_entry+z_entry
--   roles: abs=2, tied+3, abs=3, tied+1, tied=base, tied=base, tied=base, tied=base, tied+1, tied+1; 5 instances at bases [8, 9, 10]; all_strict=True; worst realized 98164953/145696145
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 4). -/
theorem shape_u828_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (24576:ℚ) * m ^ 4 + (179200:ℚ) * m ^ 3 + (36480:ℚ) * m ^ 2 - (82992:ℚ) * m + (2648:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have h3 : (0:ℚ) ≤ (m - 5) ^ 3 := by nlinarith
  have h4 : (0:ℚ) ≤ (m - 5) ^ 4 := by nlinarith
  have hshift : (24576:ℚ) * (m - 5) ^ 4 + (670720:ℚ) * (m - 5) ^ 3 + (6410880:ℚ) * (m - 5) ^ 2 + (26009808:ℚ) * (m - 5) + (38259688:ℚ) = (24576:ℚ) * m ^ 4 + (179200:ℚ) * m ^ 3 + (36480:ℚ) * m ^ 2 - (82992:ℚ) * m + (2648:ℚ) := by ring
  linarith [ht, h2, h3, h4, hshift]
#print axioms shape_u828_uniform
-- u829 [5-edge cycle] 6->1->3->4->5->(closed) | cand_progress+z_irred+z_entry+z_entry+z_entry
--   roles: abs=1, abs=10, abs=9, abs=2, abs=7, abs=7, abs=7, abs=7, abs=8, abs=8; 2 instances at bases [7]; all_strict=True; worst realized 333203/647955
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u829_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (127474560:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u829_uniform
-- u830 [5-edge cycle] 6->2->3->4->5->(closed) | cand_entry+z_entry+z_entry+z_entry+z_entry
--   roles: free+5..+6, tied+1, tied+1, tied+3, tied=base, tied=base, tied=base, tied=base, tied+1, tied+1; 4 instances at bases [6, 7]; all_strict=True; worst realized 189820659/193784525
/-- pattern tau=(5): real half-line form, mono certificate (kind ALL, strict=True, deg D = 4). -/
theorem shape_u830_pat1_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (24576:ℚ) * m ^ 4 - (65536:ℚ) * m ^ 3 - (150784:ℚ) * m ^ 2 - (62464:ℚ) * m - (114:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have h3 : (0:ℚ) ≤ (m - 5) ^ 3 := by nlinarith
  have h4 : (0:ℚ) ≤ (m - 5) ^ 4 := by nlinarith
  have hshift : (24576:ℚ) * (m - 5) ^ 4 + (425984:ℚ) * (m - 5) ^ 3 + (2552576:ℚ) * (m - 5) ^ 2 + (5802496:ℚ) * (m - 5) + (3085966:ℚ) = (24576:ℚ) * m ^ 4 - (65536:ℚ) * m ^ 3 - (150784:ℚ) * m ^ 2 - (62464:ℚ) * m - (114:ℚ) := by ring
  linarith [ht, h2, h3, h4, hshift]
#print axioms shape_u830_pat1_uniform
/-- pattern tau=(6): real half-line form, mono certificate (kind ALL, strict=True, deg D = 4). -/
theorem shape_u830_pat2_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (57344:ℚ) * m ^ 4 - (16384:ℚ) * m ^ 3 - (139520:ℚ) * m ^ 2 - (67840:ℚ) * m + (278:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have h2 : (0:ℚ) ≤ (m - 5) ^ 2 := sq_nonneg _
  have h3 : (0:ℚ) ≤ (m - 5) ^ 3 := by nlinarith
  have h4 : (0:ℚ) ≤ (m - 5) ^ 4 := by nlinarith
  have hshift : (57344:ℚ) * (m - 5) ^ 4 + (1130496:ℚ) * (m - 5) ^ 3 + (8216320:ℚ) * (m - 5) ^ 2 + (25980160:ℚ) * (m - 5) + (29965078:ℚ) = (57344:ℚ) * m ^ 4 - (16384:ℚ) * m ^ 3 - (139520:ℚ) * m ^ 2 - (67840:ℚ) * m + (278:ℚ) := by ring
  linarith [ht, h2, h3, h4, hshift]
#print axioms shape_u830_pat2_uniform
-- u831 [5-edge cycle] 6->3->1->2->5->(closed) | cand_entry+z_entry+z_entry+z_entry+z_entry
--   roles: free+6..+7, abs=9, abs=8, abs=1, abs=1, abs=2, abs=3, abs=9, abs=6, abs=6; 2 instances at bases [5]; all_strict=True; worst realized 90593/94047
/-- pattern tau=(6): real half-line form, mono certificate (kind ALL, strict=True, deg D = 1). -/
theorem shape_u831_pat1_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (3813768:ℚ) * m - (17545626:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have hshift : (3813768:ℚ) * (m - 5) + (1523214:ℚ) = (3813768:ℚ) * m - (17545626:ℚ) := by ring
  linarith [ht, hshift]
#print axioms shape_u831_pat1_uniform
/-- pattern tau=(7): real half-line form, mono certificate (kind ALL, strict=True, deg D = 1). -/
theorem shape_u831_pat2_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (3813768:ℚ) * m - (13731858:ℚ) := by
  intro m hm
  have ht : (0:ℚ) ≤ m - 5 := by linarith
  have hshift : (3813768:ℚ) * (m - 5) + (5336982:ℚ) = (3813768:ℚ) * m - (13731858:ℚ) := by ring
  linarith [ht, hshift]
#print axioms shape_u831_pat2_uniform
-- u832 [5-edge cycle] 6->4->1->2->5->(closed) | cand_progress+z_entry+z_entry+z_entry+z_entry
--   roles: abs=11, abs=13, abs=12, abs=1, abs=1, abs=6, abs=6, abs=9, abs=9, abs=9; 1 instances at bases [8]; all_strict=True; worst realized 1422843/1585075
/-- pattern tau=(): real half-line form, mono certificate (kind ALL, strict=True, deg D = 0). -/
theorem shape_u832_uniform : ∀ m : ℚ, 5 ≤ m → 0 < (23848104:ℚ) := by
  intro m _
  norm_num
#print axioms shape_u832_uniform
