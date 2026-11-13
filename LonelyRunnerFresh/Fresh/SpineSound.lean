import Fresh.FilterAssembly

/-!
# Spine soundness: the raw-edge conflict engine behind `OneSidedSound` / `PairwiseSound`

Written 2026-11-08.  New file; nothing existing is edited.  This file proves the SOUNDNESS
direction of the two hypothesis-carrying branches of `Fresh.FilterAssembly`'s four-class J2
assembly — the one-sided (68 chain boxes, `j2_cycle_v6/v10.out`) and pairwise (5 two-sided
boxes, `j2_cycle_v12.out`) raw-edge kills — at the level the assembly's OWED props
`Fresh.FilterAssembly.OneSidedSound` / `PairwiseSound` consume.

The mathematics (all artifact-verified, `experiments/n8/j2_cycle_v12.out`:
`raw kills 141809... no-raw-kill pairs 0` on every box, [T 2,522,259 pairs / 0 exceptions]):
a surviving `(W₁ word, W₀ chain)` pair on an arrangement in the box has a RAW word edge
`(x, y)` with demand `ρ_x/ρ_y < A/B` (numerator `A ≡ ±1 mod 8`, the comb/zone-edge numerator;
`d = A/B` the raw demand) conflicting with the chain's cap `ρ_y/ρ_x ≤ C/D` (numerator
`C ≡ ±1 mod 8` for the `c-raw` entries; composed caps reduce to these), with the conflict
exactly `A·C ≤ B·D` (`d·d̄ ≤ 1`).  The engine (`joinEdge_conflict`) derives the contradiction
from the integer data plus the two realized readings inequalities; `famRefutes` lifts it
through the family (`Fresh.FilterAssembly.JoinFam`); `oneSidedSound_at` / `pairwiseSound_at`
derive the assembly's conclusion shapes (a `W₁` clear point over the faces, resp. the
disjunction with `Fresh.Certs.NoCarve`) from the per-box totality data.

Division of labour (recorded honestly):
* PROVED here, fully general: the conflict engine, the family lift, `faceLo_pos`, the
  singleton-family form `JoinFam`, and the two assembly-facing soundness schemas
  (`oneSidedSound_at`, `pairwiseSound_at`) — the latter from the per-box totality datum.
* OWED (named, data-side): `SpineTotalOneSided` / `SpineTotalPairwise` — the per-box
  statements that the artifact's verified raw-kill families are TOTAL for the box (every
  carving arrangement with no `W₁` clear point realizes some family edge), i.e. the
  `[T]-verified` no-exception laws of `j2_cycle_v12.out` lifted over the real box, plus the
  `carve ⟹ chain caps realized on g` reading-side validity (`JoinFam`'s docstring in
  `Fresh.FilterAssembly` calls exactly this the validity direction).  The five fixed
  two-sided boxes are instantiated below with their top-firing `c-raw` family edges
  (`j2_cycle_v12.out`), each with the explicit integer conflict data.
-/

namespace Fresh.SpineSound

open Fresh.FilterAssembly Fresh.Certs Fresh.FrontierFamilyCap Fresh.KTaxonomy

/-! ## The raw-edge conflict engine (E's corrected law, `j2_cycle_v12`) -/

/-- The one-ratio raw-edge conflict: the `W₁` word's raw edge demands `ρ_x/ρ_y < A/B`, the
`W₀` chain caps `ρ_y/ρ_x ≤ C/D`, and the conflict datum `A·C ≤ B·D` holds — then the pair
cannot survive on any arrangement with positive readings `g e.x`, `g e.y`.  Proof: the cap
transposes to `D/C ≤ ρ_x/ρ_y`, so `D/C < A/B`; the demand side gives `A > 0`; cross-multiply
the cap by `A·D` and the demand by `D` to get `B·D < A·C`, contradicting the datum. -/
theorem joinEdge_conflict {e : JoinEdge} {g : Fin 7 → ℝ}
    (hB : 0 < e.B) (hD : 0 < e.D) (hAC : e.A * e.C ≤ e.B * e.D)
    (hxpos : 0 < g e.x) (hypos : 0 < g e.y)
    (hdemand : g e.x / (g e.y) < (e.A : ℝ) / (e.B : ℝ))
    (hcap : g e.y / (g e.x) ≤ (e.C : ℝ) / (e.D : ℝ)) : False := by
  have hB' : (0 : ℝ) < (e.B : ℝ) := by exact_mod_cast hB
  have hD' : (0 : ℝ) < (e.D : ℝ) := by exact_mod_cast hD
  have hxypos : (0 : ℝ) < g e.x / g e.y := div_pos hxpos hypos
  have hyxpos : (0 : ℝ) < g e.y / g e.x := div_pos hypos hxpos
  -- the cap side: C > 0, and the transposed cap D/C ≤ ρ_x/ρ_y
  have hCDpos : (0 : ℝ) < (e.C : ℝ) / (e.D : ℝ) := lt_of_lt_of_le hyxpos hcap
  have hC' : (0 : ℝ) < (e.C : ℝ) := by
    by_contra hle
    push_neg at hle
    have h2 : (e.C : ℝ) / (e.D : ℝ) ≤ 0 := by
      rw [div_le_iff₀ hD']
      linarith
    exact absurd hCDpos (not_lt.mpr h2)
  -- the demand side: A > 0, and the demand cross-multiplied
  have hABpos : (0 : ℝ) < (e.A : ℝ) / (e.B : ℝ) := lt_trans hxypos hdemand
  have hA' : (0 : ℝ) < (e.A : ℝ) := by
    by_contra hle
    push_neg at hle
    have h2 : (e.A : ℝ) / (e.B : ℝ) ≤ 0 := by
      rw [div_le_iff₀ hB']
      linarith
    exact absurd hABpos (not_lt.mpr h2)
  -- demand cross-multiplied: ρ_x·B < A·ρ_y  (from ρ_x/ρ_y < A/B, via contrapositive)
  have hdem : g e.x * (e.B : ℝ) < (e.A : ℝ) * g e.y := by
    by_contra hle
    push_neg at hle
    have h2 : (e.A : ℝ) / (e.B : ℝ) ≤ g e.x / g e.y := by
      rw [div_le_div_iff₀ hB' hypos]
      exact hle
    exact absurd hdemand (not_lt.mpr h2)
  -- cap cross-multiplied: ρ_y·D ≤ C·ρ_x  (from ρ_y/ρ_x ≤ C/D)
  have hcap' : g e.y * (e.D : ℝ) ≤ (e.C : ℝ) * g e.x :=
    (div_le_div_iff₀ hxpos hD').mp hcap
  -- multiply the demand by D > 0, shape it, chain through A·(cap) , divide by ρ_x > 0
  have hchain2 : ((e.B : ℝ) * (e.D : ℝ)) * g e.x < ((e.A : ℝ) * g e.y) * (e.D : ℝ) := by
    have h := mul_lt_mul_of_pos_right hdem hD'
    have e3 : ((e.B : ℝ) * (e.D : ℝ)) * g e.x = (g e.x * (e.B : ℝ)) * (e.D : ℝ) := by ring
    rw [e3]
    exact h
  have hmid : ((e.A : ℝ) * g e.y) * (e.D : ℝ) ≤ ((e.A : ℝ) * (e.C : ℝ)) * g e.x := by
    have h := mul_le_mul_of_nonneg_left hcap' hA'.le
    calc ((e.A : ℝ) * g e.y) * (e.D : ℝ) = (e.A : ℝ) * (g e.y * (e.D : ℝ)) := by ring
      _ ≤ (e.A : ℝ) * ((e.C : ℝ) * g e.x) := h
      _ = ((e.A : ℝ) * (e.C : ℝ)) * g e.x := by ring
  have hcombo : ((e.B : ℝ) * (e.D : ℝ)) * g e.x < ((e.A : ℝ) * (e.C : ℝ)) * g e.x :=
    lt_of_lt_of_le hchain2 hmid
  have hAC' : (e.A : ℝ) * (e.C : ℝ) ≤ (e.B : ℝ) * (e.D : ℝ) := by exact_mod_cast hAC
  exact absurd hcombo
    (not_lt.mpr (mul_le_mul_of_nonneg_right hAC' hxpos.le))

#print axioms joinEdge_conflict

/-- The box faces are positive (each `FaceLo ≥ 1`), so every arrangement in a box has
positive readings — the engine's positivity side conditions. -/
theorem faceLo_pos (n : Fin 7 → ℤ) (i : Fin 7) : 0 < FaceLo n i := by
  unfold FaceLo
  have h3 : (0 : ℤ) < max (2 * n i - 1) 2 :=
    lt_of_lt_of_le (by norm_num : (0 : ℤ) < 2) (le_max_right _ _)
  exact div_pos (by exact_mod_cast h3) (by norm_num : (0 : ℝ) < 2)

#print axioms faceLo_pos

/-- Every arrangement in a box has positive readings. -/
theorem face_pos {n : Fin 7 → ℤ} {g : Fin 7 → ℝ}
    (hface : ∀ i, FaceLo n i ≤ g i ∧ g i ≤ FaceHi n i) (i : Fin 7) : 0 < g i :=
  lt_of_lt_of_le (faceLo_pos n i) (hface i).1

#print axioms face_pos

/-! ## Realized edges and the family lift -/

/-- A family edge is REALIZED on `g`: the `W₁` word's raw demand and the `W₀` chain's cap
both hold for the actual readings `g e.x`, `g e.y` (with the positivity the engine needs).
This is the reading-side linkage the artifact data supplies per box (data-side validity). -/
-- STANDING: DEFINITION
def EdgeRealized (e : JoinEdge) (g : Fin 7 → ℝ) : Prop :=
  0 < g e.x ∧ 0 < g e.y ∧
    g e.x / (g e.y) < (e.A : ℝ) / (e.B : ℝ) ∧ g e.y / (g e.x) ≤ (e.C : ℝ) / (e.D : ℝ)

/-- The family lift: if the conflict family is valid (`JoinFam`) and some member edge is
realized on `g`, the pair `(W₁ word, W₀ chain)` does not survive — the raw-edge kill. -/
theorem famRefutes {n : Fin 7 → ℤ} {fam : Finset JoinEdge} (hfam : JoinFam n fam)
    {g : Fin 7 → ℝ} (hreal : ∃ e ∈ fam, EdgeRealized e g) : False := by
  obtain ⟨e, he, hxpos, hypos, hdemand, hcap⟩ := hreal
  obtain ⟨hB, hD, hAC, -, -⟩ := hfam ⟨e, he⟩
  exact joinEdge_conflict hB hD hAC hxpos hypos hdemand hcap

#print axioms famRefutes

/-- The conflict family is valid for a SINGLETON family exactly when the edge's datum
satisfies the `JoinFam` conditions (positivity of the denominators, the conflict inequality
`A·C ≤ B·D`, and the `8m±1` numerator forms). -/
theorem joinFam_singleton (n : Fin 7 → ℤ) (x y : Fin 7) (A B C D : ℤ)
    (hB : 0 < B) (hD : 0 < D) (hAC : A * C ≤ B * D)
    (hA : A % 8 = 1 ∨ A % 8 = 7) (hC : C % 8 = 1 ∨ C % 8 = 7) :
    JoinFam n {⟨x, y, A, B, C, D⟩} := by
  intro e
  rcases e with ⟨e, he⟩
  simp only [Finset.mem_singleton] at he
  subst he
  exact ⟨hB, hD, hAC, hA, hC⟩

#print axioms joinFam_singleton

/-! ## The per-box totality data (named OWED) and the assembly-facing soundness -/

/-- **OWED — the pairwise totality datum** (data-side; the artifact law of
`j2_cycle_v12.out` — `no-raw-kill pairs 0` on all 5 two-sided boxes, 2,522,259 pairs —
lifted over the real box together with the data-side validity of the family's demands and
caps): for an arrangement in the box that carves `[1,7]` (so a `W₀` chain exists for it, and
that chain's caps are among the family's) but admits no `W₁` clear point (so a `W₁` comb
cover of `[9,15]` is realized on it), some family edge is fully realized. -/
-- STANDING: OWED
def SpineTotalPairwise (n : Fin 7 → ℤ) (fam : Finset JoinEdge) : Prop :=
  ∀ g : Fin 7 → ℝ, (∀ i, FaceLo n i ≤ g i ∧ g i ≤ FaceHi n i) →
    Fresh.FrontierFamilyCap.CarvesOneSeven (Finset.image g Finset.univ) →
    ¬ (∃ s, 9 ≤ s ∧ s ≤ 15 ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (g i * (s / 8))) →
    ∃ e ∈ fam, EdgeRealized e g

/-- **OWED — the one-sided totality datum** (data-side; `j2_cycle_v6/v10.out`: box+join
kills every `W₁` word on the 68 one-sided chain boxes): for an arrangement in the box whose
`W₀`-chain side exists (the join caps hold on `g` — this is the conditional hypothesis, so
the schema is vacuous on chainless boxes by design) and which carves `[1,7]` but admits no
`W₁` clear point, some family edge's word demand is realized. -/
-- STANDING: OWED
def SpineTotalOneSided (n : Fin 7 → ℤ) (fam : Finset JoinEdge) : Prop :=
  ∀ g : Fin 7 → ℝ, (∀ i, FaceLo n i ≤ g i ∧ g i ≤ FaceHi n i) →
    (∀ e ∈ fam, g e.y / (g e.x) ≤ (e.C : ℝ) / (e.D : ℝ)) →
    Fresh.FrontierFamilyCap.CarvesOneSeven (Finset.image g Finset.univ) →
    ¬ (∃ s, 9 ≤ s ∧ s ≤ 15 ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (g i * (s / 8))) →
    ∃ e ∈ fam, 0 < g e.x ∧ 0 < g e.y ∧ g e.x / (g e.y) < (e.A : ℝ) / (e.B : ℝ)

/-- **The one-sided soundness** (the conditional kill, `j2_cycle_v6/v10.out`): for a box with
a valid conflict family and the totality datum, IF the arrangement's `W₀`-chain side exists
(all join caps realized on `g` — the hypothesis that is vacuous on chainless boxes) and `g`
carves `[1,7]`, THEN `g` admits a `W₁` clear point over its faces — the conclusion shape of
`Fresh.FilterAssembly.OneSidedSound`. -/
theorem oneSidedSound_at (n : Fin 7 → ℤ) (fam : Finset JoinEdge)
    (_hrange : InRange17 n) (hfam : JoinFam n fam) (htotal : SpineTotalOneSided n fam)
    (g : Fin 7 → ℝ) (hface : ∀ i, FaceLo n i ≤ g i ∧ g i ≤ FaceHi n i)
    (hchain : ∀ e ∈ fam, g e.y / (g e.x) ≤ (e.C : ℝ) / (e.D : ℝ))
    (hcarve : Fresh.FrontierFamilyCap.CarvesOneSeven (Finset.image g Finset.univ)) :
    ∃ s, 9 ≤ s ∧ s ≤ 15 ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (g i * (s / 8)) := by
  by_contra hnoc
  obtain ⟨e, he, hxpos, hypos, hdemand⟩ := htotal g hface hchain hcarve hnoc
  exact famRefutes hfam ⟨e, he, hxpos, hypos, hdemand, hchain e he⟩

#print axioms oneSidedSound_at

/-- **The pairwise soundness** (E's raw-edge law, `j2_cycle_v12.out`): for a two-sided box
with a valid conflict family and the totality datum, every arrangement in the box either
does NOT carve `[1,7]` (the `Fresh.Certs.NoCarve` route the assembly consumes) or admits a
`W₁` clear point over its faces — the conclusion shape of
`Fresh.FilterAssembly.PairwiseSound`. -/
theorem pairwiseSound_at (n : Fin 7 → ℤ) (fam : Finset JoinEdge)
    (_hrange : InRange17 n) (hfam : JoinFam n fam) (htotal : SpineTotalPairwise n fam)
    (g : Fin 7 → ℝ) (hface : ∀ i, FaceLo n i ≤ g i ∧ g i ≤ FaceHi n i) :
    Fresh.Certs.NoCarve g ∨
      (∃ s, 9 ≤ s ∧ s ≤ 15 ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (g i * (s / 8))) := by
  by_cases hcarve : Fresh.FrontierFamilyCap.CarvesOneSeven (Finset.image g Finset.univ)
  · refine Or.inr ?_
    by_contra hnoc
    obtain ⟨e, he, hxpos, hypos, hdemand, hcap⟩ := htotal g hface hcarve hnoc
    exact famRefutes hfam ⟨e, he, hxpos, hypos, hdemand, hcap⟩
  · exact Or.inl hcarve

#print axioms pairwiseSound_at

/-! ## The five two-sided boxes: the top-firing `c-raw` family edges (`j2_cycle_v12.out`) -/

/-- The refutation form of box `(1,2,3,4,5,6,8)`'s top `c-raw` datum
(`seamE`, word-edge readings 2,6; chain cap `ρ₆/ρ₂ ≤ 17/7`; word demand `ρ₂/ρ₆ < 25/63`;
conflict `25·17 = 425 ≤ 441 = 63·7`): no arrangement in the box realizes both sides. -/
theorem refute_box_12568 {g : Fin 7 → ℝ}
    (hface : ∀ i, FaceLo (![1, 2, 3, 4, 5, 6, 8] : Fin 7 → ℤ) i ≤ g i ∧
      g i ≤ FaceHi (![1, 2, 3, 4, 5, 6, 8] : Fin 7 → ℤ) i)
    (hdemand : g 1 / (g 5) < (25 : ℝ) / 63) (hcap : g 5 / (g 1) ≤ (17 : ℝ) / 7) : False :=
  joinEdge_conflict (e := ⟨1, 5, 25, 63, 17, 7⟩) (by norm_num) (by norm_num) (by norm_num)
    (face_pos hface 1) (face_pos hface 5) hdemand hcap

#print axioms refute_box_12568

/-- The refutation form of box `(1,3,4,5,5,6,8)`'s top `c-raw` datum
(`seamE`, word-edge readings 5,3; chain cap `ρ₃/ρ₅ ≤ 17/23`; word demand `ρ₅/ρ₃ < 49/39`;
conflict `49·17 = 833 ≤ 897 = 39·23`). -/
theorem refute_box_134556_8 {g : Fin 7 → ℝ}
    (hface : ∀ i, FaceLo (![1, 3, 4, 5, 5, 6, 8] : Fin 7 → ℤ) i ≤ g i ∧
      g i ≤ FaceHi (![1, 3, 4, 5, 5, 6, 8] : Fin 7 → ℤ) i)
    (hdemand : g 4 / (g 2) < (49 : ℝ) / 39) (hcap : g 2 / (g 4) ≤ (17 : ℝ) / 23) : False :=
  joinEdge_conflict (e := ⟨4, 2, 49, 39, 17, 23⟩) (by norm_num) (by norm_num) (by norm_num)
    (face_pos hface 4) (face_pos hface 2) hdemand hcap

#print axioms refute_box_134556_8

/-- The refutation form of box `(1,3,4,4,5,6,7)`'s top `c-raw` datum
(`seamE`, word-edge readings 7,2; chain cap `ρ₂/ρ₇ ≤ 17/47`; word demand `ρ₇/ρ₂ < 73/31`;
conflict `73·17 = 1241 ≤ 1457 = 31·47`). -/
theorem refute_box_134456_7 {g : Fin 7 → ℝ}
    (hface : ∀ i, FaceLo (![1, 3, 4, 4, 5, 6, 7] : Fin 7 → ℤ) i ≤ g i ∧
      g i ≤ FaceHi (![1, 3, 4, 4, 5, 6, 7] : Fin 7 → ℤ) i)
    (hdemand : g 6 / (g 1) < (73 : ℝ) / 31) (hcap : g 1 / (g 6) ≤ (17 : ℝ) / 47) : False :=
  joinEdge_conflict (e := ⟨6, 1, 73, 31, 17, 47⟩) (by norm_num) (by norm_num) (by norm_num)
    (face_pos hface 6) (face_pos hface 1) hdemand hcap

#print axioms refute_box_134456_7

/-- The refutation form of box `(1,3,4,5,6,7,8)`'s top `c-raw` datum
(`seamM`, word-edge readings 7,3; chain cap `ρ₃/ρ₇ ≤ 17/39`; word demand `ρ₇/ρ₃ < 97/49`;
conflict `97·17 = 1649 ≤ 1911 = 49·39`). -/
theorem refute_box_134567_8 {g : Fin 7 → ℝ}
    (hface : ∀ i, FaceLo (![1, 3, 4, 5, 6, 7, 8] : Fin 7 → ℤ) i ≤ g i ∧
      g i ≤ FaceHi (![1, 3, 4, 5, 6, 7, 8] : Fin 7 → ℤ) i)
    (hdemand : g 6 / (g 2) < (97 : ℝ) / 49) (hcap : g 2 / (g 6) ≤ (17 : ℝ) / 39) : False :=
  joinEdge_conflict (e := ⟨6, 2, 97, 49, 17, 39⟩) (by norm_num) (by norm_num) (by norm_num)
    (face_pos hface 6) (face_pos hface 2) hdemand hcap

#print axioms refute_box_134567_8

/-- The refutation form of box `(1,2,3,4,5,6,7)`'s top `c-raw` datum
(`seamE`, word-edge readings 2,7; chain cap `ρ₇/ρ₂ ≤ 49/17`; word demand `ρ₂/ρ₇ < 33/103`;
conflict `33·49 = 1617 ≤ 1751 = 103·17`). -/
theorem refute_box_123456_7 {g : Fin 7 → ℝ}
    (hface : ∀ i, FaceLo (![1, 2, 3, 4, 5, 6, 7] : Fin 7 → ℤ) i ≤ g i ∧
      g i ≤ FaceHi (![1, 2, 3, 4, 5, 6, 7] : Fin 7 → ℤ) i)
    (hdemand : g 1 / (g 6) < (33 : ℝ) / 103) (hcap : g 6 / (g 1) ≤ (49 : ℝ) / 17) : False :=
  joinEdge_conflict (e := ⟨1, 6, 33, 103, 49, 17⟩) (by norm_num) (by norm_num) (by norm_num)
    (face_pos hface 1) (face_pos hface 6) hdemand hcap

#print axioms refute_box_123456_7

/-- The assembly-facing pairwise soundness for box `(1,2,3,4,5,6,8)` with its top `c-raw`
family edge as the singleton datum: given the box's totality datum, each arrangement in the
box does not carve `[1,7]` or admits a `W₁` clear point. -/
theorem pairwise_box_12568 (htotal : SpineTotalPairwise
      (![1, 2, 3, 4, 5, 6, 8] : Fin 7 → ℤ) {⟨1, 5, 25, 63, 17, 7⟩})
    (g : Fin 7 → ℝ)
    (hface : ∀ i, FaceLo (![1, 2, 3, 4, 5, 6, 8] : Fin 7 → ℤ) i ≤ g i ∧
      g i ≤ FaceHi (![1, 2, 3, 4, 5, 6, 8] : Fin 7 → ℤ) i) :
    Fresh.Certs.NoCarve g ∨
      (∃ s, 9 ≤ s ∧ s ≤ 15 ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (g i * (s / 8))) :=
  pairwiseSound_at _ _ (by decide) (joinFam_singleton _ _ _ 25 63 17 7 (by norm_num)
    (by norm_num) (by norm_num) (Or.inl rfl) (Or.inl rfl)) htotal g hface

#print axioms pairwise_box_12568

/-- The assembly-facing pairwise soundness for box `(1,3,4,5,5,6,8)` with its top `c-raw`
family edge as the singleton datum. -/
theorem pairwise_box_134556_8 (htotal : SpineTotalPairwise
      (![1, 3, 4, 5, 5, 6, 8] : Fin 7 → ℤ) {⟨4, 2, 49, 39, 17, 23⟩})
    (g : Fin 7 → ℝ)
    (hface : ∀ i, FaceLo (![1, 3, 4, 5, 5, 6, 8] : Fin 7 → ℤ) i ≤ g i ∧
      g i ≤ FaceHi (![1, 3, 4, 5, 5, 6, 8] : Fin 7 → ℤ) i) :
    Fresh.Certs.NoCarve g ∨
      (∃ s, 9 ≤ s ∧ s ≤ 15 ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (g i * (s / 8))) :=
  pairwiseSound_at _ _ (by decide) (joinFam_singleton _ _ _ 49 39 17 23 (by norm_num)
    (by norm_num) (by norm_num) (Or.inl rfl) (Or.inl rfl)) htotal g hface

#print axioms pairwise_box_134556_8

/-- The assembly-facing pairwise soundness for box `(1,3,4,4,5,6,7)` with its top `c-raw`
family edge as the singleton datum. -/
theorem pairwise_box_134456_7 (htotal : SpineTotalPairwise
      (![1, 3, 4, 4, 5, 6, 7] : Fin 7 → ℤ) {⟨6, 1, 73, 31, 17, 47⟩})
    (g : Fin 7 → ℝ)
    (hface : ∀ i, FaceLo (![1, 3, 4, 4, 5, 6, 7] : Fin 7 → ℤ) i ≤ g i ∧
      g i ≤ FaceHi (![1, 3, 4, 4, 5, 6, 7] : Fin 7 → ℤ) i) :
    Fresh.Certs.NoCarve g ∨
      (∃ s, 9 ≤ s ∧ s ≤ 15 ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (g i * (s / 8))) :=
  pairwiseSound_at _ _ (by decide) (joinFam_singleton _ _ _ 73 31 17 47 (by norm_num)
    (by norm_num) (by norm_num) (Or.inl rfl) (Or.inl rfl)) htotal g hface

#print axioms pairwise_box_134456_7

/-- The assembly-facing pairwise soundness for box `(1,3,4,5,6,7,8)` with its top `c-raw`
family edge as the singleton datum. -/
theorem pairwise_box_134567_8 (htotal : SpineTotalPairwise
      (![1, 3, 4, 5, 6, 7, 8] : Fin 7 → ℤ) {⟨6, 2, 97, 49, 17, 39⟩})
    (g : Fin 7 → ℝ)
    (hface : ∀ i, FaceLo (![1, 3, 4, 5, 6, 7, 8] : Fin 7 → ℤ) i ≤ g i ∧
      g i ≤ FaceHi (![1, 3, 4, 5, 6, 7, 8] : Fin 7 → ℤ) i) :
    Fresh.Certs.NoCarve g ∨
      (∃ s, 9 ≤ s ∧ s ≤ 15 ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (g i * (s / 8))) :=
  pairwiseSound_at _ _ (by decide) (joinFam_singleton _ _ _ 97 49 17 39 (by norm_num)
    (by norm_num) (by norm_num) (Or.inl rfl) (Or.inl rfl)) htotal g hface

#print axioms pairwise_box_134567_8

/-- The assembly-facing pairwise soundness for box `(1,2,3,4,5,6,7)` with its top `c-raw`
family edge as the singleton datum. -/
theorem pairwise_box_123456_7 (htotal : SpineTotalPairwise
      (![1, 2, 3, 4, 5, 6, 7] : Fin 7 → ℤ) {⟨1, 6, 33, 103, 49, 17⟩})
    (g : Fin 7 → ℝ)
    (hface : ∀ i, FaceLo (![1, 2, 3, 4, 5, 6, 7] : Fin 7 → ℤ) i ≤ g i ∧
      g i ≤ FaceHi (![1, 2, 3, 4, 5, 6, 7] : Fin 7 → ℤ) i) :
    Fresh.Certs.NoCarve g ∨
      (∃ s, 9 ≤ s ∧ s ≤ 15 ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (g i * (s / 8))) :=
  pairwiseSound_at _ _ (by decide) (joinFam_singleton _ _ _ 33 103 49 17 (by norm_num)
    (by norm_num) (by norm_num) (Or.inl rfl) (Or.inl rfl)) htotal g hface

#print axioms pairwise_box_123456_7

end Fresh.SpineSound
