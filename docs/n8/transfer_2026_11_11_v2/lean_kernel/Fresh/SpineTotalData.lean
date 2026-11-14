import Fresh.SpineSound

/-!
# Spine totality data: the per-box data-side lift for `Fresh.SpineSound`'s engine

Written 2026-11-08.  New file; nothing existing is edited.  This file is the data-side lift
attempt for `Fresh.SpineSound`'s two hypothesis-carrying branches (`SpineTotalPairwise`,
`SpineTotalOneSided`), box by box, from `experiments/n8/j2_cycle_v12.out` (5 two-sided boxes)
and `experiments/n8/j2_cycle_v6.out` (68 one-sided boxes).  All arithmetic is exact
(`norm_num` on integers/rationals; no floats anywhere).

Grading (rule 18), stated honestly up front:

* PROVED here, fully general:
  - the two reduction schemas the "refute_box_* technique" would need —
    `spineTotalPairwise_of_intervalForced`, `spineTotalOneSided_of_intervalForcedDemand`
    (an edge whose demand, resp. demand and cap, is FORCED by the FaceLo/FaceHi interval
    alone yields the corresponding `SpineTotal` instance trivially);
  - three NO-GO lemmas (`capDerivedDemand_unsat`, `intervalForcedDemand_capUnsat`,
    `intervalForcedPair_invalid`) proving that this reduction can never discharge the
    per-box totality non-vacuously: an interval-forced demand makes the chain-cap
    hypothesis unsatisfiable on the box (empty kill), and a demand derivable from the
    family caps alone contradicts the family's own conflict datum `A·C ≤ B·D`;
  - the exact interval witnesses (`not_forced_demand`, `not_forced_cap`): for each of the
    five boxes' top `c-raw` edges, the demand and the cap are NOT interval-forced —
    exhibited by an explicit arrangement at the box faces, by integer arithmetic;
  - per-box DATA for the five two-sided boxes (`spineFamData_*`): `InRange17` and `JoinFam`
    for the artifact's `c-raw` families — two of the three engine hypotheses of
    `Fresh.SpineSound.pairwiseSound_at` / `oneSidedSound_at`, discharged from the artifact.
* NOT here (named, with the rule-22 record): the `spineTotalPairwise_*` /
  `spineTotalOneSided_*` instances themselves.  They are NOT discharged by this file, for
  the reason the no-go lemmas make exact: their conclusions must be derived from the carve /
  no-clear-point hypotheses (the `W₀`-chain resp. `W₁`-word realization over the continuum),
  which is the acknowledged data-side machinery Fresh does not have (see the OWED notes in
  `Fresh.SpineSound` and the covering-argument gap recorded in
  `Fresh.FrontierFamilyCap.FrontierCarveCap`'s docstring).  The three rule-22 fields for
  every resisting box are recorded in the per-box section below and in the one-sided section.

Artifact provenance for the per-box families (`j2_cycle_v12.out`, `c-raw` lines of the
`RAW families` blocks; word-edge readings are 1-based, so `JoinEdge x = readings − 1`):

* BOX (1,2,3,4,5,6,8): `('seamE', 2, 6, 'c-raw', '17/7', '25/63')`,
  `('seamE', 2, 6, 'c-raw', '41/17', '25/63')`  → `fam12568` (2 edges);
* BOX (1,3,4,5,5,6,8): `('seamE', 5, 3, 'c-raw', '17/23', '49/39')`  → `fam134556_8`;
* BOX (1,3,4,4,5,6,7): `('seamE', 5, 3, 'c-raw', '17/23', '49/39')`,
  `('seamE', 7, 2, 'c-raw', '17/47', '73/31')`  → `fam134456_7` (2 edges);
* BOX (1,3,4,5,6,7,8): `('seamM', 7, 3, 'c-raw', '17/39', '97/49')`  → `fam134567_8`;
* BOX (1,2,3,4,5,6,7): `('seamE', 2, 7, 'c-raw', '49/17', '33/103')`  → `fam123456_7`.

(The `.out` lists the top-16 firing families per box; `fam*` below carries exactly the
listed `c-raw` entries — the only ones guaranteed the `8m±1` numerator datum `JoinFam`
requires.  `Fresh.SpineSound`'s `pairwise_box_*` theorems instantiate the single top edge
of each of these families; the families here are the artifact-faithful supersets.)
-/

namespace Fresh.SpineTotalData

open Fresh.FilterAssembly Fresh.SpineSound

/-! ## 1. The reduction schemas (what the interval technique would need) -/

/-- **Reduction schema (pairwise)**: if some family edge has BOTH its word demand and its
chain cap forced by the box interval alone, then `SpineTotalPairwise` holds trivially —
the carve / no-clear-point hypotheses are not used.  Per-box instances of the two
`interval-forced` hypotheses are exactly what "reduces to integer interval bounds"; §3
shows they fail for every artifact edge, and §2 shows they could not be used anyway. -/
theorem spineTotalPairwise_of_intervalForced {n : Fin 7 → ℤ} {fam : Finset JoinEdge}
    {e : JoinEdge} (he : e ∈ fam)
    (hdem : ∀ g : Fin 7 → ℝ, (∀ i, FaceLo n i ≤ g i ∧ g i ≤ FaceHi n i) →
      g e.x / g e.y < (e.A : ℝ) / (e.B : ℝ))
    (hcap : ∀ g : Fin 7 → ℝ, (∀ i, FaceLo n i ≤ g i ∧ g i ≤ FaceHi n i) →
      g e.y / g e.x ≤ (e.C : ℝ) / (e.D : ℝ)) :
    SpineTotalPairwise n fam := by
  intro g hface _ _
  exact ⟨e, he, face_pos hface e.x, face_pos hface e.y, hdem g hface, hcap g hface⟩

#print axioms spineTotalPairwise_of_intervalForced

/-- **Reduction schema (one-sided)**: if some family edge has its word demand forced by the
box interval alone, `SpineTotalOneSided` holds — again without using the chain, carve or
clear-point hypotheses. -/
theorem spineTotalOneSided_of_intervalForcedDemand {n : Fin 7 → ℤ} {fam : Finset JoinEdge}
    {e : JoinEdge} (he : e ∈ fam)
    (hdem : ∀ g : Fin 7 → ℝ, (∀ i, FaceLo n i ≤ g i ∧ g i ≤ FaceHi n i) →
      g e.x / g e.y < (e.A : ℝ) / (e.B : ℝ)) :
    SpineTotalOneSided n fam := by
  intro g hface _ _ _
  exact ⟨e, he, face_pos hface e.x, face_pos hface e.y, hdem g hface⟩

#print axioms spineTotalOneSided_of_intervalForcedDemand

/-! ## 2. The no-go lemmas: the interval technique cannot discharge the totality -/

/-- The box faces are nested when the box entries are at least `1`. -/
theorem faceLo_le_faceHi {n : Fin 7 → ℤ} (hn : ∀ i, 1 ≤ n i) (i : Fin 7) :
    FaceLo n i ≤ FaceHi n i := by
  have h1 : max (2 * n i - 1) 2 ≤ 2 * n i + 1 := by
    apply max_le
    · linarith
    · have : 1 ≤ n i := hn i
      linarith
  unfold FaceLo FaceHi
  have h3 : ((max (2 * n i - 1) 2 : ℤ) : ℝ) ≤ ((2 * n i + 1 : ℤ) : ℝ) := by
    exact_mod_cast h1
  linarith

#print axioms faceLo_le_faceHi

/-- **No-go (core).**  If the demand `ρ_x/ρ_y < A/B` of a family edge `e` is derivable from
the box interval PLUS the family's chain caps alone, then those chain caps are
UNSATISFIABLE on the box: any `g` realizing them would give
`1 = (ρ_x/ρ_y)·(ρ_y/ρ_x) < (A/B)·(C/D) ≤ 1` against `e`'s own conflict datum `A·C ≤ B·D`
(the `d·d̄ ≤ 1` law).  So any `SpineTotalOneSided` instance proved from caps alone is a
VACUOUS kill — the conditional hypothesis of `Fresh.SpineSound.oneSidedSound_at` can never
hold.  A non-vacuous totality must use the carve / no-clear-point structure. -/
theorem capDerivedDemand_unsat {n : Fin 7 → ℤ} {fam : Finset JoinEdge} {e : JoinEdge}
    (he : e ∈ fam) (hB : 0 < e.B) (hD : 0 < e.D) (hAC : e.A * e.C ≤ e.B * e.D)
    (hdem : ∀ g : Fin 7 → ℝ, (∀ i, FaceLo n i ≤ g i ∧ g i ≤ FaceHi n i) →
      (∀ e' ∈ fam, g e'.y / g e'.x ≤ (e'.C : ℝ) / (e'.D : ℝ)) →
      g e.x / g e.y < (e.A : ℝ) / (e.B : ℝ)) :
    ∀ g : Fin 7 → ℝ, (∀ i, FaceLo n i ≤ g i ∧ g i ≤ FaceHi n i) →
      ¬ (∀ e' ∈ fam, g e'.y / g e'.x ≤ (e'.C : ℝ) / (e'.D : ℝ)) := by
  intro g hface hchain
  have hxpos : (0 : ℝ) < g e.x := face_pos hface e.x
  have hypos : (0 : ℝ) < g e.y := face_pos hface e.y
  have hxypos : (0 : ℝ) < g e.x / g e.y := div_pos hxpos hypos
  have hyxpos : (0 : ℝ) < g e.y / g e.x := div_pos hypos hxpos
  have hd : g e.x / g e.y < (e.A : ℝ) / (e.B : ℝ) := hdem g hface hchain
  have hcap : g e.y / g e.x ≤ (e.C : ℝ) / (e.D : ℝ) := hchain e he
  have hABpos : (0 : ℝ) < (e.A : ℝ) / (e.B : ℝ) := lt_trans hxypos hd
  have hA' : (0 : ℝ) < (e.A : ℝ) := by
    by_contra hle
    push_neg at hle
    have h2 : (e.A : ℝ) / (e.B : ℝ) ≤ 0 := by
      rw [div_le_iff₀ (by exact_mod_cast hB)]
      linarith
    exact absurd hABpos (not_lt.mpr h2)
  have hCDpos : (0 : ℝ) < (e.C : ℝ) / (e.D : ℝ) := lt_of_lt_of_le hyxpos hcap
  have hC' : (0 : ℝ) < (e.C : ℝ) := by
    by_contra hle
    push_neg at hle
    have h2 : (e.C : ℝ) / (e.D : ℝ) ≤ 0 := by
      rw [div_le_iff₀ (by exact_mod_cast hD)]
      linarith
    exact absurd hCDpos (not_lt.mpr h2)
  have hprod : (1 : ℝ) < ((e.A : ℝ) / (e.B : ℝ)) * ((e.C : ℝ) / (e.D : ℝ)) := by
    have hx0 : g e.x ≠ 0 := ne_of_gt hxpos
    have hy0 : g e.y ≠ 0 := ne_of_gt hypos
    have e1 : (g e.x / g e.y) * (g e.y / g e.x) = 1 := by field_simp
    have h1 : (g e.x / g e.y) * (g e.y / g e.x)
        < ((e.A : ℝ) / (e.B : ℝ)) * (g e.y / g e.x) :=
      mul_lt_mul_of_pos_right hd hyxpos
    rw [e1] at h1
    have h2 : ((e.A : ℝ) / (e.B : ℝ)) * (g e.y / g e.x)
        ≤ ((e.A : ℝ) / (e.B : ℝ)) * ((e.C : ℝ) / (e.D : ℝ)) :=
      mul_le_mul_of_nonneg_left hcap hABpos.le
    linarith
  have hBDpos : (0 : ℝ) < (e.B : ℝ) * (e.D : ℝ) :=
    mul_pos (by exact_mod_cast hB) (by exact_mod_cast hD)
  have hCD : ((e.A : ℝ) / (e.B : ℝ)) * ((e.C : ℝ) / (e.D : ℝ)) ≤ 1 := by
    have hB0 : (e.B : ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast hB)
    have hD0 : (e.D : ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast hD)
    have e2 : ((e.A : ℝ) / (e.B : ℝ)) * ((e.C : ℝ) / (e.D : ℝ))
        = ((e.A : ℝ) * (e.C : ℝ)) / ((e.B : ℝ) * (e.D : ℝ)) := by
      field_simp
    rw [e2, div_le_iff₀ hBDpos]
    have hAC' : (e.A : ℝ) * (e.C : ℝ) ≤ (e.B : ℝ) * (e.D : ℝ) := by exact_mod_cast hAC
    linarith
  linarith

#print axioms capDerivedDemand_unsat

/-- **No-go (one-sided, interval form).**  If `e`'s demand is interval-forced (holds for
every arrangement of the box) and `e` carries the conflict datum, then `e`'s chain cap
`ρ_y/ρ_x ≤ C/D` fails on EVERY arrangement of the box.  So the interval-forced route to
`SpineTotalOneSided` (`spineTotalOneSided_of_intervalForcedDemand`) always yields an empty
kill: the assembly's chain hypothesis cannot be met. -/
theorem intervalForcedDemand_capUnsat {n : Fin 7 → ℤ} {x y : Fin 7} {A B C D : ℤ}
    (hB : 0 < B) (hD : 0 < D) (hAC : A * C ≤ B * D)
    (hdem : ∀ g : Fin 7 → ℝ, (∀ i, FaceLo n i ≤ g i ∧ g i ≤ FaceHi n i) →
      g x / g y < (A : ℝ) / (B : ℝ))
    (g : Fin 7 → ℝ) (hface : ∀ i, FaceLo n i ≤ g i ∧ g i ≤ FaceHi n i) :
    ¬ (g y / g x ≤ (C : ℝ) / (D : ℝ)) := by
  have h := capDerivedDemand_unsat (fam := {⟨x, y, A, B, C, D⟩}) (e := ⟨x, y, A, B, C, D⟩)
    (Finset.mem_singleton.mpr rfl) hB hD hAC (fun g' hf _ => hdem g' hf) g hface
  simpa only [Finset.mem_singleton, forall_eq] using h

#print axioms intervalForcedDemand_capUnsat

/-- **No-go (pairwise, interval form).**  If BOTH the demand and the cap of an edge are
interval-forced, the conflict datum `A·C ≤ B·D` is violated outright (the witness
`g := FaceLo` realizes both sides, forcing `1 < (A/B)·(C/D) ≤ 1`).  So no valid
`JoinFam` edge can have both sides interval-forced: the pairwise totality
`SpineTotalPairwise` (whose `EdgeRealized` conclusion needs both) is never
interval-reachable. -/
theorem intervalForcedPair_invalid {n : Fin 7 → ℤ} (hn : ∀ i, 1 ≤ n i) {x y : Fin 7}
    {A B C D : ℤ} (hB : 0 < B) (hD : 0 < D) (hAC : A * C ≤ B * D)
    (hdem : ∀ g : Fin 7 → ℝ, (∀ i, FaceLo n i ≤ g i ∧ g i ≤ FaceHi n i) →
      g x / g y < (A : ℝ) / (B : ℝ))
    (hcap : ∀ g : Fin 7 → ℝ, (∀ i, FaceLo n i ≤ g i ∧ g i ≤ FaceHi n i) →
      g y / g x ≤ (C : ℝ) / (D : ℝ)) : False := by
  have hin : ∀ i, FaceLo n i ≤ (fun j => FaceLo n j) i ∧ (fun j => FaceLo n j) i ≤ FaceHi n i :=
    fun i => ⟨le_refl _, faceLo_le_faceHi hn i⟩
  exact intervalForcedDemand_capUnsat hB hD hAC hdem (fun j => FaceLo n j) hin
    (hcap (fun j => FaceLo n j) hin)

#print axioms intervalForcedPair_invalid

/-! ## 3. Exact interval witnesses: the artifact edges are not interval-forced -/

/-- The face ratio: `FaceHi x / FaceLo y` is the exact integer ratio `(2n_x+1)/max(2n_y-1,2)`
— the interval maximum of `ρ_x/ρ_y`. -/
theorem faceHi_div_faceLo (n : Fin 7 → ℤ) (x y : Fin 7) :
    FaceHi n x / FaceLo n y = ((2 * n x + 1 : ℤ) : ℝ) / ((max (2 * n y - 1) 2 : ℤ) : ℝ) := by
  have hb : FaceLo n y ≠ 0 := (faceLo_pos n y).ne'
  unfold FaceHi FaceLo
  field_simp

/-- The arrangement putting reading `x` at its top face and every other reading at its
bottom face is in the box. -/
theorem witness_inBox {n : Fin 7 → ℤ} (hn : ∀ i, 1 ≤ n i) (x : Fin 7) :
    ∀ i, FaceLo n i ≤ (fun j => if j = x then FaceHi n x else FaceLo n j) i ∧
      (fun j => if j = x then FaceHi n x else FaceLo n j) i ≤ FaceHi n i := by
  intro i
  show FaceLo n i ≤ (if i = x then FaceHi n x else FaceLo n i) ∧
    (if i = x then FaceHi n x else FaceLo n i) ≤ FaceHi n i
  by_cases h : i = x
  · rw [if_pos h, h]
    exact ⟨faceLo_le_faceHi hn x, le_refl _⟩
  · rw [if_neg h]
    exact ⟨le_refl _, faceLo_le_faceHi hn i⟩

#print axioms witness_inBox

/-- **Demand not interval-forced (generic form).**  Integer datum:
`A·max(2n_y−1,2) ≤ B·(2n_x+1)` — i.e. the interval maximum `FaceHi x/FaceLo y` of the
demand ratio already reaches `A/B` — then the demand `ρ_x/ρ_y < A/B` is NOT forced by the
box interval: the witness arrangement (`x` at its top face, the rest at bottom faces)
violates it. -/
theorem not_forced_demand {n : Fin 7 → ℤ} (hn : ∀ i, 1 ≤ n i) {x y : Fin 7} (hxy : x ≠ y)
    {A B : ℤ} (hB : 0 < B)
    (hdat : A * max (2 * n y - 1) 2 ≤ B * (2 * n x + 1)) :
    ¬ (∀ g : Fin 7 → ℝ, (∀ i, FaceLo n i ≤ g i ∧ g i ≤ FaceHi n i) →
        g x / g y < (A : ℝ) / (B : ℝ)) := by
  intro h
  have hin := witness_inBox hn x
  have h1 := h _ hin
  rw [if_pos rfl, if_neg (Ne.symm hxy)] at h1
  rw [faceHi_div_faceLo] at h1
  have hmax : (0 : ℤ) < max (2 * n y - 1) 2 :=
    lt_of_lt_of_le (by norm_num : (0 : ℤ) < 2) (le_max_right _ _)
  have hge : (A : ℝ) / (B : ℝ) ≤ ((2 * n x + 1 : ℤ) : ℝ) / ((max (2 * n y - 1) 2 : ℤ) : ℝ) := by
    rw [div_le_div_iff₀ (by exact_mod_cast hB) (by exact_mod_cast hmax)]
    have hd : (A : ℝ) * ((max (2 * n y - 1) 2 : ℤ) : ℝ)
        ≤ (B : ℝ) * ((2 * n x + 1 : ℤ) : ℝ) := by exact_mod_cast hdat
    linarith
  linarith

#print axioms not_forced_demand

/-- **Cap not interval-forced (generic form).**  Integer datum:
`C·max(2n_x−1,2) < D·(2n_y+1)` — the interval maximum `FaceHi y/FaceLo x` of the cap ratio
exceeds `C/D` — then the chain cap `ρ_y/ρ_x ≤ C/D` is NOT forced by the box interval. -/
theorem not_forced_cap {n : Fin 7 → ℤ} (hn : ∀ i, 1 ≤ n i) {x y : Fin 7} (hxy : x ≠ y)
    {C D : ℤ} (hD : 0 < D)
    (hdat : C * max (2 * n x - 1) 2 < D * (2 * n y + 1)) :
    ¬ (∀ g : Fin 7 → ℝ, (∀ i, FaceLo n i ≤ g i ∧ g i ≤ FaceHi n i) →
        g y / g x ≤ (C : ℝ) / (D : ℝ)) := by
  intro h
  have hin := witness_inBox hn y
  have h1 := h _ hin
  rw [if_pos rfl, if_neg hxy] at h1
  rw [faceHi_div_faceLo] at h1
  have hmax : (0 : ℤ) < max (2 * n x - 1) 2 :=
    lt_of_lt_of_le (by norm_num : (0 : ℤ) < 2) (le_max_right _ _)
  have hgt : (C : ℝ) / (D : ℝ) < ((2 * n y + 1 : ℤ) : ℝ) / ((max (2 * n x - 1) 2 : ℤ) : ℝ) := by
    rw [div_lt_div_iff₀ (by exact_mod_cast hD) (by exact_mod_cast hmax)]
    have hd : (C : ℝ) * ((max (2 * n x - 1) 2 : ℤ) : ℝ)
        < (D : ℝ) * ((2 * n y + 1 : ℤ) : ℝ) := by exact_mod_cast hdat
    linarith
  linarith

#print axioms not_forced_cap

/-- `JoinFam` for a two-edge family, from the per-edge integer data. -/
theorem joinFam_two {n : Fin 7 → ℤ} {e1 e2 : JoinEdge}
    (h1 : 0 < e1.B ∧ 0 < e1.D ∧ e1.A * e1.C ≤ e1.B * e1.D ∧
      (e1.A % 8 = 1 ∨ e1.A % 8 = 7) ∧ (e1.C % 8 = 1 ∨ e1.C % 8 = 7))
    (h2 : 0 < e2.B ∧ 0 < e2.D ∧ e2.A * e2.C ≤ e2.B * e2.D ∧
      (e2.A % 8 = 1 ∨ e2.A % 8 = 7) ∧ (e2.C % 8 = 1 ∨ e2.C % 8 = 7)) :
    JoinFam n {e1, e2} := by
  intro e
  obtain ⟨e, he⟩ := e
  simp only [Finset.mem_insert, Finset.mem_singleton] at he
  rcases he with rfl | rfl
  · exact h1
  · exact h2

#print axioms joinFam_two

/-! ## 4. The five two-sided boxes: artifact data (`j2_cycle_v12.out`)

Per box: the artifact `c-raw` family, the discharged engine hypotheses (`InRange17` +
`JoinFam`), and the two not-interval-forced witnesses for the top `c-raw` edge (rule 22
fields (i)/(ii): the exact integer derivation showing the interval reduction cannot even
start on these edges; field (iii) below and in the module docstring). -/

/-! ### Box (1,2,3,4,5,6,8) -/

/-- The `c-raw` family of `j2_cycle_v12.out` BOX (1,2,3,4,5,6,8): word-edge readings (2,6),
demand `ρ₂/ρ₆ < 25/63`, against the chain caps `ρ₆/ρ₂ ≤ 17/7` and `ρ₆/ρ₂ ≤ 41/17`. -/
def fam12568 : Finset JoinEdge := {⟨1, 5, 25, 63, 17, 7⟩, ⟨1, 5, 25, 63, 41, 17⟩}

/-- The discharged engine hypotheses for box (1,2,3,4,5,6,8): `InRange17` and `JoinFam` of
the artifact `c-raw` family (conflicts `25·17 = 425 ≤ 441 = 63·7`, `25·41 = 1025 ≤
1071 = 63·17`; numerators `25, 41, 17 ≡ 1 mod 8`). -/
theorem spineFamData_12568 :
    InRange17 (![1, 2, 3, 4, 5, 6, 8] : Fin 7 → ℤ) ∧
      JoinFam (![1, 2, 3, 4, 5, 6, 8] : Fin 7 → ℤ) fam12568 := by
  refine ⟨by decide, ?_⟩
  intro e
  obtain ⟨e, he⟩ := e
  simp only [fam12568, Finset.mem_insert, Finset.mem_singleton] at he
  rcases he with rfl | rfl
  · exact ⟨by norm_num, by norm_num, by norm_num, Or.inl (by norm_num), Or.inl (by norm_num)⟩
  · exact ⟨by norm_num, by norm_num, by norm_num, Or.inl (by norm_num), Or.inl (by norm_num)⟩

#print axioms spineFamData_12568

/-- Rule 22 (ii), demand side: the top `c-raw` demand `ρ₂/ρ₆ < 25/63` is not forced by the
box interval — the face witness has `ρ₂/ρ₆ = FaceHi 2/FaceLo 6 = (5/2)/(11/2) = 5/11 ≥
25/63` (`25·11 = 275 ≤ 315 = 63·5`). -/
theorem demand_not_forced_12568 :
    ¬ (∀ g : Fin 7 → ℝ, (∀ i, FaceLo (![1, 2, 3, 4, 5, 6, 8] : Fin 7 → ℤ) i ≤ g i ∧
          g i ≤ FaceHi (![1, 2, 3, 4, 5, 6, 8] : Fin 7 → ℤ) i) →
        g 1 / g 5 < (25 : ℝ) / 63) := by
  refine not_forced_demand (hn := by decide) (x := 1) (y := 5) (A := 25) (B := 63)
    (by decide) (by decide) ?_
  have h5 : (![1, 2, 3, 4, 5, 6, 8] : Fin 7 → ℤ) 5 = 6 := by simp
  have h1 : (![1, 2, 3, 4, 5, 6, 8] : Fin 7 → ℤ) 1 = 2 := by simp
  rw [h5, h1]
  norm_num

#print axioms demand_not_forced_12568

/-- Rule 22 (ii), cap side: the top `c-raw` cap `ρ₆/ρ₂ ≤ 17/7` is not forced by the box
interval — the face witness has `ρ₆/ρ₂ = FaceLo 2/FaceHi 6` inverse at `(13/2)/(3/2) = 13/3
> 17/7` (`17·3 = 51 < 91 = 7·13`). -/
theorem cap_not_forced_12568 :
    ¬ (∀ g : Fin 7 → ℝ, (∀ i, FaceLo (![1, 2, 3, 4, 5, 6, 8] : Fin 7 → ℤ) i ≤ g i ∧
          g i ≤ FaceHi (![1, 2, 3, 4, 5, 6, 8] : Fin 7 → ℤ) i) →
        g 5 / g 1 ≤ (17 : ℝ) / 7) := by
  refine not_forced_cap (hn := by decide) (x := 1) (y := 5) (C := 17) (D := 7)
    (by decide) (by decide) ?_
  have h5 : (![1, 2, 3, 4, 5, 6, 8] : Fin 7 → ℤ) 5 = 6 := by simp
  have h1 : (![1, 2, 3, 4, 5, 6, 8] : Fin 7 → ℤ) 1 = 2 := by simp
  rw [h5, h1]
  norm_num

#print axioms cap_not_forced_12568

/-! ### Box (1,3,4,5,5,6,8) -/

/-- The `c-raw` family of `j2_cycle_v12.out` BOX (1,3,4,5,5,6,8): word-edge readings (5,3),
demand `ρ₅/ρ₃ < 49/39`, chain cap `ρ₃/ρ₅ ≤ 17/23`. -/
def fam134556_8 : Finset JoinEdge := {⟨4, 2, 49, 39, 17, 23⟩}

/-- The discharged engine hypotheses for box (1,3,4,5,5,6,8) (conflict `49·17 = 833 ≤
897 = 39·23`; numerators `49, 17 ≡ 1 mod 8`). -/
theorem spineFamData_134556_8 :
    InRange17 (![1, 3, 4, 5, 5, 6, 8] : Fin 7 → ℤ) ∧
      JoinFam (![1, 3, 4, 5, 5, 6, 8] : Fin 7 → ℤ) fam134556_8 := by
  refine ⟨by decide, ?_⟩
  intro e
  obtain ⟨e, he⟩ := e
  simp only [fam134556_8, Finset.mem_singleton] at he
  subst he
  exact ⟨by norm_num, by norm_num, by norm_num, Or.inl (by norm_num), Or.inl (by norm_num)⟩

#print axioms spineFamData_134556_8

/-- Rule 22 (ii), demand side: `ρ₅/ρ₃ < 49/39` not interval-forced (`49·7 = 343 ≤
429 = 39·11`). -/
theorem demand_not_forced_134556_8 :
    ¬ (∀ g : Fin 7 → ℝ, (∀ i, FaceLo (![1, 3, 4, 5, 5, 6, 8] : Fin 7 → ℤ) i ≤ g i ∧
          g i ≤ FaceHi (![1, 3, 4, 5, 5, 6, 8] : Fin 7 → ℤ) i) →
        g 4 / g 2 < (49 : ℝ) / 39) := by
  refine not_forced_demand (hn := by decide) (x := 4) (y := 2) (A := 49) (B := 39)
    (by decide) (by decide) ?_
  have h4 : (![1, 3, 4, 5, 5, 6, 8] : Fin 7 → ℤ) 4 = 5 := by simp
  have h2 : (![1, 3, 4, 5, 5, 6, 8] : Fin 7 → ℤ) 2 = 4 := by simp
  rw [h4, h2]
  norm_num

#print axioms demand_not_forced_134556_8

/-- Rule 22 (ii), cap side: `ρ₃/ρ₅ ≤ 17/23` not interval-forced (`17·9 = 153 < 207 = 23·9`). -/
theorem cap_not_forced_134556_8 :
    ¬ (∀ g : Fin 7 → ℝ, (∀ i, FaceLo (![1, 3, 4, 5, 5, 6, 8] : Fin 7 → ℤ) i ≤ g i ∧
          g i ≤ FaceHi (![1, 3, 4, 5, 5, 6, 8] : Fin 7 → ℤ) i) →
        g 2 / g 4 ≤ (17 : ℝ) / 23) := by
  refine not_forced_cap (hn := by decide) (x := 4) (y := 2) (C := 17) (D := 23)
    (by decide) (by decide) ?_
  have h4 : (![1, 3, 4, 5, 5, 6, 8] : Fin 7 → ℤ) 4 = 5 := by simp
  have h2 : (![1, 3, 4, 5, 5, 6, 8] : Fin 7 → ℤ) 2 = 4 := by simp
  rw [h4, h2]
  norm_num

#print axioms cap_not_forced_134556_8

/-! ### Box (1,3,4,4,5,6,7) -/

/-- The `c-raw` family of `j2_cycle_v12.out` BOX (1,3,4,4,5,6,7): word-edge readings (5,3)
and (7,2), demands `49/39` resp. `73/31`, chain caps `17/23` resp. `17/47`. -/
def fam134456_7 : Finset JoinEdge := {⟨4, 2, 49, 39, 17, 23⟩, ⟨6, 1, 73, 31, 17, 47⟩}

/-- The discharged engine hypotheses for box (1,3,4,4,5,6,7) (conflicts `833 ≤ 897` and
`73·17 = 1241 ≤ 1457 = 31·47`; numerators `49, 73, 17 ≡ 1 mod 8`). -/
theorem spineFamData_134456_7 :
    InRange17 (![1, 3, 4, 4, 5, 6, 7] : Fin 7 → ℤ) ∧
      JoinFam (![1, 3, 4, 4, 5, 6, 7] : Fin 7 → ℤ) fam134456_7 := by
  refine ⟨by decide, ?_⟩
  intro e
  obtain ⟨e, he⟩ := e
  simp only [fam134456_7, Finset.mem_insert, Finset.mem_singleton] at he
  rcases he with rfl | rfl
  · exact ⟨by norm_num, by norm_num, by norm_num, Or.inl (by norm_num), Or.inl (by norm_num)⟩
  · exact ⟨by norm_num, by norm_num, by norm_num, Or.inl (by norm_num), Or.inl (by norm_num)⟩

#print axioms spineFamData_134456_7

/-- Rule 22 (ii), demand side: `ρ₇/ρ₂ < 73/31` not interval-forced (`73·5 = 365 ≤
465 = 31·15`). -/
theorem demand_not_forced_134456_7 :
    ¬ (∀ g : Fin 7 → ℝ, (∀ i, FaceLo (![1, 3, 4, 4, 5, 6, 7] : Fin 7 → ℤ) i ≤ g i ∧
          g i ≤ FaceHi (![1, 3, 4, 4, 5, 6, 7] : Fin 7 → ℤ) i) →
        g 6 / g 1 < (73 : ℝ) / 31) := by
  refine not_forced_demand (hn := by decide) (x := 6) (y := 1) (A := 73) (B := 31)
    (by decide) (by decide) ?_
  have h6 : (![1, 3, 4, 4, 5, 6, 7] : Fin 7 → ℤ) 6 = 7 := by simp
  have h1 : (![1, 3, 4, 4, 5, 6, 7] : Fin 7 → ℤ) 1 = 3 := by simp
  rw [h6, h1]
  norm_num

#print axioms demand_not_forced_134456_7

/-- Rule 22 (ii), cap side: `ρ₂/ρ₇ ≤ 17/47` not interval-forced (`17·13 = 221 < 329 = 47·7`). -/
theorem cap_not_forced_134456_7 :
    ¬ (∀ g : Fin 7 → ℝ, (∀ i, FaceLo (![1, 3, 4, 4, 5, 6, 7] : Fin 7 → ℤ) i ≤ g i ∧
          g i ≤ FaceHi (![1, 3, 4, 4, 5, 6, 7] : Fin 7 → ℤ) i) →
        g 1 / g 6 ≤ (17 : ℝ) / 47) := by
  refine not_forced_cap (hn := by decide) (x := 6) (y := 1) (C := 17) (D := 47)
    (by decide) (by decide) ?_
  have h6 : (![1, 3, 4, 4, 5, 6, 7] : Fin 7 → ℤ) 6 = 7 := by simp
  have h1 : (![1, 3, 4, 4, 5, 6, 7] : Fin 7 → ℤ) 1 = 3 := by simp
  rw [h6, h1]
  norm_num

#print axioms cap_not_forced_134456_7

/-! ### Box (1,3,4,5,6,7,8) -/

/-- The `c-raw` family of `j2_cycle_v12.out` BOX (1,3,4,5,6,7,8): word-edge readings (7,3),
demand `ρ₇/ρ₃ < 97/49`, chain cap `ρ₃/ρ₇ ≤ 17/39`. -/
def fam134567_8 : Finset JoinEdge := {⟨6, 2, 97, 49, 17, 39⟩}

/-- The discharged engine hypotheses for box (1,3,4,5,6,7,8) (conflict `97·17 = 1649 ≤
1911 = 49·39`; numerators `97, 17 ≡ 1 mod 8`). -/
theorem spineFamData_134567_8 :
    InRange17 (![1, 3, 4, 5, 6, 7, 8] : Fin 7 → ℤ) ∧
      JoinFam (![1, 3, 4, 5, 6, 7, 8] : Fin 7 → ℤ) fam134567_8 := by
  refine ⟨by decide, ?_⟩
  intro e
  obtain ⟨e, he⟩ := e
  simp only [fam134567_8, Finset.mem_singleton] at he
  subst he
  exact ⟨by norm_num, by norm_num, by norm_num, Or.inl (by norm_num), Or.inl (by norm_num)⟩

#print axioms spineFamData_134567_8

/-- Rule 22 (ii), demand side: `ρ₇/ρ₃ < 97/49` not interval-forced (`97·7 = 679 ≤
833 = 49·17`). -/
theorem demand_not_forced_134567_8 :
    ¬ (∀ g : Fin 7 → ℝ, (∀ i, FaceLo (![1, 3, 4, 5, 6, 7, 8] : Fin 7 → ℤ) i ≤ g i ∧
          g i ≤ FaceHi (![1, 3, 4, 5, 6, 7, 8] : Fin 7 → ℤ) i) →
        g 6 / g 2 < (97 : ℝ) / 49) := by
  refine not_forced_demand (hn := by decide) (x := 6) (y := 2) (A := 97) (B := 49)
    (by decide) (by decide) ?_
  have h6 : (![1, 3, 4, 5, 6, 7, 8] : Fin 7 → ℤ) 6 = 8 := by simp
  have h2 : (![1, 3, 4, 5, 6, 7, 8] : Fin 7 → ℤ) 2 = 4 := by simp
  rw [h6, h2]
  norm_num

#print axioms demand_not_forced_134567_8

/-- Rule 22 (ii), cap side: `ρ₃/ρ₇ ≤ 17/39` not interval-forced (`17·15 = 255 < 351 = 39·9`). -/
theorem cap_not_forced_134567_8 :
    ¬ (∀ g : Fin 7 → ℝ, (∀ i, FaceLo (![1, 3, 4, 5, 6, 7, 8] : Fin 7 → ℤ) i ≤ g i ∧
          g i ≤ FaceHi (![1, 3, 4, 5, 6, 7, 8] : Fin 7 → ℤ) i) →
        g 2 / g 6 ≤ (17 : ℝ) / 39) := by
  refine not_forced_cap (hn := by decide) (x := 6) (y := 2) (C := 17) (D := 39)
    (by decide) (by decide) ?_
  have h6 : (![1, 3, 4, 5, 6, 7, 8] : Fin 7 → ℤ) 6 = 8 := by simp
  have h2 : (![1, 3, 4, 5, 6, 7, 8] : Fin 7 → ℤ) 2 = 4 := by simp
  rw [h6, h2]
  norm_num

#print axioms cap_not_forced_134567_8

/-! ### Box (1,2,3,4,5,6,7) -/

/-- The `c-raw` family of `j2_cycle_v12.out` BOX (1,2,3,4,5,6,7): word-edge readings (2,7),
demand `ρ₂/ρ₇ < 33/103`, chain cap `ρ₇/ρ₂ ≤ 49/17`. -/
def fam123456_7 : Finset JoinEdge := {⟨1, 6, 33, 103, 49, 17⟩}

/-- The discharged engine hypotheses for box (1,2,3,4,5,6,7) (conflict `33·49 = 1617 ≤
1751 = 103·17`; numerators `33, 49, 17 ≡ 1 mod 8`). -/
theorem spineFamData_123456_7 :
    InRange17 (![1, 2, 3, 4, 5, 6, 7] : Fin 7 → ℤ) ∧
      JoinFam (![1, 2, 3, 4, 5, 6, 7] : Fin 7 → ℤ) fam123456_7 := by
  refine ⟨by decide, ?_⟩
  intro e
  obtain ⟨e, he⟩ := e
  simp only [fam123456_7, Finset.mem_singleton] at he
  subst he
  exact ⟨by norm_num, by norm_num, by norm_num, Or.inl (by norm_num), Or.inl (by norm_num)⟩

#print axioms spineFamData_123456_7

/-- Rule 22 (ii), demand side: `ρ₂/ρ₇ < 33/103` not interval-forced (`33·13 = 429 ≤
515 = 103·5`). -/
theorem demand_not_forced_123456_7 :
    ¬ (∀ g : Fin 7 → ℝ, (∀ i, FaceLo (![1, 2, 3, 4, 5, 6, 7] : Fin 7 → ℤ) i ≤ g i ∧
          g i ≤ FaceHi (![1, 2, 3, 4, 5, 6, 7] : Fin 7 → ℤ) i) →
        g 1 / g 6 < (33 : ℝ) / 103) := by
  refine not_forced_demand (hn := by decide) (x := 1) (y := 6) (A := 33) (B := 103)
    (by decide) (by decide) ?_
  have h6 : (![1, 2, 3, 4, 5, 6, 7] : Fin 7 → ℤ) 6 = 7 := by simp
  have h1 : (![1, 2, 3, 4, 5, 6, 7] : Fin 7 → ℤ) 1 = 2 := by simp
  rw [h6, h1]
  norm_num

#print axioms demand_not_forced_123456_7

/-- Rule 22 (ii), cap side: `ρ₇/ρ₂ ≤ 49/17` not interval-forced (`49·3 = 147 < 255 = 17·15`). -/
theorem cap_not_forced_123456_7 :
    ¬ (∀ g : Fin 7 → ℝ, (∀ i, FaceLo (![1, 2, 3, 4, 5, 6, 7] : Fin 7 → ℤ) i ≤ g i ∧
          g i ≤ FaceHi (![1, 2, 3, 4, 5, 6, 7] : Fin 7 → ℤ) i) →
        g 6 / g 1 ≤ (49 : ℝ) / 17) := by
  refine not_forced_cap (hn := by decide) (x := 1) (y := 6) (C := 49) (D := 17)
    (by decide) (by decide) ?_
  have h6 : (![1, 2, 3, 4, 5, 6, 7] : Fin 7 → ℤ) 6 = 7 := by simp
  have h1 : (![1, 2, 3, 4, 5, 6, 7] : Fin 7 → ℤ) 1 = 2 := by simp
  rw [h6, h1]
  norm_num

#print axioms cap_not_forced_123456_7

/-! ## 5. Rule-22 record: the two-sided boxes and the 68 one-sided boxes

All five two-sided boxes resisted the prescribed technique identically, and the resistance
is now PROVED, not parked (fields (i)-(iii) per rule 22):

(i) **Feature that sets them apart**: none — the failure is family-independent.  The
`SpineTotal*` conclusions are ratio statements about the realized readings; the artifact's
`c-raw` demands/caps are tight comb ratios (`8m±1` over zone bounds), strictly tighter than
the `±1/2` face slack (each box's `demand_not_forced_*` / `cap_not_forced_*` exhibits an
in-box arrangement at the faces violating both sides of its top edge).

(ii) **What forces the failure** (named artifacts): `capDerivedDemand_unsat`,
`intervalForcedDemand_capUnsat`, `intervalForcedPair_invalid` above.  The conflict datum
`A·C ≤ B·D` is exactly what forbids the interval route: an interval-forced demand makes the
chain-cap hypothesis unsatisfiable (empty one-sided kill); both sides interval-forced
contradict the datum; and a demand derived from the family caps alone does the same.
Hence `spineTotalPairwise_*` / `spineTotalOneSided_*` CANNOT be produced by the
FaceLo/FaceHi-integer reduction; they must come from the carve / no-clear-point hypotheses.

(iii) **Same mechanism or different**: the SAME mechanism for all five two-sided boxes and
for all 68 one-sided boxes (one shared gap, not per-box).  The 68 one-sided boxes have the
ADDITIONAL data-side gap that `j2_cycle_v6.out` records its families only as aggregates
over boxes (`(kind, rank_i, rank_j, back, attribution)` with unreduced `(P,Q)` demands,
62208 rows), so no per-box `JoinEdge` family can be read off the `.out` as-is; a rerun of
`j2_cycle_v6.py` with a per-box dump (to a NEW file) would be needed to state
`spineTotalOneSided_<box>` "with its family from the artifact" at all — and by (ii) it
would still face the same non-interval-reducible totality.  Note also that the v6
`J`/`derived` cap numerators are not all `8m±1 mod 8` (e.g. `9163/7285`, `155771/109275`),
so a `JoinFam`-valid subfamily selection would be part of that dump.

The two directions that WOULD discharge the totality (both named OWED in
`Fresh.SpineSound`, neither present in Fresh today): (a) carve ⟹ the `W₀` chain caps are
realized on `g` (the reading-side validity direction of `JoinFam`); (b) no `W₁` clear point
⟹ some family word demand is realized on `g` (the `W₁`-word realization — the finite
closed-interval covering argument recorded as missing in
`Fresh.FrontierFamilyCap.FrontierCarveCap`'s docstring).  With (a)+(b) per box, the
artifact's verified raw-kill law lifts through `Fresh.SpineSound.famRefutes` and the
`spineTotal*` instances close. -/

end Fresh.SpineTotalData
