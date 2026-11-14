import Mathlib
import Fresh.FilterAssembly

/-!
# The tail with a fast top reading (2026-11-09)

New file; nothing existing is edited.

**Source.** R8 (`Fresh/Nv_FastRunnerN.lean`, `lonely_of_fast_runner`, ported from the native
`LRC/Spec/FastRunnerN.lean`): if the slow readings are clear at `1/(n−1)` at an instant `τ` and the
fast reading exceeds `(n−1)` times each slow one, the lonely instant is `τ − δ` or an opening of the
fast runner inside `[τ − δ, τ + δ]`.  The statement there exposes only existence; the proof places
the instant in the cell.  This file re-proves the cell form in the framework's `distInt` and
feeds it to `cascadeLandsBelow17_of_clearPoint`.

**What it gives.**  With readings normalised by `d_min` (`R` the instant in units of the slowest
reading's lap, `θ = R/8`):
* `fast_cell_clear` [L]: slow set `S ∋ 1`, fast `V > 7 s` for every `s ∈ S`, and `θ` with every slow
  reading `1/7`-clear, `θ ∈ [1/7, 6/7] ∪ [8/7, 13/7]` (that is, `R` in the `1/7`-range of reading 1 in
  `W₀` or `W₁`).  Then some `x` within `1/56` of `θ` has every reading, fast and slow, `1/8`-clear,
  and `8x ∈ [1,7] ∪ [9,15]`.
* `cascadeLandsBelow17_of_fast` [L]: for an arrangement whose largest normalised disparity is more
  than 7 times every other, a `1/7`-clear instant of the other six normalised readings in
  `W₀ ∪ W₁` makes the cascade land below 17.
* `tailFast_of_nstar` [L]: the part of `TailBelow17` with a fast top reading follows from
  `NStarAtMostOne`, the statement that six readings `1 = ρ₁ ≤ … ≤ ρ₆` always have a `1/7`-clear
  instant in `W₀ ∪ W₁`.

`NStarAtMostOne` is OWED.  Its record: no six with `ρ₆ ≤ 32` violates it
[T, `experiments/n8/nstar_two_decision_v1.out`, exhaustive negative-cycle search;
PROVISIONAL: covering, open cover ⇔ no clear instant; PROVISIONAL: counting tool, finite chain
list].  It is a statement about six readings at the threshold `1/7`, the object of order seven.
-/

open Classical

namespace Fresh.TailFast

open Fresh Fresh.Cascade Fresh.KTaxonomy Fresh.Certs Fresh.FilterSkeleton
open Fresh.FrontierFamilyCap Fresh.FilterAssembly

/-- `distInt` moves by at most the distance moved. -/
theorem dI_le (x y : ℝ) : distInt x ≤ distInt y + |x - y| := by
  unfold distInt
  have h := round_le x (round y)
  calc |x - (round x : ℝ)| ≤ |x - (round y : ℝ)| := h
    _ = |(x - y) + (y - (round y : ℝ))| := by ring_nf
    _ ≤ |x - y| + |y - (round y : ℝ)| := abs_add_le _ _
    _ = |y - (round y : ℝ)| + |x - y| := by ring

theorem dI_int_add_eighth (K : ℤ) : distInt ((K : ℝ) + 1 / 8) = 1 / 8 := by
  unfold distInt
  have hr : round ((K : ℝ) + 1 / 8) = K := by
    rw [round_eq, Int.floor_eq_iff]; constructor <;> push_cast <;> linarith
  rw [hr]; norm_num

#print axioms dI_le
#print axioms dI_int_add_eighth

/-- **The fast cell (R8 in cell form, at order eight).**  Frame step (rule 1, displacement): the
six slower readings' `1/7`-clear instant is displaced by the fast reading by at most the cell
half-width `δ ≤ 1/56`, to the fast reading's next opening.  [PROVISIONAL: covering] at `hVδ`:
the fast reading's blocked arc `1/4` against the cell length `2δ`, supporting "the fast reading is
clear somewhere in the cell".  The slow readings' step uses the `1/7 − 1/8 = 1/56` margin, a
bound with slack the AP does not have [PROVISIONAL: covering], supporting "the slow readings stay
clear across the cell". -/
theorem fast_cell_clear {S : Finset ℝ} (hS1 : (1 : ℝ) ∈ S) (hpos : ∀ s ∈ S, 0 < s)
    {V : ℝ} (hV : ∀ s ∈ S, 7 * s < V) {θ : ℝ}
    (hθ : (1 / 7 ≤ θ ∧ θ ≤ 6 / 7) ∨ (8 / 7 ≤ θ ∧ θ ≤ 13 / 7))
    (hclr : ∀ s ∈ S, (1 / 7 : ℝ) ≤ distInt (s * θ)) :
    ∃ x : ℝ, ((1 / 8 ≤ x ∧ x ≤ 7 / 8) ∨ (9 / 8 ≤ x ∧ x ≤ 15 / 8)) ∧
      (1 / 8 : ℝ) ≤ distInt (V * x) ∧ ∀ s ∈ S, (1 / 8 : ℝ) ≤ distInt (s * x) := by
  have hne : S.Nonempty := ⟨1, hS1⟩
  set M := S.max' hne with hM
  have hMS : M ∈ S := S.max'_mem hne
  have hM1 : (1 : ℝ) ≤ M := S.le_max' 1 hS1
  have hM0 : 0 < M := by linarith
  have hle : ∀ s ∈ S, s ≤ M := fun s hs => S.le_max' s hs
  have hV7 : 7 * M < V := hV M hMS
  have hV0 : 0 < V := by linarith
  set δ : ℝ := 1 / (56 * M) with hδ
  have hδ0 : 0 < δ := by positivity
  have hδ56 : δ ≤ 1 / 56 := by
    rw [hδ, div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  have hMδ : M * δ = 1 / 56 := by rw [hδ]; field_simp
  -- the slow readings stay clear on the cell
  have hslow : ∀ x, |x - θ| ≤ δ → ∀ s ∈ S, (1 / 8 : ℝ) ≤ distInt (s * x) := by
    intro x hx s hs
    have hs0 := hpos s hs
    have h1 := dI_le (s * θ) (s * x)
    have h2 : |s * θ - s * x| ≤ M * δ := by
      rw [← mul_sub, abs_mul, abs_of_pos hs0, abs_sub_comm]
      exact mul_le_mul (hle s hs) hx (abs_nonneg _) hM0.le
    have h3 := hclr s hs
    linarith
  -- the window: within 1/56 of θ
  have hwin : ∀ x, |x - θ| ≤ δ → ((1 / 8 ≤ x ∧ x ≤ 7 / 8) ∨ (9 / 8 ≤ x ∧ x ≤ 15 / 8)) := by
    intro x hx
    have hx' := abs_le.mp hx
    rcases hθ with ⟨a, b⟩ | ⟨a, b⟩
    · left; constructor <;> linarith [hx'.1, hx'.2]
    · right; constructor <;> linarith [hx'.1, hx'.2]
  by_cases hc : (1 / 8 : ℝ) ≤ distInt (V * (θ - δ))
  · have hx : |θ - δ - θ| ≤ δ := by
      rw [show θ - δ - θ = -δ by ring, abs_neg, abs_of_pos hδ0]
    exact ⟨θ - δ, hwin _ hx, hc, hslow _ hx⟩
  · push_neg at hc
    set K := round (V * (θ - δ)) with hK
    have hc' : |V * (θ - δ) - (K : ℝ)| < 1 / 8 := hc
    have hk := abs_lt.mp hc'
    set x := ((K : ℝ) + 1 / 8) / V with hx
    have hVx : V * x = (K : ℝ) + 1 / 8 := by rw [hx]; field_simp
    have hlo : θ - δ < x := by
      rw [hx, lt_div_iff₀ hV0]; linarith [hk.2]
    have hVδ : 1 / 4 < V * (2 * δ) := by
      rw [hδ]; rw [show V * (2 * (1 / (56 * M))) = V / (28 * M) by field_simp; ring]
      rw [lt_div_iff₀ (by positivity)]; linarith
    have hhi : x ≤ θ + δ := by
      rw [hx, div_le_iff₀ hV0]; nlinarith [hk.1]
    have hxa : |x - θ| ≤ δ := by rw [abs_le]; constructor <;> linarith
    refine ⟨x, hwin _ hxa, ?_, hslow _ hxa⟩
    rw [hVx, dI_int_add_eighth]

#print axioms fast_cell_clear

/-- **NStar at most one (OWED).**  Six readings `1 = ρ₁ ≤ … ≤ ρ₆` (as a finite set of positive reals
containing `1`, every member at least `1`, at most six members) have an instant `θ = R/8` in the
`1/7`-range of reading 1 in `W₀` or `W₁` at which every reading is `1/7`-clear. -/
-- STANDING: OWED
def NStarAtMostOne : Prop :=
  ∀ S : Finset ℝ, (1 : ℝ) ∈ S → (∀ s ∈ S, 1 ≤ s) → S.card ≤ 6 →
    ∃ θ : ℝ, ((1 / 7 ≤ θ ∧ θ ≤ 6 / 7) ∨ (8 / 7 ≤ θ ∧ θ ≤ 13 / 7)) ∧
      ∀ s ∈ S, (1 / 7 : ℝ) ≤ distInt (s * θ)

/-- An arrangement whose largest normalised disparity exceeds 7 times every other lands below 17,
given a `1/7`-clear instant of the other normalised readings in `W₀ ∪ W₁`. -/
theorem cascadeLandsBelow17_of_fast {v : Fin 8 → ℝ} {k : Fin 8} {m : ℝ}
    (hv : IsArrangement v) (hm : IsDmin v k m) {D : ℝ} (hD : D ∈ disparitySet v k) (hmlt : m < D)
    (hfast : ∀ d ∈ disparitySet v k, d ≠ D → 7 * d < D) {θ : ℝ}
    (hθ : (1 / 7 ≤ θ ∧ θ ≤ 6 / 7) ∨ (8 / 7 ≤ θ ∧ θ ≤ 13 / 7))
    (hclr : ∀ d ∈ disparitySet v k, d ≠ D → (1 / 7 : ℝ) ≤ distInt ((d / m) * θ)) :
    CascadeLandsBelow17 (disparitySet v k) m := by
  have hpos : ∀ d ∈ disparitySet v k, 0 < d := disparitySet_pos hv k
  have hm0 : 0 < m := hpos m hm.1
  have hmD : m ≠ D := hmlt.ne
  set S : Finset ℝ := ((disparitySet v k).erase D).image (fun d => d / m) with hS
  have hS1 : (1 : ℝ) ∈ S :=
    Finset.mem_image.mpr ⟨m, Finset.mem_erase.mpr ⟨hmD, hm.1⟩, div_self hm0.ne'⟩
  have hSpos : ∀ s ∈ S, 0 < s := by
    intro s hs
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hs
    exact div_pos (hpos d (Finset.mem_of_mem_erase hd)) hm0
  have hSV : ∀ s ∈ S, 7 * s < D / m := by
    intro s hs
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hs
    have := hfast d (Finset.mem_of_mem_erase hd) (Finset.ne_of_mem_erase hd)
    rw [← mul_div_assoc, div_lt_div_iff_of_pos_right hm0]; exact this
  have hSc : ∀ s ∈ S, (1 / 7 : ℝ) ≤ distInt (s * θ) := by
    intro s hs
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hs
    exact hclr d (Finset.mem_of_mem_erase hd) (Finset.ne_of_mem_erase hd)
  obtain ⟨x, hxw, hxV, hxS⟩ := fast_cell_clear hS1 hSpos hSV hθ hSc
  refine cascadeLandsBelow17_of_clearPoint hv hm (8 * x) ?_ ?_ ?_ ?_
  · rcases hxw with ⟨a, _⟩ | ⟨a, _⟩ <;> linarith
  · rcases hxw with ⟨_, b⟩ | ⟨_, b⟩ <;> linarith
  · rcases hxw with ⟨_, b⟩ | ⟨a, _⟩
    · left; linarith
    · right; linarith
  · intro d hd
    have he : (8 * x) / 8 = x := by ring
    rw [he]
    by_cases hdD : d = D
    · rw [hdD]; exact hxV
    · exact hxS (d / m) (Finset.mem_image.mpr ⟨d, Finset.mem_erase.mpr ⟨hdD, hd⟩, rfl⟩)

#print axioms cascadeLandsBelow17_of_fast

/-- **The fast part of the tail from `NStarAtMostOne`.**  Every arrangement with a normalised
disparity past 49 that is more than 7 times every other normalised disparity lands below 17. -/
theorem tailFast_of_nstar (hN : NStarAtMostOne) {v : Fin 8 → ℝ} (hv : IsArrangement v)
    {k : Fin 8} {m : ℝ} (hm : IsDmin v k m) {D : ℝ} (hD : D ∈ disparitySet v k)
    (h49 : 49 * m < D) (hfast : ∀ d ∈ disparitySet v k, d ≠ D → 7 * d < D) :
    CascadeLandsBelow17 (disparitySet v k) m := by
  have hpos : ∀ d ∈ disparitySet v k, 0 < d := disparitySet_pos hv k
  have hm0 : 0 < m := hpos m hm.1
  have hmlt : m < D := by linarith
  set S : Finset ℝ := ((disparitySet v k).erase D).image (fun d => d / m) with hS
  have hS1 : (1 : ℝ) ∈ S :=
    Finset.mem_image.mpr ⟨m, Finset.mem_erase.mpr ⟨hmlt.ne, hm.1⟩, div_self hm0.ne'⟩
  have hSge : ∀ s ∈ S, 1 ≤ s := by
    intro s hs
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hs
    rw [le_div_iff₀ hm0, one_mul]; exact hm.2 (Finset.mem_of_mem_erase hd)
  have hcard7 : (disparitySet v k).card ≤ 7 := by
    unfold disparitySet
    calc ((Finset.univ.erase k).image (fun i => |v i - v k|)).card
        ≤ (Finset.univ.erase k).card := Finset.card_image_le
      _ = 7 := by simp
  have hScard : S.card ≤ 6 := by
    calc S.card ≤ ((disparitySet v k).erase D).card := Finset.card_image_le
      _ = (disparitySet v k).card - 1 := Finset.card_erase_of_mem hD
      _ ≤ 6 := by omega
  obtain ⟨θ, hθ, hcl⟩ := hN S hS1 hSge hScard
  exact cascadeLandsBelow17_of_fast hv hm hD hmlt hfast hθ (fun d hd hdD =>
    hcl (d / m) (Finset.mem_image.mpr ⟨d, Finset.mem_erase.mpr ⟨hdD, hd⟩, rfl⟩))

#print axioms tailFast_of_nstar

end Fresh.TailFast
