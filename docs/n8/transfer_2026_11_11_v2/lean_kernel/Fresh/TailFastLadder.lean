import Mathlib
import Fresh.TailFast

/-!
# The fast-top cell step at every threshold (2026-11-09)

New file; nothing existing is edited.  Generalises `Fresh.TailFast.fast_cell_clear` from the step
`1/7 → 1/8` to every step `1/k → 1/(k+1)`, `k ≥ 2`.

**Objects.**  `θ = R/8`.  `ClearInRange k S`: some `θ` in reading 1's `1/k`-range of `W₀` or `W₁`,
`[1/k, (k−1)/k] ∪ [1 + 1/k, 2 − 1/k]`, at which every reading of `S` is `1/k`-clear.
`NStarK k`: every set of at most `k − 1` readings, all at least 1 and containing 1, satisfies
`ClearInRange k`.  `NStarK 7` is `Fresh.TailFast.NStarAtMostOne` (`nStarK_seven_iff`).

**The ranges nest exactly.**  The cell half-width is at most `1/(k(k+1))`, and
`1/k − 1/(k(k+1)) = 1/(k+1)`, `(k−1)/k + 1/(k(k+1)) = k/(k+1)`: the `1/k`-range widened by the
cell is the `1/(k+1)`-range.  So the step keeps the landing in `W₀ ∪ W₁` at every level.

**Results [L].**
* `cell_step`: slow set `S ∋ 1` with `ClearInRange k S`, a fast reading `V > k·s` for every
  `s ∈ S`, give `ClearInRange (k+1) (insert V S)`.  Frame step (rule 1, displacement): the slow
  set's `1/k`-clear instant is displaced by at most the cell half-width, to the fast reading's next
  opening.  [PROVISIONAL: covering] at the slow step (the `1/k − 1/(k+1)` margin, supporting "the
  slow readings stay clear across the cell") and at `hVδ` (the fast reading's blocked arc
  `2/(k+1)` against the cell length, supporting "the fast reading is clear somewhere in the cell").
* `nStarK_succ_fast`: `NStarK k` gives `ClearInRange (k+1) S` for every admissible `S` of at most
  `k` readings whose largest reading exceeds `k` times every other.
* `nStarAtMostOne_fast_of_nStarK_six`: the fast-top part of `NStarAtMostOne` (`ρ₆ > 6ρ₅`) from
  `NStarK 6`, the five-reading statement at `1/6`.
-/

open Classical

namespace Fresh.TailFastLadder

open Fresh Fresh.TailFast

/-- The `1/k`-range of reading 1 in `W₀ ∪ W₁`, in `θ = R/8`. -/
-- STANDING: DEFINITION
def InRangeK (k θ : ℝ) : Prop :=
  (1 / k ≤ θ ∧ θ ≤ (k - 1) / k) ∨ (1 + 1 / k ≤ θ ∧ θ ≤ 2 - 1 / k)

-- STANDING: DEFINITION
def ClearInRange (k : ℝ) (S : Finset ℝ) : Prop :=
  ∃ θ : ℝ, InRangeK k θ ∧ ∀ s ∈ S, 1 / k ≤ distInt (s * θ)

/-- **OWED at each level** (`k = 7` is `NStarAtMostOne`). -/
-- STANDING: OWED
def NStarK (k : ℕ) : Prop :=
  ∀ S : Finset ℝ, (1 : ℝ) ∈ S → (∀ s ∈ S, 1 ≤ s) → S.card ≤ k - 1 → ClearInRange k S

theorem dI_int_add_small (K : ℤ) {c : ℝ} (h0 : 0 ≤ c) (h1 : c < 1 / 2) :
    distInt ((K : ℝ) + c) = c := by
  unfold distInt
  have hr : round ((K : ℝ) + c) = K := by
    rw [round_eq, Int.floor_eq_iff]; constructor <;> linarith
  rw [hr]; simp [abs_of_nonneg h0]

#print axioms dI_int_add_small

/-- **The cell step `1/k → 1/(k+1)`.** -/
theorem cell_step {k : ℝ} (hk : 2 ≤ k) {S : Finset ℝ} (hS1 : (1 : ℝ) ∈ S)
    (hpos : ∀ s ∈ S, 0 < s) {V : ℝ} (hV : ∀ s ∈ S, k * s < V) (hcl : ClearInRange k S) :
    ClearInRange (k + 1) (insert V S) := by
  obtain ⟨θ, hθ, hclr⟩ := hcl
  have hk0 : 0 < k := by linarith
  have hne : S.Nonempty := ⟨1, hS1⟩
  set M := S.max' hne with hM
  have hMS : M ∈ S := S.max'_mem hne
  have hM1 : (1 : ℝ) ≤ M := S.le_max' 1 hS1
  have hM0 : 0 < M := by linarith
  have hle : ∀ s ∈ S, s ≤ M := fun s hs => S.le_max' s hs
  have hVk : k * M < V := hV M hMS
  have hV0 : 0 < V := by nlinarith
  set δ : ℝ := 1 / (k * (k + 1) * M) with hδ
  have hδ0 : 0 < δ := by positivity
  have hδle : δ ≤ 1 / (k * (k + 1)) := by
    have hkk1 : 0 < k * (k + 1) := by positivity
    rw [hδ, div_le_div_iff₀ (by positivity) hkk1]
    nlinarith [mul_le_mul_of_nonneg_left hM1 hkk1.le]
  have hMδ : M * δ = 1 / k - 1 / (k + 1) := by rw [hδ]; field_simp; ring
  have e1 : 1 / k - 1 / (k * (k + 1)) = 1 / (k + 1) := by field_simp; ring
  have e2 : (k - 1) / k + 1 / (k * (k + 1)) = (k + 1 - 1) / (k + 1) := by field_simp; ring
  have e3 : 1 + 1 / k - 1 / (k * (k + 1)) = 1 + 1 / (k + 1) := by field_simp; ring
  have e4 : 2 - 1 / k + 1 / (k * (k + 1)) = 2 - 1 / (k + 1) := by field_simp; ring
  -- [PROVISIONAL: covering] the slow readings stay clear across the cell (the 1/k − 1/(k+1) margin)
  have hslow : ∀ x, |x - θ| ≤ δ → ∀ s ∈ S, 1 / (k + 1) ≤ distInt (s * x) := by
    intro x hx s hs
    have hs0 := hpos s hs
    have h1 := dI_le (s * θ) (s * x)
    have h2 : |s * θ - s * x| ≤ M * δ := by
      rw [← mul_sub, abs_mul, abs_of_pos hs0, abs_sub_comm]
      exact mul_le_mul (hle s hs) hx (abs_nonneg _) hM0.le
    have h3 := hclr s hs
    linarith
  have hwin : ∀ x, |x - θ| ≤ δ → InRangeK (k + 1) x := by
    intro x hx
    have hx' := abs_le.mp hx
    rcases hθ with ⟨a, b⟩ | ⟨a, b⟩
    · left; constructor <;> linarith [hx'.1, hx'.2]
    · right; constructor <;> linarith [hx'.1, hx'.2]
  have hk1 : 1 / (k + 1) < 1 / 2 := by
    rw [div_lt_div_iff₀ (by linarith) (by norm_num)]; linarith
  have hk1' : 0 ≤ 1 / (k + 1) := by positivity
  by_cases hc : 1 / (k + 1) ≤ distInt (V * (θ - δ))
  · have hx : |θ - δ - θ| ≤ δ := by
      rw [show θ - δ - θ = -δ by ring, abs_neg, abs_of_pos hδ0]
    refine ⟨θ - δ, hwin _ hx, fun d hd => ?_⟩
    rcases Finset.mem_insert.mp hd with rfl | hdS
    · exact hc
    · exact hslow _ hx d hdS
  · push_neg at hc
    set K := round (V * (θ - δ)) with hK
    have hc' : |V * (θ - δ) - (K : ℝ)| < 1 / (k + 1) := hc
    have hkk := abs_lt.mp hc'
    set x := ((K : ℝ) + 1 / (k + 1)) / V with hx
    have hVx : V * x = (K : ℝ) + 1 / (k + 1) := by rw [hx]; field_simp
    have hlo : θ - δ < x := by
      rw [hx, lt_div_iff₀ hV0]; linarith [hkk.2]
    -- [PROVISIONAL: covering] the fast reading's blocked arc 2/(k+1) against the cell length 2δ
    have hVδ : 2 / (k + 1) < V * (2 * δ) := by
      rw [hδ, show V * (2 * (1 / (k * (k + 1) * M))) = 2 * V / (k * (k + 1) * M) by
        field_simp]
      rw [div_lt_div_iff₀ (by linarith) (by positivity)]; nlinarith
    have hhi : x ≤ θ + δ := by
      have e : V * (θ - δ) + V * (2 * δ) = (θ + δ) * V := by ring
      have e2 : (2 : ℝ) / (k + 1) = 1 / (k + 1) + 1 / (k + 1) := by ring
      have h1 : (K : ℝ) + 1 / (k + 1) < V * (θ - δ) + 2 / (k + 1) := by
        rw [e2]; linarith [hkk.1]
      rw [hx, div_le_iff₀ hV0]
      calc (K : ℝ) + 1 / (k + 1) ≤ V * (θ - δ) + 2 / (k + 1) := h1.le
        _ ≤ V * (θ - δ) + V * (2 * δ) := by linarith [hVδ]
        _ = (θ + δ) * V := e
    have hxa : |x - θ| ≤ δ := by rw [abs_le]; constructor <;> linarith
    refine ⟨x, hwin _ hxa, fun d hd => ?_⟩
    rcases Finset.mem_insert.mp hd with rfl | hdS
    · rw [hVx, dI_int_add_small K hk1' hk1]
    · exact hslow _ hxa d hdS

#print axioms cell_step

theorem dI_half : distInt (1 / 2 : ℝ) = 1 / 2 := by
  unfold distInt
  have hr : round (1 / 2 : ℝ) = 1 := by
    rw [round_eq, Int.floor_eq_iff]; norm_num
  rw [hr]; norm_num

#print axioms dI_half

/-- `NStarK k` handles every admissible set of at most `k` readings with a fast top at level
`k + 1`. -/
theorem nStarK_succ_fast {k : ℕ} (hk : 2 ≤ k) (hN : NStarK k) {S : Finset ℝ} (hS1 : (1 : ℝ) ∈ S)
    (hge : ∀ s ∈ S, 1 ≤ s) (hcard : S.card ≤ k) {V : ℝ} (hVS : V ∈ S)
    (hfast : ∀ s ∈ S, s ≠ V → (k : ℝ) * s < V) :
    ClearInRange ((k : ℝ) + 1) S := by
  have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk
  by_cases hV1 : V = 1
  · -- every other reading would be below 1/k: S = {1}
    have hS : ∀ s ∈ S, s = 1 := by
      intro s hs
      by_contra hne
      have h1 := hfast s hs (by rw [hV1]; exact hne)
      have h2 := hge s hs
      rw [hV1] at h1; nlinarith
    refine ⟨1 / 2, Or.inl ⟨?_, ?_⟩, fun s hs => ?_⟩
    · rw [div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
    · rw [div_le_div_iff₀ (by norm_num) (by linarith)]; linarith
    · rw [hS s hs, one_mul, dI_half, div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
  · set T := S.erase V with hT
    have hT1 : (1 : ℝ) ∈ T := Finset.mem_erase.mpr ⟨fun h => hV1 h.symm, hS1⟩
    have hTge : ∀ s ∈ T, 1 ≤ s := fun s hs => hge s (Finset.mem_of_mem_erase hs)
    have hTcard : T.card ≤ k - 1 := by
      rw [hT, Finset.card_erase_of_mem hVS]; omega
    have hTcl := hN T hT1 hTge hTcard
    have hTpos : ∀ s ∈ T, 0 < s := fun s hs => by linarith [hTge s hs]
    have hTV : ∀ s ∈ T, (k : ℝ) * s < V := fun s hs =>
      hfast s (Finset.mem_of_mem_erase hs) (Finset.ne_of_mem_erase hs)
    have h := cell_step hk' hT1 hTpos hTV hTcl
    rwa [hT, Finset.insert_erase hVS] at h

#print axioms nStarK_succ_fast

theorem inRangeK_seven (θ : ℝ) :
    InRangeK ((7 : ℕ) : ℝ) θ ↔ ((1 / 7 ≤ θ ∧ θ ≤ 6 / 7) ∨ (8 / 7 ≤ θ ∧ θ ≤ 13 / 7)) := by
  unfold InRangeK; norm_num

/-- `NStarK 7` is `NStarAtMostOne`. -/
theorem nStarK_seven_iff : NStarK 7 ↔ NStarAtMostOne := by
  constructor
  · intro h S h1 hge hc
    obtain ⟨θ, hθ, hcl⟩ := h S h1 hge (by omega)
    refine ⟨θ, (inRangeK_seven θ).mp hθ, fun s hs => ?_⟩
    have := hcl s hs; norm_num at this ⊢; exact this
  · intro h S h1 hge hc
    obtain ⟨θ, hθ, hcl⟩ := h S h1 hge (by omega)
    refine ⟨θ, (inRangeK_seven θ).mpr hθ, fun s hs => ?_⟩
    have := hcl s hs; norm_num at this ⊢; exact this

#print axioms nStarK_seven_iff

/-- **The fast-top part of `NStarAtMostOne` (`ρ₆` above 6 times every other reading) from
`NStarK 6`, the five-reading statement at `1/6`.** -/
theorem nStarAtMostOne_fast_of_nStarK_six (hN6 : NStarK 6) {S : Finset ℝ} (hS1 : (1 : ℝ) ∈ S)
    (hge : ∀ s ∈ S, 1 ≤ s) (hcard : S.card ≤ 6) {V : ℝ} (hVS : V ∈ S)
    (hfast : ∀ s ∈ S, s ≠ V → 6 * s < V) :
    ∃ θ : ℝ, ((1 / 7 ≤ θ ∧ θ ≤ 6 / 7) ∨ (8 / 7 ≤ θ ∧ θ ≤ 13 / 7)) ∧
      ∀ s ∈ S, (1 / 7 : ℝ) ≤ distInt (s * θ) := by
  have h := nStarK_succ_fast (k := 6) (by norm_num) hN6 hS1 hge hcard hVS
    (fun s hs hne => by have := hfast s hs hne; push_cast; linarith)
  obtain ⟨θ, hθ, hcl⟩ := h
  refine ⟨θ, ?_, fun s hs => ?_⟩
  · have : InRangeK ((7 : ℕ) : ℝ) θ := by
      have e : ((6 : ℕ) : ℝ) + 1 = ((7 : ℕ) : ℝ) := by norm_num
      rw [← e]; exact hθ
    exact (inRangeK_seven θ).mp this
  · have := hcl s hs; norm_num at this ⊢; exact this

#print axioms nStarAtMostOne_fast_of_nStarK_six

end Fresh.TailFastLadder
