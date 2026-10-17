import LonelyRunner.LRC.Spec.OrderSevenKappaN
import LonelyRunner.LRC.Spec.OrderSevenKappaTreeCoreN
import LonelyRunner.LRC.ConstructionN.Band

/-!
# Order seven: folding the fastest runner into a five-runner window

`fold_one`: if five speeds are in band `[1/7, 6/7]` on `[s, s + W]` and `v6 W ≥ 2/7`, some instant of `[s, s + W]` has
all six in band — runner 6 sweeps an arc of length `≥ 2/7`, which meets the closed band.

* `lonely7_of_fast6`: `v6 ≥ 6 v5` (any `v1 < … < v5`), from `kappa ≥ 1/21` (`O7Kappa.kappa_ge`).
* `lonely7_of_kappa`: any five-runner window of length `3/(28 v5)` (as given by the `kappa ≥ 3/28` trees) and
  `3 v6 ≥ 8 v5`.

Everything here is proved; no `sorry`, no `native_decide`.
-/

namespace LRC.O7Fold

open LRC.MirrorCentre LRC.O7Split

/-- **The fold.** -/
theorem fold_one {S : Finset ℕ} {s W : ℝ} {v6 : ℕ} (hS : InBandOn S (Set.Icc s (s + W))) (h6 : 0 < v6)
    (hW : (2 : ℝ) / 7 ≤ v6 * W) : ∃ t : ℝ, ∀ d ∈ insert v6 S, (1 : ℝ) / 7 ≤ circDist ((d : ℝ) * t) := by
  have h6' : (0 : ℝ) < v6 := by exact_mod_cast h6
  have hW0 : 0 ≤ W := by
    by_contra hc; rw [not_le] at hc; nlinarith
  by_cases hc : (1 : ℝ) / 7 ≤ circDist ((v6 : ℝ) * s)
  · refine ⟨s, fun d hd => ?_⟩
    rcases Finset.mem_insert.mp hd with rfl | hd
    · exact hc
    · exact hS s ⟨le_rfl, by linarith⟩ d hd
  · rw [not_le] at hc
    -- `v6 s` is within `1/7` of the integer `N = round (v6 s)`
    obtain ⟨N, hN⟩ := ConstructionN.circDist_eq_abs_sub_some_int ((v6 : ℝ) * s)
    rw [hN] at hc
    have hlo : (N : ℝ) - 1 / 7 < v6 * s := by have := neg_abs_le ((v6 : ℝ) * s - N); linarith
    have hhi : (v6 : ℝ) * s < N + 1 / 7 := by have := le_abs_self ((v6 : ℝ) * s - N); linarith
    set t := ((N : ℝ) + 1 / 7) / v6 with ht
    have hts : s ≤ t := by rw [ht, le_div_iff₀ h6']; linarith
    have htW : t ≤ s + W := by rw [ht, div_le_iff₀ h6']; nlinarith
    refine ⟨t, fun d hd => ?_⟩
    rcases Finset.mem_insert.mp hd with rfl | hd
    · rw [ht, show (d : ℝ) * (((N : ℝ) + 1 / 7) / d) = (N : ℝ) + 1 / 7 by field_simp]
      exact circDist_ge_of_window (m := N) le_rfl (by linarith) (by norm_num)
    · exact hS t ⟨hts, htW⟩ d hd

/-- Six speeds lonely at `1/7` from a five-runner window of length `W` with `v6 W ≥ 2/7`. -/
theorem lonely7_of_window {v1 v2 v3 v4 v5 v6 : ℕ} {s W : ℝ}
    (hS : InBandOn {v1, v2, v3, v4, v5} (Set.Icc s (s + W))) (h6 : 0 < v6) (hW : (2 : ℝ) / 7 ≤ v6 * W) :
    ∃ t : ℝ, ∀ d ∈ ({v1, v2, v3, v4, v5, v6} : Finset ℕ), (1 : ℝ) / 7 ≤ circDist ((d : ℝ) * t) := by
  obtain ⟨t, ht⟩ := fold_one hS h6 hW
  refine ⟨t, fun d hd => ht d ?_⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hd ⊢
  tauto

/-- **`v6 ≥ 6 v5` closes order seven** (any `v1 < … < v5`), from `kappa ≥ 1/21`. -/
theorem lonely7_of_fast6 {v1 v2 v3 v4 v5 v6 : ℕ} (h0 : 0 < v1) (h12 : v1 < v2) (h23 : v2 < v3) (h34 : v3 < v4)
    (h45 : v4 < v5) (h6 : 6 * v5 ≤ v6) :
    ∃ t : ℝ, ∀ d ∈ ({v1, v2, v3, v4, v5, v6} : Finset ℕ), (1 : ℝ) / 7 ≤ circDist ((d : ℝ) * t) := by
  have hpos : ∀ d ∈ ({v1, v2, v3, v4, v5} : Finset ℕ), 0 < d := by
    intro d hd; simp only [Finset.mem_insert, Finset.mem_singleton] at hd; omega
  have hcard : ({v1, v2, v3, v4, v5} : Finset ℕ).card ≤ 5 := Finset.card_le_five
  have hV : ∀ d ∈ ({v1, v2, v3, v4, v5} : Finset ℕ), d ≤ v5 := by
    intro d hd; simp only [Finset.mem_insert, Finset.mem_singleton] at hd; omega
  obtain ⟨L, -, hL⟩ := LRC.O7Kappa.kappa_ge _ hpos hcard (by omega : 0 < v5) hV
  have h5 : (0 : ℝ) < v5 := by exact_mod_cast (show 0 < v5 by omega)
  have h6r : (6 : ℝ) * v5 ≤ v6 := by exact_mod_cast h6
  refine lonely7_of_window (s := L) (W := 1 / (21 * v5)) (fun s hs d hd => hL s hs d hd) (by omega) ?_
  rw [mul_one_div, le_div_iff₀ (by positivity)]; nlinarith

/-- **`3 v6 ≥ 8 v5` closes order seven** given a five-runner window of length `3/(28 v5)` (`kappa ≥ 3/28`). -/
theorem lonely7_of_kappa {v1 v2 v3 v4 v5 v6 : ℕ} (h5 : 0 < v5) (h6 : 8 * v5 ≤ 3 * v6)
    (hk : ∃ s₀ : ℝ, InBandOn {v1, v2, v3, v4, v5} (Set.Icc s₀ (s₀ + 3 / (28 * v5)))) :
    ∃ t : ℝ, ∀ d ∈ ({v1, v2, v3, v4, v5, v6} : Finset ℕ), (1 : ℝ) / 7 ≤ circDist ((d : ℝ) * t) := by
  obtain ⟨s₀, hs⟩ := hk
  have h5r : (0 : ℝ) < v5 := by exact_mod_cast h5
  have h6r : (8 : ℝ) * v5 ≤ 3 * v6 := by exact_mod_cast h6
  refine lonely7_of_window hs (by omega) ?_
  rw [show (v6 : ℝ) * (3 / (28 * v5)) = 3 * v6 / (28 * v5) by ring, le_div_iff₀ (by positivity)]; nlinarith

end LRC.O7Fold
