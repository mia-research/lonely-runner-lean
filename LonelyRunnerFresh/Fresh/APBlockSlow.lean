import Mathlib
import Fresh.Framework
import Fresh.Localisation
import Fresh.PathLaws
import Fresh.Grid
import Fresh.Admissible
import Fresh.AdmissibleFlank
import Fresh.ClusterTransfer

/-!
# A near-AP fast block of at most six readings with one slow reading below its unit

Written 2026-10-25.  New file.  Worklist tags: G04 (one low reading and a high group, 1 | 6), A01 and A04 (the high group is an AP `g, 2g, …, r g` with deviations at most `η`), H06 (one slow participant).
The quotient of the AP block is `{1, …, r}`; its `1/(r+1)`-clear instant `σ = 1/(r+1)` is explicit (`distInt (k/(r+1)) ≥ 1/(r+1)`), so no order-six or order-seven theorem is needed.
`ap_block_slow`: with `slow_one_vs_block`, one slow reading `s < g` is cleared by a return of the block, within the deformation allowance
`η (1/(r+1) + K) / g ≤ 1/56`, `K = 1/(4 min(s/g, 1 - s/g)) + 1`.  `APBlockSlowClass`: the subject's disparities are `s` and such a block; `apBlockSlow_isolation`.
Mechanisms: M-A (deviation absorbed by the `1/7 - 1/8` slack), M-B (return and step).  Grade [L].
-/

open Classical

namespace Fresh.APBlockSlow

open Fresh Fresh.Admissible Fresh.AdmissibleFlank Fresh.ClusterTransfer

theorem gate_of_band {γ y : ℝ} (N : ℤ) (h1 : (N : ℝ) + γ ≤ y) (h2 : y ≤ (N : ℝ) + 1 - γ) (hγ : 0 ≤ γ) :
    γ ≤ distInt y := by
  rw [Fresh.Localisation.le_distInt_iff]
  intro z
  rcases le_or_gt z N with hz | hz
  · have : (z : ℝ) ≤ N := by exact_mod_cast hz
    rw [abs_of_nonneg (by linarith)]; linarith
  · have : (N : ℝ) + 1 ≤ z := by exact_mod_cast hz
    rw [abs_of_nonpos (by linarith)]; linarith

theorem ap_quot_gate {r : ℕ} (hr : r ≤ 6) (i : Fin r) :
    (1 / 7 : ℝ) ≤ distInt ((((i : ℕ) + 1 : ℕ) : ℝ) * (1 / ((r : ℝ) + 1))) := by
  have hi : (i : ℕ) + 1 ≤ r := i.2
  have hiR : ((i : ℕ) : ℝ) + 1 ≤ r := by exact_mod_cast hi
  have hr7 : (r : ℝ) + 1 ≤ 7 := by exact_mod_cast (by omega : r + 1 ≤ 7)
  have hrpos : (0 : ℝ) < (r : ℝ) + 1 := by positivity
  apply gate_of_band (0 : ℤ) _ _ (by norm_num)
  · push_cast
    rw [show ((i : ℕ) + 1 : ℝ) * (1 / ((r : ℝ) + 1)) = ((i : ℕ) + 1) / ((r : ℝ) + 1) by ring]
    rw [le_div_iff₀ hrpos]
    have : (0 : ℝ) ≤ (i : ℕ) := Nat.cast_nonneg _
    have h17 : (1 / 7 : ℝ) * ((r : ℝ) + 1) ≤ 1 := by linarith
    linarith
  · push_cast
    rw [show ((i : ℕ) + 1 : ℝ) * (1 / ((r : ℝ) + 1)) = ((i : ℕ) + 1) / ((r : ℝ) + 1) by ring]
    rw [div_le_iff₀ hrpos]
    nlinarith

theorem ap_block_slow {r : ℕ} (hr : r ≤ 6) {f : Fin r → ℝ} {g s η : ℝ} (hg : 0 < g) (hs0 : 0 < s) (hsg : s < g) (hη : 0 ≤ η)
    (hdev : ∀ i : Fin r, |f i - (((i : ℕ) + 1 : ℕ) : ℝ) * g| ≤ η)
    (hallow : η * (1 / ((r : ℝ) + 1) + (1 / (4 * min (s / g) (1 - s / g)) + 1)) / g ≤ 1 / 56) :
    ∃ t : ℝ, 0 < t ∧ (∀ i, (1 / 8 : ℝ) ≤ distInt (f i * t)) ∧ (1 / 8 : ℝ) ≤ distInt (s * t) := by
  have hrpos : (0 : ℝ) < (r : ℝ) + 1 := by positivity
  exact slow_one_vs_block (f := f) (n := fun i : Fin r => ((i : ℕ) + 1 : ℕ)) (σ := 1 / ((r : ℝ) + 1)) hg hs0 hsg
    (by positivity) hdev (fun i => ap_quot_gate hr i) hη (by
      have : η * (1 / ((r : ℝ) + 1) + (1 / (4 * min (s / g) (1 - s / g)) + 1)) / g = η * (1 / ((r : ℝ) + 1) + (1 / (4 * min (s / g) (1 - s / g)) + 1)) / g := rfl
      exact hallow)

-- STANDING: DEFINITION
def APBlockSlowClass (v : Fin 8 → ℝ) (k : Fin 8) : Prop :=
  ∃ (r : ℕ) (f : Fin r → ℝ) (g s η : ℝ), r ≤ 6 ∧ 0 < g ∧ 0 < s ∧ s < g ∧ 0 ≤ η ∧
    (∀ i : Fin r, |f i - (((i : ℕ) + 1 : ℕ) : ℝ) * g| ≤ η) ∧
    η * (1 / ((r : ℝ) + 1) + (1 / (4 * min (s / g) (1 - s / g)) + 1)) / g ≤ 1 / 56 ∧
    ∀ d : ℝ, d ∈ disparitySet v k ↔ d = s ∨ ∃ i, d = f i

theorem apBlockSlow_isolation {v : Fin 8 → ℝ} {k : Fin 8} (h : APBlockSlowClass v k) : Isolation v k := by
  obtain ⟨r, f, g, s, η, hr, hg, hs0, hsg, hη, hdev, hallow, hmem⟩ := h
  obtain ⟨t, ht, hf, hs⟩ := ap_block_slow hr hg hs0 hsg hη hdev hallow
  refine ⟨t, ht, ?_⟩
  rw [Fresh.Localisation.isolatedAt_iff]
  intro d hd
  rcases (hmem d).1 hd with rfl | ⟨i, rfl⟩
  · exact hs
  · exact hf i

#print axioms ap_block_slow
#print axioms apBlockSlow_isolation

end Fresh.APBlockSlow
