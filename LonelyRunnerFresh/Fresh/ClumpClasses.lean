import Mathlib
import Fresh.Framework
import Fresh.Localisation
import Fresh.Admissible
import Fresh.AdmissibleFlank
import Fresh.ClumpGap
import Fresh.APSlowClump

/-!
# Arrangement classes: slow reading or slow near-AP block under a compact clump

Written 2026-10-25.  New file.  Worklist tags: G04 (1 | 6 with the six a compact train), G12, A01, A04, H06.
`SlowOneClumpClass`: one slow disparity `s` and a clump of the rest in `[x, (1+ε) x]` with `ε (x/(2s) + 2) ≤ 1/8` and `2 s ≤ 3 x`.  `APSlowClumpClass`: the slow disparities are an AP block `g, …, r g` within `η`,
the rest a clump, with the explicit separation, gate and clump conditions of `ap_slow_clump`.  Both are scale invariant (every condition is homogeneous) and carry the isolation proofs below.
**[PROVISIONAL: covering]** as in `APSlowClump`.  Grade [L].
-/

open Classical

namespace Fresh.ClumpClasses

open Fresh Fresh.Admissible Fresh.AdmissibleFlank Fresh.ClumpGap Fresh.APSlowClump

-- STANDING: DEFINITION
def SlowOneClumpClass (v : Fin 8 → ℝ) (k : Fin 8) : Prop :=
  ∃ (s x ε : ℝ) (C : Finset ℝ), 0 < s ∧ 0 < x ∧ 0 ≤ ε ∧ (∀ y ∈ C, x ≤ y ∧ y ≤ (1 + ε) * x) ∧
    ε * (x * (1 / (2 * s)) + 2) ≤ 1 / 8 ∧ 2 * s ≤ 3 * x ∧ ∀ d : ℝ, d ∈ disparitySet v k ↔ d = s ∨ d ∈ C

theorem slowOneClump_isolation {v : Fin 8 → ℝ} {k : Fin 8} (h : SlowOneClumpClass v k) : Isolation v k := by
  obtain ⟨s, x, ε, C, hs, hx, hε, hC, hdev, hxs, hmem⟩ := h
  obtain ⟨t, ht, hst, hCt⟩ := single_slow_clump hs hx hε hC hdev hxs
  refine ⟨t, ht, ?_⟩
  rw [Fresh.Localisation.isolatedAt_iff]
  intro d hd
  rcases (hmem d).1 hd with rfl | h
  · exact hst
  · exact hCt d h

-- STANDING: DEFINITION
def APSlowClumpClass (v : Fin 8 → ℝ) (k : Fin 8) : Prop :=
  ∃ (r : ℕ) (d : Fin r → ℝ) (g η ε x : ℝ) (C : Finset ℝ), r ≤ 6 ∧ 1 ≤ r ∧ 0 < g ∧ 0 ≤ η ∧ 0 ≤ ε ∧ 0 < x ∧
    (∀ i : Fin r, |d i - (((i : ℕ) + 1 : ℕ) : ℝ) * g| ≤ η) ∧ (∀ y ∈ C, x ≤ y ∧ y ≤ (1 + ε) * x) ∧
    η * (1 / (((r : ℝ) + 1) * g)) < 1 / ((r : ℝ) + 1) - 1 / 8 ∧
    (r * g + η) / (2 * x) ≤ 2 * (1 / ((r : ℝ) + 1) - η * (1 / (((r : ℝ) + 1) * g)) - 1 / 8) ∧
    ε * (x * (1 / (((r : ℝ) + 1) * g)) + 2) ≤ 1 / 8 ∧ ∀ e : ℝ, e ∈ disparitySet v k ↔ (∃ i, e = d i) ∨ e ∈ C

theorem apSlowClump_isolation {v : Fin 8 → ℝ} {k : Fin 8} (h : APSlowClumpClass v k) : Isolation v k := by
  obtain ⟨r, d, g, η, ε, x, C, hr, hr1, hg, hη, hε, hx, hdev, hC, hgate, hsep, hclump, hmem⟩ := h
  obtain ⟨t, ht, hdt, hCt⟩ := ap_slow_clump hr hr1 hg hη hε hx hdev hC hgate hsep hclump
  refine ⟨t, ht, ?_⟩
  rw [Fresh.Localisation.isolatedAt_iff]
  intro e he
  rcases (hmem e).1 he with ⟨i, rfl⟩ | h
  · exact hdt i
  · exact hCt e h

#print axioms slowOneClump_isolation
#print axioms apSlowClump_isolation

end Fresh.ClumpClasses
