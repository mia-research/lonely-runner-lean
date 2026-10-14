import Mathlib
import Fresh.Framework

/-!
# Task D: candidate (a), the path form, is equivalent to the conjecture at n = 8

`Fresh.Framework` proves `LonelyRunnerEight → DisplacementPath`.  This file proves the converse,
`displacementPath_imp_lonelyRunnerEight`, and hence `displacementPath_iff`.

What the result says, and no more: the path form (a) is a RESTATEMENT of `LonelyRunnerEight`.  Neither direction proves
either statement; both stay `-- STANDING: OWED` in `Framework.lean`.

Argument (symbolic, for all arrangements; no enumeration, no counting, no covering):
1. Relabelling: isolation of subject `k` in `v ∘ σ` is isolation of subject `σ k` in `v`
   (`isolatedAt_comp_perm`, `isolation_comp_perm`); being an arrangement is relabelling invariant
   (`isArrangement_comp_perm`).
2. Sorting: every injective `v` has a permutation `π` with `v ∘ π` strictly increasing (`exists_sorted`).
3. The straight-line path `γ s j = (1 - s)(j + 1) + s · w j` from the AP `(1, …, 8)` to a strictly increasing positive
   `w` is continuous and every point on `[0, 1]` is an ordered arrangement (all speeds positive, strictly increasing);
   its start is a grid (`idx j = j`, `d = 1`, `v₀ = 1`).  No runner is ever at speed 0 along the path.
4. `DisplacementPath` at `s = 1` gives isolation of every subject of `w = v ∘ π`, and step 1 transports it to `v`.

Provenance (existing repo, read for the argument, not imported; every proof below was re-derived and is understood):
- `isolatedAt_comp_perm` ↔ `LRC.ArrangementShape.lonely_relabel` in `LonelyRunner/LRC/Spec/ArrangementShapeN.lean`
  (same idea: substitute `σ.symm i` for the other runner).
- `exists_sorted` ↔ `LRC.ArrangementShape.exists_sorted` in the same file (sort the image Finset with
  `Finset.orderEmbOfFin`, pull back each sorted value to its label, the label map is a bijection of `Fin 8`).
- The path construction and `displacementPath_imp_lonelyRunnerEight` have no counterpart there; they are new.
-/

open Classical

namespace Fresh

/-! ## 1. Relabelling invariance -/

/-- Isolation of subject `k` after relabelling by `σ` is isolation of subject `σ k` before it. -/
theorem isolatedAt_comp_perm (v : Fin 8 → ℝ) (σ : Equiv.Perm (Fin 8)) (k : Fin 8) (t : ℝ) :
    IsolatedAt (v ∘ σ) k t ↔ IsolatedAt v (σ k) t := by
  constructor
  · intro h i hi
    have hne : σ.symm i ≠ k := by
      intro he; apply hi; rw [← he]; simp
    have := h (σ.symm i) hne
    simpa using this
  · intro h i hi
    exact h (σ i) (fun he => hi (σ.injective he))

#print axioms isolatedAt_comp_perm

theorem isolation_comp_perm (v : Fin 8 → ℝ) (σ : Equiv.Perm (Fin 8)) (k : Fin 8) :
    Isolation (v ∘ σ) k ↔ Isolation v (σ k) := by
  unfold Isolation
  simp only [isolatedAt_comp_perm]

#print axioms isolation_comp_perm

theorem isArrangement_comp_perm (v : Fin 8 → ℝ) (σ : Equiv.Perm (Fin 8)) :
    IsArrangement (v ∘ σ) ↔ IsArrangement v := by
  unfold IsArrangement
  constructor
  · rintro ⟨hp, hi⟩
    refine ⟨fun i => by simpa using hp (σ.symm i), ?_⟩
    have : v = (v ∘ σ) ∘ σ.symm := by funext i; simp
    rw [this]
    exact hi.comp σ.symm.injective
  · rintro ⟨hp, hi⟩
    exact ⟨fun i => hp (σ i), hi.comp σ.injective⟩

#print axioms isArrangement_comp_perm

/-! ## 2. Sorting -/

/-- Every injective arrangement of eight speeds is a relabelling of a strictly increasing one. -/
theorem exists_sorted (v : Fin 8 → ℝ) (hv : Function.Injective v) :
    ∃ π : Equiv.Perm (Fin 8), StrictMono (v ∘ π) := by
  let S := Finset.univ.image v
  have hc : S.card = 8 := by
    simp only [S]
    rw [Finset.card_image_of_injective _ hv]
    simp
  let w := S.orderEmbOfFin hc
  have hmem : ∀ i, ∃ j, v j = w i := by
    intro i
    obtain ⟨j, _, hj⟩ := Finset.mem_image.mp (S.orderEmbOfFin_mem hc i)
    exact ⟨j, hj⟩
  choose p hp using hmem
  have hinj : Function.Injective p := by
    intro i j hij
    apply w.injective
    rw [← hp i, ← hp j, hij]
  let π := Equiv.ofBijective p (Finite.injective_iff_bijective.mp hinj)
  refine ⟨π, ?_⟩
  intro i j hij
  change v (p i) < v (p j)
  rw [hp i, hp j]
  exact w.strictMono hij

#print axioms exists_sorted

/-! ## 3. The straight-line path from the AP `(1, …, 8)` -/

/-- The straight-line path from the AP `(1, …, 8)` (at `s = 0`) to `w` (at `s = 1`). -/
noncomputable def linePath (w : Fin 8 → ℝ) (s : ℝ) (j : Fin 8) : ℝ :=
  (1 - s) * (((j : ℕ) : ℝ) + 1) + s * w j

theorem linePath_continuous (w : Fin 8 → ℝ) : Continuous (linePath w) := by
  apply continuous_pi
  intro j
  unfold linePath
  fun_prop

#print axioms linePath_continuous

theorem linePath_one (w : Fin 8 → ℝ) : linePath w 1 = w := by
  funext j; simp [linePath]

#print axioms linePath_one

/-- The start of the path is the AP `(1, …, 8)`, a grid with `idx j = j`, `d = 1`, `v₀ = 1`. -/
theorem linePath_zero_isGrid (w : Fin 8 → ℝ) : IsGrid (linePath w 0) := by
  refine ⟨1, 1, fun j => ((j : ℕ) : ℤ), one_pos, ?_, ?_⟩
  · intro j j' h
    have hj := j.isLt
    have hj' := j'.isLt
    simp only at h
    apply Fin.ext
    omega
  · intro j
    simp [linePath]
    ring

#print axioms linePath_zero_isGrid

/-- Every point of the path on `[0, 1]` is an ordered arrangement: all speeds positive, strictly increasing. -/
theorem linePath_ordered (w : Fin 8 → ℝ) (hw : IsOrderedArrangement w) (s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    IsOrderedArrangement (linePath w s) := by
  obtain ⟨hpos, hmono⟩ := hw
  obtain ⟨hs0, hs1⟩ := hs
  have h1s : 0 ≤ 1 - s := by linarith
  rcases eq_or_lt_of_le hs0 with h | h
  · -- s = 0: the AP itself
    subst h
    refine ⟨fun j => ?_, fun i j hij => ?_⟩
    · simp [linePath]; positivity
    · simp only [linePath, sub_zero, one_mul, zero_mul, add_zero]
      have : (i : ℕ) < (j : ℕ) := hij
      have : ((i : ℕ) : ℝ) < ((j : ℕ) : ℝ) := by exact_mod_cast this
      linarith
  · -- s > 0: the `w` part is strictly positive and strictly increasing
    refine ⟨fun j => ?_, fun i j hij => ?_⟩
    · unfold linePath
      have a : 0 ≤ (1 - s) * (((j : ℕ) : ℝ) + 1) := mul_nonneg h1s (by positivity)
      have b : 0 < s * w j := mul_pos h (hpos j)
      linarith
    · unfold linePath
      have hn : (i : ℕ) < (j : ℕ) := hij
      have hr : ((i : ℕ) : ℝ) + 1 ≤ ((j : ℕ) : ℝ) + 1 := by
        have : ((i : ℕ) : ℝ) < ((j : ℕ) : ℝ) := by exact_mod_cast hn
        linarith
      have a : (1 - s) * (((i : ℕ) : ℝ) + 1) ≤ (1 - s) * (((j : ℕ) : ℝ) + 1) :=
        mul_le_mul_of_nonneg_left hr h1s
      have b : s * w i < s * w j := mul_lt_mul_of_pos_left (hmono hij) h
      linarith

#print axioms linePath_ordered

theorem isArrangement_of_ordered (v : Fin 8 → ℝ) (h : IsOrderedArrangement v) : IsArrangement v :=
  ⟨h.1, h.2.injective⟩

#print axioms isArrangement_of_ordered

/-! ## 4. The converse and the equivalence -/

/-- Candidate (a) implies the conjecture: sort the arrangement, run the straight-line path from the AP to it, read the
isolation at the end of the path, and relabel back. -/
theorem displacementPath_imp_lonelyRunnerEight : DisplacementPath → LonelyRunnerEight := by
  intro hP v hv k
  obtain ⟨π, hπ⟩ := exists_sorted v hv.2
  have hw : IsOrderedArrangement (v ∘ π) := ⟨fun i => hv.1 (π i), hπ⟩
  have hall := hP (linePath (v ∘ π)) (linePath_continuous _).continuousOn
    (fun s hs => isArrangement_of_ordered _ (linePath_ordered _ hw s hs))
    (linePath_zero_isGrid _) 1 ⟨zero_le_one, le_rfl⟩ (π.symm k)
  rw [linePath_one, isolation_comp_perm] at hall
  simpa using hall

#print axioms displacementPath_imp_lonelyRunnerEight

/-- Candidate (a) is a restatement of the conjecture at n = 8. -/
theorem displacementPath_iff : DisplacementPath ↔ LonelyRunnerEight :=
  ⟨displacementPath_imp_lonelyRunnerEight, lonelyRunnerEight_imp_displacementPath⟩

#print axioms displacementPath_iff

end Fresh
