import Mathlib
import Fresh.Framework
import Fresh.Localisation
import Fresh.OneMoverA

/-!
# S1, the mover is not the subject: the AP with one runner moved to any speed

Written 2026-10-22.  New file; nothing existing is edited.

Setting.  Eight speeds `c + i` (`i = 0 … 7`, the AP of gap 1) except that runner `m` is at speed `x`, any real.  The
subject is a runner `k ≠ m`.  `s1_other`: if `x ≠ c + k` (the mover is not at the subject's speed, so the disparity `d`
is positive) the subject is isolated at some positive instant.

Proof.  The subject's other readings are the AP gaps `|i - k|` for `i ≠ k, m`: at most six values in `{1..7}`, so some
`j ∈ {1..7}` is missing from them (`exists_j`, by `decide` over the 56 pairs).  `Fresh.OneMover.family` gives an instant
at which every reading of `{1..7} \ {j}` and the free reading `d = |x - (c + k)|` are clear; the subject's readings are
a subset of these, and `distInt` is even.  The instant is not required to be the first.

Grades: [L].  No density, cap, move count or clock.  The case where the mover is the subject (`m = k`) is separate.
-/

open Classical

namespace Fresh.OneMover

open Fresh Fresh.Localisation

/-- The one-mover arrangement: speeds `c + i`, except that runner `m` is at speed `x`. -/
noncomputable def oneMover (c x : ℝ) (m : Fin 8) : Fin 8 → ℝ :=
  fun i => if i = m then x else c + ((i : ℕ) : ℝ)

/-- The seven families, dispatched on `j`. -/
theorem family (j : ℕ) (hj1 : 1 ≤ j) (hj7 : j ≤ 7) (d : ℝ) (hd : 0 < d) :
    ∃ t : ℝ, 0 < t ∧ FrozenClear j t ∧ (1 / 8 : ℝ) ≤ distInt (d * t) := by
  interval_cases j
  · exact family_1 d hd
  · exact family_2 d hd
  · exact family_3 d hd
  · exact family_4 d hd
  · exact family_5 d hd
  · exact family_6 d hd
  · exact family_7 d hd

theorem exists_j : ∀ k m : Fin 8, k ≠ m →
    ∃ j ∈ Finset.Icc 1 7, ∀ i : Fin 8, i ≠ k → i ≠ m → (((i : ℕ) : ℤ) - ((k : ℕ) : ℤ)).natAbs ≠ j := by
  decide

theorem distInt_abs_mul (a t : ℝ) : distInt (|a| * t) = distInt (a * t) := by
  rcases abs_cases a with ⟨h, _⟩ | ⟨h, _⟩
  · rw [h]
  · rw [h, neg_mul, distInt_neg]

/-- **[PROVISIONAL: covering]** inherited from `family`.  S1 for a mover that is not the subject. -/
theorem s1_other (c x : ℝ) (k m : Fin 8) (hkm : k ≠ m) (hxk : x ≠ c + ((k : ℕ) : ℝ)) :
    ∃ t : ℝ, 0 < t ∧ IsolatedAt (oneMover c x m) k t := by
  have hd : 0 < |x - (c + ((k : ℕ) : ℝ))| := abs_pos.2 (sub_ne_zero.2 hxk)
  obtain ⟨j, hjmem, hj⟩ := exists_j k m hkm
  rw [Finset.mem_Icc] at hjmem
  obtain ⟨t, ht0, hF, hmover⟩ := family j hjmem.1 hjmem.2 _ hd
  refine ⟨t, ht0, fun i hik => ?_⟩
  have hvk : oneMover c x m k = c + ((k : ℕ) : ℝ) := by simp [oneMover, hkm]
  by_cases him : i = m
  · have hvi : oneMover c x m i = x := by simp [oneMover, him]
    rw [hvi, hvk]
    rw [← distInt_abs_mul]
    exact hmover
  · have hvi : oneMover c x m i = c + ((i : ℕ) : ℝ) := by simp [oneMover, him]
    rw [hvi, hvk]
    have hik' : (i : ℕ) ≠ (k : ℕ) := fun h => hik (Fin.ext h)
    have hi := i.isLt
    have hk := k.isLt
    set n : ℕ := (((i : ℕ) : ℤ) - ((k : ℕ) : ℤ)).natAbs with hn
    have hn1 : 1 ≤ n := by
      rw [hn]; apply Int.natAbs_pos.2; omega
    have hn7 : n ≤ 7 := by
      rw [hn]; omega
    have hnj : n ≠ j := hj i hik him
    have h1 := hF n hn1 hn7 hnj
    have hcast : ((n : ℕ) : ℝ) = |((i : ℕ) : ℝ) - ((k : ℕ) : ℝ)| := by
      rw [hn]; push_cast [Nat.cast_natAbs, Int.cast_abs]; ring_nf
    rw [hcast, distInt_abs_mul] at h1
    have e : c + ((i : ℕ) : ℝ) - (c + ((k : ℕ) : ℝ)) = ((i : ℕ) : ℝ) - ((k : ℕ) : ℝ) := by ring
    rw [e]
    exact h1

#print axioms family
#print axioms exists_j
#print axioms s1_other

end Fresh.OneMover
