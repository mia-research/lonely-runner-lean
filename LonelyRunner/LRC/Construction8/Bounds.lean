import LonelyRunner.LRC.Construction8.Window
import LonelyRunner.LRC.Construction8.Coords
import Mathlib.Data.ZMod.Basic

/-!
# The three results the manuscript listed as paper-only

`docs/n8/MANUSCRIPT_v1.md` §8 carried a table marking Theorem 4.8, Corollary 4.4 and the
geometric form of Theorem 4.9 as proved on paper but not formalised.  This file closes
that gap, so the table goes fully green and the abstract's verification claim needs no
qualification.

* `ratio_condition` — Theorem 4.8.  A reading in `[1, n-1]` is clear at `u = 1/n`.
* `lonely_ne_pred` — Corollary 4.4.  The count of simultaneously lonely runners is never
  `n - 1`; at `n = 8`, never 7.
* `wide_gap_speeds` — Theorem 4.9 on a sorted speed list, rather than the index-free core
  already in `Coords.lean`.

Nothing here states or attempts part 7 of `PROOF_CANDIDATE_v3`.
-/

namespace Construction8

/-! ## Theorem 4.8 — the ratio condition -/

/-- **Theorem 4.8.**  A reading in `[1, n-1]` is clear at `u = 1/n`.  So when
`d_max ≤ (n-1)·d_min` — which is exactly every reading lying in that range — the reference
instant isolates the subject.  The bound is sharp at both ends: at `s = 1` and at
`s = n - 1` the distance is exactly `1/n`. -/
theorem ratio_condition {n : ℕ} (hn : 1 < n) {s : ℝ}
    (h1 : 1 ≤ s) (h2 : s ≤ (n : ℝ) - 1) : (n : ℝ)⁻¹ ≤ circDist (s / n) := by
  have hn0 : (0 : ℝ) < n := by positivity
  have hn1 : (1 : ℝ) ≤ (n : ℝ) - 1 := by
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  refine (window_iff (by positivity) ?_).mpr ⟨?_, ?_⟩
  · rw [div_lt_one hn0]; linarith
  · rw [inv_eq_one_div, div_le_div_iff_of_pos_right hn0]; exact h1
  · rw [div_le_iff₀ hn0]
    have h : (1 : ℝ) - (n : ℝ)⁻¹ = ((n : ℝ) - 1) / n := by field_simp
    rw [h, div_mul_eq_mul_div, le_div_iff₀ hn0]
    nlinarith

/-! ## Corollary 4.4 — the count is never `n - 1` -/

/-- A nonempty subset of `ZMod n` closed under predecessor is everything. -/
theorem eq_univ_of_pred_closed {n : ℕ} [NeZero n]
    (A : Finset (ZMod n)) (hne : A.Nonempty) (hcl : ∀ k ∈ A, k - 1 ∈ A) :
    A = Finset.univ := by
  obtain ⟨a, ha⟩ := hne
  have hstep : ∀ j : ℕ, a - (j : ZMod n) ∈ A := by
    intro j
    induction j with
    | zero => simpa using ha
    | succ m ih =>
      have h := hcl _ ih
      have hr : a - (m : ZMod n) - 1 = a - ((m + 1 : ℕ) : ZMod n) := by push_cast; ring
      rwa [hr] at h
  refine Finset.eq_univ_iff_forall.mpr ?_
  intro x
  have h := hstep ((a - x).val)
  rwa [ZMod.natCast_val, ZMod.cast_id, sub_sub_cancel] at h

/-- **Corollary 4.4.**  The number of simultaneously lonely runners is never `n - 1`.
Either every gap clears — and then all `n` are lonely — or some gap does not, in which
case the clearing gaps have a run start and the count drops to at most `n - 2`.  There is
no configuration one runner short.  At `n = 8`: the count is never 7. -/
theorem lonely_ne_pred {n : ℕ} [NeZero n] [DecidableEq (ZMod n)] (hn : 1 < n)
    (A : Finset (ZMod n)) :
    (A.filter (fun k => k - 1 ∈ A)).card ≠ n - 1 := by
  have hcard : Fintype.card (ZMod n) = n := ZMod.card n
  by_cases hA : A = Finset.univ
  · subst hA
    have hfil : (Finset.univ.filter (fun k : ZMod n => k - 1 ∈ Finset.univ))
        = Finset.univ := by simp
    rw [hfil, Finset.card_univ, hcard]
    omega
  · rcases A.eq_empty_or_nonempty with rfl | hne
    · simp; omega
    · have hrs : (A.filter (fun k => k - 1 ∉ A)).Nonempty := by
        by_contra h
        rw [Finset.not_nonempty_iff_eq_empty] at h
        refine hA (eq_univ_of_pred_closed A hne ?_)
        intro k hk
        by_contra hc
        have hm : k ∈ A.filter (fun k => k - 1 ∉ A) := Finset.mem_filter.mpr ⟨hk, hc⟩
        rw [h] at hm
        simp at hm
      have hid := run_identity A
      have h1 : 1 ≤ (A.filter (fun k => k - 1 ∉ A)).card := Finset.card_pos.mpr hrs
      have h2 : A.card < n := by
        have hlt := Finset.card_lt_card (Finset.ssubset_univ_iff.mpr hA)
        rwa [Finset.card_univ, hcard] at hlt
      omega

/-! ## Theorem 4.9 on a sorted speed list -/

/-- **Theorem 4.9, geometric form.**  If both gaps adjacent to runner `k` reach the
average `S/c`, where `S` is the spread, then every difference at `k` is at most
`c · d_min(k)` — Branch A's hypothesis, read straight off the speed list.  `Coords.lean`
carries the index-free core; this is it on sorted speeds. -/
theorem wide_gap_speeds {n : ℕ} (v : ℕ → ℝ)
    (hmono : ∀ i j, i ≤ j → j < n → v i ≤ v j)
    (k : ℕ) (hk1 : 1 ≤ k) (hkn : k + 1 < n) (c : ℝ) (hc : 0 < c)
    (hlo : (v (n - 1) - v 0) / c ≤ v k - v (k - 1))
    (hhi : (v (n - 1) - v 0) / c ≤ v (k + 1) - v k)
    (j : ℕ) (hj : j < n) :
    |v k - v j| ≤ c * min (v k - v (k - 1)) (v (k + 1) - v k) := by
  have hn1 : n - 1 < n := by omega
  have hk : k < n := by omega
  have hjlo : v 0 ≤ v j := hmono 0 j (by omega) hj
  have hjhi : v j ≤ v (n - 1) := hmono j (n - 1) (by omega) hn1
  have hklo : v 0 ≤ v k := hmono 0 k (by omega) hk
  have hkhi : v k ≤ v (n - 1) := hmono k (n - 1) (by omega) hn1
  have hD : |v k - v j| ≤ v (n - 1) - v 0 := by
    rw [abs_le]; constructor <;> linarith
  exact wide_gap_core c (v (n - 1) - v 0) (v k - v (k - 1)) (v (k + 1) - v k)
    (|v k - v j|) hc hlo hhi hD

end Construction8
