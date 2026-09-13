import LonelyRunner.LRC.Construction8.Gaps
import Mathlib.Data.Fin.Tuple.Sort

/-!
# The sorting permutation, and equal spacing from pairwise separation

`docs/n8/PROOF_PLAN_v1.md` §2 — the combinatorial step that `Gaps.lean` names as missing.
`Gaps.lean` proves equal spacing from *adjacent* separations; both remaining targets
arrive holding *all pairwise* separations over an unsorted family.  This file closes that
gap by producing the sorted order.

`Tuple.sort q` is the permutation.  `sortedPos q` lists the positions along it, indexed by
`ℕ` so `cycGap` can consume them.  The two facts needed are then:

* the gaps of the sorted list are nonnegative — interior by monotonicity, the wrap because
  values inside `[0,1)` have spread below 1;
* adjacent entries of the sorted list are *distinct runners*, since the sort is a
  permutation, so the pairwise hypothesis applies to them.

`equally_spaced_of_pairwise` is the result: `n` positions in `[0,1)`, pairwise at circle
distance at least `1/n`, have every cyclic gap exactly `1/n`.

**What this still does not do.**  It gives the gap structure and the permutation; it does
not yet finish either target.  Part 1 needs the two gaps *flanking a given runner*, which
is `Tuple.sort q` read at that runner's index — available now, not yet written.  The
converse of 6(c) needs, on top of equal spacing, the step from "positions are `α + j/n`"
to "each `x_k` is an integer", which uses the normalisation `e₀ = 0`.

Nothing here states or attempts part 7.
-/

namespace Construction8

/-- The positions listed in sorted order, indexed by `ℕ` so `cycGap` can consume them. -/
noncomputable def sortedPos {n : ℕ} (q : Fin n → ℝ) : ℕ → ℝ :=
  fun j => if h : j < n then q (Tuple.sort q ⟨j, h⟩) else 0

theorem sortedPos_apply {n : ℕ} (q : Fin n → ℝ) {j : ℕ} (hj : j < n) :
    sortedPos q j = q (Tuple.sort q ⟨j, hj⟩) := by
  simp [sortedPos, hj]

/-- Adjacent entries of the sorted list are distinct runners — the sort is a permutation —
so a pairwise separation hypothesis applies to them.  The wrap gap goes through
`circDist_wrap`. -/
theorem cycGap_sortedPos_sep {n : ℕ} (hn : 1 < n) (q : Fin n → ℝ)
    (hsep : ∀ a b : Fin n, a ≠ b → (n : ℝ)⁻¹ ≤ circDist (q a - q b)) (i : Fin n) :
    (n : ℝ)⁻¹ ≤ circDist (cycGap n (sortedPos q) i) := by
  have hn0 : 0 < n := by omega
  unfold cycGap
  split_ifs with hlt
  · have hi : (i : ℕ) < n := i.isLt
    rw [sortedPos_apply q hlt, sortedPos_apply q hi]
    refine hsep _ _ ?_
    intro hcon
    have h2 := (Tuple.sort q).injective hcon
    have h3 : (i : ℕ) + 1 = (i : ℕ) := congrArg Fin.val h2
    omega
  · have hn1 : n - 1 < n := by omega
    rw [circDist_wrap (sortedPos q) n, sortedPos_apply q hn0, sortedPos_apply q hn1]
    refine hsep _ _ ?_
    intro hcon
    have h2 := (Tuple.sort q).injective hcon
    have h3 : (0 : ℕ) = n - 1 := congrArg Fin.val h2
    omega

/-- The gaps of the sorted list are nonnegative: interior by monotonicity of the sort, the
wrap because values inside `[0,1)` have spread below 1. -/
theorem cycGap_sortedPos_nonneg {n : ℕ} (hn : 0 < n) (q : Fin n → ℝ)
    (h0 : ∀ k, 0 ≤ q k) (h1 : ∀ k, q k < 1) (j : Fin n) :
    0 ≤ cycGap n (sortedPos q) j := by
  unfold cycGap
  split_ifs with hlt
  · have hj : (j : ℕ) < n := j.isLt
    rw [sortedPos_apply q hlt, sortedPos_apply q hj]
    refine sub_nonneg.mpr ?_
    exact Tuple.monotone_sort q
      (show (⟨(j : ℕ), hj⟩ : Fin n) ≤ ⟨(j : ℕ) + 1, hlt⟩ from Nat.le_succ _)
  · have hn1 : n - 1 < n := by omega
    have hup : sortedPos q (n - 1) < 1 := by rw [sortedPos_apply q hn1]; exact h1 _
    have hlo : 0 ≤ sortedPos q 0 := by rw [sortedPos_apply q hn]; exact h0 _
    linarith

/-- **All pairwise separations force equal spacing.**  `n` positions in `[0,1)`, pairwise
at circle distance at least `1/n`, have every cyclic gap exactly `1/n` — they are the
vertices of a regular `n`-gon.  This is part 2(a) reached from a pairwise hypothesis. -/
theorem equally_spaced_of_pairwise {n : ℕ} (hn : 1 < n) (q : Fin n → ℝ)
    (h0 : ∀ k, 0 ≤ q k) (h1 : ∀ k, q k < 1)
    (hsep : ∀ a b : Fin n, a ≠ b → (n : ℝ)⁻¹ ≤ circDist (q a - q b)) (i : Fin n) :
    cycGap n (sortedPos q) i = (n : ℝ)⁻¹ :=
  cycGap_eq_of_adjacent (by omega) (sortedPos q)
    (cycGap_sortedPos_nonneg (by omega) q h0 h1) (cycGap_sortedPos_sep hn q hsep) i

end Construction8
