import LonelyRunner.LRC.Construction8.Reference

/-!
# The cyclic gap structure

`docs/n8/PROOF_CANDIDATE_v3.md` part 1 and part 2(a); `docs/n8/GAP_FRAME_v2.md` §0 (§0 is
unchanged from v1).

This is the piece both remaining targets of `docs/n8/PROOF_PLAN_v1.md` §2 need and
neither had: the `n` cyclic gaps of sorted positions, and the fact that they sum to 1.
`gaps_all_eq` (part 2(a)) consumes exactly this and nothing in the tree supplied it.

**What `cycGap_sum` is, precisely.**  It is a telescoping identity and holds for *any*
`p : ℕ → ℝ`.  It becomes the conservation law of part 1 only when `p` is the sorted list
of the runners' positions on the circle, at which point the `i`-th value really is the
`i`-th gap.  The sorting itself is not done here, and the file does not pretend the
identity carries geometric content on its own.

**What is still missing for the two targets.**  The bridge from pairwise circle distance
to these gaps — that adjacent points realise the minimum, so `circDist` between neighbours
is the gap — needs the sorted order.  Without it, `cycGap_all_eq` cannot yet be applied to
a hypothesis stated in terms of pairwise separation, which is the form both part 1 and the
converse of 6(c) come in.

Nothing here states or attempts part 7.
-/

namespace Construction8

/-- The cyclic gap at index `i` of `n` positions listed by `p`: the step to the next, with
the last wrapping back to the first. -/
noncomputable def cycGap (n : ℕ) (p : ℕ → ℝ) (i : Fin n) : ℝ :=
  if (i : ℕ) + 1 < n then p ((i : ℕ) + 1) - p (i : ℕ) else 1 - p (n - 1) + p 0

/-- The gaps sum to 1, over `Finset.range n`.  Telescoping: the `n - 1` interior steps
collapse to `p (n-1) - p 0`, and the wrap term restores the circle. -/
theorem cycGap_sum_range (n : ℕ) (hn : 0 < n) (p : ℕ → ℝ) :
    ∑ i ∈ Finset.range n,
      (if i + 1 < n then p (i + 1) - p i else 1 - p (n - 1) + p 0) = 1 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [Finset.sum_range_succ]
  have hlast : ¬ (m + 1 < m + 1) := by omega
  simp only [hlast, if_false]
  have hcong : ∀ i ∈ Finset.range m,
      (if i + 1 < m + 1 then p (i + 1) - p i else 1 - p (m + 1 - 1) + p 0)
        = p (i + 1) - p i := by
    intro i hi
    have : i + 1 < m + 1 := by have := Finset.mem_range.mp hi; omega
    simp [this]
  rw [Finset.sum_congr rfl hcong, Finset.sum_range_sub (fun i => p i) m]
  simp

/-- **Conservation.**  `∑ cycGap = 1`.  Part 1's `Σ g_k = 1`, once `p` is the sorted
position list. -/
theorem cycGap_sum (n : ℕ) (hn : 0 < n) (p : ℕ → ℝ) :
    ∑ i : Fin n, cycGap n p i = 1 := by
  have h := Fin.sum_univ_eq_sum_range
    (fun j : ℕ => if j + 1 < n then p (j + 1) - p j else 1 - p (n - 1) + p 0) n
  simp only [cycGap]
  rw [h]
  exact cycGap_sum_range n hn p

/-- **Equal spacing.**  If every cyclic gap reaches `1/n`, every one is exactly `1/n`.
Part 2(a) applied to the gap structure: `n` numbers each at least `1/n` and summing to 1
are all equal, so the positions are the vertices of a regular `n`-gon. -/
theorem cycGap_all_eq (n : ℕ) (hn : 0 < n) (p : ℕ → ℝ)
    (hge : ∀ i : Fin n, (n : ℝ)⁻¹ ≤ cycGap n p i) (i : Fin n) :
    cycGap n p i = (n : ℝ)⁻¹ :=
  gaps_all_eq hn (cycGap n p) hge (cycGap_sum n hn p) i

/-! ## The bridge from adjacent separations to the gaps

Each cyclic gap *is* the separation of the adjacent pair it joins, so a bound on
adjacent circle distances transfers to the gaps.  The interior gaps are literally the
differences; the wrap gap differs from its pair's difference by the integer 1, which
`circDist` does not see.
-/

/-- The wrap gap's circle distance is the circle distance of the pair it joins. -/
theorem circDist_wrap (p : ℕ → ℝ) (n : ℕ) :
    circDist (1 - p (n - 1) + p 0) = circDist (p 0 - p (n - 1)) := by
  have h : (1 : ℝ) - p (n - 1) + p 0 = (p 0 - p (n - 1)) + ((1 : ℤ) : ℝ) := by
    push_cast; ring
  rw [h, circDist_add_int]

/-- **The bridge.**  A lower bound on adjacent circle distances is a lower bound on the
gaps themselves. -/
theorem cycGap_ge_of_adjacent {n : ℕ} (hn : 0 < n) (p : ℕ → ℝ)
    (hnn : ∀ i : Fin n, 0 ≤ cycGap n p i)
    (h : ∀ i : Fin n, (n : ℝ)⁻¹ ≤ circDist (cycGap n p i)) (i : Fin n) :
    (n : ℝ)⁻¹ ≤ cycGap n p i :=
  le_of_le_circDist hn (hnn i) (h i)

/-- **Equal spacing from adjacent separations.**  Every adjacent pair at least `1/n`
apart, with nonnegative gaps, forces every gap to be exactly `1/n`. -/
theorem cycGap_eq_of_adjacent {n : ℕ} (hn : 0 < n) (p : ℕ → ℝ)
    (hnn : ∀ i : Fin n, 0 ≤ cycGap n p i)
    (h : ∀ i : Fin n, (n : ℝ)⁻¹ ≤ circDist (cycGap n p i)) (i : Fin n) :
    cycGap n p i = (n : ℝ)⁻¹ :=
  cycGap_all_eq n hn p (cycGap_ge_of_adjacent hn p hnn h) i

end Construction8
