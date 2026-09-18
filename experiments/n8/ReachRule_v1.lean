import LonelyRunner.LRC.ConstructionN.LemmaPass

/-! # The reach rule: the search's inner loop, as a theorem

`GapRule` says what a *junction* costs. This says what the *scan* proves.

What the covering search actually does, stripped of bookkeeping, is carry one number — how far to
the right the bad intervals have reached so far — and push it forward:

```
    reach r []            = r
    reach r ((a,b) :: t)  = if a < r then reach (max r b) t else r
```

The theorem below says this number is a **certificate**: everything from the start up to (but not
including) `reach` is covered, and *no hypothesis of sortedness is needed* — the recursion is sound
on any list, it is only sharp on a sorted one.

Two things this buys.

* It is the mechanism, not the search. `reach` is a fold over the intervals; there is nothing to
  enumerate and nothing to sample. Establishing coverage of `[1, n−1]` is one pass.
* Combined with `GapRule.no_gap_iff`, for **integer** readings every comparison in that pass —
  `a < r` and `max r b` — is a comparison of integers after clearing denominators. The certificate
  is therefore exact arithmetic end to end, at any order `n`, with no floating point anywhere.

Neither statement mentions `8`. -/

namespace ReachRule

/-- How far the intervals have reached, scanned left to right. This is the search's inner loop. -/
def reach : ℚ → List (ℚ × ℚ) → ℚ
  | r, [] => r
  | r, (a, b) :: t => if a < r then reach (max r b) t else r

@[simp] theorem reach_nil (r : ℚ) : reach r [] = r := rfl

@[simp] theorem reach_cons (r a b : ℚ) (t : List (ℚ × ℚ)) :
    reach r ((a, b) :: t) = if a < r then reach (max r b) t else r := rfl

/-- **The reach never retreats.** -/
theorem le_reach : ∀ (l : List (ℚ × ℚ)) (r : ℚ), r ≤ reach r l
  | [], r => le_refl r
  | (a, b) :: t, r => by
      rw [reach_cons]
      split
      · exact le_trans (le_max_left r b) (le_reach t _)
      · exact le_refl r

/-- **The reach is a covering certificate.**  Every point from the start up to the reach lies in one
of the intervals. No sortedness hypothesis. -/
theorem covered_below_reach :
    ∀ (l : List (ℚ × ℚ)) (r x : ℚ), r ≤ x → x < reach r l →
      ∃ p ∈ l, p.1 < x ∧ x < p.2
  | [], r, x, hr, hx => absurd hx (by rw [reach_nil]; exact not_lt.2 hr)
  | (a, b) :: t, r, x, hr, hx => by
      rw [reach_cons] at hx
      by_cases ha : a < r
      · rw [if_pos ha] at hx
        by_cases hb : x < max r b
        · -- `x` is inside `(a, b)` itself: `a < r ≤ x`, and `x < max r b` with `r ≤ x` forces `x < b`
          have hxb : x < b := by
            rcases max_cases r b with ⟨h, _⟩ | ⟨h, _⟩
            · exact absurd (h ▸ hb) (not_lt.2 hr)
            · exact h ▸ hb
          exact ⟨(a, b), List.mem_cons_self, lt_of_lt_of_le ha hr, hxb⟩
        · obtain ⟨p, hp, hp'⟩ := covered_below_reach t (max r b) x (not_lt.1 hb) hx
          exact ⟨p, List.mem_cons_of_mem _ hp, hp'⟩
      · rw [if_neg ha] at hx
        exact absurd hx (not_lt.2 hr)

/-- **The scan decides it.**  If the reach passes the far end, the whole closed interval `[r, N]` is
covered, except possibly `N` itself — and `N` is one of the finitely many endpoint values, so it is
checked directly. -/
theorem covers_of_reach_gt (l : List (ℚ × ℚ)) (r N : ℚ) (h : N < reach r l) :
    ∀ x, r ≤ x → x ≤ N → ∃ p ∈ l, p.1 < x ∧ x < p.2 :=
  fun _ hx hxN => covered_below_reach l r _ hx (lt_of_le_of_lt hxN h)

end ReachRule
