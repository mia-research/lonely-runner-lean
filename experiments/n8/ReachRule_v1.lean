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

/-! ## The converse: the reach is where it genuinely stops

`covered_below_reach` is sound on any list. Sharpness is the other half, and it needs sortedness —
but only in one place, and the forward proof says where: in the branch where the scan **stops**. If
the scan halts at `r` because the next interval starts at `a ≥ r`, then every *later* interval also
starts at `a' ≥ a ≥ r`, and that is the only step where the order of the list is used at all. -/

/-- **The reach is uncovered.**  On a list sorted by left endpoint, no interval contains `reach r l`.
Sortedness is used in exactly one branch — the one where the scan stops. -/
theorem reach_uncovered :
    ∀ (l : List (ℚ × ℚ)), l.Pairwise (fun p q => p.1 ≤ q.1) → ∀ (r : ℚ),
      ∀ p ∈ l, ¬(p.1 < reach r l ∧ reach r l < p.2)
  | [], _, _, _, hp => absurd hp (List.not_mem_nil)
  | (a, b) :: t, hs, r, p, hp => by
      rw [List.pairwise_cons] at hs
      obtain ⟨hhead, htail⟩ := hs
      rw [reach_cons]
      by_cases ha : a < r
      · rw [if_pos ha]
        rcases List.mem_cons.1 hp with rfl | hpt
        · rintro ⟨-, h2⟩
          exact absurd h2 (not_lt.2 (le_trans (le_max_right r b) (le_reach t _)))
        · exact reach_uncovered t htail (max r b) p hpt
      · rw [if_neg ha]
        rcases List.mem_cons.1 hp with rfl | hpt
        · rintro ⟨h1, -⟩; exact ha h1
        · rintro ⟨h1, -⟩
          exact absurd (lt_of_lt_of_le h1 (not_lt.1 ha)) (not_lt.2 (hhead p hpt))

/-- **The fold decides it.**  On a sorted list, `[r, N]` is covered by the intervals **if and only
if** the single accumulated number passes `N`. Soundness is `covers_of_reach_gt`; completeness is
`reach_uncovered`, which hands back the reach itself as the witness. -/
theorem reach_decides (l : List (ℚ × ℚ)) (hs : l.Pairwise (fun p q => p.1 ≤ q.1)) (r N : ℚ) :
    (∀ x, r ≤ x → x ≤ N → ∃ p ∈ l, p.1 < x ∧ x < p.2) ↔ N < reach r l := by
  constructor
  · intro hcov
    by_contra hle
    obtain ⟨p, hp, hp1, hp2⟩ := hcov (reach r l) (le_reach l r) (not_lt.1 hle)
    exact reach_uncovered l hs r p hp ⟨hp1, hp2⟩
  · exact covers_of_reach_gt l r N

/-- **The witness is the reach.**  When the intervals fail to cover, the fold does not merely say so
— it returns the leftmost uncovered point. -/
theorem uncovered_witness (l : List (ℚ × ℚ)) (hs : l.Pairwise (fun p q => p.1 ≤ q.1)) (r N : ℚ)
    (h : reach r l ≤ N) :
    ∃ x, r ≤ x ∧ x ≤ N ∧ ∀ p ∈ l, ¬(p.1 < x ∧ x < p.2) :=
  ⟨reach r l, le_reach l r, h, reach_uncovered l hs r⟩

/-! ## What kind of number the witness is

`reach_decides` returns a point, so the next question is forced: *which* point can it be. The
recursion only ever assigns `r` its starting value or the right endpoint `b` of an interval it
crossed. It never produces anything else — so the witness is drawn from a finite, explicit list. -/

/-- **The reach is a right endpoint, or the start.**  Nothing else can come out of the fold. -/
theorem reach_mem : ∀ (l : List (ℚ × ℚ)) (r : ℚ), reach r l = r ∨ ∃ p ∈ l, reach r l = p.2
  | [], r => Or.inl rfl
  | (a, b) :: t, r => by
      rw [reach_cons]
      by_cases ha : a < r
      · rw [if_pos ha]
        rcases reach_mem t (max r b) with h | ⟨p, hp, hp'⟩
        · rcases max_cases r b with ⟨hm, -⟩ | ⟨hm, -⟩
          · exact Or.inl (h.trans hm)
          · exact Or.inr ⟨(a, b), List.mem_cons_self, h.trans hm⟩
        · exact Or.inr ⟨p, List.mem_cons_of_mem _ hp, hp'⟩
      · rw [if_neg ha]; exact Or.inl rfl

/-- **The witness set is finite and explicit.**  If every interval's right endpoint lies in a set
`E`, then the fold's output lies in `{r} ∪ E`. Covering is therefore never a question about the
continuum: it is settled by checking `r` and the finitely many right endpoints. -/
theorem reach_in_endpoints (l : List (ℚ × ℚ)) (r : ℚ) (E : Set ℚ)
    (hE : ∀ p ∈ l, p.2 ∈ E) : reach r l = r ∨ reach r l ∈ E := by
  rcases reach_mem l r with h | ⟨p, hp, hp'⟩
  · exact Or.inl h
  · exact Or.inr (hp' ▸ hE p hp)

/-- **Bounded denominator.**  Right endpoints of bad intervals are `(n·m+1)/s`. So on integer
readings the leftmost lonely point, when there is one, is `r` itself or a rational whose denominator
divides one of the readings — in particular it is at most `max sᵢ`. The continuum is gone: what is
left is a finite arithmetic check whose size is governed by the readings alone. -/
theorem reach_denom (l : List (ℚ × ℚ)) (r : ℚ) (n : ℤ) (S : Finset ℤ)
    (hS : ∀ p ∈ l, ∃ s ∈ S, ∃ m : ℤ, p.2 = ((n * m + 1 : ℤ) : ℚ) / (s : ℚ)) :
    reach r l = r ∨ ∃ s ∈ S, ∃ m : ℤ, reach r l = ((n * m + 1 : ℤ) : ℚ) / (s : ℚ) := by
  rcases reach_mem l r with h | ⟨p, hp, hp'⟩
  · exact Or.inl h
  · obtain ⟨s, hs, m, hm⟩ := hS p hp
    exact Or.inr ⟨s, hs, m, hp'.trans hm⟩

/-! ## The continuum is removable

Put the three together. `reach_decides` says the fold settles covering; `reach_mem` says the fold's
output is one of finitely many rationals; so covering an interval of the real line is equivalent to
covering a **finite list of explicitly named points**. -/

/-- **Finite check.**  `[r, N]` is covered by the intervals **if and only if** each of the finitely
many candidate points — the start `r`, and the right endpoints of the intervals — is covered. There
is no quantifier over the continuum left on either side. -/
theorem finite_check (l : List (ℚ × ℚ)) (hs : l.Pairwise (fun p q => p.1 ≤ q.1)) (r N : ℚ) :
    (∀ x, r ≤ x → x ≤ N → ∃ p ∈ l, p.1 < x ∧ x < p.2)
      ↔ (∀ x, (x = r ∨ ∃ p ∈ l, x = p.2) → r ≤ x → x ≤ N → ∃ p ∈ l, p.1 < x ∧ x < p.2) := by
  constructor
  · intro h x _ hx hxN; exact h x hx hxN
  · intro h
    rw [reach_decides l hs r N]
    by_contra hle
    have hcand : reach r l = r ∨ ∃ p ∈ l, reach r l = p.2 := reach_mem l r
    obtain ⟨p, hp, hp1, hp2⟩ := h (reach r l) hcand (le_reach l r) (not_lt.1 hle)
    exact reach_uncovered l hs r p hp ⟨hp1, hp2⟩

/-! ## Witness normalisation

The payoff of the chain. If the intervals fail to cover, there is not merely *a* witness — there is
one whose exact arithmetic shape is known in advance: the start, or `(n·m+1)/s` for a reading `s`.

Read on the Lonely Runner bad sets, where the interval of reading `s` at level `m` is
`((n·m−1)/s, (n·m+1)/s)`, this says the lonely point never needs to be an arbitrary real, or even an
arbitrary rational: **its denominator is `n` times one of the speeds, and its numerator is `≡ 1
(mod n)`.** That is a sharpening of the statement of the conjecture, and it holds at every order. -/

/-- **Witness normalisation.**  If covering fails, a witness exists in normal form: the start `r`,
or `(n·m+1)/s` with `s` drawn from the given finite set. -/
theorem witness_normalised (l : List (ℚ × ℚ)) (hs : l.Pairwise (fun p q => p.1 ≤ q.1))
    (r N : ℚ) (n : ℤ) (S : Finset ℤ)
    (hS : ∀ p ∈ l, ∃ s ∈ S, ∃ m : ℤ, p.2 = ((n * m + 1 : ℤ) : ℚ) / (s : ℚ))
    (hfail : ¬ ∀ x, r ≤ x → x ≤ N → ∃ p ∈ l, p.1 < x ∧ x < p.2) :
    ∃ x, (x = r ∨ ∃ s ∈ S, ∃ m : ℤ, x = ((n * m + 1 : ℤ) : ℚ) / (s : ℚ))
      ∧ r ≤ x ∧ x ≤ N ∧ ∀ p ∈ l, ¬(p.1 < x ∧ x < p.2) := by
  rw [reach_decides l hs r N] at hfail
  exact ⟨reach r l, reach_denom l r n S hS, le_reach l r, not_lt.1 hfail, reach_uncovered l hs r⟩

end ReachRule
