import LonelyRunner.LRC.SmallN.IntLRC_7_BS.Lemmas

/-!
# n = 7 (Barajas–Serra) — §6.6 (`|A₁| = 2`) finite tables

Source: `sources_barajas_serra_2008.txt` lines 732–786 (§6.6).

§6.6 has `A₁ = {d₁,d₂}` (residue 1), `A₂ = {d₃,d₄}` (residue 2), `A₄ = {d₅}`
(residue 4), and targets BS condition (15) — `ℓ(A₁) ≤ 2 ∧ ℓ(A₂) ≤ 2` — which
`lemma5` then closes. Condition (15) is reached directly unless
`ν(e₁₂) = ν(e₃₄) = m` with `r(e₁₂) ≠ r(e₃₄)`, which splits into BS's sub-cases
(a) `r(e₁₂) = 2r(e₃₄)` and (b) `r(e₁₂) = 4r(e₃₄)`. This file carries the two
finite `Λ₀` tables those sub-cases need.

## A sign slip in the paper, and what the tables actually say

BS writes, in sub-case (a), `q(λk · A₂) = (ẽ(d₂,d₄) − 2k, ẽ(d₂,d₄) − 2k + 1)`.
That formula does **not** reproduce their own bad-pair list (16); the list
`{(4,2),(4,4),(5,4),(6,4),(6,6)}` is reproduced exactly, and only, by
`(2k − ẽ(d₂,d₄), 2k − ẽ(d₂,d₄) + 1)` — the sign of `ẽ` is flipped. The table is
the reliable part, and `avoid_66a` below is stated with the sign that matches it.
That sign is also the one consistent with `ẽ(d,d') = 2q(d) − q(d')`, the
convention used everywhere else in this development.

Two independent consistency checks on the corrected table, both of which BS's
own text asserts and both of which hold: every bad pair has `ẽ(d₂,d₄) ∈ {4,5,6}`
(so BS's "`ν(e₂₄) < m` ⟹ `ẽ₂₄ ∉ {4,5,6}` ⟹ (16)" is right), and the bad `ẽ₂₅`
values are `{2,4}` when `ẽ₂₄ ∈ {4,5}` and `{4,6}` when `ẽ₂₄ ∈ {0,6}`, matching
BS's two avoidance prescriptions exactly.

## A retracted claim, kept as a warning

An earlier version of this file claimed a gap in BS sub-case (b): that the
exclusion `ẽ(d₂,d₄) ∉ {2,4,6}` is insufficient and unreachable from Lemma 7(i).
**That was our error, not the paper's**, and the table encoding it has been
removed along with the claim.

The mistake was taking the invariant against the wrong ratio-2 partner. Lemma 7
controls `ẽ(d,d')` only when `r(d') = 2·r(d)`; in the (b) frame `r(d₅) = 4 =
2·r(d₄)`, so `d₅` pairs with `d₄`, not `d₂`. With `ẽ(d₄,d₅)` the fifth arc is
`2k − ẽ(d₄,d₅)`, the bad set is `{2,4}` with `ℓ = 3 ≤ 4` and empty self-overlap,
and Lemma 7(i)/(ii) both apply. Sub-case (b) closes at every valuation. The table
actually used is `avoid_66b_Q` in `Case_A5.lean`.

The sub-case (a) sign correction above is unaffected and stands.

Both tables are stated with explicit `≠` rather than `Finset` membership, so
kernel `decide` applies directly.
-/

namespace IntLRC7BS
namespace Case66

/-- **BS §6.6(a) table, condition (16)** (L760–769). `e₁₂ = 2N/7`, `e₃₄ = N/7`.
With `λk ∈ Λ₀` chosen so `q(λk d₂) = k`, the five arc indices are
`k`, `k+2` (that is `A₁`), `2k − ẽ₂₄`, `2k − ẽ₂₄ + 1` (that is `A₂`), and
`4ẽ₂₅ + 4k` (that is `d₅`). Some `k ∈ {1,2,3}` avoids `{0,6}` throughout,
except for BS's five bad pairs.

The `ẽ₂₄` sign here is the corrected one — see the module docstring. -/
theorem avoid_66a (t24 t25 : ZMod 7)
    (hexc : ¬ ((t24 = 4 ∧ t25 = 2) ∨ (t24 = 4 ∧ t25 = 4) ∨ (t24 = 5 ∧ t25 = 4) ∨
               (t24 = 6 ∧ t25 = 4) ∨ (t24 = 6 ∧ t25 = 6))) :
    ∃ k : ZMod 7, (k = 1 ∨ k = 2 ∨ k = 3) ∧
      (k ≠ 0 ∧ k ≠ 6) ∧
      (k + 2 ≠ 0 ∧ k + 2 ≠ 6) ∧
      (2 * k - t24 ≠ 0 ∧ 2 * k - t24 ≠ 6) ∧
      (2 * k - t24 + 1 ≠ 0 ∧ 2 * k - t24 + 1 ≠ 6) ∧
      (4 * t25 + 4 * k ≠ 0 ∧ 4 * t25 + 4 * k ≠ 6) := by
  revert hexc; revert t24 t25; decide

end Case66
end IntLRC7BS
