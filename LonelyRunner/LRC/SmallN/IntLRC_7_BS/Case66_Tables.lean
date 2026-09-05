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

## A genuine gap in sub-case (b)

BS writes "By Lemma 7 we can assume that `ẽ(d₂,d₄) ∉ {2,4,6}`". Two problems,
both established by exhaustive check:

* `{2,4,6}` is **not sufficient**. Excluding it still leaves `ẽ₂₄ = 0`
  unresolved. The exact set of `ẽ₂₄` values that fail for some `ẽ₂₅` is
  `{0,2,4,6}` — see `avoid_66b`, which is stated with that exclusion and is the
  weakest one that makes the sub-case go through.
* Neither set is reachable from Lemma 7(i), which requires `ℓ(X) ≤ 4`:
  `ℓ({2,4,6}) = 5` and `ℓ({0,2,4,6}) = 6`, and **no** interval of length `≤ 4`
  contains `{0,2,4,6}`. So in the `ν(e₂₄) < m` branch the cited justification
  does not deliver the exclusion the argument needs.

Lemma 7(ii) *does* deliver it when `ν(e₂₄) = m`: for `X = {0,2,4,6}` we have
`X ∩ (X+1) = {0}`, and `r(e₂₄)` is a leading unit so `r(e₂₄) ≠ 0`, making
7(ii)'s hypothesis automatic. Sub-case (b) therefore closes as written **only**
in the `ν(e₂₄) = m` branch; `ν(e₂₄) < m` needs a separate argument not present
in the paper. BS do note that §6.6 leans on Lemma 7 delicately (§7 opens by
saying `m > 1` is used "in Lemma 7 and in particular situations in cases 6.3 and
6.6"), but the `ν(e₂₄) < m` sub-branch of 6.6(b) is not among the situations
they then address.

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

/-- **The five bad pairs all have `ẽ₂₄ ∈ {4,5,6}`.** This is what licenses BS's
first resolution path: if `ν(e₂₄) < m` then Lemma 7(i) with `X = {4,5,6}`
(`ℓ(X) = 3 ≤ 4`, so 7(i) genuinely applies) gives `ẽ₂₄ ∉ {4,5,6}` and (16)
holds. -/
theorem avoid_66a_of_t24 (t24 t25 : ZMod 7) (h : t24 ≠ 4 ∧ t24 ≠ 5 ∧ t24 ≠ 6) :
    ∃ k : ZMod 7, (k = 1 ∨ k = 2 ∨ k = 3) ∧
      (k ≠ 0 ∧ k ≠ 6) ∧
      (k + 2 ≠ 0 ∧ k + 2 ≠ 6) ∧
      (2 * k - t24 ≠ 0 ∧ 2 * k - t24 ≠ 6) ∧
      (2 * k - t24 + 1 ≠ 0 ∧ 2 * k - t24 + 1 ≠ 6) ∧
      (4 * t25 + 4 * k ≠ 0 ∧ 4 * t25 + 4 * k ≠ 6) := by
  revert h; revert t24 t25; decide

/-- **BS §6.6(b) table** (L771–780). `e₁₂ = N/7`, `e₃₄ = 2N/7`. With `λk ∈ Λ₀`
chosen so `q(λk d₄) = k`, the five arc indices are `k`, `k+2` (that is `A₂`),
`4ẽ₂₄ + 4k`, `4ẽ₂₄ + 4k + 1` (that is `A₁`), and `ẽ₂₄ − ẽ₂₅ + k` (that is `d₅`).

The hypothesis excludes `ẽ₂₄` from the EVEN residues `{0,2,4,6}`. BS write
`{2,4,6}`; that is not sufficient — `ẽ₂₄ = 0` fails — and neither exclusion is
reachable from Lemma 7(i). See the module docstring. -/
theorem avoid_66b (t24 t25 : ZMod 7)
    (h : t24 ≠ 0 ∧ t24 ≠ 2 ∧ t24 ≠ 4 ∧ t24 ≠ 6) :
    ∃ k : ZMod 7, (k = 1 ∨ k = 2 ∨ k = 3) ∧
      (k ≠ 0 ∧ k ≠ 6) ∧
      (k + 2 ≠ 0 ∧ k + 2 ≠ 6) ∧
      (4 * t24 + 4 * k ≠ 0 ∧ 4 * t24 + 4 * k ≠ 6) ∧
      (4 * t24 + 4 * k + 1 ≠ 0 ∧ 4 * t24 + 4 * k + 1 ≠ 6) ∧
      (t24 - t25 + k ≠ 0 ∧ t24 - t25 + k ≠ 6) := by
  revert h; revert t24 t25; decide

/-- **BS's `{2,4,6}` is not sufficient in sub-case (b).** The witness is
`ẽ₂₄ = 0`: for `ẽ₂₅ = 2` no `k ∈ {1,2,3}` works. Stated as a refutation so the
gap is recorded in the development itself and not only in prose. -/
theorem avoid_66b_246_insufficient :
    ¬ ∀ (t24 t25 : ZMod 7), (t24 ≠ 2 ∧ t24 ≠ 4 ∧ t24 ≠ 6) →
      ∃ k : ZMod 7, (k = 1 ∨ k = 2 ∨ k = 3) ∧
        (k ≠ 0 ∧ k ≠ 6) ∧
        (k + 2 ≠ 0 ∧ k + 2 ≠ 6) ∧
        (4 * t24 + 4 * k ≠ 0 ∧ 4 * t24 + 4 * k ≠ 6) ∧
        (4 * t24 + 4 * k + 1 ≠ 0 ∧ 4 * t24 + 4 * k + 1 ≠ 6) ∧
        (t24 - t25 + k ≠ 0 ∧ t24 - t25 + k ≠ 6) := by
  decide

end Case66
end IntLRC7BS
