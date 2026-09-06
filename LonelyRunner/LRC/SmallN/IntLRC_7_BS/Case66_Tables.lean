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

## RETRACTED: there is no gap in sub-case (b)

An earlier version of this file claimed a gap here. **That claim was wrong, and
the error was mine, not the paper's.** It is retracted; the reasoning is kept
because the table `avoid_66b` below still encodes the mistaken form and must not
be used.

The claim was: BS's exclusion `ẽ(d₂,d₄) ∉ {2,4,6}` is insufficient (the true
failing set being `{0,2,4,6}`) and unreachable from Lemma 7(i), which needs
`ℓ(X) ≤ 4` while `ℓ({0,2,4,6}) = 6`.

The mistake was treating BS's printed `ẽ(d₂,d₅)` as the `Λ₀`-invariant appearing
in the fifth arc. Lemma 7 controls `ẽ(d,d')` only when `r(d') = 2·r(d)`. In the
sub-case (b) frame `r(d₅) = 4 = 2·r(d₄)`, so `d₅`'s ratio-2 partner is `d₄`, not
`d₂`. Solving the `k`-frame with the correct invariant gives fifth arc
`2k − ẽ(d₄,d₅)`, and then:

```
fifth arc as I had it   ẽ(d₂,d₄) − ẽ(d₂,d₅) + k → bad ẽ₂₄ = {0,2,4,6},  ℓ = 6
fifth arc, corrected    2k − ẽ(d₄,d₅)          → bad ẽ₂₄ = {2,4},      ℓ = 3
```

`ℓ({2,4}) = 3 ≤ 4`, so Lemma 7(i) applies; and `{2,4} ∩ ({2,4}+1) = ∅`, so
Lemma 7(ii) applies too. **Sub-case (b) closes at every valuation of `2d₂ − d₄`.
There is no residual and no gap.**

`avoid_66b` and `avoid_66b_246_insufficient` below are therefore **not used by
the proof**. `avoid_66b_246_insufficient` remains true as a statement about the
mistaken arc expression, but it says nothing about Barajas–Serra. The table
actually used is `avoid_66b_Q` in `Case_A5.lean`.

The sub-case (a) analysis in this file is unaffected: `avoid_66a` reproduces BS's
list (16) exactly, and the sign correction recorded above stands.

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
