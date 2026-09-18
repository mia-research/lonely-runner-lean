# What closing `RCapped` requires: assessing the three-item route

A parallel session set out three items said to be required. They name the right three things, but
they are **not three comparable steps**: two are already done, one of those points the opposite way
to how it is used, and the third is the entire problem.

---

## Item 1 — "step dilation limits: `λ_j < (8M+1)/(8M−1)` contracts towards `1⁺`" — **true, and it is the obstruction, not a step**

The premise is exactly Theorems 6.25–6.26 of v11 (`dilation_lt_nine_sevenths`,
`dilation_lt_of_two_le`), proved and axiom-clean. The conclusion drawn from it — *"the scale cannot
dilate indefinitely"* — **does not follow.**

`R = ∏ λ_j`. A bound *above* on each factor, with the factors tending to `1`, does not bound the
product. Taking the worst case `δ = −1`, so `λ_j = (8M_j+1)/(8M_j−1)`:

```
    M grows as      K=50      K=200     K=1000    K=10000
      M = j         3.084     4.354      6.507     11.571     grows without bound
      M = 1 + j/4  12.111    45.444    223.222   2223.222     diverges
      M = √j       24.316   827.202    5.1e+06    3.6e+21     diverges
```

With `M = j` the factors are `9/7, 17/15, 25/23, …`, every one tending to `1`, and
`Σ log((8j+1)/(8j−1)) ≈ Σ 1/(4j) ≈ (1/4)·log K`, so `R ≈ K^{1/4} → ∞`.

**`λ → 1` is precisely what makes `R` hard to bound**, because it means steps can be arbitrarily
unproductive. And the deep cascades are in that regime: mean `M` rises `1.73 → 3.58` across the
23-move case, `2.07 → 4.57` across the 28-move case. v11 §6.14 says this in terms: *"There is no
matching upper bound… no ceiling on the move count follows from the step law."*

## Item 2 — "fixed-point landing: `R` must satisfy `s_i·R mod 8 ∈ [1,7]`" — **correct, and already done**

This is v11 Theorems 11.1 and 11.2: the clear set *is* `{R : ∀i, s_i·R mod 8 ∈ [1,7]}`, and `R mod 8
∈ [1,7]` is proved (`RBand.R_avoids_bad_bands`, axiom-clean, 148,892 cascades with zero violations).
It is a **characterisation of what `R` is**, not a step toward bounding it.

## Item 3 — "band 2 unreachability" — **this is the whole problem**

Stated correctly. There is no argument for it, and the natural reformulation fails.

### 3.1 The reformulation that does not work

Since `R = (8k+1)/s` for the binding reading `s` at the clear point, and `S > 7` for any non-trivial
profile, `R < 16` would follow from `(8k+1) < 16S`, i.e. `k ≤ 13`. So: **is the binding lap index
bounded?** Measured over 32,000 subjects:

```
    binding (8k+1) :  9 → 7455,  17 → 3249,  25 → 1707,  33 → 950,  41 → 637, …  max 137
    maximum k observed : 17
```

**`k` reaches 17, so `(8k+1) = 137 > 112`** — yet `R` stayed under 12 throughout, because the binding
`s` was correspondingly large. The binding reading is not always `s₇` either: the 23-move case binds
at `s = 3.2`, the 28-move case at `s = 4.78`, and only the top `R`-maximisers bind near `s₇`
(`7.46`, `7.44`).

So bounding `k` is **neither necessary nor sufficient** for bounding `R`, and it is not a softer
target.

### 3.2 What is actually owed

Band 2 needs the six non-minimal combs to cover `[1,7] ∪ [9,15]` entirely — 12 units, six sets of
density `1/4`, 18 units of bad measure available. Counting gives a factor of `1.5` and decides
nothing, as it has at every stage. A proof must show the combs **cannot interlock**, and the only
structural fact in hand pointing that way is that the best coverer (the AP) fails by eight points
protected by the unit group (v11 Theorem 11.3) — and the AP is simultaneously the *worst* case for
`R`, with `R = 1`.

---

## Summary

| item | status |
|---|---|
| 1. step dilation limits | **proved** (6.25–6.26), and it is the *obstruction*: `λ → 1` is consistent with `R → ∞` |
| 2. fixed-point landing | **proved** (11.1–11.2) — a characterisation, not a step |
| 3. band 2 unreachability | **the open problem**; `k ≤ 13` fails as a reformulation (`k` reaches 17) |

`RCapObligation_v1.lean` already carries the implication `RCapped B → DoorCapped → LonelyRunnerAt8`,
proved and axiom-clean. What is owed is item 3 alone, and nothing in items 1 or 2 reduces it.

```bash
python3 experiments/n8/lambda_no_bound_v1.py      # λ → 1 does not bound the product
python3 experiments/n8/binding_numerator_v1.py    # binding (8k+1) reaches 137, k = 17
```
