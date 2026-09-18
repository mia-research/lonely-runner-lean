# The move-charge / return-cost memo: correct algebra, and it is the Long-Return circle again

2026-09-18. Artefacts: `experiments/n8/memo_ab_v1/`. Assesses a proposal that reduces the missing
product bound to a "Bounded Return Overlap" lemma.

---

## 1. What is right, and it is most of it

| claim | verdict |
|---|---|
| CR (`S_N ≤ A + c·L_N`, `c < 1`) ⟺ uniform boundedness of the product | **correct** |
| `b(P) > a(P)` for every legal setter lap | **correct**, exact |
| `ρ(P) = a(P)/b(P)` is monotone decreasing, worst case at `P = 1` | **correct** — flagged as unchecked in the memo; checked here over `P = 1 … 4000` |
| `c_* = log(9/7)/log(5/3) ≈ 0.4920`, limit `1/3` | **correct** |

The cross-multiplication is exact: `(8P+7)(8P−1) > (8P+1)²` ⟺ `32P > 8` ⟺ `P > 1/4`, and every
setter lap is `≥ 1`.

The CR equivalence also matches what `LONG_RETURN_CIRCLE_v1` §7 found independently — a bounded lap
product and `CascadeCapped` are equivalent, so recasting the obligation in terms of the laps is not a
refinement. The memo reaches the same place by its own route. That agreement is worth having.

## 2. The identification the memo does not make

Write `s = 8P` for the reading. Expanding:

| `P` | `a(P)` | `2/s` | `b(P)` | `6/s` |
|---|---|---|---|---|
| 100 | 0.00250000 | 0.00250000 | 0.00746272 | 0.00750000 |
| 1000 | 0.00025000 | 0.00025000 | 0.00074963 | 0.00075000 |

**`a(P) ~ 2/s` and `b(P) ~ 6/s`. These are inequalities (i) and (iii) of `LONG_RETURN_CIRCLE_v1`.**
The memo has independently rederived the Long-Return circle in logarithmic notation.

The arithmetic confirms it. Each runner's return intervals are disjoint and tile its own span, so
`Σ_i b(P_i^x) ≤ L_N` per runner and `≤ 7·L_N` over seven. Then `S_N ≤ A + 7c_*·L_N`, and with the
asymptotic `c_* = 1/3`:

    7 × 1/3 = 7/3 = 2.3333

**the same composed constant already on record** as `k/3 = 2.33` at `k = 7`. At the sharp
`c_* = 0.4920` it is worse: `3.4438`.

## 3. The proposed lemma is refuted, not merely unproven

The memo stops honestly, naming **Bounded Return Overlap** as the remaining obstruction and declining
to claim closure. The threshold it needs is computable: closure requires `μ·c_* < 1`, so with
`c_* = 0.4920`,

    μ < 2.033

Measured on the two arrangements this manuscript already names:

| case | moves | distinct setters | `L_N` | `μ = Σb/L_N` | `S_N/L_N` |
|---|---|---|---|---|---|
| §6.7 climb, subject 393 | 28 | 7 of 7 | 2.3283 | **2.536** | 1.307 |
| §6.9 row, subject 1 | 23 | 7 of 7 | 2.3334 | **2.381** | 1.328 |

**Both exceed 2.033.** The overlap bound the route requires is false exactly where the cascade works
hardest. And `μ ≈ 7` is not a crude estimate — each runner's intervals *tile* its span, so when all
seven set repeatedly the multiplicity is essentially the number of such runners, which the hard cases
show is seven.

## 4. Why no repair is available

The memo's own step (1) — *"every actual move grows by less than its maximal factor"*, `L_N ≤ S_N` —
is what forbids the coefficient from dropping below 1 without the additive constant. Measured
`S_N/L_N`: **minimum 1.063 over 433 cascades, never below 1**, and 1.307 / 1.328 on the hard cases.
That is the same forcing recorded in `LONG_RETURN_CIRCLE_v1` §1, reached from the other side.

The additive `A` is what makes CR non-trivial (`L_N ≤ A/(1−c)` is a genuine cap). But `A` is bounded
by the seven unpaired first charges, `≤ 7·log(9/7) = 1.759`, and it cannot rescue a coefficient above
1: with `c ≥ 1` the inequality `(1−c)L_N ≤ A` gives no bound at all.

**A sampler warning, for the fourth time.** The random sample gave `μ` median 0.000 and max 1.537 —
every cascade satisfying `μ < 2.033`, which would have read as the lemma holding. The named
arrangements refute it. Test against `{(27,70,107,137,159,188,344,393), subj 393}` and
`{(1,31,75,97,128,160,176,225), subj 1}` first, always.

## 5. Net

Nothing here is wrong except the hope. The algebra through `b(P) > a(P)` is exact, the monotonicity
the memo flagged does hold, and the CR equivalence is right and independently confirms a result
already on record. What the work does is re-derive the Long-Return circle and arrive at its constant,
`7/3`, by a different road — and the lemma it proposes to bridge the gap is false on the hard cases
by a factor of about 1.25.

The counting routes remain closed, for the reason recorded in `THE_OBLIGATION_v1` §2: every one of
them adds where the truth is a product. Door 4 does not (see `DOOR4_v1` §1).
