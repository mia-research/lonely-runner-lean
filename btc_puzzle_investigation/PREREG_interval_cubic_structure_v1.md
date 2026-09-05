# PREREG — does confining `d` to a short interval leave cubic structure in the curve data?

**Date:** 2026-07-31. **FROZEN BEFORE DATA.** No arm has been evaluated when this file is written.

> ⚠ **`[EXPLORATORY — user-authorised gate relaxation]`**. No `experiment-designer` sign-off. This is
> the same relaxation recorded for the chirp-plane enquiry (2026-07-30), **not** a §2a unavailability
> branch. **No number produced under this spec may move a grade** until a gated replication runs.

---

## 0. Object and scope — no key set, no generator

**Object: the curve map `d ↦ x([d]G)` on secp256k1 at its own prime `P`, restricted to an interval.**
All scalars are **constructed** (`random.randrange`). **The 82 solved puzzle keys are not used, and
no null is drawn from any generator pool.** The question is a property of the curve's scalar
multiplication, not of how any integer was chosen.

**Why this regime.** `ANALYSIS_correlation_hierarchy_weil_closure_v1.md` §2 shows complete character
sums over `E(F_p)` of bounded-degree readouts are `O(k√p)` — closed. §3.2 records the boundary:
completing an **interval** sum costs `log p`, and the bound `O(√p log p)` exceeds `|I|` once
`|I| ≲ √p`, at which point it is vacuous. **Incomplete sums are the unclosed regime**, and
constructed scalars sample them at unlimited `N`.

## 1. Statistic (FROZEN)

For a set `S` of `M` points, `X_i = x(P_i)`, cubic-class counts `(a,b,c)` of `χ₃(X_i − X_j)` over all
`C(M,2)` unordered pairs (`χ₃(t) = t^{(P−1)/3}`, class = index in `{1, ω, ω²}`):

> `E₃ = [(2a−b−c)² + 3(b−c)²] / 4`

Exact integers; `χ₃` by modular exponentiation. No float in the signal path. Decision by **rank
against the null** (integer count), no float threshold.

## 2. Null (FROZEN) — and why it is matched

**Null = `M` points drawn uniformly at random from `E(F_P)`**, generated directly by sampling `x`
until `x³+7` is a QR (**no scalar multiplication**, so the null cannot inherit any property of the
scalar map). Pool of 20,000 such points, `R = 1000` resamples of `M`.

**Matching is exact because secp has cofactor 1:** every point of `E(F_P)` is in the prime-order
group, so "uniform random curve point" = "uniform random group element" = "`[d]G` for `d` uniform in
`[1,n)`". The null is therefore the *same distribution* the full-range arm produces.

## 3. Arms (FROZEN)

`d` uniform in `[2^{k−1}, 2^k)` for **`k ∈ {40, 64, 96, 128, 135, 160, 200}`**, `M = 80`, one set per
arm. `k = 135` is included because it is the length of the first unsolved puzzle; it carries no
special status in the analysis and is one arm of seven.

## 4. Controls — all must behave before any arm is read

| id | control | requirement |
|---|---|---|
| **C-NEG** | `d` uniform in `[1, n)` (full range) | **must NOT fire** — by §2 it is drawn from the null's own distribution. A fire here means the null is mis-specified and **all arms are void.** |
| **C-PLANT** | a set built with deliberate cubic imbalance (points forced into one cubic class) | **must fire** (pctile ≥ 99th). Otherwise a null on the arms is indistinguishable from an instrument that cannot fire. |
| **C-FORCED** | `a+b+c = C(M,2)`; `E₃` a non-negative integer | asserted |
| **C-EXACT** | no float in the signal path | asserted |

## 5. Decision rule (PRE-COMMITTED)

- An arm **FIRES** iff its `E₃` is at or above the **99th percentile** of the null (7 arms; 0.01×7 ≈
  0.07 family-wise, stated, not corrected — this is exploratory).
- An arm is **NULL** iff below the 95th.
- Between 95th and 99th: **INDETERMINATE, no verdict**, report the number only.

## 6. Falsification / readings (PRE-COMMITTED)

- **F-FIRE.** ≥1 arm fires with C-NEG quiet and C-PLANT firing ⇒ interval confinement leaves a
  detectable cubic signature at that length. Report as a candidate, `[EXPLORATORY]`, requiring a
  gated replication at a fresh seed before any claim.
- **F-NULL.** No arm fires, C-PLANT fires, C-NEG quiet ⇒ **a bounded magnitude**, scoped to
  `M = 80`, `E₃`, `R = 1000`, these seven lengths. **Not a closure** — `E₃` reads only marginal
  cubic-class counts of pairwise differences and is blind to phase, to orientation-odd channels, and
  to any structure in a subspace it does not project onto.
- **F-VOID.** C-NEG fires or C-PLANT fails ⇒ instrument failure, **no arm number is read.**

## 7. Power — stated honestly before the run

`M = 80` gives 3160 pairs. `E₃` is heavy-tailed (an `|·|²` of a sum of roots of unity), so a single
set is a low-power instrument by construction. **This spec detects a gross cubic imbalance, not a
subtle one**, and the plant calibrates which. `M` is limited only by `C(M,2)` exponentiations, i.e.
by compute, **not by sample availability** — unlike any design built on a fixed key set, `M` and `R`
can be raised arbitrarily in a follow-up.

## 8. Deviations

Recorded inline in the RESULT. Freeze = SHA-256 of this file, printed by the runner.
