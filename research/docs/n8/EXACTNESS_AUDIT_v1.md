# Exactness audit — every float-capable site in the n=8 line

2026-09-07, on a standing instruction: results are exact integers; be wary of any
floating-point answer. Mechanical, by AST parse rather than grep
(`experiments/n8/float_audit_v1.py`), over all 20 scripts plus the imported harness.

**Result: 9 float-capable sites, one genuine breach. It was mine, it was in a
reported claim, and it is now replaced by an exact certificate.**

---

## 1. The breach: the LR-property check on the p=41 witness

`SEARCH_REDUCTION_v3/v4` §1 and `HANDOVER_2026_09_07b` §4 state that the bad cover
`T = {1,4,12,13,14,16,20}` at `p = 41` "has the LR property as real speeds
(`max_t min_i ‖t v_i‖ = 0.14284 > 1/8`)". That number came from an inline scan over
`t = a/200000` in IEEE-754 doubles. It was never saved as a script, so it had no
artifact either.

**Redone exactly** (`experiments/n8/exact_lr_check_v1.py`, `Fraction` throughout, no
float constructed):

> `max_t min_i ‖t v_i‖ = 1/7`, attained at `t = 5/28`.
> Per-speed values at that `t`: `5/28, 2/7, 1/7, 9/28, 1/2, 1/7, 3/7`.
> `1/7 ≥ 1/8` by the integer comparison `1·8 ≥ 1·7`.

The float 0.14284 was approximating `1/7 = 0.142857…`. **The claim survives, and now
has a certificate**: `t = 5/28` is an exact witness that the tuple is lonely at `1/8`.
Every occurrence of the float figure should be read as `1/7 at t = 5/28`.

**Completeness of the exact search.** `f(t) = min_i ‖v_i t‖` is continuous and
piecewise linear; a local maximum occurs at a peak of the active `‖v_i t‖`
(`t = (2m+1)/(2v_i)`) or at a crossing of two of them, which solves
`v_i t − a = ±(v_j t − b)` and so has denominator `v_i + v_j` or `|v_i − v_j|`. The
script enumerates exactly that candidate set on `[0,1/2]` (`‖v(1−t)‖ = ‖vt‖`).
Validated against the manuscript's own §3 values: `{1,2}` gives `1/3` at `t = 1/3`;
`{1,2,3}` gives `1/4` at `t = 1/4`. It also returns `2/13` at `t = 4/13` for the `k=6`
obstruction `{1,6,7,8,9,15}` — and `4/13` lies inside `[15/49, 13/42]`, the lonely
interval `WHY_13_AND_19_v2.md` computed independently.

## 2. The other eight sites — none on a decision path

| file | line | site | status |
|---|---|---|---|
| `phase5_residue_structure.py` | 286–287 | `sum(...)/len(...)` averages | inside `main()`, which is `__main__`-guarded and **was never invoked** — the runner imports `compute_residue_structure`, `classify_lrc`, `good_cell_idx`, `lcm_list`, `gcd_list`, `isprime` only |
| `window_width_v1.py` | 18, 20, 29 | `F(m-1)/v`, `e/v`, `(a+c)/2` | **not floats** — every operand is a `Fraction`, so these are exact rational divisions. Flagged by grep, cleared by reading. |
| `enumerate_bad_covers_v1.py` | 46 | `round(v/p, 3)` | printed label only; no decision reads it |
| `run_k7_primes_v1.py` | 13 | `tot = 0.0` | wall-clock accumulator |
| `cells_v1.py` | 29 | `100*len(fails)/len(S)` | printed percentage; every §3 cell decision is an integer comparison |

**AST-clean, zero sites:** `run_n8_scan_v1.py`, `collapse_z163_v1.py`,
`two_adic_blocks_v1.py`, `pair_types_v1.py`, `max_union_v1.py`, `x5_two_odd_v1.py`,
`x4_sector_v1.py`, `phi_n_granularity_v1/v2.py`, `normalised_search_v1/v2.py`,
`lemma7_criterion_v1.py`, `prefix_bound_v1.py`, `exact_lr_check_v1.py`.

Every function on the mining import path was separately AST-checked and is
integer-only. Wall-clock timings are floats and are not results.

## 3. Reported ratios, restated exactly

Percentages were formatted from float division. The underlying counts are integers and
the comparisons are settled by cross-multiplication, with no decimal involved.

| statement | exact form | exact test |
|---|---|---|
| n=8 residual rate below n≤7 (strict) | `237/66044` vs `53/5517` | `237·5517 = 1 307 529 < 3 500 332 = 53·66044` ⟹ **lower** |
| n=8 residual rate below n≤7 (`δ=0`) | `253/69387` vs `83/8388` | `253·8388 = 2 122 164 < 5 759 121 = 83·69387` ⟹ **lower** |
| rate rises with the speed pool | `12/4122`, `59/19464`, `237/66044` | `12·19464 = 233 568 < 243 198 = 59·4122`; `59·66044 = 3 896 596 < 4 612 968 = 237·19464` ⟹ **strictly increasing** |
| in lowest terms | `2/687`, `59/19464`, `3/836` | |

The n≤7 comparison rate quoted as "0.961%" is `53/5517`; the per-`n` figures are
`2/623`, `28/2263`, `23/2631` at `n = 4,5,6`.

## 4. Standing rule adopted for this line

Exact integers or `Fraction` in anything that reaches a decision or a reported
quantity. Floats are permitted only for wall-clock timing and for a printed decimal
that sits beside its exact form. Ratio comparisons are settled by cross-multiplication.
`float_audit_v1.py` is the check; it is mechanical and should be re-run before any
result is written up.
