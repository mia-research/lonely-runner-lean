# RESULT — the `E₆` control debt is DISCHARGED; item C.2 unblocked; one new caveat on the field `E₃` null

**Date:** 2026-08-01. **Script:** `interval_cneg_recalibration_v1.py` (+ `.log`). Passes `check_no_float.py`.
**Item:** standing repair D + item C.3 of `NEXT_SESSION_PROMPT_2026-08-01_v2.md` (BLOCKING for C.2).
**Grade: `[VERIFIED — control recalibration, exact integer ranks, 20 independent draws per arm]`.**
**This is a control recalibration, not a leakage test.** No arm number and no `k`-interval was read;
nothing here can produce a positive finding, and none is claimed.

---

## 1. The debt

`RESULT_interval_multireadout_v2.md` §91–108: `C-NEG` as specified is **one draw** tested against a
quantile, so under a correct null it false-alarms 5 % of the time at the 95th. An `E₆ = 65101`
reading at the **99.7th percentile** was flagged on the GROUP arm — one draw among six control
readings (2 arms × 3 statistics), for which `P(≥1 above 99.7 %) ≈ 1.8 %`. It blocked reading
`χ₂`/`χ₆` on the group-law difference (item C.2, never run).

## 2. Result — 20 independent draws per arm, `R_null = 3000`

Readout pre-committed before running: `#above 95th` and `#above 99th` out of 20. Under a correct
null `#above-95th ~ Binomial(20, 0.05)`, so 0–3 is unremarkable, ≥5 indicates mis-calibration.
**All ranks are exact integer counts** (`100·rank ≥ 95·R_null`), no float threshold.

| arm | statistic | above 95th | above 99th | median rank | verdict |
|---|---|---|---|---|---|
| **group** | `E₂` | 1/20 | 0/20 | 1598/3000 | CALIBRATED |
| **group** | `E₃` | 1/20 | 0/20 | 1116/3000 | CALIBRATED |
| **group** | **`E₆`** | **1/20** | **0/20** | 1650/3000 | **CALIBRATED** |
| field | `E₂` | 1/20 | 0/20 | 1187/3000 | CALIBRATED |
| field | **`E₃`** | **4/20** | 0/20 | 1871/3000 | **borderline — see §4** |
| field | `E₆` | 0/20 | 0/20 | 1887/3000 | CALIBRATED |

## 3. Discharge

> **The `E₆ = 99.7` flag does not reproduce.** Over 20 fresh draws, group `E₆` is above the 95th
> once and above the 99th **zero** times; field `E₆` is above the 95th **zero** times. It was a
> single-draw artifact of exactly the kind the one-draw `C-NEG` specification produces.
>
> **⇒ `χ₂` and `χ₆` on the group-law difference (item C.2) are UNBLOCKED.**

This is the second time the repaired control has overturned a one-draw reading (the first: the
spectral run voided at 96.0, then 0/20 above the 95th). The `n ≥ 20` repair is now carrying its own
weight and should be treated as the standing specification for `C-NEG`, not an option.

## 4. ⚠ NEW — the field `E₃` null is borderline, and `E₃` is the DECIDING statistic

Field `E₃` sits above the 95th on **4 of 20** draws. Under `Binomial(20, 0.05)`, `P(≥4) ≈ 1.6 %`.
Not a firing control and **not** grounds to void anything: 0/20 above the 99th, and the fire
threshold used in the multireadout runs is the **99th**, where the calibration is clean.

But it is recorded, for two reasons. `E₃` is the statistic that **decides** in
`interval_multireadout_v3.py` (`fl = " FIRE" if e[1] >= q["E3"][2]`), and a mildly under-dispersed
null there is **anti-conservative** — it would make field-arm `E₃` readings slightly too easy to
fire, i.e. it biases toward false positives, the direction that matters. `RESULT_interval_multireadout_v2.md`
§123 checked pool dispersion for `E₃` and found *"ratio of 99th percentiles 0.96, no material
under-dispersion"* — consistent with this, since the effect here is at the 95th and not the 99th.

**Action:** not blocking. Re-check with `n ≥ 40` draws if any field-arm `E₃` result is ever read near
threshold. Do not read a field `E₃` fire between the 95th and 99th without that recheck.

## 5. Also recorded — a pre-existing float-guard failure in the instrument of record

`check_no_float.py` **fails on `interval_multireadout_v3.py`** (lines 166–169: quantile indices
`int(.95*R)`, `int(.99*R)`, and `100.0*…/…` in the percentile print). CLAUDE.md requires the guard to
pass *before any leakage test is run in this line* — so the prior interval runs were made with a
script that does not pass it.

**Assessed, not alarmed:** the signal path (`stats`, `counts_of`, `counts_from_table`) is integer
throughout; the floats are confined to quantile-index selection and printing, and at `R = 3000`,
`int(.95*3000) = 2850` exactly. **No prior interval number is affected.**

`interval_multireadout_v3.py` was deliberately **left unmodified** so the runs already on the record
stay reproducible against the exact instrument that produced them. This file is the record of the
condition; a successor instrument should use exact integer ranks as
`interval_cneg_recalibration_v1.py` does.

## 6. What is next on item C — and what it needs first

Now unblocked, in the prompt's order:
1. **The swap-invariant SUM object `x(Pᵢ + Pⱼ)`** — the readout axis that actually exists. On a
   negation-closed index set every odd character is ill-posed/zero, but the sum-set is swap-invariant
   so the **full `χ₂`/`χ₃`/`χ₆` family is legal** there. Never run.
2. **`χ₂` and `χ₆` on the group-law difference** — legal (`x(−Q) = x(Q)`), never read because the run
   mis-tagged them `[parity-void]`. **Unblocked by §3.**

**Both are leakage tests and therefore require `experiment-designer` pre-registration before running
(CLAUDE.md §2). Not yet written.** Standing repairs to carry into that spec: `C-NEG` at `n ≥ 20`
(§3); check readout parity × index-set parity before running; measure `pow` cost before sizing;
precompute the pool difference table; never pipe a long run through `tail`; OOS retest before naming.
