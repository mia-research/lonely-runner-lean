# RESULT: c-side `inv` pooled-tilt settlement (queue item C) — lead CLOSED as a candidate

**Date:** 2026-07-31
**Scripts:** `cside_pooled_tilt_settlement_v1.py`
**PREREG:** `PREREG_cside_pooled_tilt_settlement_v1.md` (FROZEN pre-data; SHA `e4a95ca3eaded16afd7ae14c84b9ca27c79b95020b0f46cba2c1e2931ae5d5e5`, recorded before the run)
**Grade: `[EMPIRICAL — SCOPED]`** for the per-prime `inv` family-wise null (retained from v1); **`[FLAGGED LEAD — CLOSED as a candidate]`** for the pooled `inv` tilt. **Not a closure of the channel** (per the counter-prior and §6 below: a candidate settle at $p\sim10^4$ is not an avenue verdict at $2^{128}$).
**Register:** purist.
**Verdict vs the pre-committed table (PREREG §9):** row 3 — calibrated $p\ge0.05$ **and** OOS fails ⇒ lead **closed as a candidate**; scoped null retained.

---

## 0. What was run, and why it was the named next step

v1 (`RESULT_cside_nonalgebraic_correlation_v1.md`) flagged a sub-detection **negative** bias of the orbit-level `inv`-map statistic $T_{\text{inv}}$ across 18 large primes: mean $z=-0.622$, 15/18 negative, Stouffer $z=-2.64$, surviving a calibration control. It was honest about the methodological defect: the pooled number rested on **z-deflation by a measured calibration std (0.793)** — z-inflation correction applied after the fact — and explicitly named the right tool ("Stouffer with a calibrated (permutation) pooled p-value rather than z-inflation", v1 §4). This run delivers exactly that, on 36 large primes, with an OOS replication gate. It is queue item C's next measurement step (`STRUCTURAL_IMPLICATIONS §8`; `NEXT_SESSION_PROMPT_2026-07-31_v1.md` step 1).

The one methodological fix (PREREG §3): replace z-deflation with an **empirical null of the pooled statistic itself** — draw one within-prime permutation index per prime, Stouffer-combine, repeat $B=10^5$ times. The per-prime under-dispersion ($\sigma_p\approx0.79$) enters **into** the pooled null automatically, so no post-hoc deflation is needed or applied.

## 1. The reduction (unchanged, recap)

$c[d]=\chi_2(y_{[d]G})$ is exactly constant on each $\mu_3$-orbit (GLV invariance $c(\lambda d)=c(d)$, forced). `inv` maps orbits to orbits. So $T_{\text{inv}}=\frac1{N_{\text{orb}}}\sum_r c_r c_{f(r)}$ is the orbit-level mean product, with effective sample size $=N_{\text{orb}}=(n-1)/3$, not $n$. Signal path exact (`twist_orbit_spectrum_run_v1.signal`); script passes `check_no_float.py` (v1's `cside_orbitlevel_v1.py` did not — it used bare `0.8`/`0.01` gate literals; the gate here uses integer comparisons `(4*norb)//5` and `ge*100<=R`).

## 2. Per-prime family-wise result — NULL at scale, with a firing control

36 large primes (p=10831…22807, 3620–7686 orbits). 30 cleared the 80%-agreement firing gate at the 1% tail (6 excluded — recorded, not hidden). Per-prime:
- **0 cells survive Bonferroni over the 30 included primes** (bar $|z|\gtrsim 3.5$); the largest is p=20959, $z=-2.82$ (one-sided $p\approx0.0024$ uncorrected, does not survive).
- The single cell flagged as "Bonferroni-significant" by the script's left-only criterion was p=19483 with $z=+3.14$ — a **positive** outlier, opposite sign to the negative lead; the recurring isolated-cell-pops pattern, not a finding.

⇒ Per-prime `inv` structure: NULL at scale, gate firing — consistent with v1.

## 3. Calibrated pooled result — the headline (the lead is closed)

- **$Z_{\text{pool}}(\text{inv})=-0.626$**, **calibrated one-sided (left) $p=0.265$** ($26451/10^5$). ⇒ **NULL** ($p\ge0.05$).
- For comparison only (non-decisional): the legacy 0.793-deflated $Z=-0.79$, and $Z_{\text{pool}}/0.793=-0.79$.
- Sign balance: **14/30 negative** (47%) — indistinguishable from a coin flip. v1 reported 15/18=83%; that does **not** reproduce.

**Decisive diagnostic (range split).** My 36-prime upward `nextprime` sample overlaps v1's 18. Splitting the 30 included primes at v1's top prime (p=15919):

| range | $N$ | mean $z$ | % negative | $Z_{\text{pool}}$ |
|---|---|---|---|---|
| v1 range ($p\le15919$) | 16 | **$+0.243$** | 37% | $+0.971$ |
| fresh range ($p>15919$) | 14 | $-0.211$ | 57% | $-0.791$ |
| all 30 | 30 | $+0.031$ | 47% | $+0.169$ |

**v1's own primes reproduce at mean $z=+0.24$ — the opposite sign** of v1's reported $-0.622$. With the calibrated (non-deflated) method, v1's tilt does not replicate even within its own range. The most economical reading: v1's $z=-2.64$ was an artifact of the z-inflation correction the record flagged as wrong; the calibrated pooled statistic on the same primes is null.

## 4. OOS

**7a — magnitude-blind SHA-256 hash-fold (K=2), PRIMARY:**
- fold 0 (17 primes): $Z_{\text{pool}}=+0.096$, $\text{cal}\,p=0.538$, 9/17 negative.
- fold 1 (19 primes): $Z_{\text{pool}}=-0.952$, $\text{cal}\,p=0.172$, 11/19 negative.
- **AND-gate replicate: FALSE** (sign flips between folds; neither fold significant). Textbook regression-to-noise.

**7b — fresh-seed retest of v1's 3 most-negative cells (characterization):**
- p=11503 $z=-2.34$, p=13147 $z=-1.80$, p=15607 $z=-2.08$ (fresh independent null seeds). These three *individually* stay negative — but they do not pool into a global tilt, and the largest (11503) did not replicate in its neighbors in v1 either (v1 §2). Isolated persistence of a few cells, not a population effect.

## 5. Secondary: the `pow7` sub-detection lead — surfaced, gate-checked, not promoted

PREREG §6 pre-committed that any pow-k hit goes through the same OOS gate before any grade moves. The secondary family surfaced **`pow7`: $Z_{\text{pool}}=-2.73$, $\text{cal}\,p_{2s}=0.0058$, Holm-significant over the secondary family (4 maps), 18/28 negative.** Per the pre-commitment, the same K=2 hash-fold OOS was applied:

- pow7 fold 0 (13 primes): $Z=-1.11$, $\text{cal}\,p=0.134$, 8/13 negative.
- pow7 fold 1 (15 primes): $Z=-2.70$, $\text{cal}\,p=0.0035$, 10/15 negative.
- **OOS replicate: FALSE** — one fold null, one significant; the classic one-lucky-subsample the AND-gate is designed to catch.

⇒ `pow7` is a **pooled-but-unreplicated sub-detection lead** — the same status v1's `inv` tilt held. The counter-prior is honored: surfaced (not buried), not promoted without the gate (P1–P3). pow5/pow11/pow13 all null (cal $p_{2s}\in[0.27,0.86]$).

## 6. Scope ceiling — what this does NOT close

- Regime $p\sim10^4$, orbits $\sim 3$–$8\times10^3$. This is **three orders of magnitude below** the puzzle's $\sqrt n\sim2^{128}$ threshold where complete-sum bounds go vacuous.
- "Lead closed as a candidate" means: *at the orbit level at $p\sim10^4$, the pooled `inv` tilt is consistent with noise.* It is **not** a statement that the c-side channel is inert at $2^{128}$.
- The operationally-decisive form — the **shortscalar arm at $2^{128}$** (`PREREG_incomplete_shortscalar_v2`) — remains **gate-blocked** (experiment-designer failed 3×) and is untouched here. No real-82-keys verdict is claimed or implied.
- Per the counter-prior: a clean scoped null is a valid result; "not found" is a failed search, never an absence. This settles one candidate lead; it does not close the avenue.

## 7. Files

- `PREREG_cside_pooled_tilt_settlement_v1.md` — frozen spec (SHA `e4a95ca3…`, recorded pre-data).
- `cside_pooled_tilt_settlement_v1.py` — the run; passes `check_no_float.py`.
- `cside_pooled_tilt_settlement_v1.json` — captured numbers (36 primes, per-prime $z$/ge/T, pooled calibrated counts, OOS folds, secondary family + OOS).
- Reference: `RESULT_cside_nonalgebraic_correlation_v1.md` (v1), `cside_orbitlevel_v1.py` (v1 test, superseded at the pooled-inference layer).

## 8. On the process

Pre-committed (PREREG §9), run against the frozen table, graded strictly. Two discipline notes:
- The `pow7` secondary hit was **not** in the original plan's focus; PREREG §6's symmetric-gate clause caught it. Adding the secondary OOS mid-run was a purely additive, deterministic change (the `inv` numbers are byte-identical to the first run); it did not alter any `inv` decision. Reported transparently rather than buried.
- Exactness: `check_no_float.py` passes on the script (an improvement over v1). The decision p-value is an exact integer count; float appears only in the ranked $z$-statistics, each marked `# noqa: float`.
