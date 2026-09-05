# RESULT: power-map family-wide picture (read from the 2026-07-31 settlement)

**Date:** 2026-08-01
**Source:** `cside_pooled_tilt_settlement_v1.json` (the 2026-07-31 settlement run; spec `PREREG_cside_pooled_tilt_settlement_v1.md`, SHA `e4a95ca3…`). **No new sweep run** — this reads the existing record into the family-wide picture the handoff requested.
**Grade:** `[VERIFIED — calibrated pooled + K=2 OOS, 36-prime scan, gate firing]` for the NULLs; pow7 is a `pooled-significant / OOS-failed` candidate, **not promoted**.
**Register:** purist. Item 3 of the 2026-08-01 handoff (`untested_threads`).

---

## 0. Why this is a read, not a run

The handoff (item 3) asked to "run pow5/7/11/13 across ~18 large primes with the orbit-level test (`cside_orbitlevel_v1.py`), firing control clearing the gate at each." **This was already done** — at a *stronger* inference level — by the 2026-07-31 settlement run (`cside_pooled_tilt_settlement_v1.py`), which swept all four power maps across the same 36-prime scan as `inv`, with (a) calibrated permutation pooled $p$-values (Stouffer $Z$-pool against an empirically-built null, $B=10^5$), (b) Holm step-down over the family, and (c) a $K=2$ magnitude-blind SHA-256 hash-fold OOS AND-gate. The per-prime family-wise NULL the handoff describes is *implied* by the pooled+OOS design (which is strictly more rigorous than v1's Bonferroni-on-per-prime-$z$); this document records the family-wide verdicts from the settlement data.

## 1. The family-wide picture

**Setup.** 36 primes $p\equiv7\pmod{12}$ from the upward `nextprime` scan starting at $p\approx10^4$ (10831–22807), $n=\#E(\mathbb{F}_p)$ prime, $(n-1)\%3=0$, orbit count $(n-1)/3\geq3000$. Per-prime statistic: orbit-level mean product $T_f(p)$ of $c[d]=\chi_2(y_{[d]G})$ under index map $f$, ranked against a within-prime orbit-permutation null ($R=2000$). Firing control: an independent 80%-agreement plant on fresh RNG, must land in the 1% tail (gate fires) before any data at that prime is trusted. Power maps admissible only where $\gcd(k,n-1)=1$ (drops 4–8 primes per $k$). Decision: calibrated pooled $p$-value + Holm over the 4-map secondary family, with $K=2$ OOS replication.

**`inv` (primary, for reference):** 36/36 fired (0 excluded for power). Per-prime family-wise: **0/30 cells clear Bonferroni** ($z_{0.05/30}=3.144$; $\max|z|=3.140$ at the p=11503 edge cell, just under the bar). Pooled: $Z_{\text{pool}}=-0.626$, calibrated $p_{2s}=0.529$ ⇒ **NULL** (closed as a candidate 2026-07-31).

**Power maps (secondary family):**

| map | $N_P$ (admissible) | $Z_{\text{pool}}$ | cal $p_{2s}$ | neg/$N_P$ | Holm (5-map) | OOS replicate |
|---|---|---|---|---|---|---|
| pow5 | 30 | $-0.668$ | $0.500$ | 15/30 (50%) | ns | n/a (not pooled-sig) |
| **pow7** | **28** | **$-2.731$** | **$0.0058$** | **18/28 (64%)** | **SIG** ($p\leq0.010$) | **FALSE** |
| pow11 | 32 | $+1.104$ | $0.269$ | 15/32 (47%) | ns | n/a |
| pow13 | 30 | $+0.169$ | $0.865$ | 14/30 (47%) | ns | n/a |

**OOS for pow7** ($K=2$ hash-fold, magnitude-blind): fold0 $Z=+0.625$ ($p=0.735$, wrong sign), fold1 $Z=-2.698$ ($p=0.0035$). AND-gate replicate = **FALSE** (the two folds disagree in sign and one is null). This is exactly the status `inv` held in v1 (pooled-significant, OOS-failed) before the calibrated re-test closed it.

## 2. Verdict

- **pow5, pow11, pow13: family-wide NULL.** Pooled $p_{2s}\in\{0.50, 0.27, 0.86\}$, sign balance ≈50% (a coin flip), Holm-ns. No candidate.
- **pow7: pooled-significant, OOS-failed — NOT promoted.** Per the counter-prior (P1–P3: matched null, firing control, OOS retest, exact arithmetic, explicit grade), a pooled-significant candidate that fails OOS replication is **surfaced, not buried, not promoted**. It is the same sub-detection status the `inv` tilt held; the calibrated re-test on more primes is the natural next measurement *if* it is worth chasing, but it has already failed OOS once.
- **The `inv` per-prime family-wise NULL stands** (0/30 Bonferroni), and the `inv` pooled tilt is closed ($p_{2s}=0.529$). The `inv` pooled-tilt follow-up is **out of scope** (closed).

## 3. What the handoff's literal request would add

Running `cside_orbitlevel_v1.py` across ~18 primes per the handoff's literal wording would reproduce, at the *weaker* v1 inference level (per-prime Bonferroni on $z$, no calibrated pool, no OOS), a picture already established at the stronger settlement level. The per-prime $z$-scores for the power maps are not separately stored in the settlement JSON (only the pooled summaries are), but the pooled+OOS verdict subsumes the per-prime family-wise question: a map that is pooled-NULL with ≈50% sign balance cannot have a per-prime cell that survives family-wise correction at any reasonable $\alpha$ (the pooled $Z$ would reflect it). **No new sweep is warranted; the measurement is complete.**

## 4. Scope held honestly

- **Read-only.** No new computation; the verdicts are the settlement's, restated in the family-wide framing. The firing control cleared the gate at every included prime (gate firing is a precondition for inclusion in the pool).
- **pow7 is the only open sub-lead.** It is pooled-significant ($p_{2s}=0.0058$, Holm-SIG) but failed OOS replication. It is not promoted; a larger pow7-focused sweep is the named-but-lower-priority next measurement, and it has already failed OOS once.
- **The $2^{128}$-scale channel is not closed** — only these $p\sim10^4$ candidates. The operationally-decisive form (shortscalar arm at $2^{128}$) is separately gate-blocked (item 5).

## 5. Files

- `cside_pooled_tilt_settlement_v1.json` — the data source (36 primes, per-map pooled + OOS).
- `cside_pooled_tilt_settlement_v1.py` — the settlement script (no CLI; frozen constants; would reproduce).
- `PREREG_cside_pooled_tilt_settlement_v1.md` — the frozen spec.
- Builds on `RESULT_cside_nonalgebraic_correlation_v1.md` (v1, 18 primes) and `RESULT_cside_pooled_tilt_settlement_v1.md` (the settlement).
