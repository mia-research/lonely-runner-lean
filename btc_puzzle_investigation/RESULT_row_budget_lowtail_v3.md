# RESULT v3 — frontier #17: the gate passes, Arm A issues its first verdict, A3′ confirms F11

*2026-07-25. Executes `PREREG_row_budget_lowtail_v3.md` (frozen pre-run). Deviations:
`PREREG_row_budget_lowtail_v3_DEVIATIONS.md` (D1 is load-bearing — read it).
Scripts: `row_budget_v3_run.py`, calibration `row_budget_v3_calib_v1/v2/v3.py`.
Data: `row_budget_v3_rows.json` (seeds `2026080x`, **uninformative — see D1**),
`row_budget_v3_rows_freshseed.json` (seeds `2026090x`, **the run**).
Predecessors: two abstentions, `RESULT_row_budget_lowtail_v1.md`, `_v2.md`.*

**No leakage, key-recovery or ECDLP claim. §XI.17 is NOT closed.** See §6.

---

## 1. Verdict

> **P-DET-A gate PASSES.** All four criteria, `C-SELFZ`, `C-DISP` and P-SIZE′ clauses (i)–(iii) pass.
> **Arm A issues a verdict for the first time in three specs** —
> `[EMPIRICAL — SEEN-DATA, CONTROL-REPAIRED]`, the maximum grade §0 allows.
>
> **Arm A3′ PASSES, including on its unseen subset** — F11's constant is confirmed and v2's
> "A3 FAILED" is superseded: the slope was the wrong instrument, not the wrong physics.

**This is not a closure.** The frontier's live question is unchanged and this run does not answer it.

## 2. ★ Correction carried from the spec: `RESULT_v2` §3 mis-states its own outcome

`PREREG_v3` §0b, recomputed from v2's own JSON (`row_budget_v3_calib_v3.py` Part A):

| clause | `RESULT_v2` §3 said | actual |
|---|---|---|
| `max\|z\| > 3` | fails at `211, 433` | **`211, 433, 19231`** — and `19231`'s `4.8889` is the **largest** |
| `frac\|z\|>2 > 0.10` | *"passes everywhere"*, `0.031…0.094` | **fails at `19231`** (`0.1406`); range `0.0312…0.1406` |

v2 concluded *"the null is calibrated, the criterion is not."* That is **true pooled and false
per-prime**. The pooled `sd = 1.019` it rested on is a **proxy**; the per-prime spread is the
**object** (`CLAUDE.md` §2b). §5 below shows the object was in fact deviant — and not where v2's
omission would have suggested.

## 3. Arm A — the verdict

Fresh-carrier run, `R = 64`, all 10 frozen primes, frozen frequency list hash-checked.

```
P-SIZE'  (i)  pooled |mean|  = 0.0128  <= 0.1186   PASS
         (ii) pooled |sd-1|  = 0.0308  <= 0.0839   PASS
         (iii)pooled max|z|  = 3.3838  <= 3.9440   PASS
         (iv) per-prime      : FAIL at p=2089 (sd = 0.7050)  -> O-A13 deflation, NOT a halt
criteria 1,2,3,4 : PASS      C-SELFZ : PASS      C-DISP : PASS
C-EQ-int = 0 exactly, all 10 primes;  C-BUDGET rel <= 1.2e-15
```

| `p` | 163 | 211 | 349 | 433 | 577 | 991 | 2089 | 4159 | 9319 | 19231 |
|---|---|---|---|---|---|---|---|---|---|---|
| `z` raw | 3.65 | 7.74 | 11.88 | 16.28 | 31.85 | 27.94 | 27.49 | 24.89 | 30.03 | 29.70 |
| `sd_p` | 1.039 | 1.075 | 1.045 | 0.834 | 1.026 | 1.012 | **0.705** | 0.796 | 0.899 | 1.106 |
| `z` used | — | — | — | — | — | — | **38.99** | — | — | — |

> **Pooled Stouffer `Z = +70.50` (raw, undeflated: `+66.87`), sign 10/10 positive.**
> Outcome cell **O-A1**: *H-ALIGN supported on seen data.*

⚠ **Flagged against myself: the O-A13 correction at `p=2089` INFLATED a verdict statistic**
(`27.49 → 38.99`), because `sd_p < 1` means the replicate spread *overstates* carrier variability.
The algebra is right and the rule was frozen before the run, but **a "correction" that strengthens the
result deserves more scrutiny than one that weakens it**, so both numbers are printed and the raw
pooled `Z = +66.87` is the one to quote if only one is quoted. Neither crosses any pre-registered
boundary.

**Grade, and what it is capped by.** `[EMPIRICAL — SEEN-DATA, CONTROL-REPAIRED; 10 model primes
163…19231, generic μ₆×conj stratum, `N_LOW` at `ρ<0.01`, nulls MN-μ6/MN-neg/MN-free]`. Arm A has **no
out-of-sample set and cannot acquire one** (§0, frozen curve list). This may not be reported as a
pre-registered discovery, and it does not upgrade either prior abstention.

## 4. Arm A3′ — F11 confirmed, with a consistent subleading offset

F11 ⟺ `C := (n−1)·layer = −0.4950`. Inverse-variance-weighted, `SE` measured in-run.

| draw | all 10 primes `[SEEN-DATA]` | **unseen `{211,349,577}`** `[confirmatory]` |
|---|---|---|
| seeds `2026080x` (D1) | `−0.5771 ± 0.0954` (0.86 SE) **PASS** | `−0.4117 ± 0.1278` (0.65 SE) **PASS** |
| seeds `2026090x` (the run) | `−0.7278 ± 0.0952` (2.45 SE) **PASS** | `−0.7459 ± 0.1278` (1.96 SE) **PASS** |

**Both draws pass on both arms, and the unseen subset is the one that counts.** The weighting does the
work the spec claimed: `433/577/349/211` carry 79% of the weight and `4159/9319/19231` together carry
`0.7%` — no prime was discarded by hand, which is exactly what made v2's post-hoc `p ≤ 991`
restriction inadmissible.

**Positive characterization, not a clean confirmation.** All four estimates land **more negative than
`−0.4950`**, by `0.6–2.5 SE`. F11 is graded `[PROVED to leading order]`, so a finite-`n` subleading
term is expected rather than surprising. **Named next object: the subleading correction to F11.**
Reported as a magnitude with its SE — not as a discrepancy and not as a confirmation beyond what two
draws support.

⇒ **v2's Arm A3 FAIL is superseded.** F11's prediction is **not** falsified; the log–log slope band was
underpowered by construction (≤3 usable points over <2 decades at any defensible `S/N` bar,
`row_budget_v3_calib_v1.py` Part 4).

## 5. ★ The instrument finding — and it is not the one v2's omission pointed at

The spec's D1 pre-committed a rule for `p=19231`'s `sd = 1.3679` before the fresh draw was read:
*structural, or a draw?*

> **Answer: a draw.** With fresh carriers `p=19231` returns `sd = 1.1059`, inside the band.
> The `m_p`-dependence hypothesis is **not** supported.

**But clause (iv) fired in both independent draws, at different primes and in opposite directions**
(`19231` at `1.368` high; `2089` at `0.705` low). Under a correct instrument that clause fires at
≥1 of 10 primes with probability **`0.0255`** (20 000 sims) — so 2 of 2 is `≈6.5×10⁻⁴`. Measured:

| | spread of the 10 `sd_p` |
|---|---|
| seeds `2026080x` | `0.1419` |
| seeds `2026090x` | `0.1359` |
| **expected under a correct instrument (`R=64`)** | **`0.0891`** |

> **The carrier-vs-replicate `z` scale is over-dispersed across primes by a factor ≈ 1.55,
> reproducibly, in both draws.** It is a **global mild mis-scaling, not a localized defect at one
> prime** — which is why v2's per-prime omission mattered and why its single-prime reading would have
> been the wrong lesson too.

**Magnitude and scope.** Typical per-prime scale error ≈ 14%. Arm A's pooled `Z ≈ +67` is far outside
anything 14% of scale can reach, so **the sign and the existence of the excess are not in question**;
what carries the extra uncertainty is each individual `z_p`. **Named next probe:** raise `R` (the
replicate spread is the suspect denominator, not the carrier) and re-measure the spread of `sd_p`
against `1/√(2(R−1))`. This is a characterization of the instrument, not a verdict about the frontier.

## 6. Status — what is and is not settled

- **§XI.17 remains OPEN.** The live question (v2 §1.4(iv)) is **unchanged**: does the character's own
  `d`-labelling give a different low-tail count from a `μ₆`-commuting relabelling, and which sub-layer
  (`λ` / `[−1]` / beyond) carries it? Arm A supports that a `char − MN-μ6` layer exists; **it does not
  decompose it.** The decomposition needs its own prereg.
- **`H-BUDGET` stays settled by algebra** (v2 §1.4(iii), `[PROVED]`): `Σ_a|U|² = n(n−1)` is Parseval
  for a unit-modulus sequence, carried identically by every arm, contributing exactly `0` to the
  contrast. **The frontier's original framing — "the one exact conservation no random-target null
  satisfies" — is accurate only about MC1/MC2, for which the constraint is vacuous, not violated.**
  This run does not revisit that and nothing here reopens it.
- **Arm B unchanged and descriptive** (O-B4; the D7 attestation does not exist). Not re-litigated.
- **Nothing transfers to `p = 2²⁵⁶−2³²−977`.** No ECDLP, extraction, key-recovery or security claim.
  `N_LOW` is a symmetric functional of one row profile at one frequency at one threshold in one fixed
  basis; **not projected onto:** which rows are low, the phases of `U` (only `|U|` enters), the
  autocorrelation, cross-frequency structure, thresholds other than `ρ<0.01`, and `p > 19231`.

## 7. On the process — the third spec, and the first that gated correctly

`RESULT_v2` §5 recorded the pattern: two frozen specs, two gate failures, **neither from the
instrument or the mathematics, both from pass-criterion calibration**, and both catchable by computing
each gate's false-failure rate in advance. v3 carried that computation as a mandatory section, and it
worked — but **not** by vindicating the plan:

- it **found two more mis-calibrated gates before the run** (criterion 5 at FFR `0.8228`; criterion 3's
  band at `0.10–0.15`), and rewrote both;
- it **cleared two gates v1/v2 had never justified** — `C-DISP` (FFR `0.00175` at the real
  `m_p ∈ [820, 26143]`; an earlier estimate using stand-in `m_p = 60…200` had wrongly alarmed at
  `0.50–0.88`) and `C-SELFZ` (`0.0267` / `0.0000`);
- it **caught a correction the predecessor RESULT had gotten wrong** (§2);
- and the run itself **caught my own deviation** (D1: reused seeds ⇒ the first execution's halt was a
  re-adjudication of seen data, carrying no information, and is **not** banked as a third abstention).

The pattern's diagnosis was right and the remedy is cheap. **Every future spec in this programme
should carry §5's gate-calibration table.** Two of the three defects it found this round were in gates
that had already *passed* a run.
