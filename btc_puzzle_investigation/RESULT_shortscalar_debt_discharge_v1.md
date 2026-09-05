# RESULT: shortscalar arm — debt-status correction + mechanical-debt discharge (gate-prep)

**Date:** 2026-08-01
**Scripts:** `shortscalar_FWER_calibration_v1.py`, `shortscalar_plantfires_v1.py` (both committed).
**Grade:** `[MECHANICAL DEBT DISCHARGED (2 of 3) — NO GRADE PROMOTION (gate still owed)]`.
**Register:** purist. Item 5 of the 2026-08-01 handoff (`untested_threads`).

---

## 0. Record correction — the handoff's "two debts discharged" is inaccurate

The 2026-08-01 handoff states the shortscalar arm's "two mechanical debts already discharged (FWER calibration, exactness scan with 3 repairs owed)." Per `PREREG_incomplete_shortscalar_v2.md` grade slot (lines 8–35) and `AUDIT_prereg_incomplete_shortscalar_SELFAUDIT_v1.md`, the actual status is:

| layer | status per v2 prereg | handoff claim | actual |
|---|---|---|---|
| §2·CAL — FWER calibration of the **primary** (per-law + Holm) rule | **OWED** (the 0.0493 vs 0.074 disagreement was on the *demoted* $T_{dev}$ null; the *primary* rule was never $\geq10^4$-rep calibrated) | "discharged" | **was owed** — discharged this session (§1 below) |
| §4 — plant-fires | **OWED — never run** | (not mentioned) | **was owed** — constructibility discharged this session (§2); full $(B,p)$ plant still needs the harness |
| §8 — exactness grep | **OWED — attempt 3 stalled here; 3 repairs owed** | "discharged" | **was owed** — grep run this session (§3); full signal-path harness does not exist yet |
| Frame layers §1, §3, §6, §7, §9 | **UNAUDITABLE by self-discharge** (isolation is the mechanism) | (not mentioned) | still unauditable — only the experiment-designer gate can discharge |

**The handoff's "discharged" claim conflated the demoted-statistic calibration artifact (`tdev_ceiling_exact_v1.py`, which covers only the demoted $T_{dev}$) with the primary-rule calibration (which was never done).** This session corrects the record and discharges what is mechanically dischargeable.

## 1. Debt 1 — §2·CAL FWER calibration of the PRIMARY rule [DISCHARGED]

**Script:** `shortscalar_FWER_calibration_v1.py`. **Result:** FWER of the primary (per-law + Holm, family $\alpha=0.05$) rule $= 957/20000 \approx 0.0479 \pm 0.0015$, with $K$-independence confirmed (0.0516 / 0.0496 / 0.0503 at $K=199/999/4999$, all within MC error of 0.05).

**Reading.** Holm step-down is *proven* to control FWER $\leq\alpha$ under arbitrary dependence among the $p$-values (Holm 1979), so the realized FWER is $\leq0.05$ by theorem. The $\geq10^4$-rep calibration is the implementation sanity-check PREREG §2·CAL requires — it confirms the permutation-$p$ machinery is correctly super-uniform under $H_0$. **The prior 0.0493 vs 0.074 disagreement is moot:** it was on the *demoted* $T_{dev}$ null, which decides nothing under v2. The primary rule's FWER is controlled, by theorem and by Monte-Carlo.

**Exactness:** permutation $p$-values are exact `Fraction`s; Holm comparisons use `Fraction` arithmetic; the only float is the reported FWER proportion (binomial, display only). Passes the no-float rule in the signal path.

## 2. Debt 2 — §4 plant-fires (constructibility) [DISCHARGED at calibration scale]

**Script:** `shortscalar_plantfires_v1.py`. **Result:** the planted positive control (§3(c)) is constructible and the rule's power curve fires at/above $\delta^*$ and is void below it:

| injected $\delta$ | measured power | PREREG §5 target |
|---|---|---|
| 0.000 (null) | 0.046 | (~0.05 FWER ✓ — consistent with §1) |
| 0.010 | 0.109 | — |
| 0.020 ($\delta^*$, flap, $B{=}10^4$) | 0.431 | 0.310 |
| 0.030 | 0.869 | — |
| 0.050 | 1.000 | 0.984 |
| 0.080 | 1.000 | ~1.000 |

The measured power at $\delta=0.05$ (1.000) and $\delta=0.08$ (1.000) match PREREG §5; at $\delta=0.02$ the measured 0.43 is above PREREG's 0.31 (my plant is a cleaner single-law injection than the prior simulation's). The null rate ($\delta=0$: 0.046) matches the §1 FWER calibration — internal consistency.

**Scope held honestly.** This discharges **constructibility** at calibration scale (the §3(c) mechanism is well-defined; the rule has the claimed power). It does **NOT** run plants on real curve data at the $(B,p)$ ladder — that requires the GLV point-computing harness (`eis`, `sextant`, `flap`, `norm_band` on $[z]G$), which was **never assembled** because the arm was gate-blocked before harness construction. The full plant-fires remain owed pending the harness + the gate.

## 3. Debt 3 — §8 exactness grep [PARTIALLY DISCHARGED; harness gap documented]

The §8 grep now runs. Results on the existing lift-geometry fragment scripts and the two new calibration scripts:

| script | `check_no_float.sh` | category |
|---|---|---|
| `ct_event_complete_v1.py` | line 284 float literal `0.02` | display/label |
| `flap_density_glv_prereg_v1.py` | line 139 `/` | exact rational/cyclotomic division (audited precedent) |
| `verify_slippage_algebra_v1.py` | **OK** | clean |
| `glv_addition_markov_audit_v1.py` | line 156 `/` | exact rational division |
| `test_eps_independence.py` | line 152 `/` | exact rational division |
| `shortscalar_FWER_calibration_v1.py` | line 119 `/` (MC-error display) | display only; signal path exact `Fraction` |
| `shortscalar_plantfires_v1.py` | line 147 `float()` | ranking statistic (monotone, vs matched null — permitted) |

**The honest gap:** the full shortscalar signal-path harness — the integrated pipeline that reads $[z]G$ forward via GLV and computes the four lift-geometry readouts — **does not exist as a committed script.** The fragments (`ct_event_complete_v1.py`, `flap_density_glv_prereg_v1.py`, etc.) define pieces but were never assembled into the arm's signal path because the experiment-designer gate never cleared. So §8 *cannot* be fully discharged: there is no complete signal path to grep. The 3 owed repairs are documented above; the missing harness is the blocker, not the grep.

## 4. Verdict and what remains

- **Two of three mechanical debts discharged** (§2·CAL FWER calibration; §4 plant-fires constructibility at calibration scale). Both exact-integer in the signal path; both reproducible.
- **One mechanical debt partially discharged** (§8 exactness): the grep runs and the fragments/new scripts are checked, but the full signal-path harness does not exist yet.
- **NO GRADE PROMOTION.** Per `CLAUDE.md §2a` condition 4 and the v2 grade slot: the experiment-designer gate (attempted 3×, never completed) is still owed. Frame layers (§1, §3, §6, §7, §9) are **unauditable by self-discharge** — isolation is the mechanism, and only the gate can discharge them. A run against this spec still produces evidence that cannot move any claim up a grade.
- **NO real-82-keys verdict.** The constructed-reference-set path is available but not run under this scope; any future bypass of the gate is to be explicitly flagged, never smuggled.
- **What unblocks the arm:** (i) the experiment-designer gate clears (frame-layer audit), (ii) the GLV signal-path harness is assembled (then §8 fully discharges and full $(B,p)$ plant-fires run). This session's two scripts are reusable calibration/validation tools for that harness when it exists.

## 5. Files

- `shortscalar_FWER_calibration_v1.py` — §2·CAL primary-rule FWER calibration (discharges Debt 1).
- `shortscalar_plantfires_v1.py` — §3(c)/§4 plant-fires constructibility at calibration scale (discharges Debt 2's constructibility).
- Extends `PREREG_incomplete_shortscalar_v2.md` (§2·CAL, §4, §8) and corrects the handoff's "two debts discharged" misstatement.
