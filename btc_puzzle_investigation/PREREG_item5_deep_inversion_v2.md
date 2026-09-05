# PRE-REGISTRATION v2 — Item 5 deep run (supersedes v1 after a VOIDED adjudication)

**Written after `VOID_item5_k128_adjudication_v1.md`, before any unread arm is inspected. Frozen.**
`experiment-designer` gate: **OWED, not run.** No grade promotion until it clears.

## 0. Why v2 exists

v1's `C-NULLSD` used **500 shuffles** to police a **2% threshold**. The sd of an sd estimated from
`R` shuffles has relative error `≈ 1/√(2R)` = **3.2% at R = 500** — so v1's control could not
distinguish a correctly-scaled null from a 2%-mis-scaled one, and would false-alarm routinely. **The
control was under-powered by construction.** That is a design defect in v1, and it voids v1's
adjudication rather than excusing it.

## 1. Corrected control

**`C-NULLSD`: R = 50 000 explicit shuffles** on a 400k subsample.
Estimator precision `1/√(2R)` = **0.32%**, giving ~6σ of headroom against a 2% threshold.

> **Rule (frozen): if analytic sd and empirical sd disagree by >2%, the run is VOID — and this time
> the control has the precision to mean it.** No post-hoc reinterpretation of this rule is admissible.
> If it fires, the correct response is a v3 that states the new defect, not an argument.

Pre-declared sanity check, to be reported whichever way it goes: at R = 50 000 the *expected*
sampling deviation is 0.32%, so a passing run should land well inside 2%; a run landing between 1%
and 2% is passing-but-flagged and must be reported as such.

## 2. Unchanged from v1

Object, arms, `M = 6.25×10⁶`, statistic `S` two-sided, analytic permutation moments
`E[S] = (Σa)(Σb)/M`, `Var[S] = [Σ(aᵢ−ā)²][Σ(bᵢ−b̄)²]/(M−1)`, **FIRE = |z| ≥ 3.0**, claim requires
**|z| ≥ 3.4** (Bonferroni/4), OOS replication on 5 reserved seeds before naming anything,
C-BALANCE / C-DUP / C-FIX / C-PLANT as specified in v1 §4.

## 3. Arm status, declared now

| arm | status |
|---|---|
| k=128 | **CONTAMINATED** — outcome known before this spec was written. May be reported only with that label; cannot carry a claim. |
| k=135 | clean, unread |
| k=160 | clean, unread |
| full-range control | clean, unread |

## 4. Self-audit — what v2 still does not cover

- The v1 self-audit carries over verbatim (object/disjointness unaudited; single readout and single
  map; `|z|` has no power against variance-only or higher-order structure).
- **New:** v2 fixes only the control that failed. The other four controls were never stress-tested
  for their own power; C-DUP, C-FIX and C-BALANCE are exact counts and need none, but **C-PLANT's
  dilution curve is estimated from a single realisation per fraction** and carries its own sampling
  error, which is not quantified here.
