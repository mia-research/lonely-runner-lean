# RESULT — Sy sign-skew: CONFIRMED real, but curve-generic (not secp-special, not a leak)

**Date:** 2026-07-18. Executes `PREREG_Sy_sign_skew_v1.md` (committed before any computation).
Script `_sy_skew_test_v1.py`. Read strictly against the pre-registered decision rules.

## Outcome, per the committed rules

`Sy(p) = Σ_{P≠O} s_y(P)χ₂(y_P)` on `y²=x³+7`, sample = `p∈[10000,40000)`, `p≡1 mod 6`, `p≡3 mod 4`,
`n` prime (**82 primes**, fresh — the audit only looked at `p<10000`; 663 skipped for `n` composite,
reported).

| test | result | rule |
|---|---|---|
| **S1 sign lean (PRIMARY)** | `k/M = 58/82 = 0.707`, two-sided binom **p = 2.2e-4** | `< 0.01` ⇒ **CONFIRM** |
| S3 `6\|Sy` (bug-check) | True (all) | must hold ✓ |
| convention flip | flipped `k = 24 = 82−58` (exact mirror) | must mirror ✓ (no free knob) |
| **C2 shuffle null** | null `k`: mean 41, central-90% `[33,48]`; observed **58 OUTSIDE** | calibrates ✓ |
| **C1 random-b (deck-check)** | see below | decides curve-generic vs b-specific |

**C1 — the control that would have caught self-deception:**
```
b= 1: 48/82 =0.585 (p=0.15)     b= 2: 52/82 =0.634 (p=0.020)
b= 3: 57/80 =0.713 (p=1.8e-4)   b= 5: 52/82 =0.634 (p=0.020)
b=11: 55/82 =0.671 (p=0.0026)   b=13: 60/82 =0.732 (p=3.2e-5)
b=17: 43/82 =0.524 (p=0.74)     b= 7: 58/82 =0.707 (p=2.2e-4)   <-- the curve
```
The lean appears for most `b`; **`b=3` and `b=13` lean MORE than `b=7`. `b=7` is unremarkable.**

## Verdict (the pre-registered branch that fired)

*"S1 `p<0.01` AND C2 calibrates AND C1 shows curve-generic ⇒ skew CONFIRMED, curve-generic (H2);
scoped fact about `Σ s_y χ₂`, tied to lower-half `χ₂` distribution. NOT a leak."*

- **The skew is REAL** (out-of-sample, `p=2.2e-4`, outside the shuffle null, convention-robust).
- **It is CURVE-GENERIC** — a property of `Σ s_y(P)χ₂(y_P)` over elliptic curves `y²=x³+b`, driven by
  the base field `F_p` (the lower-half `χ₂` distribution, the same excess-of-QRs-in-(0,p/2) that the
  `h(−p)` class-number formula measures for `p≡3 mod 4`). **`b=7` / secp carries no special role.**
- **It is NOT a leak** — `Sy` is an x/y character sum inside the Part V bound; and being curve-generic,
  it says nothing about secp specifically.
- It is **not** an exact `h(−p)` identity: `Sy` takes both signs (24/82 negative), while `h(−p)>0`
  always. So the connection is distributional (the lean), not `Sy = c·h(−p)`. That over-tidy
  hypothesis is **rejected by the data**, not entertained.

## What was NOT concluded (exploratory, Holm-flagged, not claimed)

C1 hints `b≡1 mod 8` (`b=1,17`) may lean less — **post-hoc, not pre-registered, not claimed.** If
pursued it needs its own pre-registration. Recorded only so it is not silently rediscovered as "new".

## Why this is not deck-stacked

Every free choice was fixed in `PREREG_Sy_sign_skew_v1.md` before computing: the sample range, the one
primary statistic and its α, the sign convention (with a mandatory mirror-check), the single
explanatory hypothesis, and — decisively — the random-`b` control **whose whole purpose is to fire if
`b=7` looked special when it isn't.** It didn't look special. The result is a confirmed-but-mundane
fact, which is the outcome a fair test was always most likely to give, and it is reported as such
without inflation.

*(Resolves the open item flagged in `AUDIT_negative_bias_session2to4_v1.md`. Corrects the audit's
"generic" only in that `Sy`'s lean is a real, characterized bias — but a curve-generic one, so the
audit's leakage-neutral conclusion stands.)*
