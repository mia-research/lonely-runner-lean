# RESULT — P1″ INCONCLUSIVE: instrument bug caught, then the pre-registered statistic found to SATURATE. The b=1-artifact question is NOT answered; the design is degenerate and needs R1's per-target statistic.

**Date:** 2026-08-14. Executes `PREREG_semaev_cross_twist_yield_P1pp_v1.md`. **Grade:** `[INCONCLUSIVE — two
instrument/design defects, neither foreseen by the same-model gate; caught only by running + controls +
diagnostics].` No verdict on the object question. Scripts: `p1pp_run.py`. Model-scale; no secp claim.

---

## 1. Defect A — a=0 summation polynomial applied to non-CM curves (CAUGHT, fixed)

First run reported PRIMARY W = **37/37** and every per-twist 37/37 — CM out-yielding non-CM at *every*
prime and *every* twist, perfectly. **The perfection was the tell** (a real statistical effect is not
222/222). Cause: `S3coeffs` used the `a=0` Semaev polynomial, but non-CM curves have `a≠0`; the wrong
polynomial starved `Q_nonCM`. My original S₄ validation only covered a=0 curves, so it missed it. **Fixed**
(general `a,b` S₃) and **re-validated against exact point-enumeration on both a=0 and a≠0 curves** (8/8 match).
The buggy 37/37 is discarded. *(R1's own Sage/Macaulay instrument is a≠0-correct and is unaffected; my
earlier direct-point-enumeration sanity is also a≠0-correct.)*

## 2. Defect B — the pre-registered statistic `Q_total` SATURATES (design-degenerate)

Corrected run, N=37 primes: PRIMARY W = 8/37 (no reject), k=0 = **0/37**, all per-twist far below ½,
phase R = −0.007 (null), **C4 = 10/37, p=0.0038 → matching biased → distrust primary** (pre-committed rule).
Diagnostic dump explains all of it:

| prime | Q values (CM & non-CM, all twists) |
|---|---|
| p=523 | Qcm `[719,762,761,732,761,762]`, Qnc `[762,762,762,746,762,762]` |
| p=769 | 40 non-CM curves: **Q ∈ [732, 762]** (range 30), `Spearman(Q_total,#E)=+0.62` |

**`Q_total = Σ_{all targets} #{triples with S₄=0}` saturates at ~762 for essentially every curve.** Because
`P₁±P₂±P₃` is *always* on-curve, each of the `|V|³=216` triples reaches ~3.5 distinct valid targets, so the
total is pinned near the combinatorial ceiling `|V|³ × multiplicity`, ~curve-independent. There is no
dynamic range for a yield signal. C4 fires because the only residual variation is a weak #E correlation.
`k=0 = 0/37` is a **saturation edge-effect** (b=1 sits a hair below the ceiling), NOT real CM<nonCM.

The pre-reg §1 flagged the `|V|³/#E` confound but claimed #E-matching removes it; it **missed that the total
saturates** (the `|V|³·mult` term is not merely an #E confound — it is the dominant, ceiling-pinned term).
The same-model `experiment-designer` gate did not catch this — consistent with the standing note that these
gates catch mechanical/frame defects, not every design pathology; **running caught it.**

## 3. Status of the object question (UNANSWERED — not closed)

Whether R1's CM yield excess is a general μ₆ effect or a b=1 artifact is **NOT answered.** Both a valid
instrument (Defect A) and a non-degenerate statistic (Defect B) are prerequisites, and only A is now fixed.
Nothing here supports OR refutes the b=1-artifact hypothesis. Per the counter-prior this is a failed test,
not evidence of absence.

## 4. What a correct P1″ needs (redesign, re-pre-register)

- **Statistic with dynamic range:** R1's own object — per-target yield on a fixed set of *decomposable*
  targets (or the Macaulay-matrix `quo`), NOT the all-target total. That is where R1 saw the 2.3× and where
  a twist dependence could live. (My independent direct-enumeration sanity, |V|=5, showed CM>nonCM on 5/6
  primes — a non-saturated setup; the all-target total was the wrong aggregation.)
- **Unbiased #E-matching** so C4 is clean (or match on exactly-equal #E where the six-twist / non-CM #E
  values coincide).
- Keep the twist-axis `B_k` machinery (validated) and the decorrelation gate (passed, +0.003).

## 5. What worked (process note)

The two defects were caught by **suspicion of a too-clean positive** → validate on the breaking case
(Defect A), and by **a firing control (C4) + a diagnostic dump** (Defect B). The instrument was never
trusted on its headline; both times the check, not the number, decided. Recorded so the redesign starts
from R1's statistic, not the all-target total.
