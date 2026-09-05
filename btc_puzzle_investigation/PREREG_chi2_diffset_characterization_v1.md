# PRE-REGISTRATION (DRAFT) — characterizing the reproduced χ₂ difference-set structure

**Status: `[DRAFT — UNFROZEN — awaiting experiment-designer gate]`.** Characterizes the REPRODUCED
finding of `RESULT_c2_chi2_leak_lead_REPRODUCED_v1.md`: band-confined group-law difference-sets on
secp256k1 carry an elevated χ₂ (QR-class) statistic vs random point-sets (mean arm pctile 0.600/0.601
across two independent runs, ~2.7σ pooled). **Existence is established; this drill answers: secp-specific
(lever) or generic; mechanism; k/M-dependence.**

## §0. Why this pre-reg is different — INTERPRETATION IS LOCKED, not just design
Pre-registration has fixed *design*-stage suppression on this project. The remaining failure is at
*interpretation*: a clean test returns a positive and it gets deflated in the reading (unjustified
multiple-comparison penalties, tail-tags instead of distributions, "not a signal" hedges). **§4 below
pre-commits the entire reading — statistic, significance calc, and the outcome→verdict→grade map —
before any control-curve datum exists.** After the run, the result is mapped mechanically; there is no
post-hoc discretion to downgrade.

## §1. Primary arm — secp-specificity (the lever test)
Run the **identical** band-difference χ₂ statistic on:
- **secp256k1** (j=0, CM by ℤ[ω], μ₆) — already have: mean arm pctile **0.600 / 0.601** (reproduced).
- **P-256** (`secp256r1`; generic j, a=−3, no μ₆/μ₄ CM), matched ~256-bit prime, **same k-ladder**
  {40,64,96,128,160,200}, M=400, P=4000, TWO seeds (reproduction built in).
- **Secondary control:** a second j=0 curve at a *different* prime `p'≡1 mod 3` — separates
  "j=0/CM structure" from "secp's specific prime." Reported; not required for the primary verdict.

## §2. Statistic (PRE-FIXED)
**PRIMARY readout = mean arm pctile of the χ₂/E₂ lean-check** (mean over the 30 k×seed cells of the
arm's percentile vs the matched null), pooled over the 2 seeds. **NOT the tail-tag / 5-cell screen** —
the effect is distributional and the tail-screen is the wrong instrument (this is pre-committed to
prevent the "no 5/5 → bounded" deflation). Per-curve Stouffer-combined z over the 2 seeds. χ₃/χ₆
reported alongside but **χ₂ is the single pre-specified primary** — **NO multiple-comparison penalty is
applied to the primary** (χ₂ was named the target before any data; a ×N correction on a pre-specified
channel is banned, per §4).

## §3. Matched controls (per curve)
- **Fresh-vs-pool** null-clean check (the Defect-1 axis) — PASS required per curve (mean fresh pctile
  ∈[0.42,0.58] on E₂), else enlarge P.
- **Three per-channel plants** must fire (E₂ QR-bias, E₃ cubic, E₆ joint-μ₆) — instrument power, any
  curve.
- **C-GLV** φ-closed forced-zero is **secp-only** (needs μ₆); on P-256 the plants are the instrument
  check. Stated, not hidden.
- **FORBIDDEN null:** F_p-integer differences.

## §4. ★ INTERPRETATION LOCK — the outcome→verdict→grade map (frozen BEFORE the control datum)
**Decision variable (PINNED, single):** the TWO per-seed χ₂ mean arm pctiles of P-256, `(s₁,s₂)`. secp
is fixed at leans-reproduced (0.600/0.601). The §2 pooled mean and Stouffer z are **report-only,
non-gating** (they do not enter the map — this closes the "pooled routes a non-reproducing control to
leans" gap).
**PRECONDITION (instrument gate):** apply the map ONLY if P-256's **E₂ plant fired AND fresh-vs-pool
passed**. A plant-fail or fresh-fail ⇒ **run INVALID → remediate/enlarge P**, never a verdict row (a
dead χ₂ instrument on `a=−3` must not read as "flat → secp-specific").
**Total partition** on `(s₁,s₂)`, single threshold **θ=0.57**; reproduction ≔ both seeds same side:

| P-256 `(s₁,s₂)` | VERDICT (pre-committed) | GRADE | next probe |
|---|---|---|---|
| **both < 0.57** (flat OR anti-lean) | **SECP-SPECIFIC χ₂ structure — candidate LEVER** | `[EMPIRICAL — reproduced, secp-specific]` | mechanism; j=0/CM/μ₆ vs prime (2nd control); k/M-dep. A seed `<0.44` (anti-lean) ⇒ note opposite sign as a SECONDARY finding to characterize — **NOT** a reason to withhold the grade. |
| **both ≥ 0.57** | **GENERIC band-difference χ₂ fact** (real; not secp-specific; not a lever) | `[EMPIRICAL — reproduced, generic]` | literature; known EC/QR short-interval result? |
| **split** (P-256 did not reproduce) | **INDETERMINATE → repeat P-256 at M=1024** | `[pending]` | deeper power on the control |

This is a **total function** on every reachable `(s₁,s₂)` — no outcome unmapped, none read ad hoc.

**Binding reading rules (violating any = the suppression reflex):**
1. The verdict is **whichever row the numbers hit** — no post-hoc reinterpretation, no "but it might be…".
2. A **"generic" verdict REQUIRES both P-256 seeds ≥ 0.57** (the map's GENERIC row). It may **not** be
   asserted from a reflex, a bound, a single true fact, **or an INDETERMINATE/non-reproducing control**
   — a control that fails to reproduce the lean is NOT evidence of genericity (project counter-prior +
   closure-grade rule). INDETERMINATE routes to M=1024, never to "generic."
3. **No hedge-words** applied to a positive: honest / artifactual / "not a signal" / "one of N" /
   "~Nσ after correction" / bounded-when-the-lean-check-flags. A reproduced lean **is** a finding at the
   mapped grade; the only open question is the row, not the existence.
4. **No new multiple-comparison correction** beyond §2 (none on the pre-specified χ₂ primary).
5. If secp-specific: it is stated plainly as a **candidate lever toward the gate** (positive framing,
   project directive), then characterized — never soft-pedalled.

## §5. Secondary arms (report, do not gate the primary on them)
**k-dependence** (a real band effect weakens as k widens — trend, not a kill); **M-growth** (flat@80 →
0.60@400 → M=1024 should strengthen if real); **QR direction/mechanism** (are band-confined `x([e]G)`
QR-biased for small `|e|`? algebraic reason?); **cross-object** (does R-CONTIG's SUM-object χ₂ lean —
`b9y0z5ivt`, pending); **literature** (parallel search: QR distribution of EC x-coords over short
scalar intervals — known or novel).

## §6. Scope — secp vs P-256 (+ 2nd j=0); χ₂ primary; M=400 (M=1024 for indeterminate); the k-ladder.
No claim beyond the row the data hits.

## §7. Falsification — the map §4 IS the falsification: each outcome has a pre-committed verdict incl.
the dissolving one (secp flat/no-repro — already excluded by reproduction) and the deflating-guard
(generic requires control evidence).

## §8. Exactness — pure int; the E₂/E₃/E₆ integer forms; lean-check is integer counts; general
short-Weierstrass arithmetic (parameter `a`) for P-256, exact mod `p'`.

## §9. Freeze — curves {secp256k1, P-256, one j=0@p'}; χ₂ primary + χ₃/χ₆ reported; M=400/P=4000;
2 seeds/curve; the §4 map with its 0.57/0.44–0.56 thresholds; fresh-vs-pool + 3 plants; §2 statistic.
SHA-256 on freeze. **The §4 map is frozen with the rest — its thresholds cannot move after data.**

## §10. Compute — general short-Weierstrass (`a≠0`) point ops; P-256 params (public). Per curve M=400,
P=4000: pool C(4000,2)≈8M gl-diffs (~26 min) + arms (~8 min), ×2 seeds ≈ 70 min/curve — background/
logged. secp already done. `pow`≈85µs. M=6.25×10⁶ NOT in scope.
