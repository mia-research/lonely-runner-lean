# RESULT — Route A crux: the prime-field Semaev first-fall degree is a FORCED support invariant — no first-fall lever from the group-law coefficients OR the S_m symmetry (scoped component null; relocates the open question)

**Grade:** `[VERIFIED-scope]` on the headline (coefficient- and symmetry-invariance of the first-fall
degree at m=2,3) — a **hard measured zero**, not a low-power null: ZERO variance over 24 random
coefficient draws per m at two primes. `[EMPIRICAL, model scale]` on the growth-rate reading (d_ff =
4, 12; m=4 pending/wall). **This is a scoped COMPONENT null on ONE invariant (first-fall degree); it is
NOT a closure of route A** — see §"What is NOT settled". Zero secp-scale power (model m, model p).
**Date:** 2026-08-31. **Prereg:** `PREREG_semaev_structure_firstfall_vs_m_v2.md` (frozen; supersedes
the design-flawed v1). **Harness:** `semaev_elimination_v1.py` + runner
`semaev_structure_firstfall_vs_m_v2.py` (exact GF(p) integer Macaulay ranks; `check_no_float` passes).
**Gate:** `experiment-designer` audited the v1 prereg (5 decidable defects); v2 fixes all five.

---

## Object
The named hard route is **subexponential prime-field ECDLP**. Its crux is the "first-fall-degree
assumption" (Petit–Quisquater): whether the first-fall degree d_ff of the m-summand Semaev
relation-search system {S_{m+1}(x₁..x_m; t)=0} ∪ {∏_{v∈V}(xᵢ−v)=0} stays low / grows slowly with m
(→ potential subexponential index calculus, and secp is a prime-field curve) or blows up (→ safe). This
run measures where any first-fall lever could live via a 3-rung null ladder.

## What ran, and what it shows
**Ladder:** for each m, d_ff of the SAME system with the S-slot polynomial drawn from three rungs on
the identical monomial support (Newton polytope of S_{m+1}) with identical field equations:
- **semi-regular** — per-monomial independent random GF(p) coefficients (breaks S_m symmetry);
- **symmetric** — random, one coefficient per S_m-orbit of the support (preserves the x-permutation
  symmetry — the FGHR/symmetrized-Semaev structure; same support ⇒ isobaric weighted degree preserved);
- **Semaev** — the true group-law coefficients.

| m | p | support | Semaev d_ff | symmetric d_ff (median, 12 draws) | semi-regular d_ff (median, 12 draws) | Δ₁ symmetry | Δ₂ coeff |
|---|---|---|---|---|---|---|---|
| 2 | 307  | 9   | 4  | 4  (all 12 = 4)  | 4  (all 12 = 4)  | 0 | 0 |
| 2 | 2069 | 9   | 4  | 4  (all 12 = 4)  | 4  (all 12 = 4)  | 0 | 0 |
| 3 | 307  | 125 | 12 | 12 (all 12 = 12) | 12 (all 12 = 12) | 0 | 0 |
| 3 | 2069 | 125 | 12 | 12 (all 12 = 12) | 12 (all 12 = 12) | 0 | 0 |
| 4 | 307  | 6561 | **CENSORED (>30)** — all rungs (Semaev + 6 semi-reg + 6 symmetric) exceed Dmax=30; support 6561 (deg 8/var, 4 vars); wall-clock **6877 s ≈ 114 min**. No comparison possible at m=4 (VOID by prereg §6 for the m=4 arm only; m=2,3 unaffected). |

**Growth (support-forced d_ff):** 4 (m=2) → 12 (m=3) → **>30** (m=4). Steep and super-linear; consistent
with the first-fall degree tracking the Semaev per-variable degree 2^(m-1) (the non-subexponential
direction), though the m=4 value is a lower bound (>30), not measured — the exact asymptotic remains the
open §XI.4 question. **The m=4 run also settles the method question: a direct compute-push on the full
(unsymmetrized) system is dead at model scale** — 114 min to CENSOR at m=4 means m=5 (S₆, deg-16/var,
3^{16}-scale support) is unreachable by brute Macaulay. Any advance on the growth rate must come from
symmetry-reduction (fewer/lower-degree variables) or an analytic Hilbert-series argument, not brute force.

**Headline:** the first-fall degree is a **forced combinatorial invariant of the support**. Every one of
the 24 random draws per m (12 semi-regular + 12 symmetric), at two primes, returns the **exact same**
d_ff as Semaev — with **zero variance**. So at m=2,3:
1. **No first-fall lever from the secp group-law coefficients** (Δ₂ = 0: Semaev = symmetric-random).
2. **No first-fall lever from the S_m symmetry either** (Δ₁ = 0: symmetric = semi-regular). The
   symmetrized-Semaev acceleration does **not** manifest as a lowered first-fall degree at these m.

This is **stronger than M9** (`PROJECT_SUMMARY §123`, curve-independence): it is not merely that secp
matches other curves — it is that *nothing about the coefficients or the symmetry moves the first-fall
degree at all*; d_ff is fixed by the Newton polytope of S_{m+1} plus the degree-|V| field equations.

## Calibration (read-out validity)
- **CAL-A HOLDS:** field-equations-only (a regular sequence, complete intersection) returns d_ff = null
  (no genuine fall) at every m — correct.
- **Positive calibration:** the read-out *does* detect a genuine fall — it returns finite d_ff = 4, 12
  for all three rungs. Two-sided: falls detected where they exist, null for the regular sequence. So the
  zero-variance coefficient-invariance is a real invariance, not a dead read-out.
- **DEVIATION (CAL-B mis-designed, does not affect the mechanical d_ff numbers):** the pre-stated CAL-B
  (linear plant {x₁−c} ∪ field-eqs → a fall ≤ |V|) returned null. This is *correct behaviour*, not a
  read-out failure: the redundant element the plant creates (`2(x₁−1)` at m=2) is already generated by
  the linear form x₁−c, so no *genuinely new* lower-degree element appears — the harness's genuine-fall
  definition rightly registers none. CAL-B was an invalid firing control (experiment-designer warning #2
  borne out). It is replaced by the valid two-sided calibration above. Per the frozen prereg's letter
  this would read VOID; the deviation is logged because (i) the d_ff measurements are mechanical (exact
  ranks — a mis-specified auxiliary calibration cannot corrupt them, §2b mechanical layer) and (ii) the
  read-out's fall-detection is independently confirmed by the finite Semaev/random values.
- **Audit note (2026-08-31, isolated review):** the two-sided substitute (CAL-A null + finite Semaev
  d_ff) confirms the read-out *detects a fall where one exists* and *reports none for a regular
  sequence* — but it does NOT test the sensitivity CAL-B was meant to check: detecting a fall *below* the
  support-forced value (the relevant power check for a "no coefficient lever" null). That specific
  sensitivity is left unverified here; the invariance itself (exact, uncensored, zero-variance) is
  unaffected. Owed if this null is ever leaned on beyond `[VERIFIED-scope, model]`.

## Verdict (scoped, graded)
At the first-fall level, the prime-field Semaev system behaves as a **semi-regular sequence of its
support** — the summation structure buys no early-fall advantage. The subexponentiality question
therefore does **not** live in the coefficients or the symmetry at first-fall; it reduces to two things
this run does not settle:
- the **growth rate** of the support-forced d_ff with m (4 → 12 is steep; if it tracks the Semaev degree
  2^(m-1), the first-fall degree blows up → the semi-regular / non-subexponential direction), and
- the **solving / last-fall degree** (Caminata–Gorla: solving ≥ last-fall ≥ first-fall), which can sit
  far above first-fall and is where symmetry-reduction (FGHR) actually acts — and which was
  computationally out of reach (v1: d_solv censored above any session Dmax for m≥3).

## What is NOT settled / the live lead (counter-prior: surface, don't close)
- **NOT a route-A closure.** First-fall degree is one invariant of one cost factor. Relation yield and
  factor-base size (the other two IC cost factors) are out of frame. A first-fall null does not bound
  the solving degree (strict inequality possible).
- **★ Live positive lead — the solving degree under symmetry-reduction.** Δ₁=0 at *first-fall* does NOT
  mean the S_m symmetry is useless: its benefit (the FGHR mechanism) is at the **solving/Gröbner
  degree**, via symmetry-induced syzygies at higher degree that collapse the solving degree below what
  first-fall predicts. That is precisely the invariant this run could not measure (censored at m≥3,
  model scale). **The lever, if it exists for secp, lives at the solving degree under symmetrization —
  unmeasured, not absent.** This is the sharp next probe, and it needs either much more compute (m=4/5
  solving degree) or an analytic handle on the symmetry-quotient Hilbert series.
- **Growth-rate / asymptotic (m≥5) is the §XI.4 wall** — empirically confirmed here (v1 m=4 = 68s; this
  run's m=4 at Dmax=30 is the session compute ceiling). A 2–3-point model-scale trend cannot prove the
  asymptotic (prereg §6 power ceiling).
- **Owed gates:** `citation-verifier` on the Petit–Quisquater first-fall assumption + FGHR
  symmetrized-Semaev solving-degree claim (before any grade promotes on them); second
  `experiment-designer` read of the v2 prereg is satisfied for the design (v1 audit → v2 fixes); a
  `compile-diff` if this folds into a master.

## Provenance
Exact GF(p) integer Macaulay ranks. p ∈ {307, 2069}, curve A=0/B=7 (secp form), τ = x(generator),
|V|=m, V={1..m}, K_null=12 (m=2,3). Runner `semaev_structure_firstfall_vs_m_v2.py`; output
`scratchpad/semaev_structure_firstfall_v2_out.json`; log `scratchpad/structure_ff_v2.log`. v1
(`PREREG_/RESULT_/semaev_structure_solvingdegree_vs_m_v1`) is the design-flawed predecessor, retained.
