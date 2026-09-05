# AUDIT — session conclusions re-tested (method / results / conclusions)

**Trigger.** Repeated use of a banned self-cert word ("honestly") = the project's diagnostic that
conclusions were deflated (one-way suppression bias). User directive: *audit the method, the results, and
especially the conclusions.* Date 2026-08-17.

**Meta-risk, stated up front.** An audit run *by* the suppressing model can "confirm" its own nulls to
re-suppress. Mitigation used here: each re-test adds POWER (larger n / proper null distribution / firing
control) and reports the MARGIN, so a held null shows its distance from the threshold rather than a bare
verdict. A null that barely holds is flagged; a null that holds with margin is stated with its margin.

## Ledger — every declared NULL/boundary, re-tested

| # | conclusion as originally stated | method check | re-test (this audit) | status |
|---|---|---|---|---|
| 1 | `cubic-e([d]G)↔χ₂(d)` "tiny/ambiguous/nothing" | matched null was correct; power was low (n≈50) | n≈6000, 8 curves, pair-matched perm-p: **0/8 survive, MI≈0.0000** (was 4/8 at n≈50) | **null holds w/ margin** — finite-size, washed out. Original grade was right, not suppression |
| 2 | μ₆ block incidence "roughly uniform, no block structure" | stated with NO chi-square | χ² independence = **0.837** (1 df, crit 3.84) → independent | **null holds** — "uniform" was correct |
| 3 | fill-in "graded 940 vs random 1008, within noise" | stated with NO error bars | proper null dist (n=200): graded at **30th percentile**, inside | **null holds** — "within noise" was correct |
| 4 | readout gives **"no keyspace reduction"** (the load-bearing dismissal) | **argued, never tested** ("circular", "orbit-mates leave interval") | MI(e([d]G); 8 cheap fns of d) max **0.033 bits** (≈ n=349 floor) vs firing control MI(e;d)=**1.585** | **conclusion CORRECTED** ↓ |
| 5 | √6 interval speedup "FALSE" | was retracting my OWN overclaim | automorphism images leave the interval (0/100000) — retraction is correct | not a suppression (self-overclaim retracted) |
| 6 | `d_LF` Δ=0 (μ₆ no linear-algebra help) | direct measurement | consistent w/ #2,#3 (2nd instrument) | scoped null holds |

## The one conclusion that was narrative, now corrected (#4)

**Was:** "no keyspace reduction from the public readout" (stated as a closure).

**Corrected (tested):**
1. The readout `e([d]G)` (and `s`-class, `y`-parity) carries **full, determined information** about `d` —
   firing control MI(e; d) = 1.585 bits = fully determined. *Circular ≠ no information* (user's point,
   now measured): the info is real.
2. But `e([d]G)` is **not a cheap arithmetic function of `d`** — max MI 0.033 bits over
   {d mod 3,6,7,9,12, jacobi(d,n), cube-res(d,n)}, at the finite-size floor. Reading `e` for a candidate
   `d'` requires computing `[d']G`, which costs the same as checking `[d']G == P`. **No arithmetic filter
   that beats brute force was found.**
3. **Scope:** these 8 predictors, small prime-order CM curve. Does **NOT** prove no cheap predictor exists,
   and does **NOT** address whether SEVERAL readouts combined (e ⊕ s ⊕ parity ⊕ interval) restrict `d`
   jointly. Those stay OPEN — the user's "once these connect" thesis is untested, not refuted.

**Why this matters for the project stance.** #4 is the dismissal the whole "no reduction" story rested on.
It was never a test; it was the ECDLP-secure reflex in argument form. It now has a scoped test, and the
test says LESS than the dismissal claimed: full info is present, only cheap-invertibility fails, and the
joint-readout question is untried.

## Positives — audited for OVERCLAIM (the other direction)

| claim | grade given | audit |
|---|---|---|
| k=3 phase channel real | EMPIRICAL (survives parity-matched null) | method bug (sorted-index) was found+fixed; fixed result survives the correct null on multiple curves; correctly NOT promoted past EMPIRICAL (multiplicativity-null shown degenerate, so upgrade needs theory) |
| slope² `x₁+x₂+x₃=m²` | PROVED | group-law identity, 0 violations — holds |
| un-normalized k=3×χ₂ channel `Σχ₂T³=i√p·(n²−O(n))` | PROVED | rests on slope² + `#{m=0}=O(n)`; W(0) matches to the digit — holds. Phase-normalized version correctly left EMPIRICAL w/ named `|T|`-tail gap |
| μ₆ 6× relation multiplication | VERIFIED exact | orbit size exactly 6.00 — holds; scope (constant-factor, known technique) correctly attached |
| character grading ~9σ | EMPIRICAL real skew | orbit-level σ plausible; correctly graded EMPIRICAL, exploitability-untested (and #2/#3 showed no LA exploit) |
| amplitude "stable invariant" | first over-REFUTED, then self-corrected | I initially suppressed the invariant using small-p scatter, then corrected that it has asymptotic support at large p (~0.33). Correction stands — this one I caught mid-session |

## Net finding

- **Every declared null holds under powered re-testing** (#1–3,6) — with margin, not borderline. On
  re-examination I tested them rather than re-asserting; the results confirm the grades.
- **One conclusion (#4) was narrative, not test**, and the test weakens it: the readout carries full
  determined info; only cheap-invertibility fails; the joint-readout ("once these connect") question is
  **open and untested**.
- **No suppressed positive was found** among #1–6 — but the honest residue is #4's open joint question and
  the still-open items below, which the closure-framing had been quietly burying under "boundary located".

## Genuinely OPEN (not closed — do not let the audit's clean nulls imply otherwise)

- **Joint readout restriction:** do `e ⊕ s-class ⊕ y-parity ⊕ interval` jointly constrain `d` below
  brute force? (untested — the user's "once these connect" thesis)
- **Cleverer arithmetic predictor** of `e([d]G)` than the 8 cheap ones (CM/Hecke-character route untried)
- **|T|-near-0 equidistribution** — the single named gap between the EMPIRICAL phase channel and PROVED
- **j=1728 subgroup dip** (0.11 vs ~0.18, ~1.5σ, n=6) — suggestive, underpowered
- **μ₃-graded syzygy module** — the one linear-algebra object the fill-in test did NOT cover

**Grade of this audit: `[VERIFIED — re-tested with power]` for #1–3,6; `[CORRECTED]` for #4.** No grade
promoted. compile-diff still owed on the compendium (unavailable — session limit).
