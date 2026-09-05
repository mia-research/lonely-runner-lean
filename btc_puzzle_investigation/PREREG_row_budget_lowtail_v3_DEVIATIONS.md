# DEVIATIONS — `PREREG_row_budget_lowtail_v3.md`

Opened at the first deviation, per v3 §9. Every entry names the frozen text it departs from.

*(Recorded here first: **v2 never had a `_DEVIATIONS` file**, and v2's run did deviate — its RESULT §3
mis-states its own criterion-5 outcome. That gap is what v3 §0b documents.)*

---

## D1 — the first v3 execution reused v2's frozen RNG seeds. **My error, not the spec's.**

**Frozen text departed from:** none directly — v3 §4 requires P-SIZE′ to be evaluated on "the
unplanted carrier", and §0 lists v2's 640 carrier `z` as **SEEN**. The spec does not fix the seeds.

**What I did:** `row_budget_v3_run.py` (first execution, `row_budget_v3_rows.json`,
`row_budget_v3_run.log`) hard-coded `rngA = 20260801`, `rngB = 20260802` — v2's streams — with the
stated rationale *"so that the ladder is the same object"*.

**Why it is a deviation in substance.** Identical seeds ⇒ **identical carrier draws** ⇒ P-SIZE′ was
evaluated on the *same 640 `z`* v2 produced, which §0 declares SEEN and whose failure v3 §4 had
already **pre-declared** (`max|z| = 4.889 > 3.944`, clause (iv) at `p=19231`). Confirmed: the first
execution reproduced v2's per-prime `z` to the digit (`4.06, 7.46, 11.13, 17.28, 26.98, 28.77, 29.40,
31.23, 30.92, 33.10`).

> **Consequence: the first execution's P-SIZE′ HALT carries no information.** It is a
> re-adjudication of seen data under a repaired gate, not a test of the instrument. It must not be
> reported as a third abstention, and it does not discharge §7.

**What is unaffected.** A3′ is **not** touched by this: the per-frequency layer SE was never computed
by v1 or v2, so `layer_se_pct` is new information regardless of the seed, and the
`{211, 349, 577}` subset is unseen by §0 on its own terms.

**Remedy, executed:** `--seedA/--seedB` added; re-run with fresh streams
`A = 20260901`, `B = 20260902` → `row_budget_v3_rows_freshseed.json`,
`row_budget_v3_run_freshseed.log`. **No gate, bound, criterion or statistic was changed** — only the
draw. Both executions are retained and reported side by side.

**This is not post-hoc tuning, and the distinction is the point.** Changing a *gate* after seeing it
fire would be tuning. Drawing *fresh carriers* is what a negative control consumes; reusing spent
ones is the defect. The frozen bounds
(`0.1186 / 0.0839 / 3.9440 / 0.2673`) are unchanged and were computed before either execution.

**What the re-run decides, pre-committed here before reading it:** whether `p=19231`'s carrier spread
`sd = 1.3679` is **structural** (a property of the instrument at `m_p = 820`) or **a draw**.

- `sd` at `p=19231` again outside `1 ± 0.2673` ⇒ **structural**, the `m_p`-dependence is real, O-A13
  deflation governs, and the named next probe is raising `R` or `m_p` at the top primes.
- `sd` back inside the band ⇒ **it was a draw**; the v2/first-execution failure was a one-draw event
  and P-SIZE′ then adjudicates the arm on its own terms.

Either way the outcome is a **characterization of the instrument**, not a verdict about the frontier,
and §XI.17 stays open.

---

## D2 — A3′'s per-prime `σ_p` could not be pre-computed for the unseen subset

**Frozen text:** v3 §3.3 — *"`σ_p` at those primes was never printed, so its SE is measured in-run and
its power is reported post-hoc **as a scope statement, never as a verdict-strengthener**."*

**Status: not a departure — the spec anticipated this and it is recorded only for completeness.**
The `{211, 349, 577}` SEs came out of the run (`0.1452, 0.0688, 0.0312` % of REF-RAY). They are
reported as scope. **No power claim is attached to the A3′ confirmatory result.**
