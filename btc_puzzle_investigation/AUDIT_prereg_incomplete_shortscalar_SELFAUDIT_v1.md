# SELF-AUDIT (interim) — `PREREG_incomplete_shortscalar_v1.md`, decision-statistic layer only

*2026-07-29. **THIS IS NOT THE GATE.** `experiment-designer` was launched twice and failed both times
(§0). This is a self-audit: no context isolation, which CLAUDE.md §2b names as the mechanism rather
than care. It does **not** discharge the mandatory pre-data audit. **ARMS REMAIN HELD.***

---

## §0 — Gate status: two failed launches, no artifact

| attempt | outcome |
|---|---|
| 1 | terminated: *"Your organization has disabled Claude subscription access for Claude Code"* |
| 2 | terminated: *"You've hit your weekly limit · resets 3am (Australia/Brisbane)"* — 3 tool calls in, partial output only |

Per this record's own precedent with the three failed `citation-verifier` runs: **a run that did not
complete is a run that did not happen, not a run that passed.** The gate must be re-run before any
arm executes.

**Coverage of this self-audit:** §1 (object), §2 (statistic), §5 (power) of the spec, read directly.
**NOT covered:** §3 matched controls, §4 planted control, §6 scope, §7 falsification, §8 exactness,
§9 pre-commitment, and the tooling inventory. **This is a partial audit of one layer.**

---

## §1 — What was checked, and how

Object-level, by simulation of the spec's **exact** decision procedure (`tdev_calib.py`, `diag.py`),
not by reading it. Cell-probability vectors are the record's own: sextant `[1/6]×6`, flap `¾:⅛:⅛`,
`C_T = (¾:⅛:⅛)⊗(¾:⅛:⅛)` (9 cells), norm-band 4 cells. `K = 199` controls, `M = 2000` sample units,
leave-one-out ensemble mean exactly as §2 specifies.

⚠ The simulation uses floats for `G` and an RNG for multinomial draws. That is a **calibration study
of the test procedure**, not a signal-path computation — the folder's no-float OVERRIDE governs the
real run, where §2 correctly requires `fractions.Fraction` on integer counts.

---

## §2 — CLEAN: the null is calibrated

The pooled statistic re-uses the same control ensemble twice (ranks `R_ℓ` are computed against it,
then `T_dev` is ranked against it again). That is the obvious place for an anti-conservative null.
**It is handled correctly by the leave-one-out scheme.**

```
NULL, M=2000, K=199, 1500 reps:   FPR@.05 = 0.0493     FPR@.01 = 0.0107
NULL, M= 500, K=199, 1500 reps:   FPR@.05 = 0.0600     FPR@.01 = 0.0127
per-law flap alone (800 reps):    FPR@.05 = 0.055      Holm×4 @.05 = 0.011
```

⚠ **One loose end:** a second, smaller run (800 reps) returned `FPR@.05 = 0.074` for the pooled
statistic — ≈3σ high against its own Monte-Carlo error. The two runs disagree. **The pooled null
deserves a proper calibration run (≥10⁴ reps) before it is trusted at `α = 0.01`.** The per-law nulls
were clean in both runs.

---

## §3 — ★ DEFECT: the decision statistic is badly underpowered, and non-monotone

Spec §5 asserts, parenthetically: *"pooled `T_dev` is strictly sharper"* than the single-cell test.
**Measured power at `α = 0.05`, `M = 2000`, `K = 199`, planting a shift `δ` on one flap cell
(base rate `1/8`):**

| `δ` | **pooled `T_dev`** (the decision statistic) | single-law flap | flap, Holm ×4 |
|---|---|---|---|
| 0.00 | 0.074 | 0.055 | 0.011 |
| 0.02 | 0.152 | **0.555** | 0.310 |
| 0.05 | **0.189** | **0.999** | **0.984** |
| 0.08 | 0.193 | 1.000 | 1.000 |
| 0.12 | **0.181** | 1.000 | 1.000 |

Three things, each decidable:

1. **The claim is false and the direction is reversed.** At `δ = 0.05` — a 40% relative shift on the
   cell — the decision statistic fires 19% of the time while the *demoted* per-law test fires 98%
   **after** a 4× multiplicity correction.
2. **`T_dev` SATURATES.** Power rises to ≈0.19 and then stops: `δ=0.12` (0.181) is **lower** than
   `δ=0.08` (0.193). Once `R_flap` hits its ceiling (199), further effect adds nothing while the other
   three laws contribute uniform noise ranks. **This is structural, not a tuning issue** — the pooled
   rank-sum has a hard power ceiling under ≈0.20 against a deviation confined to one law.
3. **The spec's power table describes a different instrument than the one that decides.** §5's `δ*`
   figures (flap-ε `δ* = 0.022` at `B=10⁴`) are single-cell/single-law 4σ thresholds — consistent with
   the 0.555 I measure for the single-law test at `δ=0.02`, and **not** with the pooled statistic's
   0.152. The stated power is therefore not the power of the decision rule.

**Why it happens:** the expected deviation is *concentrated* — an incomplete-sum effect need not
disturb all four laws equally — while `T_dev` weights four ranks equally. Three laws of pure noise
dilute the one informative rank.

**Concrete fix — invert §2.** Make the **per-law `G_ℓ` permutation tests with Holm adjustment over the
4 laws (+joint) at family `α = 0.05` the PRIMARY decision**, and demote `T_dev` to characterization.
The spec already computes exactly these ("Characterization output (not additional decision gates)");
the repair is a relabelling, not new machinery. It retains 0.984 power at `δ=0.05` and 0.310 at
`δ=0.02` where the pooled rule gives 0.189 and 0.152. If a pooled statistic is still wanted, use one
that does not saturate — Fisher/Stouffer combination of the four per-law permutation p-values — but
Holm-per-law is sufficient and is already specified.

⚠ **This changes what the run can conclude, not just how it reads.** Under the current §2 a real
concentrated deviation of the size the spec itself calls detectable would be **missed four times out
of five**, and the pre-committed null reading would be recorded as a scoped bound at a `δ*` the
statistic cannot actually achieve.

---

## §4 — Not checked (so it is not cleared)

§3 matched controls (are they β-closed / μ₆-carrying rather than plain shuffles?), §4 planted control
constructibility and its fires-criterion, §6 scope, §7 falsification, §8 exactness coverage of every
signal-path quantity, §9 pre-commitment completeness, and the disclosed ill-posed points. **Absence
from this document is not clearance.**

Two items I noted but did not test: the spec's own disclosure that the **dynamic** `C_T` transition
operator is ill-posed on a subfamily (replaced by a static fixed-step histogram, spectral version
deferred) — a correct disclosure, and the deferral should stay deferred; and the secondary `T_joint`
internal label-shuffle null, which is valid *given* the disjoint-construction argument of §1 but was
not independently checked here.

---

## §5 — Status

**ARMS HELD.** Two blockers, in order:

1. **Re-run `experiment-designer`** when the limit resets. This self-audit does not substitute for it
   — it covers one layer and has no context isolation.
2. **Repair §2** (invert primary/characterization) and re-issue as `v2`, or record a reasoned
   rejection of the repair. Do not run `v1` as written.

Also owed: a ≥10⁴-rep calibration of the pooled null (§2 loose end), whichever statistic ends up
primary.
