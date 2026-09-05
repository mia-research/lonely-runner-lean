# PRE-REGISTRATION (DRAFT) — swap-invariant SUM object `x(Pᵢ+Pⱼ)` on short-scalar intervals

**Status: `[DRAFT — UNFROZEN — awaiting experiment-designer frame-gate sign-off]`.**
**Grade slot: `[PENDING GATE]`** — no arm may be run and no number claimed until (i) the
experiment-designer gate audits §1/§3/§6/§7/§9 (frame layers), and (ii) this file is frozen with a
SHA-256 over its body (§9). If the gate is UNAVAILABLE, `CLAUDE.md §2a` provisional conditions apply
and every output is tagged `[PROVISIONAL — experiment-designer unavailable]`.

**Executes handoff item C1** (`NEXT_SESSION_PROMPT_2026-08-01_v2.md`): *"The swap-invariant SUM object
`x(Pᵢ+Pⱼ)` … the full χ₂/χ₃/χ₆ family is legal on it. This is the readout axis that actually exists.
Never run."* Control spec inherited from `RESULT_shortscalar_cneg_recalibration_v1.md` (n≥20 C-NEG).

---

## §0. Counter-prior and scope boundary (binding)

- **Constructed scalars only.** `d` is sampled at will inside each interval; **no puzzle keys, no
  82-key object, no generator pool anywhere in the design.** The tell (`CLAUDE.md`): check the null's
  provenance — it is uniform random *curve points*, never `constructed_keys_*.csv`.
- The object is a property of **scalar multiplication on secp256k1 at its own prime** — not of how any
  integer was chosen. This is not a generation-side test.
- **No closure may be declared from an empirical null.** A quiet arm is a **bound** (§5, Rule 5), never
  a closed channel.

## §1. Object and disjointness (FRAME — gate must audit)

**The object.** For a set `S = {P₁,…,P_M}` of curve points, the **sum multiset** is
`Σ⁺(S) = { x(Pᵢ + Pⱼ) : i < j }`, `T = C(M,2)` values. The arm's `S` is
`{ [d]G : d sampled uniformly in the dyadic interval [2^{k−1}, 2^k) }`.

**Why the full χ₂/χ₃/χ₆ family is legal here (algebraic, per Rule 1 — proved on the object, not
imported from a global identity).** `x(Pᵢ+Pⱼ)` is **swap-invariant** (`Pᵢ+Pⱼ = Pⱼ+Pᵢ`), so each
unordered pair yields ONE canonical field value; and `x(−Q)=x(Q)` removes any sign ambiguity. Unlike
the **field**-difference multiset `{xᵢ−xⱼ}` — which is negation-closed in the value, forcing every
odd character (`χ₂,χ₆`) to `0` identically (`ANALYSIS_diffset_readout_parity_void_v1.md` §1) — the sum
multiset is **not** negation-closed: `Pᵢ+Pⱼ = [dᵢ+dⱼ]G` sits at scalar `s = dᵢ+dⱼ ∈ (2^k, 2^{k+1})`,
strictly positive, with no `−s` partner in the multiset. **Hence χ₂ and χ₆ carry information here for
the first time.** (Formal check to run in the C-GLV control §3: on a φ-closed `S` the sum multiset is
β-closed ⇒ E₃=E₆=0 *forced*, confirming legality and instrument.)

**This is a joint-2 property of the SET, not a per-point marginal.** A single `χ(x([s]G))` is
Farey-generic (uniform by the `d↔(X,Y)` bijection) — an expected null and not the object. `Σ⁺` sums a
nonlinear readout over the **structured** sumset that the short interval leaves; per
`ANALYSIS_correlation_hierarchy_weil_closure_v1.md`, complete character sums are Weil-closed but the
**incomplete/structured-set** regime is the one the closure does not reach. The test asks whether the
interval's joint structure survives the ECDLP scramble into `Σ⁺`'s character distribution — the only
kind of property that *can* survive (`CLAUDE.md`).

**Disjointness (no residue-vs-component tautology, per the 2026-07-14 memory).** The **feature** is a
character of a *pairwise sum point*; the **structure under test** is interval-confinement of the
*individual* scalars. The feature is not an algebraic component of the target (the character of
`x([dᵢ+dⱼ]G)` is a nonlinear function of the point, not the interval-membership bit). No shared
variable makes the statistic fire by construction. **Gate must confirm** the arm's `Σ⁺` and the null's
`Σ⁺` differ only in the presence/absence of the short-scalar `d`-relationship, nothing else.

## §2. Statistic and decision rule

**Readouts:** χ₂ (Legendre, order 2), χ₃ (cubic, order 3), χ₆ = χ₂·χ₃ (order 6). On secp
`p ≡ 3 mod 4`, `p ≡ 1 mod 3`. **Statistics are exact integer quadratic forms** over `Σ⁺(S)` (derivation
in Appendix A):
`E₂ = (n₊−n₋)²`, `E₃ = A₃²−A₃B₃+B₃²`, `E₆ = A₆²+A₆B₆+B₆²`, all `= |Σ χ_k|²`.

**Decision (pre-committed):**
1. Compute `(E₂,E₃,E₆)` on each of the 6 arms.
2. Rank each arm statistic against the matched-null reference distribution (§3); convert to a rank
   p-value (exact integer count / R, `Fraction`).
3. **Holm** step-down over the family of **6 arms × 3 readouts = 18** hypotheses, family α = 0.05.
4. **Fire** an (arm, readout) cell iff its rank exceeds the **99th** percentile of the matched null
   AND it survives Holm AND it **survives an OOS retest on ≥1 fresh seed** (Section-D rule). **Null
   (bounded)** iff below the 95th on all cells. **Indeterminate** between — reported as such, never as
   closure.
5. **C-NEG** certifies the null tail per the recalibrated **n≥20** rule
   (`RESULT_shortscalar_cneg_recalibration_v1.md` §4): pass iff the fraction of ≥20 independent control
   draws above the 95th is within the binomial 2σ band of 0.05. A single high draw is not a fire.

## §2·CAL. Calibration (MECHANICAL — self-audit sufficient, but owed before any fire is claimed)

- **FWER of the 18-cell Holm rule** calibrated to ≥10⁴ reps under H₀ (matched null vs matched null),
  target realized FWER ≤ 0.05. Method mirrors `RESULT_shortscalar_debt_discharge_v1.md` §1 (Holm is
  proven ≤ α under arbitrary dependence; the calibration is the implementation sanity check).
- **C-NEG** already discharged for χ₂/χ₃/χ₆ on the group-law object (Step 1); re-confirm on `Σ⁺` (the
  sum object) at the chosen M — same code path, expected CALIBRATED.

## §3. Matched control / null geometry (FRAME — gate must audit; Rule 3)

**Primary null (geometric, Rule 3).** Uniform random curve points via QR-rejection on `x³+7`, **NO
scalar multiplication** ⇒ on secp (cofactor 1) a uniform random group element. The null replaces the
short-interval `S` with `M` such points and reads the identical `Σ⁺` statistic. **This preserves the
curve geometry (valid points, real group-law sums) and destroys only the short-scalar `d` relation.**
- **FORBIDDEN null (Rule 3):** differences/sums of uniform random integers in `F_p`. Geometrically
  misaligned ⇒ adjudication void. Not used.
- Pool-precompute (Rule 2): a pool of `P` null points has its `C(P,2)` pairwise **sum**-classes
  computed ONCE; null draws subsample `M`-subsets and look up sub-sums (zero modexps per draw), exactly
  as validated in Step 1 for the difference object.

**C-GLV (forced-zero instrument check).** A φ-closed `S` (`{(x,y),(βx,y),(β²x,y)}` triples, β³≡1) has a
β-closed sum multiset ⇒ **E₃=0, E₆=0 exact**; assert both. Confirms the instrument reads `Σ⁺` and that
χ₃/χ₆ are legal on it. `E₂` not forced (β is a QR).

**C-PLANT (instrument-is-live).** A set whose sum multiset is greedily biased toward one cubic class
must fire ≥99th (constructibility in §4). Confirms non-zero power.

**C-NEG (false-alarm calibration).** Per Step 1, n≥20 independent null draws; tail rate within band.

## §4. Plant-fires (MECHANICAL — owed before a run)

Construct C-PLANT and confirm the decision rule (i) fires at/above the injected `δ*`, (ii) is void
below it, at calibration scale — as in `shortscalar_plantfires_v1.py`. The plant is a point set whose
`Σ⁺` cubic-class counts carry a controlled single-class excess `δ`; power curve measured at
`δ ∈ {0, 0.5·δ*, δ*, 2·δ*}`.

## §5. Power and the measured bound (Rule 5 — silence is a BOUND, never a closure)

With `T = C(M,2)` sum values, a single-class fractional excess `ε` (one cubic class at `T/3·(1+ε)`)
gives `E₃ ≈ (9/4)(εT/... )` — concretely, firing at the null 99th percentile `V₉₉` requires an
absolute single-class excess `δ ≈ (2/3)√V₉₉`, i.e. a **fractional** excess
`ε* = δ/(T/3) = 2√V₉₉ / T`. Since `V₉₉` scales ~ `T`, `ε* ~ 1/√T ~ 1/M`.

**The bound is reported, per M, as the measured `ε*`** from the matched-null `V₉₉` — e.g. "the arm
excludes a single-class cubic bias ≥ ε*% at this M; it is BLIND below ε*." Expected floors by the
1/M law (calibrated against the on-file M=80 → 7.7% point):

| stage | M | `T=C(M,2)`/arm | expected floor `ε*` |
|---|---|---|---|
| A | 400 | 79,800 | ≈ **1.5%** |
| B | 1024 | 523,776 | ≈ **0.6%** |
| C | 2000 | 1,999,000 | ≈ **0.3%** |

The reported RESULT states the **exact measured** floor from the realized null, not this estimate.

## §6. Scope (FRAME — gate must audit; Rule 4)

- **secp256k1's own `p`, its own `G`.** Interval arithmetic is hyper-sensitive to `p, G, n`; any
  structure found is a **localized cryptographic fact about secp**, never "generic to CM curves."
  Labeling a secp interval anomaly "generic" is banned from any synthesis of this run.
- Arms: `k ∈ {40, 64, 96, 128, 160, 200}`, dyadic `[2^{k−1}, 2^k)`, `d` uniform in-interval. `k=128` is
  reported with the rest and holds no special status in the design.
- **Not in scope here** (deferred, not dismissed): non-dyadic / non-uniform intervals, triples and
  higher-order sum objects, the full 6-cell joint-histogram readout, and the group-law **difference**
  χ₂/χ₆ arm (item C2 — sibling prereg).

## §7. Falsification (FRAME — gate must audit)

- **Arm fires** ⇒ pre-committed reading: the short interval induces a χ_k-class concentration in `Σ⁺`
  exceeding the matched geometric null at the 99th, Holm-surviving, OOS-replicating. Reported as a
  candidate localized lever (positive framing), **not** yet a mechanism — mechanism requires the
  anomaly-drill characterization (symmetry type / eigenvector / subspace), never a verdict.
- **Arm bounded** ⇒ the interval leaves no single-class χ_k bias ≥ ε* in `Σ⁺` at this M; **stated as a
  magnitude with its floor**, the channel remains open below ε* and at higher M / other readouts.
- **Kill condition for a claimed fire:** dies on OOS retest, or the matched control fails to fire
  (C-PLANT), or C-NEG mis-calibrates, or the "fire" is reproduced by the forbidden `F_p`-integer null
  (⇒ artifact, not curve). Any one voids the fire.

## §8. Exactness (MECHANICAL; BTC `CLAUDE.md` no-float rule)

Signal path is pure Python `int`: point arithmetic mod `p`, character classes via `pow(a,e,p)`, the
three statistics are integer quadratic forms (Appendix A), rank p-values are exact `Fraction`
(integer count / R). The only floats are display (percentages, the ε* estimate). `check_no_float.sh`
must pass on the arm's signal-path script before any run; the driver imports named functions and never
calls a plotting/`main` path (the R4 procedural rule).

## §9. Pre-commitment and freeze (FRAME — gate must audit)

**Frozen before any arm runs:** the 6 `k` values; the 3 readouts; M per stage; R (null reference) and
n (C-NEG) ≥ 20; the pool size P; the Holm-18 rule and the 99th-fire / 95th-bound / OOS thresholds; the
two null constructions (geometric primary; `F_p`-integer forbidden); C-GLV/C-PLANT/C-NEG; the seeds.
On freeze, compute SHA-256 over the file body (through the end-of-body marker) and record it; results
execute against that SHA. **This DRAFT is unfrozen** — the gate may require edits to §1/§3/§6/§7 first.

## §10. Compute plan (Rule 2 — Big-O and op count BEFORE any run)

Per arm at size M: `M` scalar-mults (the points) + `C(M,2)` group additions + `2·C(M,2)` character
modexps (χ₂,χ₃; χ₆ derived). 6 arms. Measured `pow` ≈ 86.5 µs (Step 1). **Op count and the
single-response cutoff are stated here and must be re-printed by the run script before it executes.**

| stage | M | arm modexps (6·2·C(M,2)) | est. arm time @86.5µs | mode |
|---|---|---|---|---|
| A | 400 | 957,600 | ≈ 83 s | **single-response** (≤300s budget) |
| B | 1024 | 6,285,312 | ≈ 9.1 min | **background + logged** (`-u`, log file, never `tail`) |
| C | 2000 | 23,988,000 | ≈ 34.6 min | **background + logged**, or **sampled estimator** |

- **Single-response cutoff ≈ M ≤ 512** (6·2·C(M,2)·86.5µs ≤ ~300 s). **M ≥ 1024 runs as a logged
  background job**; any reported `E`/rank carries the raw terminal timing (Rule 2).
- **Sampled estimator (Rule 2, for M ≳ 2000):** if `C(M,2) > Q_max = 10⁶`, sample `Q_max` pairs
  uniformly per arm (identically sub-sampled in the null); power falls but the test stays exact. State
  `Q_max` and the realized pair count in the RESULT.
- **`M = 6.25×10⁶` is NOT in this ladder:** `C(M,2) ≈ 1.95×10¹³` ≈ 4.7×10⁵ h of modexps (Step 1
  projection). It requires a mathematically reduced/sampled estimator and its own prereg; no claim may
  be made for it from a hallucinated run.
- Null: pool-precompute `C(P,2)` sum-classes ONCE (P ≈ 2·M), then all draws are integer lookups.

---

## Appendix A — exact integer statistics (no float in the signal path)

For the sum multiset, tabulate per value the pair `(b,c)`, `b = χ₂-class ∈ {0,1}`, `c = χ₃-class ∈
{0,1,2}`, into a 6-cell histogram `H[code]`, `code = 3b+c`. Then (validated in Step 1):
- `E₂ = ((H0+H1+H2) − (H3+H4+H5))²`.
- `A₃ = (H0+H3)−(H2+H5)`, `B₃ = (H1+H4)−(H2+H5)`; `E₃ = A₃²−A₃B₃+B₃²`.
- `nm = [H0,H5,H1,H3,H2,H4]` (m=0..5, `m=(2c+3b) mod 6`);
  `A₆ = nm0−nm2−nm3+nm5`, `B₆ = nm1+nm2−nm4−nm5`; `E₆ = A₆²+A₆B₆+B₆²`.
All integers; rank p-values are integer counts over R. No float decides any verdict.

## Appendix B — reused, validated instrument (Step 1)

`shortscalar_cneg_recalibration_v1.py` already implements: secp constants (self-checked β³≡1, cube-root
labelling), uniform random curve points (no scalar mult), the χ₂/χ₃ classes, the three integer
statistics, the φ-closed forced-zero check, and the pool-precompute + n≥20 C-NEG calibration. The sum
arm reuses all of it; the only new code is (i) `[d]G` for interval `d`, (ii) group **addition** for
`Pᵢ+Pⱼ` (vs the difference already coded), and (iii) the arm/Holm driver.
