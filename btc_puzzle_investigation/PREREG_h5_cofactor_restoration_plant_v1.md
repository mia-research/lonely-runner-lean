# PRE-REGISTRATION — H-5 cofactor RESTORATION plant (forward test of the confinement mechanism)

**Date written:** 2026-08-30 (BEFORE any forward-run data seen)
**Author:** experiment-designer (Claude Code), mandatory gate per btc CLAUDE.md §2 / Math Ex CLAUDE.md §2.
**Status:** SPEC ONLY. No forward-run cell has been evaluated. This file is frozen before `sage` is run.
**What it forward-tests:** `RESULT_h5_cofactor_artifact_v1.md` concluded *backward* (via Pearson r=0.96
of T1_j0 against log n₂) that the Semaev relation-yield lever T1 is a cofactor / subgroup-confinement
artifact of non-cyclic j=0 model curves. This experiment INDUCES the confinement on CYCLIC control
curves and asks whether the lever reappears with the same law. A confirmed forward prediction beats a
backward correlation; a failure to restore names a residual the cofactor story missed.
**Instrument reused verbatim:** `measure_system` / `decomposition_system` / `decomposable_target` from
`semaev_elimination_v1.py`; `logmean(qs)=math.log(sum(qs)/len(qs))` from `analyze_h5_followup_v1.py`.

---

## 0. Frozen targets computed from PRIOR (already-collected) data — recorded before the forward run

These are computed ONCE from the frozen `h5_followup_results_v1.jsonl` (SHA to be recorded in the
results header) as step 0 of the run script, and written into the results header BEFORE any forward
cell is evaluated. They use prior data only; computing them is not "seeing" this experiment's data.

- **β_j0 (construction-matched target).** OLS slope of the j0 *same-curve* confinement differential
  `Δ_j0(p) = logmean quo_j0(gens) − logmean quo_j0(randpoint)` (the prior run's F8 arm, at |V|=6)
  regressed on `ln(n₂_j0(p))`, over the 24 frozen primes. This mirrors the forward statistic
  (confined − full, SAME curve) exactly, so it is the correct comparison target — NOT the cross-curve
  T1 and NOT the Pearson coefficient.
- **β_j0_crosscurve (secondary).** OLS slope of the prior cross-curve `T1_j0(p) = logmean quo_j0(gens)
  − logmean quo_ctrl(full)` on `ln(n₂_j0(p))`, |V|=6, for the secondary cross-curve arm.
- **Both are frozen as scalars in the results header before cell 1.**

> DESIGN FLAG (task framing). The task asks for the forward slope to match "j0's measured Pearson(T1,
> log n₂)=0.96." **A Pearson correlation coefficient is not a slope** (r is unit-free; a slope has
> units of ΔT1 per ln-unit). The published extremes (n₂=24→T1≈1.55; n₂=14→T1≈1.34) imply an empirical
> ln-slope of ≈0.5, i.e. mean-yield ∝ √n₂ — which itself contradicts §6's stated "yield ∝ n₂"
> (slope 1). The statistic below therefore targets β_j0 (the OLS slope from frozen data, ≈0.5 expected)
> and REPORTS separately whether §6's slope-1 holds. r=0.96 is retained only as a goodness-of-linear-fit
> descriptor, never as the slope target.

---

## 1. OBJECT

The object is the **causal dependence of Semaev decomposition yield `quo` on subgroup index c**, on a
curve that is CYCLIC by construction, where the only thing varied is the index c of the subgroup to
which factor-base and target sampling are confined.

- `quo = I.vector_space_dimension()` of the ideal `{S_{m+1}(x₁..x_m, tval)=0} ∪ {∏_{r∈V}(x_i−r)=0}`
  (`measure_system`), i.e. the multiplicity-counted number of ordered m-tuples of factor-base
  x-coordinates whose points admit a signed sum equal to the target — the exact object the cofactor
  story is about, not a proxy.
- **Confinement is by construction, not by non-cyclicity.** E is CYCLIC (single abelian invariant);
  `G = E.gens()[0]` generates the whole group; the order-q subgroup is `H := c·G` (unique subgroup of
  order q = #E/c for c | #E). Confined sampling draws multiples of H only. The full-group baseline
  draws the whole group. The curve's group structure is IDENTICAL between the two arms — the ONLY
  difference is the sampling restriction. This is what isolates confinement from the non-cyclic
  confound that produced the original j0 effect.
- **No shared construction between feature and target (tautology check).** The feature is the design
  variable c (chosen). The target is quo (measured by an independent Gröbner computation over GF(p)).
  They share no construction step; c does not enter `measure_system`. Not a tautology.

## 2. STATISTIC (exactly one)

**β_induced** = the ordinary-least-squares regression slope of `T1_induced(cell)` on `ln(c)`, pooled
over all confined cells (c ≥ 2), where a *cell* = a (prime p, cyclic curve X, index c, |V|) tuple and

    T1_induced(cell) = logmean_K quo(confined to <c·G>, curve X)   −   logmean_K quo(full group, curve X)

with `logmean(qs)=ln(mean(qs))` over the K decomposable targets (identical to the frozen instrument).
The full-group baseline uses **random_point sampling** (mirrors the j0 F8 baseline). The confined arm
uses **c·G-multiples**. β_induced is fit within each |V| separately and pooled (|V| as a covariate /
stratum), primary readout at |V|=6 to match β_j0's |V|=6.

- **Null distribution.** Under H₀ (confinement has no effect on quo) the c↔T1 pairing carries no
  information, so β_induced is centered at 0 with spread set by the matched control (§3). Significance
  = permutation rank, not a parametric t.
- **One statistic, aimed AT the predicted structure** (a positive ln-c slope), not a max over cells.
- Reported alongside (decision inputs, NOT separate statistics): the intercept of the same OLS (should
  be ≈0 by the mechanism, T1_induced(c=1)=0); per-cell T1_induced(c) values (for the subspace check in
  §7); and quo/|V|^m per cell (saturation guard, §6).

> DESIGN FLAG (does the statistic separate the alternatives?). SE(β)≈0.04 (§5) cleanly separates the
> three live magnitude alternatives: β≈0.5 (confinement reproduces j0's EMPIRICAL law), β≈1 (§6's naive
> "∝ n₂" law), β≈0 (no confinement effect), and β<0 (anti-prediction). The statistic is a slope
> (magnitude + sign), never a bare "signal / nothing".

## 3. MATCHED CONTROL

**Primary matched null = within-curve permutation of the c-labels.** For each curve X, take the set of
its confined cells {(c, T1_induced)} and randomly re-pair the T1_induced values with the ln(c) values;
recompute the pooled OLS slope β_perm. Repeat 10⁴ times. `p = fraction of permutations with
β_perm ≥ β_induced` (one-sided; prediction is a positive slope).

- **Preserves:** the curve and its full group structure, the Semaev instrument and ALL its forced
  symmetries (isobaric/λ→λT homogeneity of S_{m+1}, S_m factor-base permutation symmetry, the
  quo≥1 forcing of a decomposable target), the |V|/m/K parameters, the finite-subgroup sampling, and
  the entire marginal distribution of T1_induced values and of ln(c) values.
- **Destroys ONLY:** the c ↔ T1_induced pairing (the tested structure).
- **Why this null and NOT a point-shuffle.** Shuffling factor-base points across the confined/full
  boundary would break the confinement exactly as it breaks a real effect (the failure mode of the
  r=v−w tautology and the μ₆ shadow-shuffle). The c-label permutation leaves every forced symmetry
  intact and cannot destroy a symmetry the readout has by definition.
- **Secondary null (robustness):** global c-label permutation across all curves (higher power, but does
  not respect grouping); reported only as a cross-check.

**Firing/null plant embedded here (c=1).** Two INDEPENDENT full-group draws on the same curve, both
labelled "confined" and "full": their difference must be ≈0, and assigning fake ln(c) labels to
full-group-only cells must give β≈0 (perm-p not significant). If the c=1 arm shows a significant slope
or a T1 far from 0, the baseline is miscalibrated → HALT.

## 4. PLANTED CONTROL (positive controls that MUST fire)

1. **Confinement-verification plant (instrument).** For every sampled confined point P, assert
   `q·P == O` and `(q/ℓ)·P ≠ O` for each prime ℓ | q — i.e. the point's order divides q and the
   subgroup is genuinely <c·G> of order q. Exact integer point arithmetic. If any sampled point escapes
   the order-q subgroup, the sampler is broken → HALT (no conclusion).
2. **Synthetic-slope plant (the SLOPE pipeline must fire).** Replace each confined-arm quo by
   `quo_full · c` (exact int multiply — synthetically imposing §6's yield ∝ c). Run the ENTIRE
   T1_induced → OLS → permutation pipeline on this synthetic data. It MUST recover β_synthetic ≈ 1
   (ln units) at perm-p < 0.01. If it does not fire, the slope estimator has no power and the null is
   uninformative → HALT. (This is the correct positive control for a SLOPE statistic; the prior run's
   +0.5 additive-shift plant validated only the T1 estimator, not the slope estimator.)
3. **Additive-shift plant (T1 estimator, carried over).** Inject +0.5 into logmean of the confined arm;
   confirm the per-cell T1_induced shifts by +0.5 ± floor. Confirms the T1 estimator is calibrated.
4. **c=1 null plant** (from §3): must return β≈0, non-significant.

If plant 1 or 2 does not fire, the experiment HALTS with no verdict — a null that cannot fire is not a
result (btc CLAUDE.md, "a control that cannot fire invalidates the null").

## 5. POWER (with explicit floor)

- **Per-cell noise.** T1_induced = ln(mean_K quo_confined) − ln(mean_K quo_full). With K=25 and quo a
  small integer (few…tens), SE(ln mean) ≈ CV(quo)/√K ≈ 1/5 = 0.20 per term, so σ_resid ≈ √2·0.20 ≈
  0.28 per cell.
- **Slope SE.** With N_cells ≈ 25 curves × ≈4 usable c-values = ~100 confined cells and an ln(c) spread
  of SD ≈ 0.7 (Σ(ln c − mean)² ≈ N·0.49 ≈ 49): **SE(β) ≈ 0.28/√49 ≈ 0.04.**
- **Detection floor.** Minimal slope detectable at 3σ ≈ **0.12**. Against β_j0 ≈ 0.5 this is ~12σ; the
  design distinguishes β=0.5 from β=1 from β=0 at ≥6σ each.
- **Comparison tolerance ("restored").** |β_induced − β_j0| ≤ **0.15** (≈3–4×SE; wide enough to absorb
  estimation noise, narrow enough to EXCLUDE §6's slope-1 given β_j0≈0.5) AND perm-p(β_induced>0) < 0.01.
- **Floor is a design constraint, not a post-hoc number:** if the run yields < 60 usable confined cells
  (e.g. too few cyclic composite-order curves found), SE(β) rises above 0.05 and the ±0.15 tolerance is
  under-powered → the run is declared UNDERPOWERED and no "restored"/"residual" verdict is issued until
  more curves are added. State N_cells and SE(β) on every β reported.
- **c-range power (binding).** To trace the slope across j0's n₂-range [2,24] the design needs c up to
  ≈24 with q≥q_floor; this forces the extended prime band (§6). At the matched model scale (p∈[523,823])
  only c∈{2,3} is reachable (weak per-curve lever) — that band is a comparability check, not the
  primary power source.

## 6. SCOPE

Every number the run emits carries this scope; none may be stated without it.

- **Instrument:** m = 3; |V| ∈ {4, 5, 6}; K = 25 decomposable targets per cell (matches the frozen
  h5 instrument). Dmax = 2^(m−1) + m·|V| + 5 (as in the harness).
- **Curves — construction:** for each candidate prime p, draw random (A,B) with 4A³+27B²≠0; keep E iff
  (i) E is CYCLIC (`len(E.abelian_group().invariants()) ≤ 1`), and (ii) #E admits ≥4 integer divisors
  c with 2 ≤ c and q=#E/c ≥ **q_floor = 200**. Confine to <c·G>, index c, for each such c.
  Curves are GENERIC (j ≠ 0, 1728) — REQUIRED, because j=0 model curves are systematically non-cyclic
  at p≡1 mod 3 (the original confound). See j-independence flag in §9.
- **Primary prime band (power):** p prime in **[10007, 50021]**, selected until **≥25 cyclic curves**
  meeting (i),(ii) are found, giving c up to ≈24 with q ≥ 200. (measure_system cost is p-independent:
  linear algebra over GF(p); only coefficient size ~ log p grows — negligible.)
- **Secondary prime band (comparability):** p ∈ [523, 823] (the frozen j0 model primes), cyclic curves,
  c ∈ {2,3} where available — direct comparability at j0's own scale, accepted as low-c-range.
- **Subgroup indices:** c ∈ {2,3,…} restricted to divisors of #E with q=#E/c ≥ 200; report the
  realized multiset of c per curve.
- **Saturation guard (pre-registered, not post-hoc):** drop any cell with quo ≥ 0.5·|V|^m (finite-group
  saturation regime, a different phenomenon from the yield mechanism); the drop count is disclosed in
  the results header. q ≥ 200 already keeps most cells out of this regime.
- **K, wall-clock:** K = 25; 10⁴ permutations per null; resumable JSONL (one record per cell, skip
  cells already present), time-box **4 hours** wall-clock; if incomplete, report the partial cell count
  and the resulting SE(β) and apply the §5 underpowered rule.
- **Exact-int quantities:** #E, q, c, quo, point orders, divisor lists — all int.

## 7. FALSIFICATION

The hypothesis under forward test is: *"artificial confinement to index c inflates quo, with T1_induced
growing linearly in ln(c) at slope β_j0."* It is FALSIFIED if, with plants 1 & 2 fired and the c=1 null
plant clean:

- **β_induced not significantly > 0** (perm-p ≥ 0.01, β within [−floor, +floor]≈±0.12): confinement does
  NOT reproduce the lever → the j0 effect is NOT (fully) a confinement artifact → a residual the
  cofactor story misses. **Before concluding "flat," inspect the per-cell T1_induced(c) curve for
  subspace structure** (curvature/saturation; effect present only for prime-index c; dependence on
  q's factorization or on gcd(q, p−1)); if such structure exists, the finding is that residual, NOT
  "no effect."
- **β_induced significantly ≠ 0 but sign negative:** anti-prediction; the mechanism is wrong as stated.

## 8. EXACTNESS

- **Signal path is exact.** #E, subgroup order q, index c, `quo` (= `vector_space_dimension`, int),
  point orders, and divisor enumeration are all Python/Sage integers. The confinement plant (order
  divides q) is exact integer point arithmetic.
- **Float carve-out (only place floats appear):** `logmean = math.log(sum(quo)/len(quo))`, the OLS
  slope β, and the permutation ranking. These are a **monotone statistic ranked against a matched
  permutation null**; the inputs (quo, c, q) are exact ints. Each such line carries
  `# noqa: float — (stat) monotone statistic on exact-int quo ranked against label-permutation null`
  per btc CLAUDE.md. No float ever decides a discrete/algebraic property (no square/vanishing/root-of-
  unity test in float). `check_no_float.py` must pass before any result is reported.
- quo ≥ 1 always (a decomposable target forces the identity tuple into the variety), so `log(quo)` is
  always defined; assert quo ≥ 1 per cell.

## 9. PRE-COMMITMENT (each outcome → its conclusion, filled in BEFORE the run)

Gate order: plant 1 (confinement real) → plant 2 (slope pipeline fires) → c=1 null clean → then read
β_induced. If any gate fails, HALT with the stated non-verdict.

| Outcome | Pre-committed conclusion |
|---|---|
| Plant 1 fails (points escape <c·G>) | HALT — sampler bug. No verdict. |
| Plant 2 fails (synthetic β≉1) | HALT — slope estimator underpowered / broken. Null uninformative. |
| c=1 null plant fires (β≠0 or T1≠0) | HALT — baseline miscalibrated. No verdict. |
| N_cells < 60 / SE(β) > 0.05 | UNDERPOWERED. Report β with its SE; issue NO restored/residual verdict; owe more curves. |
| **β_induced > 0, perm-p<0.01, |β_induced − β_j0| ≤ 0.15** | **Cofactor mechanism CONFIRMED prospectively (construction-matched slope reproduced on cyclic curves).** M25/N22 H1 leg → `[VERIFIED — cofactor/confinement, forward-predicted]`, closes hard at model scale. Also report whether §6's slope-1 is excluded (expected yes: β≈0.5, so "yield ∝ √n₂" supersedes "∝ n₂" as the magnitude law — a refinement, not a residual). Scope: model primes, cyclic j≠0 curves; NO 256-bit / ECDLP / keyspace claim; secp256k1 is prime-order so the mechanism is absent there. |
| β_induced > 0, perm-p<0.01, but 0.15 < β_induced (right direction, wrong magnitude) | Confinement reproduces the DIRECTION but not j0's magnitude. Do NOT close. Name the residual = the slope gap (|β_induced − β_j0|); report whether the gap is toward §6's slope-1 (then j0's √n₂ shortfall is the residual) or below β_j0. M25 null remains INCOMPLETE. |
| β_induced not significant (flat), no subspace structure found | Confinement does NOT reproduce the lever. The j0 effect has a residual the cofactor story misses. Do NOT close M25; name the residual and design the next probe. This is a POSITIVE finding (a residual), not a closure. |
| β_induced flat overall BUT per-cell subspace structure present | Report the subspace (e.g. prime-index-only, or q-factorization dependence) as the residual object; do NOT read the flat pooled slope as "nothing." |
| β_induced significantly < 0 | Anti-prediction; the confinement mechanism as stated is wrong; open an investigation, do not close. |

Secondary cross-curve arm (β_j0_crosscurve vs a forward cross-curve T1) is reported as robustness only;
it does not change the primary verdict, which is the construction-matched same-curve slope.

---

## DESIGN DEFECTS FLAGGED (summary — the agent is not scored on problems; these are disclosed, not fatal)

1. **Pearson ≠ slope (task framing).** "Same slope as Pearson 0.96" conflates a correlation coefficient
   with a regression slope. Resolved: target β_j0 (OLS slope from frozen data, ≈0.5), report r=0.96
   only as fit quality. (§0, §2.)
2. **§6's "yield ∝ n₂" (slope 1) already disagrees with j0's own data (slope ≈0.5 ⇒ ∝√n₂).** Not a
   defect in THIS design but a magnitude-law tension the run must preserve: a confirmed β≈0.5 confirms
   the confinement MECHANISM while refining §6's magnitude claim. Flagged so a β≈0.5 is not misread as
   a partial failure. (§0, §9.)
3. **Baseline mismatch (j0 cross-curve vs forward same-curve)** — RESOLVED by targeting β_j0 from the
   prior F8 same-curve differential (Q_gens−Q_randpoint), which is construction-matched. Cross-curve
   kept only as secondary. (§0, §2.)
4. **Saturation confound** at small q (quo→|V|^m is a finite-group artifact, not the yield mechanism):
   guarded by q_floor=200 and the pre-registered quo ≥ 0.5·|V|^m drop. (§6.)
5. **c-range vs power at model scale:** p∈[523,823] only reaches c∈{2,3}; the extended band [10007,50021]
   is required for the c-up-to-24 lever arm. Both bands reported; primary power from the extended band.
   (§5, §6.)
6. **c and 1/q are collinear at fixed #E** — this is the MECHANISM (yield ∝ index = ∝ 1/subgroup-order),
   not a confound; noted so "it's really q not c" is not a valid re-reading. (§1.)
7. **j-independence scope:** forward curves are generic (j≠0) cyclic curves, because cyclic j=0 curves
   are rare at the model primes. A confirmed slope proves confinement SUFFICES to produce a j0-magnitude
   lever (strong prospective confirmation); a magnitude SHORTFALL cannot by itself rule out an
   additional j0-specific residual, since "j0 + confinement together" is not directly sampled. (§6, §9.)

**Verdict on well-posedness:** the experiment is WELL-POSED. The confinement is induced by construction
on curves that are cyclic (isolating it from the original non-cyclic confound), the target stays
decomposable inside the subgroup, the statistic is a single slope that separates the three live
alternatives (β≈0/0.5/1), the matched null destroys only the tested pairing while preserving every
forced symmetry, both a firing SLOPE plant and a firing/null c=1 plant are embedded, and the decision
rule maps every outcome (including the subspace-residual case) to a pre-committed conclusion. The two
substantive cautions are the task's Pearson-vs-slope conflation (resolved by retargeting to β_j0) and
the requirement of an extended prime band to obtain the c-range that matches j0's n₂ range.
