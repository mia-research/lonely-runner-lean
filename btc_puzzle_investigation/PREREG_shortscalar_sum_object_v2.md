# PRE-REGISTRATION (DRAFT v2) — swap-invariant SUM object `x(Pᵢ+Pⱼ)` on short-scalar sets

**Status: `[DRAFT — UNFROZEN — awaiting experiment-designer frame-gate sign-off]`.**
**Grade slot: `[PENDING GATE]`.** Supersedes `PREREG_shortscalar_sum_object_v1.md`, which is retained
as the record of the audit-caught defects. No arm runs and no number is claimed until the gate audits
the frame layers and this file is SHA-frozen (§9).

**Executes handoff item C1** (the swap-invariant sum object, never run). Control spec inherited from
`RESULT_shortscalar_cneg_recalibration_v1.md` (n≥20 C-NEG).

---

## §0.1. Changes from v1 — driven by self-audit (2026-08-02), all three defects were real

1. **RETRACTED the k≥128 "Weil-zone / null-expected" framing (Rule-1 violation).** v1 used a global
   upper bound to pre-label half the arms' nulls "expected." A Weil/Pólya–Vinogradov bound constrains
   the *maximum of a complete/long sum*; it does **not** predict that a specific **incomplete** sub-sum
   washes out. Moreover the **matched null is k-independent** (M uniform random points), so no k is
   a-priori "less informative." Any structural limitation on an interval must be shown **algebraically
   on that interval** (Rule 1), never imported. The down-weighting is deleted; all arms are read on
   equal footing.
2. **FIXED the sampling (v1 tested only uniform-random-in-band, which destroys contiguity).** Uniform
   sampling of M scalars from a 2^k bucket has typical gaps ~2^k/M — it probes only *bit-length-band
   membership*, a marginal-ish channel, and has **low power for local arithmetic structure**. v2 adds a
   **contiguous-block regime** whose sum-set is a genuinely short incomplete interval at every k, and
   demotes uniform-band to a labeled secondary arm. See §1.2.
3. **REPLACED Holm-FWER-as-gate with OOS-replication-as-gate (power-preserving).** FWER is conservative
   and can crush a faint real signal when power is low. The project's documented risk is the opposite —
   false alarms that die on retest. So the **gate is OOS replication on multiple fresh seeds** (a real
   effect replicates; a fluke does not); every per-cell rank p-value is reported **uncorrected**; Holm
   is demoted to a reported secondary summary. To keep raised sensitivity from tipping toward false
   positives, the OOS requirement is **hardened to ≥5 independent seeds** (§2, §7).

---

## §0. Counter-prior and scope boundary (binding)

- **Constructed scalars only** — sampled at will; **no puzzle keys, no 82-key object, no generator
  pool.** The null's provenance is uniform random *curve points*, never `constructed_keys_*.csv`.
- Object = a property of scalar multiplication on secp256k1 at its own prime; **not** generation-side.
- **No closure from an empirical null.** A quiet arm is a **bound** (§5, Rule 5), never a closed channel.

## §1. Object, sampling, and disjointness (FRAME — gate must audit)

### §1.1 The object
For points `S = {P₁,…,P_M}`, the **sum multiset** is `Σ⁺(S) = { x(Pᵢ+Pⱼ) : i<j }`, `T = C(M,2)`.
`x(Pᵢ+Pⱼ) = x([dᵢ+dⱼ]G)`.

**Why χ₂/χ₃/χ₆ are all legal (algebraic, Rule 1 — on the object, not imported).** `Σ⁺` is
swap-invariant and `x(−Q)=x(Q)`, so each unordered pair gives ONE canonical value; and the sum
multiset is **not** negation-closed (`s = dᵢ+dⱼ > 0`, no `−s` partner), unlike the field-difference
multiset that forces odd characters to 0. Confirmed forced-zero in the C-GLV control (§3): on a
φ-closed `S` the sum multiset is β-closed ⇒ E₃=E₆=0 exact.

### §1.2 Sampling regimes — each targets a *different* alternative; stated honestly
The individual points `[d]G` are marginally uniform (ECDLP) in **every** regime, so **all** power comes
from **joint set structure**. The regimes differ in *which* joint structure they can see:

- **(R-CONTIG) Contiguous block [PRIMARY, high-power local probe].** `d = d₀, d₀+1, …, d₀+M−1`,
  `d₀ ∈ [2^{k−1}, 2^k)`. Sum-set = `[s]G` for `s` in a **width-(2M−3) contiguous interval** near
  `2^k`. Genuinely short/incomplete at *every* k (2M ≪ √p), so the completion bounds are vacuous here
  by construction (this is the Rule-1-correct incomplete regime). Detects **local** arithmetic
  structure among nearby scalars. `k` = location (high bits); `M` = window width.
- **(R-CLUSTER) Dense sub-window [intermediate].** `d` sampled densely in a width-`W` window,
  `M ≤ W ≪ 2^k`. Interpolates between contiguity and band membership; `W` is a scanned knob.
- **(R-BAND) Uniform in the dyadic band [SECONDARY, marginal-sensitivity].** `d` uniform in
  `[2^{k−1}, 2^k)` (the v1 design). Tests **bit-length-band membership** only — the puzzle-relevant
  channel, but low power for locality. **Labeled as such; not the main event.**

`k ∈ {40, 64, 96, 128, 160, 200}` for all regimes; `k` holds no privileged value.

### §1.3 Disjointness (no residue-vs-component tautology)
The **feature** is a character of a *pairwise sum point*; the **structure under test** is the d-set's
contiguity/band-membership. The feature is a nonlinear function of the point, not an algebraic
component of the target — no shared variable fires the statistic by construction. **Gate must confirm**
arm and null `Σ⁺` differ only in the presence/absence of the d-structure.

## §2. Statistics and decision rule

**Readouts:** χ₂, χ₃, χ₆. **Magnitude statistics** (exact integer forms, Appendix A):
`E₂=(n₊−n₋)²`, `E₃=A₃²−A₃B₃+B₃²`, `E₆=A₆²+A₆B₆+B₆²` — sensitive to a **coherent** class bias.
**Deviation statistic** `D₆` = exact integer χ²-numerator of the 6-cell (b,c)-histogram vs. its
matched-null mean (`D₆ = Σ_cell (obs−exp)²` over integer counts, ranked; captures **non-coherent /
sparse** concentration the magnitude misses). 4 readouts × (regimes × k) cells.

**Decision (pre-committed):**
1. Compute all readouts on each arm; rank each vs. the matched-null reference (§3) → exact rank
   p-value (`Fraction`, integer count / R). **Report every per-cell p-value uncorrected.**
2. **SCREEN:** a cell is a candidate iff its statistic exceeds the **99th** percentile of the matched
   null. (No FWER suppression at the screen.)
3. **GATE = OOS replication:** a screened cell is **named a candidate finding only if it exceeds the
   99th on ≥5 independent fresh-seed reruns** (arm points and null both re-drawn). A cell that screens
   once but fails OOS is reported as a **non-replicating screen**, explicitly not a finding.
4. **Bound** (Rule 5): cells below the 95th on all seeds → report the measured floor ε* (§5), never
   "closed."
5. **C-NEG** certifies the null tail per the recalibrated **n≥20** rule (Step 1); a single high control
   draw is not a fire.
6. **Holm over the cell family is computed and REPORTED as a secondary summary** — it does not gate,
   suppress, or veto. It is context, not a filter.

## §2·CAL. Calibration (MECHANICAL — owed before any fire is claimed)
- **Screen+OOS false-positive rate** calibrated under H₀ (matched null vs matched null): measure the
  rate at which a cell screens at the 99th AND replicates ≥5/5 by chance, ≥10⁴ reps. Target ≪ 0.05
  family-wise (the 5/5-replication requirement is what buys this without a power-killing penalty).
- **C-NEG** re-confirmed on `Σ⁺` at the chosen M (same code path as Step 1; expected CALIBRATED).

## §3. Matched control / null geometry (FRAME — gate must audit; Rule 3)
**Primary null (geometric).** Uniform random curve points via QR-rejection on `x³+7`, **no scalar
multiplication** ⇒ uniform group element (cofactor 1); same `Σ⁺` statistic. Preserves curve geometry,
destroys only the d-structure. Identical construction for all three regimes (it breaks contiguity,
cluster, and band alike). **FORBIDDEN:** sums of random `F_p` integers (geometrically misaligned ⇒
void).
**Secondary control for R-CONTIG (isolates contiguity vs. location):** a contiguous block at a
**random** `d₀` — same contiguity, shuffled location. Distinguishes "contiguity leaks" from "this band
leaks." Reported, not gating.
**C-GLV** (forced-zero): φ-closed `S` ⇒ E₃=E₆=0 exact (instrument + legality check).
**C-PLANT** (instrument-live): a sum-set greedily biased toward one cubic class must fire ≥99th (§4).
**C-NEG** (false-alarm calibration): n≥20 draws, tail within band (Step 1).

## §4. Plant-fires (MECHANICAL — owed before a run)
Construct C-PLANT; confirm the screen+OOS rule fires at/above injected δ* and is void below, at
calibration scale (as in `shortscalar_plantfires_v1.py`). Power curve at δ ∈ {0, ½δ*, δ*, 2δ*}.

## §5. Power and the measured bound (Rule 5 — silence is a BOUND)
`|Σχ|²` detects a **coherent** single-class fractional excess `ε* = 2√V₉₉ / T ~ 1/M` from the measured
null V₉₉. **Reported per regime × M as the measured ε*** ("excludes a coherent single-class χ_k bias
≥ ε* here; BLIND below"). Expected floors (1/M law, calibrated to on-file M=80→7.7%):

| M | T=C(M,2)/arm | expected coherent floor ε* |
|---|---|---|
| 400 | 79,800 | ≈ 1.5% |
| 1024 | 523,776 | ≈ 0.6% |
| 2000 | 1,999,000 | ≈ 0.3% |

**Explicit power caveat (audit item 2):** `|Σχ|²` is blind to non-coherent/sparse structure; `D₆` and
the anomaly-drill follow-up cover that axis. The RESULT states the **measured** floor, not this estimate.

## §6. Scope (FRAME — gate must audit; Rule 4)
- **secp256k1's own `p`, `G`.** Any structure found is a **localized cryptographic fact about secp** —
  labeling a secp interval anomaly "generic" is banned from any synthesis of this run.
- **No global-bound down-weighting of any k** (audit item 1). All arms read on equal footing.
- Deferred (not dismissed): non-dyadic intervals, triples/higher-order sum objects, the group-law
  **difference** χ₂/χ₆ arm (item C2, sibling prereg).

## §7. Falsification (FRAME — gate must audit)
- **Candidate finding** ⇒ a cell screens at the 99th AND replicates **≥5/5 fresh seeds** vs the matched
  geometric null. Reported as a candidate localized lever (positive framing); mechanism requires the
  anomaly-drill characterization (symmetry type / eigenvector / subspace), never a verdict.
- **Bounded** ⇒ below the floor on all seeds; stated as a magnitude with its ε*, channel open below.
- **Kill conditions:** fails OOS (<5/5); C-PLANT fails to fire; C-NEG mis-calibrates; the "fire" is
  reproduced by the forbidden `F_p`-integer null (⇒ artifact); or R-CONTIG fires but the random-`d₀`
  secondary control fires equally (⇒ generic contiguity, not a secp-location fact — still reported, but
  re-scoped, not a leakage claim).

## §8. Exactness (MECHANICAL; no-float rule)
Pure `int` signal path: point arithmetic mod p, characters via `pow(a,e,p)`, statistics are integer
quadratic forms + integer χ²-numerator, rank p-values exact `Fraction`. `check_no_float.sh` passes
before any run; the driver imports named functions, never a plotting/`main`/`selftest` path.

## §9. Pre-commitment and freeze (FRAME — gate must audit)
Frozen before any arm runs: the 3 regimes + their knobs (M window, W); 6 `k`; 4 readouts; M per stage;
R and n≥20; pool P; the screen-99th / OOS-≥5-seeds / bound-95th rule; the two nulls (geometric primary;
`F_p` forbidden) + the R-CONTIG secondary control; C-GLV/C-PLANT/C-NEG; all seeds. On freeze, SHA-256
the body; results execute against that SHA. **This DRAFT is unfrozen.**

## §10. Compute plan (Rule 2 — Big-O and op count BEFORE any run)
Per arm at M: point generation (R-CONTIG: 1 scalar-mult + M−1 additions; R-BAND: M scalar-mults) +
`C(M,2)` group additions + `2·C(M,2)` character modexps (χ₂,χ₃; χ₆ derived; +the histogram gives D₆
free). `pow` ≈ 86.5 µs (Step 1). **The run script must re-print these counts before executing.**

| stage | M | modexps/arm (6·2·C(M,2)) | est. time @86.5µs | mode |
|---|---|---|---|---|
| A | 400 | 957,600 | ≈ 83 s | single-response (≤300 s) |
| B | 1024 | 6,285,312 | ≈ 9.1 min | background + logged (`-u`, log file, never `tail`) |
| C | 2000 | 23,988,000 | ≈ 34.6 min | background + logged, or sampled estimator |

- Multiply by the number of active regimes × the 5 OOS seeds for the full budget; state the realized
  total in the RESULT with raw timing.
- **Single-response cutoff ≈ M ≤ 512.** M ≥ 1024 is background/logged.
- **Sampled estimator (M ≳ 2000):** if `C(M,2) > 10⁶`, sample 10⁶ pairs/arm (identically in the null);
  power falls, test stays exact; state realized pair count.
- **M = 6.25×10⁶ is NOT in this ladder** — `C(M,2) ≈ 1.95×10¹³` ≈ 4.7×10⁵ h of modexps (Step 1); needs
  its own reduced/sampled prereg. No number may be claimed for it from a hallucinated run.
- Null: pool-precompute `C(P,2)` sum-classes ONCE (P ≈ 2M), draws are integer lookups.

---

## Appendix A — exact integer statistics
6-cell histogram `H[code]`, `code = 3b+c`, `b=χ₂-class∈{0,1}`, `c=χ₃-class∈{0,1,2}` (validated Step 1):
`E₂=((H0+H1+H2)−(H3+H4+H5))²`; `A₃=(H0+H3)−(H2+H5)`, `B₃=(H1+H4)−(H2+H5)`, `E₃=A₃²−A₃B₃+B₃²`;
`nm=[H0,H5,H1,H3,H2,H4]`, `A₆=nm0−nm2−nm3+nm5`, `B₆=nm1+nm2−nm4−nm5`, `E₆=A₆²+A₆B₆+B₆²`;
`D₆ = Σ_{code} (H[code] − H̄[code])²` where `H̄` is the integer-rounded matched-null cell mean (ranked
against the null, so the rounding is display-safe — the rank is exact). All integers.

## Appendix B — reused, validated instrument (Step 1)
`shortscalar_cneg_recalibration_v1.py` supplies: secp constants (self-checked), uniform random points
(no scalar mult), χ₂/χ₃ classes, the integer statistics, the φ-closed forced-zero check, and the
pool-precompute + n≥20 C-NEG. New code: `[d]G` for interval d (contiguous via +G iteration), group
**addition** for `Pᵢ+Pⱼ`, D₆, and the regime/OOS driver.
