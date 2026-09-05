# PREREG — Incomplete-sum / short-scalar lift-geometry deviation (curve-arithmetic) — **v2**

**FROZEN pre-registration. Written before any short-family data is seen.** Output of a run against
this spec is a CHARACTERIZATION (which law / which cell / magnitude / symmetry type) plus the
per-law decision p-values — never a verdict, never a closure (Anomaly-Drill protocol,
`feedback_anomaly_drill_protocol_2026_07_17`, binding). Freeze SHA at end of file.

> ## ⚠ GRADE SLOT — `[PROVISIONAL — experiment-designer unavailable]`
>
> Per root `CLAUDE.md` §2a (decided 2026-07-30). The mandatory pre-data gate has been attempted
> **three times and has never completed**:
>
> | attempt | date | outcome |
> |---|---|---|
> | 1 | 2026-07-29 | terminated — *"Your organization has disabled Claude subscription access for Claude Code"* |
> | 2 | 2026-07-29 | terminated — weekly limit, 3 tool calls in, partial output only |
> | 3 | 2026-07-30 | stalled — no progress for 600s, stream watchdog did not recover; had reached §8 |
>
> Three attempts, three distinct causes, no completed run. This is a persistent inability, not a
> transient outage — weigh the "gate owed" debt accordingly.
>
> **Unaudited sections, named explicitly (§2a condition 2 — absence from an audit is not clearance):**
> - **FRAME layers — isolation is the mechanism, self-audit CANNOT discharge these:**
>   §1 object/disjointness · §3 matched-control adequacy · §6 scope · §7 falsification ·
>   §9 pre-commitment.
>   *(v1's self-audit listed §1 as covered. §1 is a frame layer — disjoint construction is exactly
>   the retraction-24 tautology trap — so that coverage claim is withdrawn here.)*
> - **MECHANICAL layers still owed:** §4 plant-fires (never run) · §8 exactness grep (attempt 3
>   stalled at precisely this section).
> - **MECHANICAL layers discharged with artifacts:** §2 statistic (null calibration) and §5 power —
>   see §2·CAL and §5·CEIL below.
>
> **§2a condition 4 — NO GRADE PROMOTION.** A run against this spec produces evidence; it cannot
> move any claim up a grade until the gate clears.

Motivating frontier: `SYNTHESIS_brainstorm_seven_cycles_v1.md §4.1` ("Incomplete sums / short
scalars — no bound applies, and nothing has been run"). **Scope boundary quoted verbatim from §4.1:**
*"short scalars are a curve-arithmetic question (the distribution of `[z]P` for `z` in a box). This is
not the PRNG/generation angle and must not drift into it."* This spec studies ONLY the distribution of
`x([z]G)` for `z` in a lattice box. It says nothing about how any integer was generated
(`CLAUDE.md` scope clause; `feedback_no_prng_generation_side_2026_07_14`).

Matched-control precedent followed: `RESULT_semaev_cm_lever_v1.md` (secp j=0 / non-CM / j=1728 CM-i
as the three matched curves).

---

## CHANGELOG v1 → v2  *(the only substantive change is §2; everything downstream follows from it)*

**v1 is superseded and must not be run as written.** Its decision statistic was provably blind to
the effect the spec was built to detect.

1. **§2 INVERTED (the repair).** The per-law `G_ℓ` permutation tests with Holm adjustment are now
   the **PRIMARY decision**; the pooled rank-sum `T_dev` is **demoted to characterization**. v1 had
   these exactly backwards. No new machinery — v1 already computed both; this is a relabelling.
2. **§5 rewritten** to state the power of the rule that actually decides, and to carry the ceiling
   proof for the demoted statistic.
3. **§3(c), §6 (α), §7, §9 restated** in terms of the per-law rule, so the spec is internally
   consistent. v1 additionally carried two different α's (§6 said `α=0.01` on `T_dev`; §2's
   characterization line said family `α=0.05` Holm) — resolved to one.
4. **Grade slot added** (above) per `CLAUDE.md` §2a.
5. **§2·CAL** records the outstanding null-calibration debt.

Unchanged from v1 and carried verbatim: §0 baselines and the forced-structure ledger (F1–F3), §1
object, §3(a)(b) controls, §6 curve family and p-ladder, §8 exactness, the out-of-sample hash-split,
the tooling inventory, and the four disclosed ill-posed points.

---

## 0. Baselines CONFIRMED (from first principles + RESULT files)

All four complete-orbit laws are re-derived from the public curve constants (no test data), and
agree with the record. **These are COMPLETE-ORBIT values; the whole premise (§4.1) is that NONE of
them is forced on a short subfamily.**

| law | complete-orbit baseline | source confirmed | note |
|---|---|---|---|
| **Sextant / angle** | secp: pinned pair `c0=c3=1/8` **exact**; `c1=c4=0.12970`; `c2=c5=0.24530`. Central symmetry `c_s=c_{s+3}` forced up to `O(perim/p)` boundary (`eis(−X)=−eis(X)`, `sextant(−w)=sextant(w)+3`; measured 21/40000 boundary violations). **NOT `β`-invariant: `c0≠c2≠c4`** (measured `[7480,7556,15117,7467,7538,14842]`). | `lift_sextant_law_proof_v1.py` (ran); MASTER_v4 angle law | `p₀(θ)=(3/4)|cos2θ|/(2cos2θ+1)`, secp `p₀=0.2349002681…`, θ=50.55° |
| **Norm-band** | `s=N(eis x)/p ∈ [0, 3/4]`, mean `1/6`, density `2π/√3` on `[0,3/16]`, breakpoints `3/16, 1/4, 3/4`. θ- and p-independent after scaling. | `norm_band_law_proof_v1.py` (ran: max\|emp−CDF\|=8e-4, E[s]=0.16678) | universality re-checked p=10009 vs secp |
| **Flap / CM-spine** | Cap Law: `ε(x)≠0 ⟺ |u−v|>1/2`; core:flap⁺:flap⁻ = `3/4 : 1/8 : 1/8`. `ε∈{0,+R,−R}` is a **μ₃-orbit invariant** (constant on `{X,βX,β²X}`), ⊥χ₆. | ran (p=1e6+3, N=2e5): core `0.7510`, `+R 0.1247`, `−R 0.1242` | corrections `c=eis(βX)−ζ·eis(X)∈{0,+R,−R}` |
| **C_T** | 9×9 carry-state operator on `(c₁,c₂)∈{−1,0,1}²` of `eis(x_P)+eis(x_Q)`; tensor law `C_T≈C₁⊗C₂`, degenerate block trace `2/3`. | `ct_event_complete_v1.py`; `ANOMALY_DRILL_01_CT_SPLIT_v1.md` | dynamic operator scope = "this orbit / generator / prime" |

Secp GLV data confirmed: `p≡7 mod 12` (⇒ `p≡1 mod 3` j=0 OK, but `p≡3 mod 4` ⇒ **j=1728 is
supersingular at the secp prime — the μ₄ mechanism control CANNOT run there**); GLV eigenvalue
`λ = 0xac9c52b33fa3cf1f5ad9e3fd77ed9ba4a880b9fc8ec739c2e0cfc810b51283ce` (`λ²+λ+1≡0 mod n`, verified).

**Forced-structure ledger (drives control design).**
- **F1 — μ₃/β-closure of the x-multiset.** The box `{N(z)<B}` is exactly closed under `z↦ωz`
  (`N(ωz)=N(z)`), and `x([ωz]G)=β·x([z]G)`; `[−z]G` has the same x. So the short-family x-multiset is
  **exactly β-closed (μ₃)**, identical in kind to the complete orbit. β-closure does **NOT** force a
  marginal symmetry (`c0≠c2≠c4` above) — it induces μ₃-**triple correlations** (variance structure).
  *A control that is not β-closed would mis-estimate the null variance — the exact
  "shuffle destroys a symmetry the readout has by definition" trap (`feedback` μ₆-null-mismatch,
  DRILL notes). Hence Control (a) is β-closed.*
- **F2 — central symmetry `c_s=c_{s+3}`.** Holds for the COMPLETE orbit / uniform-X (via
  equidistribution), NOT necessarily for the short family (not closed under `X↦−X`). Therefore it is
  **an observable, not a forced-equal collapse**: keep all 6 sextant cells; a short-family
  `c_s≠c_{s+3}` is a genuine deviation.
- **F3 — the values themselves** (area-law proportions, `1/6`, `3/4:1/8:1/8`, `C_T≈C₁⊗C₂`) are
  complete-orbit values; **unforced on any subfamily** (§4.1). Nothing is forced to MATCH between
  short and complete → no cell carries zero information a priori.

---

## 1. OBJECT  *(unchanged from v1 — but see grade slot: this is a FRAME layer and is UNAUDITED)*

For a curve `E: y²=x³+b` over `𝔽_p` with `p≡1 mod 3`, CM by `ℤ[ω]`, `G` of prime order `n`, and box
bound `B`, the object is the **cell distribution of the four proved lift-geometry readouts of the
x-coordinate `x([z]G)`, taken over the short-scalar family `{z∈ℤ[ω] : 0<N(z)<B}`** (points computed
FORWARD via GLV: `z=a+bω ↦ d=(a+bλ) mod n ↦ [d]G`; `λ` = root of `x²+x+1 mod n`; cheap, no discrete
log), compared against the complete-orbit baseline of §0.

- **Sample unit = a β-triple** `{X,βX,β²X}` of distinct x-values (one per μ₆-orbit of `z`; `z=0`
  excluded). This removes the ±-multiplicity nuisance and makes F1 explicit.
- Feature and target are **disjoint-construction**: the readout is a function of the POINT
  `x([z]G)` and the prime `p`; the box index `N(z)` is a function of the SCALAR. The only link is the
  ECDLP-hard map `z↦[z]G`. (Contrast the `r=v−w` tautology, `feedback_residue_vs_component_tautology`:
  there feature=target by construction; here they are not.) **No tautology claimed — and this claim
  is exactly what the unavailable gate would have checked. It rests on our own reading.**

Secondary object (EXPLORATORY): the joint `(N(z), N(eis(x([z]G))))` — the only statistic
simultaneously short-vector AND non-Fourier.

## 2. STATISTIC — **per-law Holm is PRIMARY** *(inverted from v1)*

### 2.1 Per-law discrepancy (unchanged construction)

For each law `ℓ∈{sextant, norm, flap, C_T}` let `G_ℓ` be the cell-histogram discrepancy of the short
family vs the Control-(a) ensemble mean `ê_{ℓ,c}` (leave-one-out):
`G_ℓ = Σ_c (o_c − M_ℓ ê_c)² / (M_ℓ ê_c)`, computed as an exact `fractions.Fraction` on integer counts
`o_c`. Its permutation p-value against the same β-closed ensemble is the integer ratio
```
        p_ℓ  =  (1 + #{k : G_ℓ(control_k) ≥ G_ℓ(short)}) / (1 + K)
```

### 2.2 ★ PRIMARY DECISION RULE

> **Holm step-down over the 5 tests `{sextant, norm, flap, C_T, joint}` at family-wise `α = 0.05`.**
> Sort `p_(1) ≤ … ≤ p_(5)`; reject `p_(i)` iff `p_(j) ≤ α/(5−j+1)` for all `j ≤ i`.
> **The arm FIRES iff at least one law is rejected after Holm.** The rejected law(s) name the
> deviation; a per-law rejection is the unit of the finding.

Holm controls FWER at 0.05 over the family, so no additional pooled gate is needed or permitted.

### 2.3 `T_dev` — DEMOTED to characterization

`T_dev = R_sextant + R_norm + R_flap + R_CT` (integer permutation ranks, equal weight), ranked
against the same ensemble. **Reported as a characterization number only. It decides nothing.**

**Why it was demoted — `[PROVED]`, exactly, artifact `tdev_ceiling_exact_v1.py`.** Against a
deviation confined to ONE law, in the best possible case for the statistic (that law's rank pinned
at its maximum, `R_ℓ = K`, the other three uninformative):

| | `H₀`: `T/K ~ Irwin-Hall(4)` | `H₁`: `T/K ~ 1 + Irwin-Hall(3)` |
|---|---|---|
| | mean 2, sd 0.577 | mean 2.5, sd 0.500 |

| α | exact critical value | **`T_dev` power CEILING** |
|---|---|---|
| 0.05 | 2.953361 | **0.1910** |
| **0.01** (v1's actual primary α, §6) | 3.300073 | **0.0571** |

Three consequences, each decidable:
1. **The ceiling is `K`-independent.** Both laws are expressed in units of `K`, so `K=199` and
   `K=10⁴` give the same limit. v1's `K=10⁴` does not rescue it.
2. **It is a ceiling, not an estimate.** It assumes the informative rank is *saturated*; no effect
   size, however large, exceeds it. This is why the earlier simulation saw power *fall* from
   `δ=0.08` (0.193) to `δ=0.12` (0.181) — it was already at the ceiling and adding effect only
   added noise through the other three ranks.
3. **At v1's own `α=0.01` the ceiling is 0.0571** — against a 0.01 false-positive rate. v1's
   decision statistic was very nearly blind to the effect the spec exists to detect.

The exact computation reproduces the independent simulation (0.189–0.193 at α=0.05 vs 0.1910
predicted), so the empirical and analytical routes agree.

**Contrast, same saturated case, single-law test:** `p_flap = 1/(1+K)`, which fires at `α=0.01` for
any `K ≥ 99`. Prior simulation of the per-law rule with Holm×4 at family α=0.05 measured power
**0.984 at `δ=0.05`** and **0.310 at `δ=0.02`**, against 0.189 and 0.152 for the pooled rule.

### 2.4 Cell definitions (all integer / exact-threshold; unchanged)

- Sextant: 6 cells `sextant(eis(X))∈{0..5}` (keep all 6 per F2).
- Norm-band: 4 cells by `s=N(eis X)/p` via integer compares — `16N<3p` | `16N≥3p ∧ 4N<p` |
  `4N≥p ∧ 2N<p` | `2N≥p`.
- Flap: 3 cells `ε∈{0,+R,−R}` from `c=eis(βX)−ζ·eis(X)` (one ε per β-triple; exact integer vector
  match to `{0, +R, −R}`).
- C_T (static, well-posed on a subfamily): for a FIXED step set `g∈{1,ω,1+ω,−1,−ω,−(1+ω)}` (the 6
  units), the 9-cell carry-state `state(eis(x([z]G)), eis(x([z+g]G)))∈{0..8}`, pooled over `z` and the
  6 steps. **The DYNAMIC transition operator `s_g[d]→s_g[d+g]` (ct_event_complete) is ILL-POSED on a
  subfamily** (the family is not closed under `+g`); it is replaced by this static fixed-step histogram
  and the spectral/eigenvector version is DEFERRED (named next probe, not run here).

### 2.5 Characterization output (never a decision gate)

`T_dev` (§2.3); per-cell signed standardized residual `(o_c − M ê_c)/√(M ê_c)`; the driving cell(s);
the **symmetry type** — is the deviation central-symmetry-breaking (`c_s vs c_{s+3}`, F2), flap
±-asymmetry (`#{+R} vs #{−R}`), or a μ₃-covariant reweighting? — and its magnitude at `(B, p)`.

### 2.6 Secondary (EXPLORATORY) `T_joint`

16-cell association `(N(z) in 4 within-family quantile bands) × (norm-band 4 cells)`, statistic =
exact `G²` on integer counts, ranked against the **internal label-shuffle null** (permute the `N(z)`
labels across the family, preserving both marginals; valid because feature/target are
disjoint-construction, §1). `T_joint` enters the Holm family as the 5th test (§2.2); its own
label-shuffle null is distinct from Control (a) and that distinction is disclosed in ill-posed
point 4.

### 2.7 §2·CAL — null calibration, OWED before the run

Prior simulation of the per-law nulls was clean in both runs (per-law flap `FPR@.05 = 0.055`;
Holm×4 at family .05 → `0.011`, i.e. conservative). **But two runs of the pooled null disagreed
(`FPR@.05` of `0.0493` vs `0.074`, ≈3σ apart on their own Monte-Carlo error), and no ≥10⁴-rep
calibration has been done for either.**

**Required before any arm executes:** a ≥10⁴-rep calibration of the PRIMARY (per-law + Holm) rule at
family `α=0.05`, reporting realized FWER. If realized FWER exceeds 0.05 the rule is not usable as
written. The pooled `T_dev` null needs no calibration — it decides nothing.

## 3. MATCHED CONTROLS  *(3(a),(b) unchanged; 3(c) restated for the new primary — FRAME layer, UNAUDITED)*

- **(a) FINITE-SIZE / MATCHED NULL** — *β-closed, same-size random subsets of the full orbit.* Draw
  random `d∈[1,n)`, form the μ₃-triple `{d, λd, λ²d} mod n` (x-values `{X,βX,β²X}`), take the same
  number of triples as the short family. **Preserves:** F1 (μ₃/β-closure) and equidistribution
  (hence approximate F2). **Destroys:** shortness (the box clustering near 0 in `ℤ[ω]`). Finite-size
  floor `O(1/√M)`. This is the null in every `p_ℓ`. *(Must be β-closed — a non-β-closed shuffle is an
  invalid null here, F1.)*
- **(b) MECHANISM** — *is the deviation CM-driven, CM-generic, or just shortness?* Same statistic on:
  - **(b-i) non-CM curve, same `p`, short INTERVAL** `z∈{c₀,…,c₀+B−1}⊂ℤ` (no ℤ[ω]/GLV exists off
    j=0; the only short-scalar notion is an integer interval). `eis/sextant/norm/flap` are properties
    of `p` (not the curve) so are defined identically. Its matched control = random same-size subsets
    (the interval is not β-closed, so **this arm's** null is NOT β-closed — each arm matches its own
    symmetry). **MUST STAY FLAT** if the effect is CM-driven; if it FIRES, the effect is generic
    incomplete-sum ("shortness"), not CM.
  - **(b-ii) j=1728 curve `y²=x³+ax`, `p≡1 mod 4`, ℤ[i] box** `{z∈ℤ[i] : N(z)<B}`,
    `N(a+bi)=a²+b²`; lift into the Gaussian square domain (μ₄; the i-endomorphism `(x,y)↦(−x,iy)` sends
    `x↦−x`, so the x-multiset is μ₂-closed under `X↦−X` — this arm's control (a) is μ₂-closed). **FLAT
    ⟹ the deviation is μ₃-specific to j=0; FIRES ⟹ CM-generic** (any CM box deviates from its own law).
  - *Fires/flat table:* CM(j=0)-μ₃ ⟹ {j0 FIRES, b-i FLAT, b-ii FLAT}; CM-generic ⟹ {j0 FIRES, b-i
    FLAT, b-ii FIRES}; shortness-generic ⟹ {all FIRE incl. b-i}.
  - **Scope:** b-ii requires `p≡1 mod 4` ⇒ runs on the ladder rungs (all `≡1 mod 12`) but **NOT at
    the secp prime** (`p≡3 mod 4`). At secp only j0 + b-i run.
- **(c) PLANTED / POSITIVE (power)** — take a Control-(a) draw and move a KNOWN fraction `δ` of
  β-triples from `ε=0` (core) to `ε=+R` (a flap-density deviation of exactly `δ` from `1/4`); also, in
  separate plants, tilt the sextant even/odd split by `δ` and shift one norm-band's mass by `δ`.
  **FIRES-CRITERION (restated for the new primary): the plant must be REJECTED BY THE HOLM RULE of
  §2.2** at the pre-computed `δ*(B,p)` of §5 — not `p_perm(T_dev) ≤ α`, which v1 required and which
  §2.3 proves could not have been met more than 5.7% of the time at v1's α.
  **If the plant does not fire at `δ*`, the test is VOID at that `(B,p)` (underpowered) — the null is
  uninformative, full stop** (`feedback_test_on_both`: check the control row fires).

## 4. PLANTED CONTROL — see 3(c). Fires-criterion = Holm rejection at injected `δ = δ*(B,p)`.

*(MECHANICAL layer, OWED — never run; see grade slot.)*

## 5. POWER — of the rule that actually decides

`M ≈ 3.63·B` z-values (measured ratio 3.30–3.60 at `B=10²–10⁴`, converging to `2π/√3`), i.e.
`≈ M/6 ≈ 0.55–0.60·B` β-triples (the flap-ε sample), `≈ M/2 ≈ 1.8·B` distinct x (per-sextant-cell
sample).

**These `δ*` are single-cell/single-law 4σ thresholds — which is now the correct instrument, because
the per-law test is primary.** In v1 this table described a different instrument than the one that
decided; that mismatch is the defect this version repairs.

| statistic | n | δ*(B=1e4) | δ*(B=1e5) | δ*(B=1e6) |
|---|---|---|---|---|
| flap-ε (e=1/4, n≈0.6B) | 6.0e3 / 6.0e4 / 6.0e5 | **0.022** | **0.0070** | **0.0022** |
| sextant cell (e≈0.245, n≈1.8B) | 1.8e4 / 1.8e5 / 1.8e6 | 0.013 | 0.0040 | 0.0013 |

**Measured power of the primary rule** (prior simulation, `M=2000`, `K=199`, flap plant, Holm×4 at
family α=0.05): `δ=0.02 → 0.310`; `δ=0.05 → 0.984`; `δ≥0.08 → 1.000`. Consistent with the `δ*=0.022`
row.

### 5·CEIL — the demoted statistic, for the record
`[PROVED]`, `tdev_ceiling_exact_v1.py`: pooled `T_dev` cannot exceed **0.1910** power at α=0.05 or
**0.0571** at α=0.01 against a one-law deviation, at any effect size and any `K`. See §2.3.

The **expected** effect size is unknown by design (§4.1: incomplete-sum error `~√p·log p` bounds the
character sum, not the histogram proportion) — power states only what is DETECTABLE. A run reports the
`δ*` actually achieved (`M` observed) as the bound-with-power. Underpowered rungs (`B=10³`, p_lo) are
CROSS-CHECKS, explicitly not primary.

## 6. SCOPE  *(unchanged except α; FRAME layer, UNAUDITED)*

- **Curve family:** j=0 `y²=x³+b` (b=7 where a prime-order curve exists, else smallest such b),
  `G` prime-order, forward GLV points only.
- **p-ladder (frozen, all `≡1 mod 12` except secp):**
  - `p_val = 4000081` — instrument validation: enumerate the FULL orbit for the exact empirical
    baseline; confirm analytic law, Control-(a) variance, and plant firing. No short-family claim.
  - `p_lo  = 1000000009` (√p≈3.16e4), `B∈{1000}` (`B/√p≈0.03`) — cross-check rung (weak power).
  - `p_mid = 10000000000129` (√p≈3.16e6), `B∈{1e4, 1e5}` (`B/√p≈3e-3 … 3e-2`) — PRIMARY.
  - `p_hi  = 10000000000000000273` (√p≈3.16e9), `B∈{1e5, 1e6}` (`B/√p≈3e-5 … 3e-4`) — PRIMARY.
  - `secp` (`p≡7 mod 12`), `B∈{1e5, 1e6}` — PRIMARY, **j0 + non-CM only (no j=1728, §0)**.
- Mechanism arms (b-i, b-ii) run at every rung where their prime condition holds (b-ii: ladder only).
- **Every number the run emits inherits `(law, cell, B, p, statistic, n=M)` and may not be stated
  without them.**
- **`K = 10⁴` permutation draws. ONE α: family-wise `α = 0.05` via Holm over the 5 tests (§2.2).**
  (v1 carried `α=0.01` on `T_dev` in this section and `α=0.05` Holm in §2 — resolved.)

## 7. FALSIFICATION  *(restated for the per-law rule; FRAME layer, UNAUDITED)*

For a given `(B,p)`: **if NO law is rejected by the Holm rule of §2.2 on the j=0 arm AND the planted
control (c) FIRES at `δ*(B,p)`**, the pre-registered conclusion is the SCOPED, POWERED null:
> "No CM-driven short-family lift-geometry deviation of per-cell size `≥ δ*(B,p)` (flap `δ*` in §5),
> at box `B`, prime `p`, sample `M`, per-law Holm rule at family α=0.05."

This is a **bounded magnitude with power + scope**, NOT a closure of §4.1 (Anomaly-Drill: a drill ends
in a sharper law / bounded magnitude / named next probe). The named next probes are: larger `B`
(smaller `δ*`), finer cells, the deferred C_T dynamic-spectral operator, and the tail/extreme-value
instrument (§4.3) — none of which this null touches. A single-rung null never generalizes across the
ladder (`feedback_scope_negatives_tightly`).

**A null under this spec is additionally capped by the grade slot:** it is `[PROVISIONAL]` and, per
`CLAUDE.md` §2a condition 4, cannot be promoted or cited as a settled bound until the gate clears.

## 8. EXACTNESS (NO FLOAT IN SIGNAL PATH — CLAUDE.md)  *(unchanged; MECHANICAL, grep OWED)*

- Points: `[d]G` via integer Jacobian double-and-add (`mul_jac`), `d=(a+bλ) mod n`, all `int`.
- Lift: `eis` via `rdiv` (exact integer rounded division `q+1 if 2r≥de else q`) against the reduced
  `ℤ[ω]` basis `R1,R2` (`N(R1)=N(R2)=p`); `N(w)=u²−uv+v²`; `sextant` by integer ω-rotation
  `(u,v)→(v,v−u)`; flap `ε` and `state` by integer sign/clip. All `int` / `int64` (verified exact:
  intermediates `≤ p^{1.5} ≪ 2^{63}` at `p≤p_hi`; secp uses Python bigint).
- Cell membership: integer cross-multiplication only (`16N<3p`, etc.). Counts: `int`. `G_ℓ`:
  `fractions.Fraction`. `p_ℓ` and the Holm comparisons: integer count ratios, compared by integer
  cross-multiplication (`p_ℓ = a/(1+K)` vs `α/(5−j+1)` ⇒ compare `a·(5−j+1)·100` vs `5·(1+K)`).
  **No `/`, `float()`, `**0.5`, `math.*` on any key/point/decomposition/feature.**
- **Float carve-outs (declared, no key in path):** (i) the C_T eigen/`G²`/log used ONLY as a monotone
  ranking value against the matched null (permitted by the no-float rule); this spec ranks the C_T
  9-cell **histogram** discrepancy (Fraction), so C_T needs no float at all in the primary path —
  the spectral version (float eigen) is the DEFERRED probe. (ii) `θ` degrees, analytic `δ*`, and CDF
  overlays are report/label only. `check_no_float.sh` must pass on the run's signal-path files.
- **OWED:** the gate's §8 grep over every named script has never completed (attempt 3 stalled here).
  `check_no_float.sh` must be run and its output attached before any arm executes.

## 9. PRE-COMMITMENT (filled BEFORE the run)  *(restated for the per-law rule; FRAME layer, UNAUDITED)*

"FIRES" below means **rejected by the Holm rule of §2.2**.

| outcome on j=0 primary | non-CM (b-i) | j=1728 (b-ii) | replicates both hash-halves? | CONCLUSION (pre-committed) |
|---|---|---|---|---|
| ≥1 law fires, plant fires | FLAT | FLAT | yes | **μ₃/CM(j=0)-specific short-family deviation** in the named law(s). Characterize law/cell/symmetry-type/magnitude at (B,p). Next probe: scale B, eigenvector. |
| ≥1 law fires, plant fires | FLAT | FIRES | yes | **CM-generic short-family deviation** (not μ₃-unique). Report per-curve magnitudes; scope. |
| ≥1 law fires, plant fires | FIRES | — | yes | **Generic incomplete-sum ("shortness") effect, not CM.** Report as a shortness law; scope to B/p. |
| ≥1 law fires, plant fires | any | any | **no** | Not named — treat as finite-size fluctuation/artifact; report the non-replication; no law claimed. |
| no law fires, plant fires | — | — | — | **Scoped powered null** (§7): bounded magnitude `δ*(B,p)`; NOT a closure; list next probes. |
| plant does NOT fire at δ* | — | — | — | **Test VOID at (B,p)** (underpowered); increase M (larger B); the arm is uninformative. |

**Which law fires is part of the finding, not a nuisance.** Under Holm the rejected law names the
deviation; report the full sorted `p_ℓ` vector in every case, fired or not, so that a later run can
compare the whole profile rather than a single bit.

**Out-of-sample partition (UP FRONT, hash-split — not a magnitude boundary).** Assign each β-triple to
half `H0/H1` by `blake2b(key=b"shortscalar-v1", (min(d,λd,λ²d)).to_bytes(40,'big')).digest()[0] & 1`
(a keyed hash of the triple's canonical scalar rep — NOT `N(z)<B/2`, which would confound with
shortness). **The key string stays `shortscalar-v1` deliberately** — changing it would re-randomize
the split and constitute a second look. Both halves stay β-closed. Discover on `H0`, confirm on `H1`
(and symmetric). A law/cell is NAMED (fired or zero) only if it holds on BOTH halves
(`feedback_anomaly_drill_protocol`: retest out-of-sample before naming; count only UNFORCED hits —
per F3 all cells are unforced, per F1 the μ₃ correlation is matched, so every fired cell counts).

## Tooling inventory (so the spec is runnable; DO NOT run here)

**Exists / reusable:** exact `eis`, `sextant`, `N` — `eisenstein_lift_sextant_exact_v1.py`,
`lift_sextant_rhombus_law_proof_v2.py` (`reduced_basis`, `rdiv`, `enorm`). Integer Jacobian point mult
+ batch inversion + flap `ε` classifier — `flap_density_glv_prereg_v1.py` (`mul_jac`, `eps`, precomputed
`2^i·G` table). Exact 9-cell `state()` + Control-(a)-style matched surrogate — `ct_event_complete_v1.py`
(`Lift.state_vec`, `--selftest` firing calibration). β/ω action + CM-spine identity —
`glv_fundamental_domain_law_v1.py` (`om`, `om2`, `reduce_P`). Sextant/norm exact baselines —
`lift_sextant_law_proof_v1.py`, `norm_band_law_proof_v1.py`. Power ceiling of the demoted pooled
statistic — `tdev_ceiling_exact_v1.py` (ran; §2.3).

**Must be WRITTEN:** (1) the short-box enumerator `{z∈ℤ[ω]:0<N(z)<B}` → β-triple sampler →
`d=(a+bλ) mod n` → forward points (thin driver over `mul_jac`). (2) the per-law `G_ℓ` + Holm engine
with the β-closed permutation null (`Fraction` `G_ℓ`, integer `p_ℓ`, `K=10⁴`) — **and its ≥10⁴-rep
FWER calibration, §2·CAL**. (3) the static fixed-step C_T 9-cell histogram over the box. (4) the
Gaussian `ℤ[i]` lift (quadrant/flap analog) for arm b-ii — no ready script exists. (5) the j=1728 and
non-CM prime-order curve selectors at each ladder p. (6) the `T_joint` label-shuffle engine.
No component requires a discrete log; all are forward + integer.

## Ill-posed points found (disclosed, not assumed away)

1. **C_T dynamic transition operator is ill-posed on a subfamily** (family not closed under `+g`).
   Replaced by the static fixed-step 9-cell histogram; spectral/eigenvector C_T DEFERRED.
2. **j=1728 mechanism control does not exist at the secp prime** (`p≡3 mod 4` ⇒ supersingular).
   Confined to the `≡1 mod 12` ladder; secp tests only j0 vs non-CM.
3. **Non-CM arm cannot use a ℤ[ω] box** (no endomorphism) — uses a ℤ interval; the arms are matched on
   "shortness / incomplete-sum," not on box shape. Disclosed; it is the correct control for "is it just
   shortness," while b-ii (ℤ[i] box) is the correct control for "is it μ₃ or CM-generic."
4. **`T_joint` uses an internal label-shuffle null**, distinct from Control (a); valid only because
   `N(z)` (scalar) and `N(eis x)` (point) are disjoint-construction (§1 — itself unaudited).
5. **(v2)** The four `G_ℓ` are not independent — they are four readouts of the same x-multiset.
   Holm is valid under arbitrary dependence (it needs no independence assumption), so the FWER
   guarantee holds; but the *realized* FWER may be conservative, costing power. §2·CAL measures it.
   Do not substitute Šidák or a Simes/Hochberg step-up, which do require positive dependence that has
   not been established here.

=== END OF FROZEN SPEC BODY ===

**FREEZE-SHA256** (sha256 of all bytes through the `END OF FROZEN SPEC BODY` marker line, inclusive):
`d560abddebdeee87ad15721773a842b08e6d77903b3dff11eca8a52d7645ae5c`

Verify: `python3 -c "import hashlib;d=open(0,'rb').read();m=d.find(b'=== END OF FROZEN SPEC BODY ===')+31;print(hashlib.sha256(d[:m]).hexdigest())" < PREREG_incomplete_shortscalar_v2.md`
