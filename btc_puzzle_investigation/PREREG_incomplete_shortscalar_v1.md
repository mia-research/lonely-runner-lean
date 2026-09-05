# PREREG — Incomplete-sum / short-scalar lift-geometry deviation (curve-arithmetic)

**FROZEN pre-registration. Written before any short-family data is seen.** Output of a run against
this spec is a CHARACTERIZATION (which law / which cell / magnitude / symmetry type) plus one pooled
decision p-value — never a verdict, never a closure (Anomaly-Drill protocol,
`feedback_anomaly_drill_protocol_2026_07_17`, binding). Freeze SHA at end of file.

Motivating frontier: `SYNTHESIS_brainstorm_seven_cycles_v1.md §4.1` ("Incomplete sums / short
scalars — no bound applies, and nothing has been run"). **Scope boundary quoted verbatim from §4.1:**
*"short scalars are a curve-arithmetic question (the distribution of `[z]P` for `z` in a box). This is
not the PRNG/generation angle and must not drift into it."* This spec studies ONLY the distribution of
`x([z]G)` for `z` in a lattice box. It says nothing about how any integer was generated
(`CLAUDE.md` scope clause; `feedback_no_prng_generation_side_2026_07_14`).

Matched-control precedent followed: `RESULT_semaev_cm_lever_v1.md` (secp j=0 / non-CM / j=1728 CM-i
as the three matched curves).

---

## 0. Baselines CONFIRMED (from first principles + RESULT files, this session)

All four complete-orbit laws are re-derived here from the public curve constants (no test data), and
agree with the record. **These are COMPLETE-ORBIT values; the whole premise (§4.1) is that NONE of
them is forced on a short subfamily.**

| law | complete-orbit baseline | source confirmed | note |
|---|---|---|---|
| **Sextant / angle** | secp: pinned pair `c0=c3=1/8` **exact**; `c1=c4=0.12970`; `c2=c5=0.24530`. Central symmetry `c_s=c_{s+3}` forced up to `O(perim/p)` boundary (`eis(−X)=−eis(X)`, `sextant(−w)=sextant(w)+3`; measured 21/40000 boundary violations). **NOT `β`-invariant: `c0≠c2≠c4`** (measured `[7480,7556,15117,7467,7538,14842]`). | `lift_sextant_law_proof_v1.py` (ran); MASTER_v4 angle law | `p₀(θ)=(3/4)|cos2θ|/(2cos2θ+1)`, secp `p₀=0.2349002681…`, θ=50.55° |
| **Norm-band** | `s=N(eis x)/p ∈ [0, 3/4]`, mean `1/6`, density `2π/√3` on `[0,3/16]`, breakpoints `3/16, 1/4, 3/4`. θ- and p-independent after scaling. | `norm_band_law_proof_v1.py` (ran: max|emp−CDF|=8e-4, E[s]=0.16678) | universality re-checked p=10009 vs secp |
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

## 1. OBJECT

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
  there feature=target by construction; here they are not.) **No tautology.**

Secondary object (EXPLORATORY): the joint `(N(z), N(eis(x([z]G))))` — the only statistic
simultaneously short-vector AND non-Fourier.

## 2. STATISTIC (exactly one decision statistic)

**Primary decision statistic `T_dev` (one number, one p-value).** For each law
`ℓ∈{sextant, norm, flap, C_T}` let `G_ℓ` be the cell-histogram discrepancy of the short family vs the
Control-(a) ensemble mean `ê_{ℓ,c}` (leave-one-out): `G_ℓ = Σ_c (o_c − M_ℓ ê_c)² / (M_ℓ ê_c)`,
computed as an exact `fractions.Fraction` on integer counts `o_c`. Convert each `G_ℓ` to its integer
**permutation rank** `R_ℓ = #{controls k : G_ℓ(control_k) ≤ G_ℓ(short)}`. The single pooled statistic is
```
        T_dev  =  R_sextant + R_norm + R_flap + R_CT      (integer, equal weight across laws)
```
ranked against the SAME control ensemble: `p_perm = (1 + #{k : T_dev(control_k) ≥ T_dev(short)}) / (1+K)`.
This is **pooled/targeted, not a max-over-cells** (a max would be upward-biased and low-power). It is
aimed at the μ₃-covariant subspace: the four `G_ℓ` are each computed on cells whose only forced
structure (F1) is absorbed by the β-closed control, so `T_dev` measures the **unforced** residual only.

**Cell definitions (all integer / exact-threshold):**
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

**Characterization output (not additional decision gates):** per-law `G_ℓ` with Holm-adjusted
permutation p-values over the 4 laws (+joint =5) at family α=0.05; per-cell signed standardized
residual `(o_c − M ê_c)/√(M ê_c)`; the driving cell(s); the **symmetry type** — is the deviation
central-symmetry-breaking (`c_s vs c_{s+3}`, F2), flap ±-asymmetry (`#{+R} vs #{−R}`), or a
μ₃-covariant reweighting? — and its magnitude at `(B, p)`.

**Secondary (EXPLORATORY) `T_joint`.** 16-cell association `(N(z) in 4 within-family quantile bands) ×
(norm-band 4 cells)`, statistic = exact `G²` on integer counts, ranked against the **internal
label-shuffle null** (permute the `N(z)` labels across the family, preserving both marginals; valid
because feature/target are disjoint-construction, §1). Reported, never a decision gate.

## 3. MATCHED CONTROLS

- **(a) FINITE-SIZE / MATCHED NULL** — *β-closed, same-size random subsets of the full orbit.* Draw
  random `d∈[1,n)`, form the μ₃-triple `{d, λd, λ²d} mod n` (x-values `{X,βX,β²X}`), take the same
  number of triples as the short family. **Preserves:** F1 (μ₃/β-closure) and equidistribution
  (hence approximate F2). **Destroys:** shortness (the box clustering near 0 in `ℤ[ω]`). Finite-size
  floor `O(1/√M)`. This is the null in `p_perm`. *(Must be β-closed — a non-β-closed shuffle is an
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
  separate plants, tilt the sextant even/odd split by `δ` and shift one norm-band's mass by `δ`. The
  primary `T_dev` **must fire** (`p_perm≤α`) at the pre-computed `δ*(B,p)` of §5. **If the plant does
  not fire at `δ*`, the test is VOID at that `(B,p)` (underpowered) — the null is uninformative, full
  stop** (`experiment-designer` rule; `feedback_test_on_both`: check the control row fires).

## 4. PLANTED CONTROL — see 3(c). Fires-criterion is `p_perm ≤ α` at injected `δ = δ*(B,p)`.

## 5. POWER

`M ≈ 3.63·B` z-values (measured ratio 3.30–3.60 at `B=10²–10⁴`, converging to `2π/√3`), i.e.
`≈ M/6 ≈ 0.55–0.60·B` β-triples (the flap-ε sample), `≈ M/2 ≈ 1.8·B` distinct x (per-sextant-cell
sample). Detectable cell-proportion shift at 4σ (single cell; pooled `T_dev` is strictly sharper):

| statistic | n | δ*(B=1e4) | δ*(B=1e5) | δ*(B=1e6) |
|---|---|---|---|---|
| flap-ε (e=1/4, n≈0.6B) | 6.0e3 / 6.0e4 / 6.0e5 | **0.022** | **0.0070** | **0.0022** |
| sextant cell (e≈0.245, n≈1.8B) | 1.8e4 / 1.8e5 / 1.8e6 | 0.013 | 0.0040 | 0.0013 |

The **expected** effect size is unknown by design (§4.1: incomplete-sum error `~√p·log p` bounds the
character sum, not the histogram proportion) — power states only what is DETECTABLE. A run reports the
`δ*` actually achieved (`M` observed) as the bound-with-power. Underpowered rungs (`B=10³`, p_lo) are
CROSS-CHECKS, explicitly not primary.

## 6. SCOPE

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
  without them.** `K = 10⁴` permutation draws; primary `α = 0.01` (one-sided upper tail on `T_dev`).

## 7. FALSIFICATION

For a given `(B,p)`: **if the primary `p_perm(T_dev) > α` on the j=0 arm AND the planted control (c)
FIRES at `δ*(B,p)`**, the pre-registered conclusion is the SCOPED, POWERED null:
> "No CM-driven short-family lift-geometry deviation of per-cell size `≥ δ*(B,p)` (flap `δ*` in §5),
> at box `B`, prime `p`, sample `M`, statistic `T_dev`."

This is a **bounded magnitude with power + scope**, NOT a closure of §4.1 (Anomaly-Drill: a drill ends
in a sharper law / bounded magnitude / named next probe). The named next probes are: larger `B`
(smaller `δ*`), finer cells, the deferred C_T dynamic-spectral operator, and the tail/extreme-value
instrument (§4.3) — none of which this null touches. A single-rung null never generalizes across the
ladder (`feedback_scope_negatives_tightly`).

## 8. EXACTNESS (NO FLOAT IN SIGNAL PATH — CLAUDE.md)

- Points: `[d]G` via integer Jacobian double-and-add (`mul_jac`), `d=(a+bλ) mod n`, all `int`.
- Lift: `eis` via `rdiv` (exact integer rounded division `q+1 if 2r≥de else q`) against the reduced
  `ℤ[ω]` basis `R1,R2` (`N(R1)=N(R2)=p`); `N(w)=u²−uv+v²`; `sextant` by integer ω-rotation
  `(u,v)→(v,v−u)`; flap `ε` and `state` by integer sign/clip. All `int` / `int64` (verified exact:
  intermediates `≤ p^{1.5} ≪ 2^{63}` at `p≤p_hi`; secp uses Python bigint).
- Cell membership: integer cross-multiplication only (`16N<3p`, etc.). Counts: `int`. `G_ℓ`:
  `fractions.Fraction`. `p_perm`: integer count ratio. **No `/`, `float()`, `**0.5`, `math.*` on any
  key/point/decomposition/feature.**
- **Float carve-outs (declared, no key in path):** (i) the C_T eigen/`G²`/log used ONLY as a monotone
  ranking value against the matched null (permitted by the no-float rule); this spec ranks the C_T
  9-cell **histogram** discrepancy (Fraction), so C_T needs no float at all in the primary path —
  the spectral version (float eigen) is the DEFERRED probe. (ii) `θ` degrees, analytic `δ*`, and CDF
  overlays are report/label only. `check_no_float.sh` must pass on the run's signal-path files.

## 9. PRE-COMMITMENT (filled BEFORE the run)

| outcome on j=0 primary | non-CM (b-i) | j=1728 (b-ii) | replicates both hash-halves? | CONCLUSION (pre-committed) |
|---|---|---|---|---|
| `p_perm≤α`, plant fires | FLAT | FLAT | yes | **μ₃/CM(j=0)-specific short-family deviation.** Characterize law/cell/symmetry-type/magnitude at (B,p). Next probe: scale B, eigenvector. |
| `p_perm≤α`, plant fires | FLAT | FIRES | yes | **CM-generic short-family deviation** (not μ₃-unique). Report per-curve magnitudes; scope. |
| `p_perm≤α`, plant fires | FIRES | — | yes | **Generic incomplete-sum ("shortness") effect, not CM.** Report as a shortness law; scope to B/p. |
| `p_perm≤α`, plant fires | any | any | **no** | Not named — treat as finite-size fluctuation/artifact; report the non-replication; no law claimed. |
| `p_perm>α`, plant fires | — | — | — | **Scoped powered null** (§7): bounded magnitude `δ*(B,p)`; NOT a closure; list next probes. |
| plant does NOT fire at δ* | — | — | — | **Test VOID at (B,p)** (underpowered); increase M (larger B); the arm is uninformative. |

**Out-of-sample partition (UP FRONT, hash-split — not a magnitude boundary).** Assign each β-triple to
half `H0/H1` by `blake2b(key=b"shortscalar-v1", (min(d,λd,λ²d)).to_bytes(40,'big')).digest()[0] & 1`
(a keyed hash of the triple's canonical scalar rep — NOT `N(z)<B/2`, which would confound with
shortness). Both halves stay β-closed. Discover on `H0`, confirm on `H1` (and symmetric). A law/cell is
NAMED (fired or zero) only if it holds on BOTH halves (`feedback_anomaly_drill_protocol`: retest
out-of-sample before naming; count only UNFORCED hits — per F3 all cells are unforced, per F1 the μ₃
correlation is matched, so every fired cell counts).

## Tooling inventory (so the spec is runnable; DO NOT run here)

**Exists / reusable:** exact `eis`, `sextant`, `N` — `eisenstein_lift_sextant_exact_v1.py`,
`lift_sextant_rhombus_law_proof_v2.py` (`reduced_basis`, `rdiv`, `enorm`). Integer Jacobian point mult
+ batch inversion + flap `ε` classifier — `flap_density_glv_prereg_v1.py` (`mul_jac`, `eps`, precomputed
`2^i·G` table). Exact 9-cell `state()` + Control-(a)-style matched surrogate — `ct_event_complete_v1.py`
(`Lift.state_vec`, `--selftest` firing calibration). β/ω action + CM-spine identity —
`glv_fundamental_domain_law_v1.py` (`om`, `om2`, `reduce_P`). Sextant/norm exact baselines —
`lift_sextant_law_proof_v1.py`, `norm_band_law_proof_v1.py` (both re-ran clean this session).

**Must be WRITTEN:** (1) the short-box enumerator `{z∈ℤ[ω]:0<N(z)<B}` → β-triple sampler →
`d=(a+bλ) mod n` → forward points (thin driver over `mul_jac`). (2) the pooled `T_dev` +
β-closed permutation engine (`R_ℓ` ranks, Fraction `G_ℓ`, `K=10⁴`). (3) the static fixed-step C_T
9-cell histogram over the box. (4) the Gaussian `ℤ[i]` lift (quadrant/flap analog) for arm b-ii — no
ready script exists. (5) the j=1728 and non-CM prime-order curve selectors at each ladder p. (6) the
`T_joint` label-shuffle engine. No component requires a discrete log; all are forward + integer.

## Ill-posed points found (disclosed, not assumed away)

1. **C_T dynamic transition operator is ill-posed on a subfamily** (family not closed under `+g`).
   Replaced by the static fixed-step 9-cell histogram; spectral/eigenvector C_T DEFERRED.
2. **j=1728 mechanism control does not exist at the secp prime** (`p≡3 mod 4` ⇒ supersingular).
   Confined to the `≡1 mod 12` ladder; secp tests only j0 vs non-CM.
3. **Non-CM arm cannot use a ℤ[ω] box** (no endomorphism) — uses a ℤ interval; the arms are matched on
   "shortness / incomplete-sum," not on box shape. Disclosed; it is the correct control for "is it just
   shortness," while b-ii (ℤ[i] box) is the correct control for "is it μ₃ or CM-generic."
4. **`T_joint` uses an internal label-shuffle null**, distinct from Control (a); valid only because
   `N(z)` (scalar) and `N(eis x)` (point) are disjoint-construction (verified §1). EXPLORATORY.

=== END OF FROZEN SPEC BODY ===

**FREEZE-SHA256** (sha256 of all bytes through the `END OF FROZEN SPEC BODY` marker line, inclusive):
`d9778fbd1fbdd97a82678c740d13479aec404efdfaa1ed1e254b6d1c494c0c20`

Verify: `python3 -c "import hashlib;d=open(0,'rb').read();m=d.find(b'=== END OF FROZEN SPEC BODY ===')+31;print(hashlib.sha256(d[:m]).hexdigest())" < PREREG_incomplete_shortscalar_v1.md`
