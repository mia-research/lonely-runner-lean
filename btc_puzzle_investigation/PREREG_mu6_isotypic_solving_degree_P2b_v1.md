# PREREG — P2b: does the ω-isotypic block structure of the σ-invariant target-orbit Semaev ideal give a genuine SOLVING-DEGREE lever, or only the known ≤κ=3 constant-factor speedup?

**Date:** 2026-08-14. **Status:** PRE-RUN. No per-isotype `d_LF` computed on real cells. To `experiment-designer` before any scored run. No leakage/ECDLP claim; model-scale.

## Provenance / why this exists
`RESULT_mu6_solving_degree_v1.md` (P2) found `Δ(d_LF)=0` quo-matched for the **fixed-target** system, and named follow-up #1: "measure the ω-isotypic decomposition of the Gröbner staircase — the subspace a scalar `d_LF` cannot see." Exploratory probes (`omega_isotypic_staircase_v1/v2.py`, exact, p=523, m=3, both controls fire) established:
- the **fixed-target** decomposition ideal is provably **not** σ-invariant (σ: xᵢ↦βxᵢ *rotates the target*, `σ(Sx)=S(x,β⁻¹t)`, κ=0) — so P2 measured the symmetry-**broken** object;
- the **target-orbit** ideal (`xT³−t³`, targets {t,βt,β²t} together) **is σ-invariant, 0-dim**, quotient 36 = **12/12/12** ω-isotypic, top-degrees {6,4,5}.
So the well-posed "symmetry supplies syzygies" object exists. This prereg tests whether it is a **degree** lever.

## Object
The σ-invariant target-orbit Semaev decomposition ideal `I` for the j=0 CM curve `E:y²=x³+7`, on a μ₃-invariant factor base V, at model primes `p≡1 mod3`. `R/I` carries the diagonal σ-action (β³=1); the Macaulay matrix block-diagonalizes by ω-isotype for σ-invariant `I`.

## Statistic (frozen)
Per-isotype last-fall degree `d_LF^(r)`, r∈{0,1,2}, from `macaulay_stats` restricted to the ω-isotype-r column/row blocks (exact GF(p) rank; extends `semaev_elimination_v1.macaulay_stats` by an isotype mask on monomials by total-degree mod 3 — valid **only** because σ preserves `I`, verified per cell). Primary:
> **`Δ_iso = d_LF(whole target-orbit I) − max_r d_LF^(r)`** for j0.
`max_r` because the blocks solve independently, so the effective degree is the max per-block.

## Pre-committed reading
- **`Δ_iso ≥ 1`** (a block resolves ≥1 degree below the whole) **AND** the matched-nonCM control shows `Δ_iso^{nonCM}=0` → the μ₆ isotypic structure gives a genuine **degree** lever the scalar P2 null missed. Report magnitude + power + scope; next probe = scaling with (m,|V|) and whether it beats generic √p.
- **`Δ_iso = 0`** (every block resolves at the whole's degree) → no degree lever; the target-orbit structure is at most the **known ≤κ=3 constant-factor** automorphism speedup (bounded, not a lever). Report as a scoped component null with power+scope (per `feedback_negative_bias_enlarge_nulls`) — the well-posed object is now measured, not "μ₆ dead".

## Controls (all must fire; no verdict if any fails)
- **σ-invariance gate (per cell):** verify `σ` preserves `I` before decomposing (else the isotype mask is meaningless → skip cell). Already True on target-orbit, False on fixed-target/generic (probe v1/v2).
- **FIRING PLANT — certified per-block gap:** a σ-invariant ideal with a KNOWN per-isotype `d_LF` gap (e.g. `x_i³−c_i` blocks resolving at different degrees, top-degs {6,4,5} observed); the per-isotype machinery must read the gap. If it does not → instrument blind → VOID.
- **Matched-nonCM arm:** a #E-matched non-CM curve has no μ₃ automorphism; build its "target-orbit" from 3 *arbitrary* (non-μ₃) targets → **no** σ-invariance → `Δ_iso^{nonCM}` must be null/undefined. Isolates μ₆ from the mere act of bundling 3 targets.
- **C-NOFLOAT:** AST check; signal path integer/GF(p).

## Power & scope
Small Gröbner-tractable `p` (start {523,541,547,571,577,601}), m=3, |V|∈{invariant-9}; report whether `d_LF^(r)` varies by integer across configs (liveness) and the MDE (smallest detectable `Δ_iso`). **Scope = these primes/m; does not reach secp** — a lever claim at scale needs the *mechanism* (why the ω-grading drops a block's regularity), not these numbers. Output = characterization + power + scope, never a verdict.

## Falsification
If the FIRING PLANT shows no per-block gap where one is planted, the instrument is blind → no result.

## Anti-bias note (binding on the report)
Two traps, both pre-committed against: (i) **suppression** — a `Δ_iso=0` is a scoped null on the *now-correct* object, NOT a closure of the CM/Semaev avenue (m=4/5, the yield channel, and full IC-cost remain open, exactly as P2 stated). (ii) **inflation** — a `Δ_iso≥1` must be separated from the known ≤κ=3 constant-factor speedup: a degree drop is a lever only if it is not reproducible by the matched-nonCM 3-target bundling (the control), and only as a bounded magnitude with stated power until scaling is shown.

## Gates / deliverables
`experiment-designer` before run; `check_no_float`; `compile-diff` if promoted (target master **v9**). Deliverables: `mu6_isotypic_solving_degree_P2b_v1.sage` (extends `semaev_elimination_v1`, ≤300 lines); `RESULT_…_v1.md` (graded, power+scope).
