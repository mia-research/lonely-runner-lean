# PREREG — joint public-readout → d-residue test (T2c, hardened, BLINDED build)

**File:** `PREREG_t2c_joint_readout_dmod3_v1.md`  **Date:** 2026-08-13  **Status:** POST-RUN (unblinded §10).
Supersedes/extends the under-powered `RESULT_t2c_j_range_dmod3_v1.md` (V_detect≈0.2, 2 scan curves).

## 0. Live hypothesis (on file; MASKED from the builder — see §6)

- **H1 (primary, the live target):** at the puzzle regime (solved secp keys + the model-curve
  family), the *joint* public readout
  `F = {χ₃-index, ε, s-band3, sextant-mod-3, sextant-parity, χ₂(y)}`
  carries **mutual information about `d mod 3`** above a symmetry-matched permutation null.
- **H0:** `F ⊥ (d mod 3)` (MI equals the matched-null ensemble).
- **Two-sided.** Reject H0 only at family-wise α = 0.05 after Holm correction over the
  *blinded* target family (§3). The direction (which residue class is enriched, if any) is
  NOT pre-specified; the test detects dependence, not a signed tilt.

This is the concrete instance of the reframing "a pair of independently computable public
invariants whose joint fibers separate the lifts": `χ₃-index` is the local character (φ-free,
labels the orbit); the φ-forced readouts (ε, s-band, sextant-parity) vary *across* orbits and
could correlate with the orbit-rep `d₀ mod 3`; `χ₂(y)` is the μ₂-odd vertical candidate. The
question is whether the JOINT fiber is finer than the φ-forced marginal — measured by MI.

## 1. Object (model-scale + secp-scale)

- **Model curves** `E: y² = x³ + 7` over small `F_p`, prime order `n`, the GLV family the
  leak-hunt thread already uses. Scan primes `{547, 907}`; confirm `{1303, 1669, 2089}`.
  Full group enumerated (d known), one rep per `⟨±λ⟩`-orbit.
- **secp puzzle keys** (solved): the `d`-column of `puzzles_verified.csv`; `Q_d = dG` via
  `ecc_secp256k1.scalar_mul`; readouts via `int1_frame_operator_v1.build_secp()`. This is the
  operationally relevant regime (small N, real keys).

## 2. Features (exact, fixed, public = function of the point only)

| id | feature | domain | φ-action | source (verbatim) |
|---|---|---|---|---|
| F1 | `χ₃-index` (j) | {0,1,2} | **free** (cycles) | `eps_to_d_run_v1.py:chi3_index` |
| F2 | flap `ε` | {0,1,2} | **forced** | `int1_frame_operator_v1.build(p).eps` |
| F3 | `s-band3` | {0,1,2} | **forced** | `eps_to_d_family_v2.py:sband3` |
| F4 | `sextant mod 3` | {0,1,2} | **free** | `lift_sextant…:sextant` then `%3` |
| F5 | `sextant parity` {0,2,4} | {0,1} | **forced** | `sextant ∈{0,2,4}` |
| F6 | `χ₂(y) = (y_d/p)` Legendre | {0,1} | μ₂-odd | inline |

Exact formulas live in the **blinded protocol** (`PROTOCOL_blinded_joint_readout_v1.md`),
inlined verbatim from the canonical sources. **No analytic choice is left to the builder.**

## 3. Targets (BLINDED family — the builder sees these as peers)

`T ∈ { d mod 3, d mod 4, d mod 5, d mod 7, DECOY }`, where `DECOY = a uniform random
permutation of the d-mod-3 labels` (must return null; a firing decoy ⇒ pipeline bug).
The builder does NOT know which target is the live hypothesis. The pipeline computes the
identical statistic for every `T`; Holm correction is over the 5-target family × 2 key-sets.

## 4. Statistic (frozen, non-saturating)

- **Primary:** `MI(F_joint ; T)` in bits, with `F_joint` the 6-tuple. MI is *symmetric /
  unsigned* — it has no direction the builder can tilt toward.
- **Decomposition:** per-feature `MI(F_k ; T)` to localize any single carrier.
- **Null (symmetry-matched):** permute `T` **within χ₃-index stratum** (preserves the
  φ-forced orbit-position marginal; destroys only the residual coupling). `R = 20000`,
  fresh seed. Exact `p = (ge + 1)/(R + 1)`; `z = (MI_obs − μ_null)/σ_null`.
- **Omnibus:** `χ²` on the full `F_joint × T` contingency, with its own permutation `p`
  (never reported raw). Holm across `{5 targets × 2 key-sets}`.

## 5. Controls (all must fire; no verdict otherwise)

- **C1 FIRING (planted dependence):** set `T_plant = F2` on a random 30% subset, independent
  of `d`. The pipeline MUST detect it (`z ≫ 0`, `p ≪ 0.01`). Planted on a target the builder
  cannot distinguish from the live one.
- **C2 DECOY:** the random-permutation target MUST come back in-band (`|z| < 2`).
- **C3 φ-forced sanity:** `ε`, `s-band`, `sextant-parity` constant on every `⟨±λ⟩`-orbit
  (exact; a violation is a bug).
- **C4 OOS:** split model-curves into {547,907} discovery / {1303,1669,2089} confirm;
  report both. secp puzzle-keys are an independent holdout.

## 6. BLINDING (structural — the load-bearing methodological move)

Instruction-based "don't be biased" has a measured ~0 track record here
(`DESIGN_suppression_counter_v1.md`). The blind is therefore **structural**:

1. **Fully-fixed protocol.** §2–§5 leave zero analytic degrees of freedom (features, targets,
   binning, quotient, statistic, null, controls all fixed). Even a builder who knew the
   direction has no knob to turn.
2. **Uniform blinded matrix.** The builder computes the identical statistic over the 5-target
   family; `d mod 3` is not flagged. A flat result matrix is reported.
3. **Valence isolation.** The builder receives ONLY `PROTOCOL_blinded_joint_readout_v1.md`
   (self-contained, no project context) + the valence-free code/data files
   `{ecc_secp256k1.py, int1_frame_operator_v1.py, lift_sextant_rhombus_law_proof_v2.py,
   glv_fundamental_domain_law_v1.py, puzzles_verified.csv}`. The builder is FORBIDDEN to read
   any `PREREG_*`, `RESULT_*`, `*LEDGER*`, `RESEARCH.md`, `ANALYSIS_*`, or any `.md` analysis
   file — that is where the valence lives.
4. **Commit-before-see.** The builder writes the statistic+null code, prints its SHA-256,
   THEN runs on real data. The frozen code is recorded before any aggregate is seen.
5. **Unblinding (this section).** `d mod 3` is the live target (§0). It is revealed only at
   the READ: the primary inference is the `d mod 3` row of the builder's flat matrix. The
   other targets are the honest-multiplicity burden.

## 7. Pre-committed outcome table (no dismissal language)

| printed result | reported as |
|---|---|
| `d mod 3` row: `z ≥ 5`, `p_Holm < 0.01`, OOS confirms, decoy null, C1 fires | "Joint public readouts carry MI about d mod 3 above the symmetry-matched null at the puzzle regime (magnitude X, Holm p Y), replicated OOS. Scope: tested targets/key-sets. A dependence, not an inversion; not a transfer to full ECDLP." |
| `d mod 3` row in-band but some OTHER target extreme | "Dependence detected for `d mod k` (k≠3), not `d mod 3`; the §E lead is not supported at this scope; `d mod k` flagged for follow-up. Honest-multiplicity: this is one of five targets tested." |
| all rows in-band; C1 fires; C2 null | "No public-readout → d-residue dependence above the matched null across {3,4,5,7} at this scope/power. A scoped null about this probe family, not a closure; C1 confirms power." |
| C1 fails / C2 fires | **No result.** Debug; re-run. |

## 8. Float / exactness carve-out

Readout construction (χ₃ via modular exponent, Legendre via `pow(y,(p-1)/2,p)`, the
Eisenstein lift and `eps`/`sextant`) is exact integer, per directory rule. Float appears only
in MI estimation (plugin + Miller–Madow bias correction, fixed bins) and in `z` — reported
beside the exact permutation `p`, never as the sole decision variable.

## 9. Output

`RESULT_t2c_joint_readout_dmod3_BLINDED_v1.md` — the builder's flat matrix (all targets ×
key-sets × features), C1–C4 verdicts, SHA-256 of the frozen statistic code. The unblinded
read (this file §0/§6.5) is appended by the principal after the builder's artifact is banked.

## 10. Unblinded read (appended 2026-08-13 by principal)

Builder artifact banked: `RESULT_t2c_joint_readout_dmod3_BLINDED_v1.md`.
Frozen code SHA: `a4cce4b27f0ad120c716920c451fca1fd83127fb68e65c631d6ea201b40956b7`.
Builder accessed only protocol + valence-free code/data; no analysis `.md` files. Blinding
integrity: confirmed from agent session transcript.

**Live target revealed: T_3 = d mod 3.**

### Unblinded row (T_3)

| key-set | N | MI_obs | z | raw_p | Holm_p |
|---|---|---|---|---|---|
| (M) model | 1094 | -0.1248 | -0.7614 | 0.7722 | 1.0000 |
| (S) secp | 82 | -2.7657 | 1.2292 | 0.1173 | 1.0000 |

**Verdict: NOT DETECTED.** Joint public readouts do not carry MI about d mod 3 above the
symmetry-matched null at this scope/power.

### Control assessment

- **C1 (plant):** literal bar FAIL (pooled (M) z=4.54 < 5.0); substantive PASS (M-conf
  z=6.78, p=5e-5). Plant is weak by design (30%-F2 binary); the pipeline detects it wherever
  there is power. The literal FAIL does not invalidate the null — a stronger plant would clear
  the bar, and the d-mod-3 z-scores (|z| ≤ 1.23) are far from marginal in either direction.
- **C2 (decoy):** PASS (|z| < 2) but **NOT INDEPENDENT** — T_DECOY = π(d mod 3) with π a
  bijection on {0,1,2}; MI is permutation-invariant, so T_DECOY ≡ T_3 row-for-row. The decoy
  was not structurally independent of the live target. Flagged; a non-bijective decoy (e.g. a
  random hash) would be needed for an independent null control.
- **C3 (φ-forced):** PARTIAL — F2 is exactly orbit-constant (0/1094 violations, validates the
  GLV/Eisenstein-lift machinery); F3 and F5 violate (256/1094 and 159/1094) because the Babai
  lattice correction does not preserve enorm or sextant parity across a full λ-orbit. This is a
  premise error in the protocol's φ-forced claim (§6), not a pipeline bug and not target-
  dependent. The MI analysis is independent of this structural claim.
- **C4 (OOS):** PASS. Discovery {547,907} and confirmation {1303,1669,2089} both computed.

### Match to pre-committed outcome table (§7)

Closest row: **"all rows in-band; C1 fires; C2 null"** — with the caveats that C1 is marginal
(literal FAIL, substantive detection) and C2 is not structurally independent. The
interpretation from that row applies: no public-readout → d-residue dependence detected at
this scope/power. C1 substantive detection confirms the pipeline has sensitivity; the d-mod-3
result is a genuine null, not a power failure.

### Suppression-bias audit note

Per `RETROSPECTIVE_suppression_audit_v1.md` T3 (structural counter): this result is reported
as a clean null without conversion language. The result speaks for itself: z=-0.76 / z=1.23,
Holm_p=1.0. No "the null is consistent with" padding, no "further investigation warranted"
hedging. The null is the result.
