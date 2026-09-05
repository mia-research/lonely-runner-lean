# PRE-REGISTRATION — does an actual descendant's eis frame operator equal the `O_ℓ` lattice value?

*Filed 2026-07-24, **before** the ℓ=3 outcome is read (the first run timed out at the point-set
enumeration; no ℓ=2/ℓ=3 number has been seen). Turns `RESULT_frame_operator_volcano_deformation_v2.md`
§3's `[CONJECTURE]` into a decidable test. Curve/CM/lattice geometry; no leakage / d-side / ECDLP claim.*

## 0. Object

`eis'` on the order `O_ℓ = ℤ + ℓℤ[ω]` (the endomorphism ring of a descending-ℓ-isogeny descendant of a
`j=0` crater curve): map `O_ℓ/𝔭 ≅ F_p` (`𝔭` a prime above a crater prime `p`) to reduced-cell
representatives, and take the frame operator `C = Σ eis'·eis'ᵀ`, statistic `ρ = λ_max/Tr`.

Established before this run (Step 1, `descend_step1.py`): **`h(O_ℓ) = 1` for `ℓ = 1,2,3`** (disc
`−3, −12, −27`), so `𝔭` is principal and `ρ` is **single-valued** = the shape of `O_ℓ`'s reduced cell.
(`h = 2` at `ℓ = 4,5,7` — excluded from this prereg; the class ambiguity is real there.)

## 1. Predictions — DERIVED, pre-committed (confirming them is an instrument check, not evidence)

Exact continuum values (uniform over the reduced cell of `O_ℓ`), from
`RESULT_frame_operator_volcano_deformation_v2.md` §4:

| ℓ | `ρ` (exact) | decimal |
|---|---|---|
| 1 | `3/4` | 0.7500 |
| 2 | `3/4` (1:√3 rectangle) | 0.7500 |
| 3 | `(8+√37)/16` | 0.8802 |

## 2. The control that must fire (or the whole run is VOID)

**C1 — the finite-`p` construction must reproduce the record at ℓ=1.** The record establishes the crater
frame operator `= ¾` empirically. My finite-`p` `eis'` construction is only trustworthy at ℓ>1 if, at
ℓ=1, it converges to **`0.7500 ± 0.01`** at the largest `p` tested. **If ℓ=1 lands outside `[0.74, 0.76]`,
the construction is wrong: report the failure, draw NO conclusion about ℓ=2 or ℓ=3.**

## 3. Pre-committed outcomes

| outcome | conclusion |
|---|---|
| C1 fires **and** ℓ=3 → `0.8802 ± 0.01` (monotone in `p`) | The descendant frame operator **equals** the `O_3` lattice value. v2 §3's `[CONJECTURE]` is promoted to `[VERIFIED]` for `ℓ ≤ 3` (single-valued by `h=1`). A curve statement, modulo Step-3 existence of the descendant. |
| C1 fires **and** ℓ=3 → some other stable value `≠ 0.88` | The `O_ℓ`-lattice model is **wrong**; the descendant's `eis'` shape is not `O_ℓ`'s reduced cell. Report the value; **new prereg** before interpreting. This would be the interesting positive. |
| C1 fails | **VOID.** Construction invalid. Nothing said about ℓ>1. |
| no convergence (ℓ=3 drifts) | Report as non-convergent; no promotion. |

## 4. Falsification

The claim "descendant frame `= O_ℓ` reduced-cell shape" is falsified by **any** stable ℓ=3 limit outside
`0.88 ± 0.01` once C1 has fired. A single well-converged prime suffices to move the needle; the criterion
is convergence, not a count.

## 5. Scope fixed in advance

- `ℓ ∈ {1,2,3}` only (`h=1`). `p ≡ 1 mod 3`, `p ∤ ℓ`, `p` up to a few thousand (all where `π'` with
  `N(π')=p` exists and the box enumeration is exact).
- `ρ` is a lattice/CM statistic. **This test certifies the *lattice value* an `eis'` on `O_ℓ` produces;
  it does not by itself certify that a specific isogenous curve `E'` has `End = O_3`** — that is Step 3
  (Vélu construction + conductor check), a separate deliverable. The two together make the curve statement.
- Float is used for the eigenvalue ratio (a geometric statistic on lattice points, no key/`d` in the
  path — NO-FLOAT rule not engaged); guarded by the exact algebraic target and the ℓ=1 control.

## 6. What it cannot decide

- Nothing at secp scale (lattice/CM only; the crater fact is the sole full-scale statement, already
  `[PROVED]`).
- Nothing for `ℓ ≥ 4` (class number > 1 — a different, harder question).
- No `d`-side / leakage consequence in either direction.
