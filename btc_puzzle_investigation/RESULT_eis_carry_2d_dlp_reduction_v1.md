> **⚠ CORRECTION 2026-08-18 (`REVIEW_eis_carry_framing_suppression_v1.md`).** The single-point
> reduction below **stands**, but two framings were over-closed (one-way suppression, user-flagged):
> (a) **"ECDLP-equivalent" is the GENERIC-`d` statement only** — for the **range-restricted puzzle
> keys** the carry is gated at the *range* difficulty (kangaroo `≈2^{(k−1)/2}·√6`), the actual puzzle
> problem, **not** full `2¹²⁸`; (b) the **T2c range route and the amicable second-equation are OPEN,
> not dead** — an exact computation (`t2c_range_glv_structure_v1.py`) shows the public range induces a
> **real carry skew** near the √n boundary (`k=129`: `eps`-rate **0.809**), and the reduction
> **relocates** the carry onto the GLV/endomorphism/kangaroo surface where the OPEN `√6`-composition
> question lives. Read the scope lines below with that correction.

# RESULT — the eis(X) single-point public-route to the scalar carry is ECDLP-EQUIVALENT (2-D DLP)

**Date 2026-08-18. Grade: `[PROVED — reduction; R1/R2/R3 exact-verified]` for the equivalence;
`[EMPIRICAL — powered family null]` corroboration (`RESULT_eps_to_d_constraint_v2`).** Curve
secp256k1. Script: `eis_carry_2d_dlp_reduction_v1.py` (exact integer; one EC scalar-mult). Brick B
analytical step of `ROADMAP_REDIRECT_v3.md`, following the object-identity discharge
(`RESULT_n16_eps_object_identity_crosscheck_v1`).

## The question (Brick B, analytical part)
Does the now-canonical lift/flap give a **public handle on the scalar carry** `ε_LBE`? Concretely: is
`ε_LBE` computable from public data `(x_P, y_P)` alone, poly-time, single-point? This is the input the
whole conditional d-shadow arsenal is gated on, and the piece behind N16's main question (`eps == ε_LBE`).

## The reduction (what was proved + exact-verified)
The scalar carry `ε_LBE` is a deterministic function of the **GLV halves** `(a,b) = glv(d)` (the
balanced `Z[ω]` decomposition, `d ≡ a + bλ mod n`). Three exact identities (verified in-script):
- **(R1)** `φ(G) = (β·x_G mod p, y_G) = [λ]G` — the GLV endomorphism. **Verified True** on secp.
- **(R2)** `glv(d) = (a,b)` with `d ≡ a + bλ (mod n)` — **4000/4000 exact identity** ⇒ for every `d`,
  `P = [d]G = [a]G + [b]·φ(G)`.
- **(R3)** `ε_LBE = f(a,b)` — a genuine bit of the halves (near-balanced split 1985/2015 over 4000 `d`).

**Consequence.** Computing `ε_LBE` from the public point `P` requires the halves `(a,b)` — i.e. finding
**short** `(a,b)` with `[a]G + [b]φ(G) = P`, `a,b ~ √n`. That is the **2-dimensional simultaneous DLP**
on `{G, φ(G)}`, which is **ECDLP-equivalent** (recover `(a,b)` ⇒ `d = a + bλ`; and it is a standard
instance of the DLP — the exact reason GLV accelerates the *signer* who knows `d` but not the
*attacker* who has only `P`). So:

> **`ε_LBE` is CHEAP from a candidate `d`** (one Babai round on the public GLV lattice) **but
> ECDLP-gated from the public point `P`.** No per-point public function of `(x_P, y_P)` yields `ε_LBE`
> below ECDLP cost.

## What this settles
- **Sharpens `ANALYSIS_public_gate_glv_carry_circularity_v1` §4** from the informal "a public function of
  `P` is redundant with `P`" (an *information* argument, and only for the orbit *label*) to a precise
  **computational** statement about the *carry*: it is ECDLP-equivalent, naming the exact hard problem
  (2-D DLP on `{G, φ(G)}`).
- **Explains the powered family null scope-free.** `RESULT_eps_to_d_constraint_v2` found (pre-registered,
  z ≥ 11, plants fired, OOS-checked) that the public flap covariants + 31 maps + omnibus do not predict
  `ε_LBE`. That null was scoped to 5 covariants at `p ∈ {547,907,…}`. The reduction says **why any
  per-point public map fails, at any `p`** — the carry lives behind the 2-D DLP.
- **Resolves N16's main question in the negative (conditional on ECDLP).** `eps(x)` is a public per-point
  function; `ε_LBE` is ECDLP-gated; under ECDLP-hardness they cannot be identically equal — generalizing
  the direct empirical disproof (`RESULT_eps_to_d_constraint_v1`: 21–93 violations) from "`eps`
  specifically" to **any** per-point public readout.

## Placement, not closure (project stance)
This is an **ECDLP-equivalence**, graded as such. Per the project stance (ECDLP assumed-not-proven, the
residual object of study), showing a route is ECDLP-equivalent is **neither** a closure (ECDLP is not
proven hard) **nor** a lever (no shortcut was found) — it is a precise placement: the single-point
eis/flap → carry route is the **same problem**, not an easier one. The value is the redirect: effort on
**per-point** public readouts of the carry is effort on ECDLP itself.

## What stays OPEN (burden-on-closure; the null is NOT enlarged)
- **T2c — the public known-bit-range route** (`RESULT_eps_to_d_constraint_v2` §"still open"): uses the
  **public range** `d ∈ [2^{k−1}, 2^k)` (a property of the number, generator-independent — **in-bounds**
  per the 2026-08-18 boundary decision), **not** a per-point readout. It is the one route that does not go
  through the reduction above. ⚠ **Not prejudged:** it faces its own dichotomy — the range's GLV image is
  a computable strip `R_k`; if `ε_LBE` is constant on `R_k` it is public-but-**redundant** with the range
  (0 new bits), if it varies on `R_k` it is a real bit but still **DLP-gated** within the range. Which
  holds is a concrete, deterministic computation (no leakage null needed to start) and is the next Brick B
  sub-step.
- **Joint / multi-point (N15):** the reduction is single-point; a public function of the **SET** `{[dᵢ]G}`
  is untouched.
- **The amicable second-equation (my `ANALYSIS_idea_improvements…` §3), examined and weakened here:** for a
  **generic** scalar it **dissolves** — the aliquot 2-cycle `n ↔ p` is a property of the curve's **orders**,
  not of an individual `d`, and there is no natural point-map `E(F_p) → E'(F_n)` (different curves, different
  fields) to furnish a second congruence on `d`. It could bite **only** if `d` is range-restricted or
  CM-special — i.e. it **folds into T2c**, it is not an independent lever. *(Stated straight, not inflated:
  the second-equation hope does not survive contact with a generic scalar.)*

## Roadmap consequence
`ROADMAP_REDIRECT_v3` Brick B analytical step: **the per-point eis/flap public-route to the carry is
ECDLP-equivalent** — the predicted clean "No" (flap ≠ carry, computationally), collapsing the per-point
circular arsenal. Brick B continues at **T2c (public range)** and the **joint/lattice** channels, not the
per-point flap. No grade elsewhere moves; this removes a dependency by placing it, and names the two
surviving non-circular directions.

## Owed
`compile-diff` if folded into a master. T2c's range-dichotomy computation (next). The "no per-point
shortcut" direction is conditional on ECDLP-hardness (the project's residual) — stated, not hidden.
