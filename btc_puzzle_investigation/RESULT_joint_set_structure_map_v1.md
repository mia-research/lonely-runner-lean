# RESULT — Joint (x,y) set: full structure map + N2 supersingular differential (v1)

**Date:** 2026-07-20
**Scope of this file:** consolidates one session's mapping of the joint object
`U(a,b,c) = Σ_d e_p(b x_d + c y_d) e_n(−a₀ d)` on `E: y²=x³+7`, prime order `n`, plus a direct
verification of the N2 supersingular differential. **No ECDLP or security claim is made or
approached anywhere in this file.**
**Scripts (scratchpad + investigation dir):** `joint_shadow_decompose_v1.py` (author's, re-run),
`joint_map.py`, `joint_battery2.py`, `recon_sup.py`, `n2b.sage` / `n2b.log`, `eig_check2.sage`.
**Grades are attached to every line. Nothing is promoted to a master document by this file;
`compile-diff` gates that.**

---

## 1. The joint (x,y) shadow reproduces `[VERIFIED, 2 independent implementations]`

`ρ_inf = |Corr|/‖F‖_∞` (true point-space sup-norm), aligned readout `F̂ = conj(U)/|U|`:

| p | author's script (joint) | independent reimpl (joint) | x-only |
|---|---|---|---|
| 349 | 0.9534 | 0.9530 | 0.33 |
| 433 | 0.9523 | 0.9453 | 0.35 |
| 577 | 0.9597 | 0.9555 | 0.30 |

Two separately-written implementations agree to ~0.005 on the joint; x-only reproduces the
published 0.29–0.36. Planted perfect character pins `ρ_inf = 0.997`. **The 0.93–0.96 joint
magnitude is real.**

## 2. …but the magnitude is generic — now confirmed in BOTH norms `[VERIFIED]`

M14 recorded that the scalar-fidelity (`ρ₂`) control does not separate the character from a random
target. This session added the **sup-norm** control that M14 did not compute:

| p | `ρ₂` char / random | `ρ_inf` char / random |
|---|---|---|
| 163 | 0.9992 / 0.9993 | 0.9342 / 0.9325 |
| 349 | 0.9996 / 0.9997 | 0.9534 / 0.9567 |
| 433 | 0.9997 / 0.9997 | 0.9523 / 0.9449 |
| 577 | 0.9997 / 0.9997 | 0.9597 / 0.9448 |

**`ρ_inf` is generic too** — a random target reaches the same sup-norm fidelity. M14's control
failure is therefore *stronger* than recorded: it holds in both normalizations. The 0.93 is the
coordinate geometry's phase-only reconstruction quality, in the sup-norm basis as well as the L2
basis. (This does not touch H3's separate `[PROVED, by construction]` claim that a leaking readout
*exists* at DLP cost; that is a construction, not a discrimination statistic, and is out of scope
for this control.)

## 3. Complete symmetry of U: exactly {parity ℤ/2} × {GLV μ₆}, nothing more `[VERIFIED exact]`

**Exact algebraic layer** (holds to 1e-11 at p = 163…823):

- `U(−a,b,c) = U(a,b,−c)` (x-even, y-odd) — exact.
- `U(a,b,c) = U(aλ, βb, c)` (GLV/μ₆) — exact, on **both** parity halves.
- phase rigidity under GLV: `arg Uₒ(aλ,βb) − arg Uₒ(a,b)` has mean 0.000, **std 0.000** — the μ₆
  character acts as a rigid phase; no residual phase freedom.

**Energy layer** (forced by the symmetries):

| p | even-in-c (x) | odd-in-c (y) |
|---|---|---|
| 163 | 0.4964 | 0.5036 |
| 433 | 0.4987 | 0.5013 |
| 823 | 0.4994 | 0.5006 |

Parity split → ½ each (tightening with p); odd half sits **exactly 0** on the `c=0` line
(forced). The **6-cell budget (parity × μ₃) is equipartitioned**, each cell 0.1655–0.1679 ≈ 1/6
(consistent with M15).

**Statistical layer — all generic:**

- `|U|/√n` distribution is **Rayleigh to 3 dp** (mean 0.884 vs 0.886; var 0.216 vs 0.215).
- top-k mass and support overlap at chance (0.050); top-5% mass 0.199 char vs 0.200 random.
- `max|U|/√p` = 3.0–3.4, odd-half 2.1–2.5, even-half 2.0–2.5, all under the Weil ceiling 4.0.
  **No spike; odd-half max does not exceed even.** (H3 open frontier #2, the T_y max corner: no
  exceptional non-cancelling `(b,c)` found in the tested range.)
- odd-half aligned phase carries **no hidden `d`-encoding**: best linear slope `s = a₀`, alignment
  `R ≈ 0.64` (the known alignment), residual std 2.40 (over-dispersed vs random 1.81).

**Interpretation `[SCOPED]`:** the character-specific content of the joint object is *exactly* the
two symmetries `{parity × μ₆}`; within the 6 isotype cells, energy is equipartitioned, magnitude is
Rayleigh, symmetry-phase is rigid. Those two symmetries are M16's barrier (μ₆-symmetric ⇒ constant
on `{±d, ±λd, ±λ²d}` ⇒ cannot isolate `d`). The joint set is mapped to its edges: an exact fence.
This is a bounded characterization at p ≤ 823, not a statement about `2²⁵⁶` and not a null of the
form "nothing here."

## 4. N1 / the 2+2: a candidate mechanism, and its tension `[CANDIDATE — not confirmed]`

Two ½'s from the same coordinate's parity, both now shown **parity-class-independent**:

- additive `e_p(cy)`: odd-half energy of U = exactly ½ (§3).
- multiplicative `χ₂(y)`: saturation ≈ ½ at **both** `p mod 4` classes (M4 cross-check, 8 primes:
  p≡3 → 0.476, 0.480, 0.497; p≡1 → 0.481, 0.477, 0.472, 0.500, 0.489; → ½ as p grows).

**Candidate mechanism:** the involution `[−1]: P↦−P` (= `d↦n−d`, `y↦−y`) splits `A_new`'s
4-dimensional `H¹` into 2+2 by parity; a *definite-parity* `y`-readout couples to only its own
2-dim half ⇒ saturates a dim-4 (`4√p`) ceiling at exactly ½. This is class-independent because
either parity yields a 2-dim half — which is **why M4 saw ½ in both classes and why its "odd
causes it" reading failed**: the correct statement is "definite-parity ⇒ ½," which is
parity-class-symmetric. This names N1's "2 of 4 eigenvalues" as the `[−1]`-eigenspace split.

**Unresolved tension (why this is a candidate, not a result):** `bx` (x-only, even parity)
saturates 0.909, not ½. The resolution must be dimensional (`bx` measured against a dim-3 ceiling,
`χ₂(y)` against dim-4), but that has **not** been verified. **Decidable test that would confirm or
kill it:** compute the dimensions of the `[−1] = ±1` eigenspaces of the involution on `H¹(A_new)`
and whether `χ₂(y)`'s sum projects onto one 2-dim half. That converts N1 from "unexplained ½" to an
eigenspace dimension count. Not run in this session.

## 5. N2: supersingular differential verified 8/8 `[VERIFIED empirical; argument scale-free but review-pending]`

The μ₄ argument predicts `A_new` supersingular **exactly when p≡3 mod 4** (`i^p=−i` forces
Frobenius to anticommute with the cover's order-4 automorphism). Direct point-count test
(`n2b.log`, L-poly of `C` factored by `P_E`):

| p mod 4 | primes | verdict |
|---|---|---|
| 3 | 19, 23, 31, 43 | supersingular (trace 0, roots √p·ζ) — 4/4 |
| 1 | 13, 29, 37, 53 | ordinary — 4/4 |

**p=29 and p=53 are the sharp controls:** trace `b₁=0` there, yet **ordinary** (`b₂ ≢ 0 mod p`, no
`√p·ζ`). So trace-zero is necessary, not sufficient; the mechanism switches on `p mod 4`, exactly
the parity of `i^p`. A generic extrapolation has no reason to also predict the p≡1 ordinary cases;
this one does.

**Status `[PROVED — pending independent review]`:** the argument is scale-free (its ingredients —
the ζ₄ cover automorphism, `i^p=−i` at p≡3 mod 4, the surface p-rank/End⁰ dichotomy — are
p-independent or pure field arithmetic that hold at secp), so it reaches `2²⁵⁶` with **no
extrapolation**. The one open gap is **rigor, not scale**: the p-rank/End⁰ dichotomy step was
already **wrong once** (the first draft's "non-commutative End⁰ ⇒ ss" is refuted by `E_ord×E_ss`)
and its corrected form has not had independent adversarial re-derivation. Master v4's P13 language
("unproved dimension-2 extrapolation") is **stale** — it predates this argument and reflects the
withdrawn "Q(i) inert" reasoning; the record is internally inconsistent because the master is not
yet updated, not because the result is shaky. **No ECDLP claim.**

## 6. CORRECTIONS LEDGER (errors made and caught this session)

1. **The ζ₁₂ eigenvalue error — perpetuated across several turns.** I stated the `m=1`
   eigenvalues as `√p·{±ζ₁₂, ±ζ₁₂⁵}` (primitive 12th roots). **Wrong.** From
   `u⁴ + m u² + 1 = 0`: `m=1` gives root orders `[3,3,6,6]` (primitive **3rd/6th**), while the
   primitive **12th** roots are `m=−1` (`[12,12,12,12]`). The error was inherited from an external
   pasted specification and propagated without being checked against the defining polynomial, into
   two versions of the Jacobi result file and multiple conversational turns. **Caught by an
   object-level computation** — the `N_coinc` pair-product count in the N1 prereg, then an
   independent `eig_check2.sage` — not by rereading. The predecessor memory
   `secp_mu4_eigenvalue_individual_2026_07_20` had it right throughout; the error contradicted a
   correct memory. Corrected in `RESULT_jacobi_closed_form_m_law_v3.md`/`v4.md`. **Lesson: a claim
   about a root system must be checked against its defining polynomial before it is repeated,
   especially when it arrives from an external source.**
2. **"34/34" was inflated to "15 distinct."** The Jacobi-reduction verification reported 34/34
   configurations; the correct distinct count is 15 — **19 (56%) were algebraically forced, and 12
   of those forced by a step (F2) of the derivation being tested** (circular). Corrected in
   `RESULT_jacobi_closed_form_m_law_v4.md`.
3. **The D1 non-additivity was mis-scoped.** I described M18's `0/666 additivity` as a p=43-only
   artifact resting on a killed test; M18 records it at **p ∈ {43,67,79}, 666 triples, controls
   fired**. The scope error was mine; M18 stands.
