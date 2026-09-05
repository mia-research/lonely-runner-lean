# NOTE — L-mono GKR-input, first piece: the measured 1-point marginal IS the SU(2) half-trace cos θ (decidable MC); one convention error caught + corrected

**Date 2026-08-23.** First concrete step of the L-mono campaign (`PLAN_lmono_monodromy_campaign_v1.md`
§7.1 GKR-input). Scope: this is a SETUP/first-piece brick — it validates the candidate-group model at the
1-point level and corrects a convention slip; it does **not** prove the monodromy or pin the group. No
leakage/ECDLP claim. Decidable, self-contained group-Haar Monte Carlo (no curve, no L-polynomial
conventions) — `scratchpad`-style, seed 20260823, N=4×10⁶.

## 0. Where L-mono stands (banked vs owed)
**Banked numeric certificates (strong):**
- 1-point marginal `t=Im(V₁)/(2√p)` = SU(2) semicircle, `m_{2k}=Catalan_k/4^k`, max dev 8.4e-4 at
  p=100003 / 49,833 cells (`RESULT_monodromy_sato_tane_at_scale_v1`). `m₄=1/8` excludes the torus.
- 2-point statistics: **iid** Sato–Tate (spacing/number-variance/tail/small-ball NULL vs the semicircle
  null, 17+15 primes) — NOT GUE-rigid (`RESULT_semicircle_null_and_verification_v1`).
- `g = deg gcd(L*(T), L*(ζ₃T)) = 2` (the 120° / T2 law) `[PROVED-exact]` at 22 primes ×
  their cells (`RESULT_n1_120deg_exact_v1`); the exact ζ₃-multiset law per cell (`d2_twist_rigidity_certificate_v1`).
- non-abelian eigenvalue fields (the ζ₃ is internal to the GL-structure, not eigenvalue-arithmetic);
  A_new supersingular ∀ p≡3 mod4 `[PROVED — Prong 1]`.

**The gap (the real prize):** a PROOF that the arithmetic monodromy FORCES `α₂/α₁=ζ₃` for all cells
(T1/T2/T3). Route A = Katz/GKR rigidity: if the det-twisted moment invariants of a candidate group match
the sheaf's, the geometric monodromy IS that group. Candidate: `G = SL₂ (diag on W) · μ₃ (Kummer on W⊗ψ)
· {±1}` on `H¹ = W ⊕ (W⊗ψ)`.

## 1. The piece done here — the 1-point marginal, from the GROUP side
GKR's first owed input is: does the candidate `G` reproduce the MEASURED cell statistics? At the 1-point
level, Haar-sample the connected component (SU(2) via uniform unit quaternions `q∈S³`, half-trace
`cos θ = q₀`), and compare candidate normalized statistics' moments to the measured `Catalan_k/4^k`:

| candidate statistic (from the SU(2)/tensor model) | m₂ | m₄ | m₆ | m₈ | vs measured |
|---|---|---|---|---|---|
| **`cos θ` (SU(2) half-trace of W)** | 0.2501 | **0.1250** | 0.0782 | 0.0547 | **MATCH** |
| `−sin(θ+π/3)` (informal "tensor Im-trace" — see §2) | 0.3751 | 0.2501 | 0.1954 | 0.1641 | no |
| `sin θ` | 0.7499 | 0.6249 | 0.5467 | 0.4920 | no |
| measured (`RESULT_monodromy_sato_tane_at_scale`) | 0.2492 | 0.1247 | 0.0781 | 0.0549 | — |

> **The measured marginal `t=Im(V₁)/(2√p)` is distributionally IDENTICAL to the SU(2) half-trace `cos θ`
> of the rank-2 piece W.** The candidate group's connected component reproduces the measured semicircle
> and `m₄=1/8` exactly. This is the necessary GKR input at the 1-point level (it does not yet PIN the
> group — §3).

## 2. A convention error, caught and NOT propagated (per the eigenvalue-convention memory)
Reasoning informally from the validated ζ₃-multiset `{α, ζ₃α, −ᾱ, −conj(ζ₃α)}` (p≡3 mod4 arm of
`d2_twist_rigidity_certificate`), I derived `t = −sin(θ+π/3)`. The MC shows that is **wrong** (m₄=0.25, not
0.125) — an eigenvalue/reality-convention slip, exactly the failure mode
`feedback_verify_root_system_against_defining_polynomial` names. It was caught by the decidable check, not
written into a result. **Recorded fact (decidable):** the measured `t` marginal ≡ `cos θ`; a from-scratch
symbolic re-derivation of *why* `Im(V₁)/(2√p)` reduces to the W half-trace `cos θ` (through the (1+ζ₃)
tensor factor and the p≡3 mod4 pairing) is owed before any such relation is stated as an identity — it is
NOT asserted here.

## 3. What this does NOT do — and the concrete owed brick
- **Does NOT pin the group.** A 1-point marginal is shared by SU(2), SU(2)×{finite center}, and any
  group whose W-trace is SU(2) (the sato_tane RESULT §3 already flagged this). This piece confirms the
  candidate is *consistent* at 1-point and fixes which trace the measured statistic is; it adds the
  group-side reproduction the GKR argument needs as input, and corrects the convention.
- **The owed GKR brick (the discriminating step):** compute the **det-twisted 4th-moment invariants** of
  `G = SL₂·μ₃·{±}` in the **rank-4** rep `W⊕(W⊗ψ)` (the `⟨det⊗⟩`-masked moments GKR/Goursat–Kolchin–Ribet
  consume) and match them against the FFT-measurable cell statistics — the piece that PINS the geometric
  monodromy. This needs the rank-4 eigenvalue bookkeeping done symbolically from the L-polynomial FIRST
  (per §2), because the informal route is convention-fragile. It is the substantive next step, not done
  here.
- The 2-point discriminator is already banked (iid, NULL for GUE-rigidity).

## 4. Companion / interplay
Brick E (`RESULT_brick_e_cd_degree_v2`) just bounded the transfer-map DEGREE as maximal (generic ceiling,
powered); L-mono targets the spectral GEOMETRY (why the cover's ζ₃ rigidity survives the twist). This NOTE
advances only the 1-point GKR input + a convention correction.

*Inputs: `RESULT_monodromy_sato_tane_at_scale_v1`, `RESULT_semicircle_null_and_verification_v1`,
`RESULT_n1_120deg_exact_v1`, `d2_twist_rigidity_certificate_v1.py`, `NOTE_anew_subgroup_structure_map_v1`.
Plan: `PLAN_lmono_monodromy_campaign_v1` §5A/§7.1.*
