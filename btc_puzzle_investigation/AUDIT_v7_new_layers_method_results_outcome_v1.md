# AUDIT — the new v7 layers (tensor / splitting-field / phase channel): method, results, outcome

**Date:** 2026-08-09
**Target:** the material folded into `POSITIVE_FINDINGS_MASTER_v7.md` — P16, M21–M24, N8–N10, Parts XIII–XIV.
**Register:** purist. Symmetric audit (over-claim AND over-suppression), decidable artifacts only.
**Verdict:** **CONFIRMED with one downward certification fix.** The load-bearing reduction (P16) is
independently re-derived; every headline number reproduces; the census identity is now *exactly*
certified at the two largest primes that were previously modular-only. One real fix: the census /
120°-law certification in v7 was stated slightly stronger than the on-disk `CORRECTION` allows — folded
down into v8.

Reproduction scripts (this audit): `scratchpad/audit_reduction_check.py` (sympy),
`audit_e2_convolution_largep.py`, `audit_disc_and_alglayer.py`; plus reruns of the ZCode
`twist_identity_reduction_v1.py`, `discriminator_tensor_decomp_v1.py`, `channel_mechanism_verify.py`.

---

## 1. METHOD

### 1.1 The discriminator reconstructs L*, it does not point-count it — this is *why* it reduces
`discriminator_tensor_decomp_v1.py:226–242` builds `L*(T)` from two twisted census sums `(V1,V2)` and
then **imposes** `e3 = χ₂(−1)·p·e1` and `e4 = p²`. It is a Newton reconstruction from two moments under
a forced functional equation, **not** an independent 4-term point count of the cover. Consequently the
only free data is `e2` vs `e1`, and the twist factorization pins them. This is the mechanical reason the
"tensor-decomposition discriminator" collapses to a scalar identity — the method **cannot** see the full
4-dimensional module, so it cannot confirm the decomposition. v7's `[HYPOTHESIS]` grade and
"necessary-not-sufficient" are the correct reading; the audit sharpens it (see §1.2, §3).

### 1.2 P16 reduction — independently re-derived, EXACT
`audit_reduction_check.py` (sympy, independent of the ZCode script): expanding
`(T²+AT+B)(T²+ζ₃AT+ζ₃²B)` and eliminating `A,B` under `e3=εp·e1, e4=p²` gives, for **both** `ε=±1`:
`R₀ = c1²−c0·c3² ≡ 0` identically, and `R₂ = c2c3−c3³+c1 = (e1/p³)[ε(e1²−e2)−p]`. Hence off `e1=0`,
twist factorization ⇔ **`e2 = e1² − χ₂(−1)p`**; and `Q·Q̃ − L = 0` (all T-coefficients, reduced mod
`q²+q+1`) once the identity holds. The ZCode `twist_identity_reduction_v1.py` reruns clean:
`forced_residual`, `discriminating_residual`, `e2_identity`, `factorization` failures all **0** at
p=43 (31 freq), 67 (79 freq), 127 (21 μ₆). **P16 stands.**

### 1.3 Census identity = 120° law — certification strength varies by prime; the strong route is exact
- **Equivalence (from `RESULT_e2_identity_extended_verification_v1.md`):** `e2=e1²+p` ⇔ `V2=V1²+2p` ⇔
  the 120° law. So the discriminator is a **re-encoding of the 120° law**, not independent evidence for
  the tensor decomposition — even sharper than v7's wording.
- **The strong certificate is the exact integer convolution** `f=h2−h1⋆h1` (const off 0, `f[0]−c=2p`),
  which needs no factoring and no modular reduction. Prior work ran it at **7 primes (43–547)**. **This
  audit extends it to p=823 and p=1303** (`audit_e2_convolution_largep.py`): both **CERTIFIED EXACT**
  (`f[d]=0` ∀`d≠0`; `f[0]−c=2p`; cyclotomic `V1²+2p==V2` at sampled cells). These two were previously
  reachable *only* by the discriminator's modular PATH B.
- **The weak route is the modular `min_l deg gcd`** (discriminator PATH B; the master's 120° cells).
  `CORRECTION_120deg_census_certification_direction_v1.md` shows it is **one-sided**
  (`min_l g_l ≥ g_true`, real inflation witness: a true `g=0` plant reads `g=2` at l=13,37). For a
  *scalar* identity across ≥7 large CRT primes this is far stronger than the *geometric* gcd case, but
  the clean certificate remains the exact convolution — now done at the range endpoints.

### 1.4 Controls
- **Within-curve:** `a=0` control PASSes (reproduced, §2). ✓
- **Cross-object:** the `CORRECTION`'s PLANT-B (`α=3+2i,β=2+3i`, ratio `i`) has true `g=0` — a
  non-120° object the exact route separates. So the identity is **not** a generic reconstruction artifact.
- **Residual (noted, not fixed):** a cross-*curve* firing control — running the census identity on a
  **non-j=0** Weierstrass curve (no `x↦ωx` automorphism) and confirming it **fails** — was not run at the
  discriminator level. The j=0 specificity currently rests on the automorphism argument + PLANT-B, not on
  a non-j=0 discriminator negative. A cheap, decisive add (frontier).

### 1.5 Algebraic-number layer — method sound, reproduced
Q-norm `N_{Q(ζn)/Q}(L_a)`, factor over Q, cycle types mod ℓ. Reproduced at p=43 (§2). The
square-discriminant ⟹ `G⊆A₄₀` step is exact; the full transitive-group identification is (correctly)
left open (degree 40 beyond PARI/KASH).

### 1.6 Phase channel — controls the right shape, no float-in-signal-path violation
`channel_mechanism_verify.py`: signal path (`b`, `χ₂(b)=pow(b,(p−1)/2,p)`) is exact integer; float
appears only in the phase/regression *statistic* (`np.angle`, `lstsq`) ranked against controls — the
allowed monotone-statistic regime. Controls: k=1/3/5/7 selectivity, curve-type (j0/j1728/nonCM), the
complex-weight/Kloosterman firing control (breaks the real-weight `μ₂` mechanism), generator invariance.
Sound; reproduced at result level (§2).

## 2. RESULTS — reproduction table

| claim (v7) | independent check | result |
|---|---|---|
| P16 reduction `R₀≡0, R₂=(e1/p³)[ε(e1²−e2)−p]` | sympy re-derivation, both `ε=±1` | **reproduced** (R₀=0; R₂−target=0; Q·Q̃−L=0) |
| P16 residuals vanish on census data | rerun `twist_identity_reduction_v1` | **0 failures** at 43/67/127 (131 cells) |
| M21 census identity `e2=e1²+p` (=120° law) | exact convolution `f=h2−h1⋆h1` | **CERTIFIED EXACT at p=823, 1303** (new) |
| discriminator 6/6 PASS incl control, p=43 | rerun `run_prime(43, use_exact)` | **control a=0 PASS; 5/5 cells PASS** |
| M23 minpoly deg `4(n−1)/3`, mult 3 | Q-norm + factor at p=43 | **deg 120 = (deg 40)³; mult 3** |
| M23 `G⊆A₄₀` (square disc) + tower even-in-T | discriminant + Q(ω) factor at p=43 | **disc a square; [20,20], both even in T** |
| M24 amplitude / phase / k=3 selectivity | rerun `channel_mechanism_verify` | **j0 0.506 / j1728 0.317 / nonCM 0.430; φ_p by p mod 4; k=3 ≈0.5 vs k≠3 ≤0.09** |

Every headline number reproduces.

## 3. OUTCOME / grades (symmetric)

- **P16 `[PROVED — exact symbolic]`** — CORRECT (§1.2).
- **Tensor decomposition `[HYPOTHESIS]`, discriminator necessary-not-sufficient** — CORRECT and **not
  over-suppressed**: the census identity and the algebraic-number layer are genuine, credited positives;
  only the unproven module splitting is withheld. The audit *sharpens* the wording (discriminator ≡ 120°
  law re-encoding).
- **M23 `[VERIFIED — exact]`** — CORRECT (reproduced).
- **M24 `[EMPIRICAL — controls-validated]`** — CORRECT (reproduced).
- **The one fix (downward, warranted):** v7 M21 / §XIII.2 state the census/120°-law certification without
  citing the `CORRECTION`. The 120° law's `min_l deg gcd` certification is **one-sided** — the law is
  `[VERIFIED]`, not `[PROVED-exact]` — and v7 implies uniform exact arithmetic where PATH A (true exact
  factoring) ran at only 3 primes. Correct framing: the **exact convolution** is the strong certificate
  (now 9 primes: 43–547 + 823, 1303 from this audit); the modular PATH B / gcd route is one-sided. This
  is over-statement corrected **down** — the opposite of the project's suppression bias, hence explicitly
  logged as a genuine catch, not a reflex deflation.
- **No over-suppression found.**

## 4. Net

The new v7 layers are substantially confirmed. The tensor discriminator is exactly what v7 says it is —
a re-encoding of the 120° law, `[HYPOTHESIS]` for the decomposition — and the census identity behind it
is now exactly certified across the full prime range, not merely modularly. The algebraic-number layer
and phase channel reproduce number-for-number. The single certification-framing over-statement is folded
into v8 (§3), together with the new exact endpoints and the missing cross-curve firing control (a
frontier). Cross-references owed: this audit + the `CORRECTION` should be cited from M21/§XIII.2.
