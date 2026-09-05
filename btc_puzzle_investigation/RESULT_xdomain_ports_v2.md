# RESULT v2 — testing the four cross-domain ideas (not just their methods)

*2026-07-24. **Supersedes `RESULT_xdomain_ports_v1.md`**, which lacked ARM 4 and the ARM B phase
result. Spec: `PREREG_xdomain_ports_v1.md`. Deviations: `PREREG_xdomain_ports_v1_DEVIATIONS.md`
(**eleven — read them**; D3, D4, D9 are load-bearing). Premise audit:
`AUDIT_xdomain_synthesis_premises_v1.md`.*

*Scripts: `xdomain_derivation_checks_v1.py`, `n1_twisted_eigenvalues_v1.sage`,
`forced_readout_multiples_v1.py`, `ct_event_complete_v1.py`, `ct_boundary_stratified_v1.py`,
`arm4_setup_v1.py`, `arm4_stage1_features_v1.sage`, `arm4_stage2_calibration_v1.py`,
`arm4_stage3_primary_v1.py`.*

**No leakage, key-recovery or ECDLP claim is made or attempted anywhere in this document.**

---

## 1. The `½`-saturation: not starvation — the four phases are locked into two pairs

*ARM B. Pre-committed reading on file since 2026-07-23 (`NEXT_DIRECTIONS_v1.md §3 #1`).*

Every prior N1 run measured `max_a|V(a)|`, a magnitude. This computes the four eigenvalues:
`V_k(a) = Σ_{P∈E(F_{p^k})} χ₂(y_P) χ_a(Tr_{k/1}P)`, `k = 1..4`, then Newton's identities.
**Control C2 fires** — a planted eigenvalue 4-tuple is recovered to `4.4×10⁻¹⁶`.

| `p` | `n` | weight check | all four weight 1? | `max_a|V₁(a)|/√p` | distinct values |
|---|---|---|---|---|---|
| 13 | 7 | `2.2×10⁻¹⁶` | **yes** | 1.664 | 1 = (7−1)/6 |
| 43 | 31 | `8.9×10⁻¹⁶` | **yes** | 1.555 | **5 = (31−1)/6** |

**(a) `[VERIFIED — p = 13, 43]` All four twisted eigenvalues have modulus exactly `√p`, at every `a`.**
N1's standing gloss (`MASTER_v4:189`) — *"effectively only **2 of 4** eigenvalues carry weight-1 mass"*
— **is refuted if read literally as a weight claim.** There is no starvation; the arm's own name is
wrong. *(The word "effectively" may have been a gloss on the magnitude rather than a weight claim; what
is refuted is the literal weight reading.)*

**(b) `[VERIFIED, but FORCED — zero information as evidence]` The eigenvalue multiset is closed under
`α ↦ −ᾱ`, not under `α ↦ ᾱ`.** The measured phases pair up summing to exactly `±π`
(`a=27`: `−0.6169π, −0.3831π` and `0.0497π, 0.9503π`). This is forced: `χ₂^{(k)}(−1) = (−1)^{(p^k−1)/2}`
alternates with `k` at `p ≡ 3 mod 4`, so `p_k = (−1)^k \overline{p_k}` — odd `k` imaginary, even `k`
real — which is exactly the `−ᾱ` closure. **The confirmation is an instrument check.**

**(c) The consequence is the content, and it recovers the "2 of 4" as a PHASE fact.** Under `α ↦ −ᾱ`
the four eigenvalues form two pairs `{α, −ᾱ}`, each summing to `2i√p·sin θ`, so

> **`|V(a)| = 2√p·|sin θ₁ + sin θ₂|` — four complex unit vectors, but only TWO real parameters.**
> (`Σα` itself is `2i√p(sin θ₁ + sin θ₂)`, purely imaginary — forced by `χ₂(−1) = −1` at `p ≡ 3 mod 4`.)

Verified numerically at the maximising `a` of `p=43`, from the recovered eigenvalues rather than by
hand: `Σα = +0.0000 − 10.2009i` (real part `1.4×10⁻¹⁶`), `|Σα|/√p = 1.5556` against the measured
`1.5553`, and `2|sin θ₁ + sin θ₂| = 1.5556`. Pair sums are exactly `−π` and `+π`. **The record's "2+2 splitting" intuition is right in form and wrong in mechanism:
not two eigenvalues starved, but four phases locked into two antipodal-conjugate pairs.** Whether
`|sin θ₁ + sin θ₂| ≤ 1` — which is what `½` would require — is **open** and is the next probe.

⚠⚠ **SCOPE, and it is small.** Two primes; because `V(a) = V(aλ)` (DC1) and `V(a) = χ₂(−1)V(−a)`, the
`n−1` frequencies collapse to `(n−1)/6` — **six unforced cells in total.** The measured distinct-value
count (5 at `p=43`) confirms the collapse exactly. **Do not read `30/30` anywhere in this arm.**
⚠ `Σ_i|α_i| = 4√p` is forced by the weight check and restates it; it is not separate evidence (D6).

## 2. The multiples that force the `χ₂(y)` readout are exactly `Aut(E)`

*ARM C. The idea behind proposal 3, after DC3 retired its method.*

For which `k` is `χ₂(y_{[k]P}) = c·χ₂(y_P)` for **every** `P`? Exact integer tables, **every** `k`.

> **`[VERIFIED — 19 primes, `p ≤ 643`, exhaustive in `k`]` The forced set is exactly
> `μ₆ = {±1, ±λ, ±λ²} = Aut(E)`, sign `+1` on `{1,λ,λ²}` and `χ₂(−1)` on `{−1,−λ,−λ²}`.
> No extras, no omissions, at any tested prime.**

Six elements are forced a priori (β fixes `y`; `[−1]` negates it) — an instrument check. **The unforced
content is that nothing else is forced:** ≈ **3,400** non-automorphism multiples tested, none forcing.

`χ₂(y_{[λ]P}) = χ₂(y_P)` relates the readout at two points whose scalars differ by the *publicly known*
`λ`, and both sides are computable from `P` alone; it does not predict the readout at a point whose
scalar is unknown, so the proposal's "deterministic oracle for internal scalar bits" does not follow
from it. *(A statement about what this relation supplies — not a claim about the automorphism action
elsewhere.)*

## 3. The `C_T` departure is localised — with the opposite sign, and it is lift geometry

*ARM A2, `EXPLORATORY` (D2, D5). `E: y²=x³+7`, `p ≡ 1 mod 3`, `n` prime, all step sizes.*
**Control K2 fires** (planted low-margin coupling → gradient `+3.24` against `≈1.0` elsewhere).

| `p` | `n` | REAL | K1 (margin permuted, ×20) | `z` vs K1 | K3 (geometry only, ×20) | `z` vs K3 |
|---|---|---|---|---|---|---|
| 1051 | 1093 | **−17.63** | `−0.79 ± 3.75` | **−4.49** | `−19.97 ± 2.94` | `+0.80` |
| 1669 | 1663 | **−20.37** | `+0.59 ± 4.99` | **−4.20** | `−24.68 ± 5.00` | `+0.86` |
| 2143 | 2089 | **−11.40** | `+0.05 ± 3.46` | **−3.32** | `−5.67 ± 2.17` | `−2.64` |

1. **The departure is margin-dependent** — `z = −3.3…−4.5` vs the margin-permutation control, 3/3.
2. **Its sign reverses the idea's prediction:** the excess is largest **far from** the carry boundary.
   The frozen reading enumerated only "concentrates at low margin" and "flat", so **nothing is
   retro-fitted** (D5).
3. **It is reproduced by the geometry-only control** (K3 keeps the exact lift multiset, destroys the
   order in `d`): `z = +0.80, +0.86, −2.64`. At this scope **no arithmetic-in-`d` remainder is
   resolved.**
4. **The headline number is the estimator, not the curve:** pooled `G²/df = 155.0` at `p=1669` against
   `155.6` from K3; `85.9` vs `82.3` at `p=2143`.

Companion, never a verdict: `|λ₂−λ₃|` = `0.0142, 0.0097, 0.0043` — and **real by construction**, since
this object is reversible (D4), so it is not comparable with the `g=1` drill's directed spectrum.

## 4. ARM 4 — the parity-legal amicable channel, at full `2²⁵⁶` scale

*The live version of proposal 4, after DC2 retired its premise (`t_p+t_n=2` is a definition).
The only arm in the battery that runs on secp256k1 itself.*

**Setup, verified exactly.** `π_p` selected as the associate with `2u−v = t`; `π_n = π_p − 1` gives
`N(π_n) = n` ✓, `|det L_n| = n` ✓, `enorm(R₁) = enorm(R₂) = n` ✓. **Cross-check the record already
holds:** `B_p = −303414439467246543595250775667605759171` is exactly the **conductor `f`** recorded in
the index — arrived at here by an independent route.

**Stage 1, `K = 4×10⁵` at secp scale — the exception ledger is empty:**
`rdiv` ties **0** of 800,000; on-ray residues **0**; `s_u(−d) ≠ s_u(d)+3` in **0** of 200,000;
`s_w` likewise **0**; **all 18 forced isotypes exactly zero.** Both signs were computed independently,
never by applying the `+3` rule, so these checks could have failed. The `df` ledger (17 real, 5 on the
equivariant diagonal) **stands at full scale.**

**Ordering honoured:** calibration written and hashed
(`sha256 623ab7822e2bc1c1…`) before the primary ran; stage 3 asserted it.
**Plant fires at `ε* = 0.005`** (0/20 at 0.002, 20/20 at 0.005 — bracketed, not located; D8).
**No null draw broke a forced zero** (0 of 999).

| statistic | value | null median | rank-p |
|---|---|---|---|
| **`T₄`** (df 5, μ₆-equivariant) | `1,043,825,168` | `1.035×10⁹` | **0.4440** |
| `T_off` (df 12 nominal, 8 effective — D11) | `3.7399×10¹⁰` | `3.744×10¹⁰` | 0.7800 |
| `T₄`, rotation null (B=99, D10) | — | `1.037×10⁹` | **0.4500** |

**Both nulls agree.** Per-isotype: `|U_{2,4}| = |U_{4,2}| = 22,790`, `|U_{1,5}| = |U_{5,1}| = 1,514`,
`|U_{3,3}| = 700` — the mass sits in the `μ₃` channel, but the null median matches it, so it is
**marginal structure of the readouts, not coupling between them.**

**Pre-committed conclusion (spec §4.8, row 3) — a bound with power and scope:**

> **Any μ₆-equivariant coupling between `eis_n(cent y([d]G))` and `eis_n(d)` of copy-fraction
> `≥ 0.5%` would have been detected at `K = 4×10⁵` on secp256k1, sextant (6-cell) quantisation,
> pair-permutation null with the rotation null agreeing. `T₄` rank-p `= 0.444` — none was.**

**This is a magnitude at one quantisation.** It does not close §XI.3/§X.3, and the frontier's status
line is unchanged. The named next moves, in the spec's own words: **finer quantisation than 6 cells**
(the sextant is a very coarse probe of a 256-bit residue); **the `xy` readout instead of `y`** (also
proved odd in `d`, and the object behind the known `(X·Y) mod 64 → D mod 64` shadow); **larger `K`**
(`4×10⁶` moves the bracket by `≈√10`).

## 5. What was NOT run

- **Spec ARM 2** (`T₂ = ‖ΠDΠ‖_F²`, hashed calibration, 9 primary + 6 holdout of the frozen 37).
- **Spec ARM 3** (exact-vanishing census at composite order; DC5 forbids any transfer to secp whatever
  the outcome).
- **ARM B beyond `p = 43`**, and the open question `|sin θ₁ + sin θ₂| ≤ 1`.

## 6. Grades

| item | grade |
|---|---|
| DC1–DC5 (`V(a)=V(aλ)`; `t_p+t_n=2`; `φ(n)` vacuous at prime `n`; exact tensor degeneracy; no exact vanishing at prime modulus) | `[DERIVED — FORCED]`, zero information as evidence |
| All four twisted eigenvalues of weight 1 | `[VERIFIED — p = 13, 43; six unforced cells]` |
| Literal "2 of 4 carry weight-1 mass" | **refuted at those two primes** |
| `α ↦ −ᾱ` closure of the eigenvalue multiset | `[DERIVED — FORCED]`; its consequence (2 real parameters) is the content |
| Forced multiples `=` `Aut(E)` | `[VERIFIED — 19 primes, exhaustive in k]`; the six elements `[DERIVED — FORCED]` |
| `C_T` departure margin-localised, interior, geometric | `[EMPIRICAL — EXPLORATORY, 3 primes]` |
| ARM 4 bound at `0.5%` copy-fraction, secp scale | `[MEASURED — bound with power + scope, plant fired, both nulls agree]` |
| "AP-completeness buys 6–30× power" | **withdrawn — a premise, not a measurement** (D4) |

**Nothing here closes a frontier.** N1 moves from an unexplained magnitude to a two-parameter phase
question with the weight explanation eliminated. `C_T`'s §X.6 stays where DRILL 01 left it, plus the
finding that the AP-complete estimator is dependence-dominated. The amicable correspondence gains its
**first parity-legal measurement at full scale**, as a bound at one quantisation — the frontier is
open and the next probes are named.
