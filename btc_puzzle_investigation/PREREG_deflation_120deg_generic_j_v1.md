# PRE-REGISTRATION — is the 120° law generic to odd-order cyclic elliptic curves, or specific to `j=0`?

**Date:** 2026-08-01, written BEFORE any `V₃`/`V₄` data exists. **Status: FROZEN pre-data.**
**Deviations go in `PREREG_deflation_120deg_generic_j_v1_DEVIATIONS.md`, not here.**

---

## 1. The question, and why it is decidable now

`ANALYSIS_120deg_exact_factorization_certificate_v1.md` §1 establishes, symbolically with `e₁, p`
free indeterminates and both `ε = χ₂(−1)` branches:

> `e₂ = e₁² − εp` **∧** `e₃ = εp·e₁` **∧** `e₄ = p²`  ⟹  `deg gcd(L*(T), L*(ζ₃T)) ≥ 2` (the 120° pairing)

`RESULT_jclass_B_relevance_check_v1.md` measured the **first** conjunct on 30 curves with
`j ∉ {0,1728}` (`Aut = μ₂`, no `μ₃`) and found it holds 30/30, both branches. That result is graded
`[PROVISIONAL — this gate OWED]`.

**If the other two conjuncts also hold at generic `j`, the 120° law is a general fact about
odd-order cyclic elliptic curves and carries no information specific to `j=0`, `μ₃`, or secp256k1.**
That is the hypothesis under test. It is deflationary to a large part of the N1 line, which is
precisely why it gets a pre-registration and a firing control rather than a quick confirmation.

## 2. Why this is affordable (the cost claim, stated so it can be checked)

`e₃` requires `V₃`, `e₄` requires `V₄`, via Newton's identities. The record treats these as an
`O(p³)/O(p⁴)` wall — **true for the census primes (`p ≤ 2503`), false for this question**, which needs
only small `p`. At `p = 43`: `p³ = 79507`, `p⁴ = 3418801`. Both are ordinary loops.

**Pre-committed cost budget:** `V₃` at all sampled `p ≤ 127`; `V₄` at `p ≤ 67` only. If a cell exceeds
**900 s** it ABSTAINS and is reported as abstained — an abstention is not a pass and not a failure.

## 3. Objects and statistic — EXACT INTEGER ARITHMETIC ONLY

For `k = 1..4`, on `E: y² = x³+Ax+B` over `F_p` with `E(F_p)` **cyclic of odd order `n`**:

    h_k[d] = sum over P in E(F_{p^k}) with dlog(Tr_{k/1} P) = d  of  chi2^{(k)}(y_P)
    P_k    = -V_k   (Lefschetz);  as vectors in Z[x]/(x^n - 1):  P_k_vec = -h_k

Newton's identities, all divisions asserted exact in `ℤ`:

    e1 = P1
    e2 = (e1*P1 - P2)/2
    e3 = (e2*P1 - e1*P2 + P3)/3
    e4 = (e3*P1 - e2*P2 + e1*P3 - P4)/4

**Equality convention (load-bearing).** A vector `v` evaluates to `Σ_d v[d]·ζ_n^{ad}` at cell `a`.
Two vectors agree at every `a` with `gcd(a,n)=1` **iff they differ by a CONSTANT vector**. So every
test below is *"this difference vector is constant"*, never *"this difference vector is zero"*.

**The three test statistics** (each a boolean per curve):

| | statistic | tests |
|---|---|---|
| **T2** | `e2 − (e1∘e1 − εp·δ₀)` is constant | `e₂ = e₁² − εp` |
| **T3** | `e3 − εp·e1` is constant | `e₃ = εp·e₁` |
| **T4** | `e4 − p²·δ₀` is constant | `e₄ = p²` |

(`∘` = circular convolution; `δ₀` = unit vector at index 0.) **T3 and T4 have never been measured at
`j ≠ 0`. They are the new content; T2 is carried for continuity with the 30/30.**

## 4. Arms, and the sampling rule — FIXED BEFORE DATA

**The v2 defect this fixes:** `RESULT_jclass_B_relevance_check_v1.md` §4 names its own uncovered
frame layer — the curve sample was self-chosen, first-fit, `A=1` in most cells. Here the sample is
randomized under a fixed seed and the rule is frozen before any curve is drawn.

    SEED = 20260801.  For each prime p, draw (A,B) uniformly from [1,p-1]^2, reject unless:
      j(E) not in {0, 1728}, E nonsingular, E(F_p) cyclic, n = #E(F_p) ODD.
    Keep the first 3 accepted draws per prime.  Draw order is the RNG's, not the analyst's.

| arm | curves | role |
|---|---|---|
| **A0** `j = 0` (`y²=x³+B`), odd cyclic `n`, `p ≡ 1 mod 3` | 1 per prime | **POSITIVE CONTROL — runs FIRST, run HALTS if it fails** |
| **A1** generic `j`, odd cyclic `n`, `p ≡ 3 mod 4` (`ε = −1`) | 3 per prime | primary |
| **A2** generic `j`, odd cyclic `n`, `p ≡ 1 mod 4` (`ε = +1`) | 3 per prime | primary, other branch |
| **A3** generic `j`, **even** `n` | 2 per prime | **FIRING CONTROL — T2/T3/T4 must FAIL here** |

**Primes.** `A1`: 43, 67, 79, 127 (`p≡3 mod4`). `A2`: 73, 97, 109 (`p≡1 mod4`).
**Scope extension the prior run lacked:** include `p ≢ 1 mod 3` (`p = 47, 53, 59, 71, 89, 101`) in
A1/A2 — the prior run was **entirely `p ≡ 1 mod 3`**. Note A0 cannot run at `p ≢ 1 mod 3` (`j=0` is
supersingular there), so those primes carry no positive control and are reported separately.

## 5. Controls, and what each one rules out

1. **A0 positive control (ordered FIRST, halts on failure).** The instrument is new code computing
   `V₃`/`V₄` for the first time. A null at generic `j` is uninterpretable unless the same code
   reproduces T2/T3/T4 = PASS on `j=0`, where the record already asserts them. **Halt on failure.**
2. **A3 firing control.** Even-`n` curves must FAIL. If T2/T3/T4 pass everywhere including A3, the
   statistic is vacuous and the whole run is void.
3. **Plant control.** Perturb `h₃[d] += 1` at one `d ≠ 0` and confirm T3 flips to FAIL; likewise
   `h₄`, T4. A test that survives a plant is not testing anything.
4. **Newton exactness.** Every division by 2, 3, 4 is asserted exact in `ℤ`. A non-exact division
   means the degree-4 model is wrong for that curve — recorded as `MODEL-FAIL`, distinct from a
   clean T-failure, and NOT counted as either a pass or a fail.

## 6. Power and scope — stated honestly

**Power.** The statistic is exact and deterministic; there is no sampling noise and no threshold. So
"power" here is **not** statistical — it is entirely a question of **which curves are covered**. A
pass on `k` curves is a statement about those `k` curves and nothing else. The design's actual power
claim is narrow and is this: *if T3 or T4 distinguishes `j=0` from generic `j` at all, and does so at
small `p`, this run detects it with certainty on the sampled curves.* It cannot detect a distinction
that appears only at large `p`, and it cannot detect one that appears only on curves the sampler did
not draw.

**Scope.** `p ≤ 127`; `n` odd and cyclic; 3 curves per prime; `V₄` only at `p ≤ 67`. Nothing here
extends to large `p`, to non-cyclic `E(F_p)`, or to `j = 1728` (structurally excluded — rational
2-torsion forces `n` even, and even `n` fails T2 by the prior run).

## 7. Pre-committed outcome table — written before the data

| T2 | T3 | T4 | at generic `j`, with A0 passing and A3 failing | pre-committed conclusion |
|---|---|---|---|---|
| pass | **pass** | **pass** | all three conjuncts generic | **The 120° law is GENERIC to odd-order cyclic curves within scope. The `j=0`/`μ₃` framing carries no content the generic case lacks.** Deflation CONFIRMED in scope. |
| pass | **fail** | any | `e₂` generic, `e₃` not | **Deflation REFUTED.** `j=0` is special in the `e₃` layer; the 120° law is not generic; the N1 line's object survives. Characterize *how* `e₃` differs — that difference is then the real object. |
| pass | pass | **fail** | `e₄ ≠ p²` at generic `j` | same as above at the `e₄` layer. Deflation REFUTED. |
| **fail** | any | any | contradicts the prior 30/30 | **Do not conclude.** Instrument discrepancy between this code and `jclass_e2_relation_probe`; resolve before any reading. |
| any | any | any | **A0 fails** | run VOID, halt. |
| any | any | any | **A3 passes** | statistic vacuous, run VOID. |

**Binding.** A fired outcome cell is the conclusion of record and goes in §1 of the result. Any
follow-up statistic computed after seeing the data goes under a heading `EXPLORATORY` and cannot
override a fired cell. (`feedback_prereg_abstention_is_the_finding_2026_07_19`.)

**What this run CANNOT conclude, whatever it returns:** that the 120° law is generic at
cryptographic `p`; that secp256k1 carries no structure; that any avenue is closed. A pass in the
first row is a scoped statement about curves with `p ≤ 127`, and per the standing counter-prior an
empirical result of any sign does not close an avenue.

## 8. Falsification condition

The deflation hypothesis is falsified by **a single generic-`j`, odd-cyclic curve at which A0 passes,
Newton divisions are exact, and T3 or T4 FAILS.** One such curve is sufficient; no rate is needed,
because the claim under test is a universal algebraic identity, not a tendency.
