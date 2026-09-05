# RESULT — Phase 2: what superspeciality buys. 2a is a restatement (proved both ways); 2b bounds this cover family only

*2026-08-02. Plan Phase 2, conditional on the Phase-0a reader clearing (it did). Artifacts:
`anew_superspecial_consequences_v1.sage` / `.log`, `anew_phase2b_embedding_v1.sage` / `.log`. Exact
arithmetic throughout. **No leakage, ECDLP, or key-recovery claim, in any part.***

---

## 2a — the congruence `#C(F_{p^n}) ≡ #E(F_{p^n}) (mod p)`

### Measured

| arm | result |
|---|---|
| **MAIN** `p ∈ {7,11,19,23,31,43}`, `p ≡ 3 mod 4`, 4 cubics, `n = 1…5` (field size capped at `3·10⁵`) | **83/83 congruences hold** |
| **CONTROL** `p ∈ {5,13,17,29}`, `p ≡ 1 mod 4` | **41 of 60 FAIL** — the control fires, so the congruence is not vacuous |

### The pre-committed question, answered: it is a restatement — and that is provable, not asserted

Write `α₁,…,α₄` for the Frobenius eigenvalues on `H¹(A_new)`. Since `L_C = L_E · L_new`,

> `#C(F_{p^n}) − #E(F_{p^n}) = − Σᵢ αᵢⁿ`,

so the congruence for all `n` says exactly `Σᵢ αᵢⁿ ≡ 0 (mod p)` for all `n ≥ 1`.

- **Forward.** `A_new` supersingular ⇒ every `v_p(αᵢ) = 1/2` ⇒ `v_p(Σαᵢⁿ) ≥ n/2 ≥ 1` for `n ≥ 2`; and
  at `n = 1`, `Σαᵢ = −b₁ = 0` exactly. So the congruence **follows** from what is already established.
- **Converse.** If `Σαᵢⁿ ≡ 0 (mod p)` for all `n`, Newton's identities force every elementary
  symmetric function `≡ 0 (mod p)`, i.e. `p ∣ b₁` and `p ∣ b₂` — which is `p`-rank `0`.

> **⇒ the congruence is EQUIVALENT to `(p`-rank `0) ∧ (p ∣ b₁)`, i.e. to the supersingularity statement
> already in hand. It carries no information that statement does not.**

**Closure grade, stated to the bar** (`feedback_closure_grade_2026_07_28`): **object** — the congruence
`#C(F_{p^n}) ≡ #E(F_{p^n}) mod p`, `n ≥ 1`; **class of observable it closes** — point-count observables
of the cover against `E`, reduced mod `p`; **power** — 83/83 with a control failing 41/60, plus a
two-directional proof, so this is an *equivalence*, not a failed search; **scope** — the equivalence is
general, the verification is `p ≤ 43`, `n ≤ 5`.

This is the outcome the prereg pre-committed to accepting and writing down as such. It is
scale-free and holds at `p = 2²⁵⁶−2³²−977`, but holding at scale does not make it a lever: it
restates a fact already known there.

---

## 2b — complete decomposability and Route 3 (N4)

### Derived, not cited

`anew_phase2b_embedding_v1.log` — root systems of `z⁴ + mz² + 1` computed **from the defining
polynomial** in `ℚ(ζ₂₄)` (this project has a logged incident of a root-system claim being repeated
incorrectly from an external source, so it is re-derived here):

| `m` | factorization over `ℚ` | root orders | `k = lcm` |
|---|---|---|---|
| `−2` | `(z−1)²(z+1)²` | `[1,1,2,2]` | 2 |
| `−1` | `z⁴−z²+1 = Φ₁₂` | `[12,12,12,12]` | 12 |
| `0` | `z⁴+1 = Φ₈` | `[8,8,8,8]` | 8 |
| `+1` | `(z²−z+1)(z²+z+1)` | `[3,3,6,6]` | 6 |
| `+2` | `(z²+1)²` | `[4,4,4,4]` | 4 |

`π = √p·ζ` with `ζ^k = 1` ⇒ `π^{2k} = p^k` ⇒ every eigenvalue of `Frob^{2k}` is the rational integer
`p^k` ⇒ **the embedding degree of `A_new` is at most `2k ≤ 24`.**

### What follows, scoped

`Jac(C) ~ E × A_new` with `A_new` supersingular of embedding degree `≤ 24`, and
`Hom(E, A_new) = 0`. So on this cover the discrete-log problem splits into an `E`-part — the original
problem, unchanged — and an `A_new`-part that a Weil/Tate pairing transfers into `F_{p^{≤24}}`, and
**nothing crosses between them.**

> **`[VERIFIED — this cover family only]`** For `C : w⁴ = f(x)` with `f` a separable cubic and
> `p ≡ 3 mod 4`, transferring the `E`-discrete-log into `Jac(C)` inherits **no advantage** from the
> decomposability: the image lies in the `E`-part, and the easy factor is disjoint from it.

**Closure grade, stated to the bar.** **Object** — the `μ₄` cover family `w⁴ = f`, `f` separable
cubic, `p ≡ 3 mod 4`. **Class of algorithm closed** — transfer of the `E`-DLP into `Jac(C)` for
*these* covers, followed by genus-3 index calculus. **Power** — the supersingularity input is
`[PROVED — reviewed]` for *all* such `p` and *all* separable cubics (curve-independent, scale-free),
and the embedding-degree bound is an exact derivation, so this is not a sampled null. **Scope — and
this is the load-bearing part:**

> **N4's actual open item is untouched.** N4 is *"`Õ(p^{4/3})` is the cost of the best known genus-3
> algorithms on **one** cover, **not a proof over the cover family**, which is large"*
> (`POSITIVE_FINDINGS_MASTER_v4.md:192`). This result speaks only about covers of the form
> `w⁴ = f`. **Every other cover of `E` is untouched, and that is precisely what N4 is about.**
> Route 3 remains **OPEN**.

---

## 3. The live lead this opens — a derived prediction, not yet run

The Cartier argument vanishes on the new part because the eigenspace paired with `V₃` under
`b ↦ −b (mod 4)` is `V₁`, and `dim V₁ = ⌊3/4⌋ = 0`. **That is special to `m = 4`, `deg f = 3`.**

For `w^5 = f(x)`, `deg f = 3`, `p ≡ −1 (mod 5)`: `dim V_b = ⌊3b/5⌋ = (0,1,1,2)` for `b = 1,2,3,4`.
The pairing `b ↦ −b (mod 5)` gives `(1,4)` and `(2,3)`. So

- `𝒞(V₄) ⊆ V₁ = 0` — that half vanishes, as before;
- but `dim V₂ = dim V₃ = 1`, both non-zero, so `𝒞(V₂) ⊆ V₃` has **no reason to vanish**.

> **Prediction, exact and falsifiable:** at `m = 5`, `p ≡ −1 mod 5`, the new part of `Jac(w⁵ = f)`
> should **not** be entirely supersingular — it should split into a supersingular piece (`V₁ ⊕ V₄`)
> and a piece that can be ordinary (`V₂ ⊕ V₃`).

If that holds, the `μ_m` cover construction yields a **new part that is not uniformly easy** — an
object of a different type from the one this family produces. That is the natural next probe, and it
is a prediction *of the reviewed derivation*, so it also functions as an out-of-sample test of it.
**Not run here**: it needs its own pre-registration and gate before any sweep, and it is not claimed
in either direction.

---

## 4. Ledger effect

| item | before | after |
|---|---|---|
| congruence `#C ≡ #E mod p` for all `n` | not in the record | **`[PROVED]` equivalent to `(p`-rank `0) ∧ (p∣b₁)`** — a restatement, no new information. Verified 83/83, control fires 41/60 |
| embedding degree of `A_new` | not stated | **`≤ 2k ≤ 24`**, `k` derived per `m` from the defining polynomial |
| Route 3 / N4 | OPEN — *"one cover, not a family bound"* | **unchanged, OPEN.** Bounded only for the `w⁴ = f` family; the cover family N4 ranges over is untouched |
| `μ_m` covers, `m ≠ 4` | not examined | **new live probe** with an exact prediction (§3), unrun |

**Owed:** pre-registration + gate before the `m = 5` probe; `compile-diff` before any of this reaches a
master or handover document.
