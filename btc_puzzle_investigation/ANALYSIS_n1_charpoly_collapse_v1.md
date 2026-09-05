# The twisted char poly has TWO free coefficients — and 120° is ONE algebraic relation

**Date:** 2026-07-30. Script: `verify_charpoly_collapse_v1.sage`.
**Grade: `[DERIVED + VERIFIED — exact, every frequency, p = 43, 67, 127]`.**
This is a **derivation**, not a sweep. It closes nothing empirically; it reduces the open item.

---

## 0. Why the record's "decisive ideal test" should NOT be run

`ANALYSIS_n1_cap_anew_channel_kronecker_route_v1.md` proposes measuring `(α₁)` and `(α₂)` as ideals:
*"Equal ⇒ Kronecker applies… Different ⇒ THE ROUTE IS DEAD — clean falsifier."* The **same file**
carries the refutation (its D-2): 120° ⇒ `α₂/α₁ = ζ₃` ⇒ the ratio is a **root of unity** ⇒ a **unit**
⇒ `(α₁) = (α₂)` **identically**. The measurement's outcome is fixed before it runs.

**Confirmed, and not run.** The ideal equality is a corollary, never evidence. What Kronecker needs is
the ideal equality **derived** — which is the Stickelberger route, a derivation.

## 1. (D1) The closure forces `e₃` and `e₄` — they are not independent facts

The closure `α ↦ −ᾱ` is `[PROVED — FORCED]`. With `|α|² = p` we have `ᾱ = p/α`, so `−ᾱ = −p/α`, and
the root multiset is closed under `α ↦ −p/α`. Roots therefore pair with product `−p` and sum
`s_i = α_i − p/α_i`:

> `P(T) = (T² − s₁T − p)(T² − s₂T − p) = T⁴ − (s₁+s₂)T³ + (s₁s₂−2p)T² + p(s₁+s₂)T + p²`

Reading off against `P(T) = T⁴ − e₁T³ + e₂T² − e₃T + e₄`:

| | forced value | record's status |
|---|---|---|
| `e₁` | `s₁+s₂` | free |
| `e₂` | `s₁s₂ − 2p` | free |
| **`e₃`** | **`−p·e₁`** | `[CONFIRMED-independent]` via Sage `V₁..V₄` |
| **`e₄`** | **`p²`** | `[CONFIRMED-independent]` |

At `p ≡ 1 mod 4` the closure is `α ↦ ᾱ` (the record's D4 correction), giving `(T²−sT+p)` factors and
`e₃ = +p·e₁`. Together: **`e₃ = χ₂(−1)·p·e₁`, `e₄ = p²` — the record's D4 relation, DERIVED from the
closure rather than measured.**

> **⇒ The twisted char poly has exactly TWO free coefficients, `e₁` and `e₂`.**

## 2. (D2) ★★ 120° ⟺ `e₂ = e₁² + p` — a single algebraic relation

Put `α₁ = √p·e^{iθ}`, so `s₁ = 2i√p·sin θ`. The 120° law says `α₂ = ζ₃α₁`, i.e.
`s₂ = 2i√p·sin(θ+120°)`. Then with `ψ = θ + 60°`:

- `e₁ = s₁+s₂ = 2i√p[sinθ + sin(θ+120°)] = 2i√p·sin ψ`  (so `e₁² = −4p sin²ψ`)
- `e₂ = s₁s₂ − 2p = −4p·sinθ·sin(θ+120°) − 2p = 2p·cos 2ψ − p = p − 4p sin²ψ`

> **`e₂ = e₁² + p`** ∎

And since `p₂ = e₁² − 2e₂` and `V_k = −p_k`, this is **identically** `V₂ = V₁² + 2p`.

**⇒ Three separately-recorded items are ONE relation:**
1. the **120° law** (`α₂/α₁ = ζ₃`, `[PROVED-exact]` at 22 primes / 2464 cells),
2. the **`V₂ = V₁² + 2p` identity** (`[VERIFIED-exact]`, sign resolved to `+2p` today),
3. **"uniform `u = ζ₃`"** — `ANALYSIS_..._v3.md` §4's *"sole remaining structural gap… per-cell is
   proved; uniform is not, and no finite sweep gives it."*

**The open item is therefore: prove `e₂(a) = e₁(a)² + p` for all `a`, all `p`.** One polynomial
identity between the first two coefficients of the twisted L-polynomial — both of which are
Gauss/Jacobi-sum-type objects, i.e. exactly what Stickelberger factorizes. That is a sharper and
smaller target than "the ratio of eigenvalue pairs is a cube root of unity."

## 3. Verification — nothing assumed except the closure

`V₁` and `V₂` computed **directly** from `E(F_p)` and `E(F_{p²})` by exact integer histograms; the
120° law is **not** used to obtain them. Then `e₁ = −V₁`, `e₂ = (e₁² + V₂)/2`, and `e₃, e₄` from §1.
Roots of the resulting `P(T)` at 160-bit precision, **every frequency `a ≠ 0`**:

| p | n | `max|e₂ − (e₁²+p)|` | `max ||root| − √p|` | `max` ratio-to-`ζ₃^k` | degenerate |
|---|---|---|---|---|---|
| 43 | 31 | **6.7e−45** | 6.1e−46 | **1.0e−46** | 0 |
| 67 | 79 | **1.0e−43** | 2.4e−43 | **4.5e−44** | 0 |
| 127 | 127 | **4.6e−43** | 1.1e−43 | **2.3e−44** | 0 |

So at these primes: `e₂ = e₁²+p` holds, all four roots have `|α| = √p` (**purity, at eigenvalue
level**), and the roots form `{α, αζ₃, −ᾱ, −ᾱζ̄₃}` (**120°, at eigenvalue level, independently of the
`g = deg gcd` route** used in `RESULT_n1_120deg_exact_v1.md`).

## 4. Scope

- The **derivations** (§1, §2) are general — they assume only the closure, which is `[PROVED-FORCED]`.
- The **verification** (§3) is 3 small primes, all `p ≡ 3 mod 4`. It confirms the algebra and gives an
  eigenvalue-level check of 120° by a route independent of the existing one; it does **not** prove
  uniformity, and per the record *no finite sweep can*.
- **Nothing here proves the cap.** The chain is
  `e₂ = e₁²+p ⇒ V₂ = V₁²+2p ⇒ S_y ≤ 2 ⇒ |V| ≤ 2√p`, and the first link is the open one.
- ⚠ Also still open and untouched here: purity at every embedding (A3, `[CITED]`, untested), which the
  cap needs alongside the uniform `ζ₃`.
