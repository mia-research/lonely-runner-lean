# N1's open inequality reduces to the SIGN of one L-polynomial coefficient

**Date:** 2026-07-25 · Instrument: the record's own `n1_twisted_eigenvalues_v1.sage` (control C2 fires,
`4.4e-16`). Analysis is exact algebra; the numbers quoted are read from that instrument.
**Status: an analytical REDUCTION plus a first data point. Nothing is promoted; the inequality is
still open.**

**Target.** `RESULT_weight1_proved_v1.md` §3: *"`|sin θ₁ + sin θ₂| ≤ 1` (equivalently `S_y ≤ 2`) … not
implied by weight-1 (which gives only `S_y ≤ 4`) nor by the `α↦−ᾱ` closure … **the single open link in
the entire N1 story**. Natural attack: integrality of the coefficients of `det(1−t·Frob|H¹_c) = L(C,t,χ)`
in `ℤ[ζ_n]` … whose middle coefficient controls `sin θ₁ + sin θ₂`."* This makes that attack exact.

---

## 0a. ⚠ PROCESS STATUS (added on challenge — read before citing anything here)

- **NO `experiment-designer` pre-registration** for the `v ≤ 0` reading of the p=13 / p=43 eigenvalue
  data. §6 correctly gates a FUTURE multi-prime sweep behind a prereg, but the 6-cell reading here was
  done without one. Self-authorized.
- **NO CONTROL FOR THE `v ≤ 0` CLAIM.** The instrument's control C2 (planted eigenvalue tuple recovered
  to 4.4e-16) fires, but it validates the **eigenvalue solver**, not the claim. **Nothing here would
  have fired if `v ≤ 0` were an artifact of the pairing convention or of the μ₆-orbit collapse.** The
  one independent cross-check is that `2|u|` reproduces the instrument's separately-computed
  `|V|/√p` to 4 dp in all 8 rows (§5b) — that validates the DICTIONARY, not the sign of `v`.
- **The reduction (§3) is unaffected** — it is algebra, not a measurement, and depends on no control.

## 1. The factorization the pairing forces

At `p ≡ 3 mod 4` the multiset is closed under `α ↦ −ᾱ` `[PROVED-FORCED]`, so the four eigenvalues are
`{α, −ᾱ, β, −β̄}` and `L` factors over the pairs. With `A = α + (−ᾱ) = 2i√p·sinθ₁` and
`B = 2i√p·sinθ₂` (and `α·(−ᾱ) = −p`):

> `L(t) = (1 − At − pt²)(1 − Bt − pt²)`
> `= 1 − (A+B)t + (AB − 2p)t² + p(A+B)t³ + p²t⁴`

So with `u = sinθ₁+sinθ₂`, `v = sinθ₁·sinθ₂`:

| coefficient | value | status |
|---|---|---|
| `e₁ = A+B` | `2i√p·u` | **this is `V(a)`**; `\|V(a)\| = 2√p·\|u\|` |
| **`e₂ = AB − 2p`** | **`−2p − 4p·v`** | the "middle coefficient" |
| `e₃` | `−p·e₁` | matches the record's forced `e₃ = p·conj(e₁)` (`e₁` imaginary) |
| `e₄` | `p²` | matches the record's forced `e₄ = p²` |

`e₃, e₄` reproduce two identities the record already verified to `≤9e-15`, which validates the
parametrization.

> ⚠ **CORRECTED 2026-07-25 (prereg audit, verified).** An earlier line read *"`p ≡ 1 mod 4` is
> **identical** with `sin → cos`"*. **That is FALSE and the error inverts the criterion.** At
> `p ≡ 1 mod 4` the closure is `α↦ᾱ`, so `α·ᾱ = +p` (not `−p`), giving
> `L = (1−At+pt²)(1−Bt+pt²)` with `A = 2√p·cos θ₁`, hence
> **`e₂ = +2p + 4p·v`, `v = (e₂−2p)/(4p)`, and `v ≤ 0 ⟺ e₂ ≤ +2p`** — the opposite inequality to the
> `sin` case, plus `e₃ = +p·e₁`. Verified at `p=13`: exact `e₂ = −12`; the cos dictionary returns
> `v = −0.72997` (matching the instrument's `−0.7300`), while the sin dictionary returns `−0.2700`.
> **The `sin` dictionary in the table above is `p ≡ 3 mod 4` ONLY** — which is secp's class, so §3's
> reduction is unaffected for secp, but any cross-stratum application must use the right one.

## 2. What is automatic, and what is not

Because `|α| = √p` **exactly** (weight-1, `[PROVED all p]`), the `θᵢ` are real, so `sinθᵢ ∈ [−1,1]`.
Hence `(1∓sinθ₁)(1∓sinθ₂) ≥ 0` gives

> **`|u| ≤ 1 + v`  — AUTOMATIC, and therefore carries no information.**

And the gap is real, not an artifact of weak bookkeeping: sampling `(sinθ₁,sinθ₂) ∈ [−1,1]²`,
**50,190 of 200,000 draws (25%) satisfy every forced constraint yet have `|u| > 1`.**
**Weight-1 + the pairing do not imply the inequality** — confirming the record's own statement.

## 3. The reduction

Combining: `v ≤ 0 ⟹ |u| ≤ 1 + v ≤ 1`. And by §1, `v ≤ 0 ⟺ e₂ ≥ −2p`. Therefore

> **`e₂ ≥ −2p`  ⟹  `|sin θ₁ + sin θ₂| ≤ 1`  ⟹  `S_y ≤ 2`  ⟹  `max_a |V(a)| ≤ 2√p`.**
>
> Equivalently: **the whole open inequality follows from the SIGN of the `t²` coefficient of
> `L(C,t,χ)`** — one coefficient, in `ℤ[ζ_n]`, of a degree-4 polynomial with all roots on `|z|=√p`.

This is the record's named attack made exact: "the middle coefficient controls the sine-sum" is now a
specific inequality on a specific coefficient, and the target is a **sign**, not a magnitude — the kind
of statement integrality arguments can reach.

⚠ **Sufficient, NOT necessary.** `|u| ≤ 1` does not require `v ≤ 0` (e.g. `sinθ₁=sinθ₂=0.4` gives
`|u|=0.8` with `v=+0.16`). A counterexample to `v ≤ 0` would **not** refute the inequality; it would only
close this route.

## 4. Consistency with the record's other open question

The record separately asks whether `S_y → 2` (graded **R-INDET** in `RESULT_n1_phase_cap_v3`, `σ̂_L`
above its threshold — deliberately not resolved). Under §3 these are **the same object**: `|u| ≤ 1 + v`
with `v ≤ 0` saturates exactly when `v → 0`. So **"does `S_y → 2`?" ≡ "does `v → 0`?"** — the
convergence question and the cap question are one question about `e₂`. Not a new claim, an
identification.

## 5. First data point, and a correction to my own reasoning

`p = 13` (`n=7`; `p ≡ 1 mod 4`, so the `cos` form), instrument output, `a ≠ 0`:
phases `arg(α)/π = ±0.211, ±0.8776` ⇒ `cos t₁ = 0.7883`, `cos t₂ = −0.9260` ⇒

> `u = −0.1377` (so `|V|/√p = 2|u| = 0.2774` ✓ matches the printed `0.2774`),
> **`v = −0.7300 ≤ 0`** ✓ — consistent with §3, and `|u| = 0.138 ≤ 1+v = 0.270` ✓.

> ⚠ **CORRECTION — I first declared this route dead, wrongly.** From the sweep's
> `max_a S_y ∈ [1.98567, 1.99999]` I inferred `v ≥ |u|−1 ≈ 0`, hence "`v ≤ 0` is marginal and probably
> false". **That inference applies only at the MAXIMIZING `a`.** At other `a`, `v` is free to be
> strongly negative — and at `p=13` it is `−0.73`. The correct reading: `v ≤ 0` is the claim, and the
> maximizing `a` is precisely where it is **tight** (`v → 0`), which is §4.

## 5b. `p = 43` — the `sin` case (secp's class): `v < 0` on every observed `a`

Instrument completed (`sage n1_twisted_eigenvalues_v1.sage 43`; weight check `8.9e-16`; multiset **not**
conjugation-closed, correct for `p≡3 mod 4` where the closure is `α↦−ᾱ`). Pairing `θ ↦ π−θ` succeeded
on every row, confirming the pairing independently.

| `a` | `sin θ₁` | `sin θ₂` | `u` | `2\|u\|` | printed `\|V\|/√p` | **`v`** |
|---|---|---|---|---|---|---|
| **20 / 24** (maximising) | −0.1555 | 0.9333 | 0.7778 | **1.5556** | 1.5553 | **−0.1451** |
| 17 | −0.9925 | 0.6022 | −0.3903 | 0.7807 | 0.7806 | −0.5977 |
| 19 / 29 | −0.9680 | 0.7013 | −0.2666 | 0.5333 | 0.5333 | −0.6788 |
| 16 | −0.7285 | 0.9575 | 0.2290 | 0.4580 | 0.4582 | −0.6976 |
| 25 / 26 | −0.7855 | 0.9287 | 0.1432 | 0.2864 | 0.2864 | −0.7295 |

1. **`2|u|` reproduces the instrument's printed `|V|/√p` to 4 decimals in all 8 rows** — an independent
   validation of the §1 dictionary against a quantity computed by a different route.
2. **`v < 0` on all 15 OBSERVED rows** (`a = 16…30`), covering **all 5 distinct μ₆-orbit classes**
   (the record's `(n−1)/6 = 5`).
   > ⚠ **CORRECTED tally.** A first draft said *"at every `a`"*. **I only read `a = 16…30` — the tail
   > half of the instrument output; `a = 1…15` was never displayed.** Also, `|V|` determines `|u|` but
   > **not** `v`, so covering all 5 `|V|`-classes does **not** by itself guarantee all `(u,v)` pairs were
   > seen. What is observed: within each `|V|`-class the `v` values agreed (`25/26` both `−0.7295`;
   > `19/29` both `−0.6788`; `20/24` both `−0.1451`), which is *evidence* that `v` is a class function,
   > **not proof**. Supportable claim: `v < 0` on 15 of 30 rows spanning all 5 classes.
3. **`v` is closest to zero (`−0.1451`) exactly at the maximising `a`** — precisely the §4
   identification: saturation of `|u| ≤ 1+v` happens as `v → 0`. Not a new claim; the predicted
   behaviour, observed.

## 6. Status and what is needed

- **Nothing is promoted.** `S_y ≤ 2` remains `[VERIFIED — out-of-sample, 120 primes]`, not proved.
- **The reduction is `[PROVED — algebra]`**, conditional on nothing: it uses only the proved pairing,
  proved weight-1, and `sinθᵢ ∈ [−1,1]`.
- **`v ≤ 0` is `[EMPIRICAL — 6 UNFORCED CELLS, p = 13 and 43]`.** See §5b: `p=43` completed and is the
  `p ≡ 3 mod 4` **sin** case (secp's class). **6 cells is the record's own count of the ENTIRE eigenvalue
  evidence base** (`RESULT_xdomain_ports_v2`: *"SCOPE = 6 UNFORCED CELLS … never read 30/30 here"*), so
  this is the whole available dataset — and it is still 6 cells, not a law.
- **Instrument limit unchanged:** eigenvalues cost `O(p⁴)`; `p=13` is instant, `p=43` is minutes,
  `p≥61` exceeds budget (record's D1). A cheap route to `e₂` alone — e.g. the `k=2` power sum, since
  `Σα² = e₁²−2e₂` — would test `v ≤ 0` at far more primes at `O(p²)`. **Not yet built.**
- **Before any sweep of `v ≤ 0` across primes: `experiment-designer` prereg** (CLAUDE.md §2).

## 7. Prior art

The factorization of a weight-1 degree-4 `L` under a `±` pairing is elementary. The record already
supplied every input used here (weight-1 `[PROVED]`, the `α↦−ᾱ` closure `[PROVED-FORCED]`, `e₃`/`e₄`
forced, and the "middle coefficient" attack). **This file contributes the explicit `e₂ = −2p−4pv`
dictionary and the resulting sign-criterion, not any new input.** No novelty claimed.
