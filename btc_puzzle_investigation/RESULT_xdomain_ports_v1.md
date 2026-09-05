# RESULT — testing the four cross-domain ideas (not just their methods)

*2026-07-24. Spec: `PREREG_xdomain_ports_v1.md`. Deviations: `PREREG_xdomain_ports_v1_DEVIATIONS.md`
(**seven — read them**, D3 and D4 are load-bearing). Premise audit:
`AUDIT_xdomain_synthesis_premises_v1.md`. Scripts: `xdomain_derivation_checks_v1.py`,
`n1_twisted_eigenvalues_v1.sage`, `forced_readout_multiples_v1.py`, `ct_event_complete_v1.py`,
`ct_boundary_stratified_v1.py`.*

**No leakage, key-recovery or ECDLP claim is made or attempted anywhere in this document.**

> **What was tested.** The four proposals were first checked as *premises* (the audit), which retired
> three of them as stated. This document tests the **ideas** underneath — the substantive claims about
> the curve, separated from the methods proposed to reach them. Three ideas were tested; the fourth
> (ARM 4, the parity-legal amicable channel) is specified in the spec and **was not run**.

---

## 1. The `½`-saturation is NOT eigenvalue starvation — all four twisted eigenvalues have weight 1

*ARM B. `n1_twisted_eigenvalues_v1.sage`. Pre-committed reading on file since 2026-07-23
(`NEXT_DIRECTIONS_v1.md §3 #1`), which pre-dates this run.*

**The object, not a proxy.** Every prior N1 run measured `max_a |V(a)|`, a magnitude. This computes
the four Frobenius eigenvalues themselves: `V_k(a) = Σ_{P∈E(F_{p^k})} χ₂(y_P) χ_a(Tr_{k/1}P)` for
`k = 1..4`, then Newton's identities.

**Control C2 fires:** a planted eigenvalue 4-tuple is recovered to `4.4×10⁻¹⁶`.

| `p` | `n` | weight check `max_a max_i ‖α_i‖/√p − 1‖` | all four weight 1? | `max_a|V₁(a)|/√p` |
|---|---|---|---|---|
| 13 | 7 | `2.2×10⁻¹⁶` | **yes** | 1.664 |
| 43 | 31 | `8.9×10⁻¹⁶` | **yes** | 1.555 |

> **`[VERIFIED — p = 13, 43 only]` All four twisted Frobenius eigenvalues have modulus exactly `√p`,
> at every frequency `a`.**

**What this settles.** N1's standing gloss (`MASTER_v4:189`) is *"effectively only **2 of 4**
eigenvalues carry weight-1 mass at the maximizing frequency — the 2+2 splitting."* **Read literally as
a statement about weights, that is refuted here:** four of four carry weight 1, at every `a`, not two.
The `½` is therefore **not** a rank or weight deficit. It is a statement about the **phases** — four
unit-modulus numbers whose sum is limited by their configuration, not by their sizes.

⚠ **The word "effectively" in the record's phrasing may have been a gloss on the magnitude rather than
a weight claim.** What is refuted is the literal weight reading. The prereg named this arm
"eigenvalue starvation"; **there is no starvation.**

⚠ **`Σ_i |α_i| = 4√p` is a tautology given weight 1** and is not evidence of anything (D6). The
non-tautological question — what the *actual* phase configuration permits — is the live remainder and
its run is still in progress.

⚠⚠ **SCOPE, and it is small.** Two primes. Because `V(a) = V(aλ)` (DC1) and `V(a) = χ₂(−1)V(−a)`, the
`n−1` frequencies collapse to `(n−1)/6` distinct configurations: **1 at `p=13`, 5 at `p=43` — six
unforced cells in total.** Measured distinct nonzero `|V₁(a)|/√p` values at `p=43`: **5 = (31−1)/6**,
exactly as forced. Do not read `30/30` or `36/36` anywhere in this arm.

## 2. The multiples that force the `χ₂(y)` readout are exactly `Aut(E)` — complete, exhaustive

*ARM C. `forced_readout_multiples_v1.py`. The idea behind proposal 3, after DC3 retired its method.*

**Question asked directly:** for which `k` is `χ₂(y_{[k]P}) = c·χ₂(y_P)` for **every** `P`? Exact
integer contingency tables, **every** `k` tested, no threshold, no statistic.

> **`[VERIFIED — 19 primes, `p ≤ 643`, exhaustive in `k`]` The forced set is exactly
> `μ₆ = {±1, ±λ, ±λ²} = Aut(E)`, with sign `+1` on `{1,λ,λ²}` and `χ₂(−1)` on `{−1,−λ,−λ²}`.
> No extras, no omissions, at any tested prime.**

Six elements are **forced a priori** (β fixes `y`; `[−1]` negates it) and are an instrument check.
**The unforced content is that nothing else is forced:** ≈ **3,400** non-automorphism multiples tested
across the 19 curves, none of them forcing.

**What it means, stated narrowly.** The relation `χ₂(y_{[λ]P}) = χ₂(y_P)` connects the readout at two
points whose scalars differ by the *publicly known* constant `λ`, and both sides are computable from
`P` alone. It therefore does not predict the readout at a point whose scalar is unknown, and the
proposal's "deterministic oracle for internal scalar bits" does not follow from it. *(This is a
statement about what this relation supplies — not a claim that the automorphism action is without
consequence elsewhere.)*

## 3. The `C_T` departure IS localised — with the opposite sign, and it is lift geometry

*ARM A2, `EXPLORATORY` (D2, D5). `ct_boundary_stratified_v1.py`. `E: y²=x³+7`, `p ≡ 1 mod 3`,
`n` prime, AP-complete population over all step sizes.*

The idea under test: the carry-leak is a **deterministic boundary event**, so the departure from the
tensor law should concentrate where the lift sum lands near the exact decision boundary
`a_i ∈ ℤ + ½`. Exact integer margin `M = min_i(DET − 2|N_i − c_i·DET|)`, five quantile strata,
pooled `G²/df` for the factorisation within each stratum.

**Control K2 fires:** a coupling planted in the low-margin stratum only gives gradient `+3.24` against
`≈1.0` elsewhere.

| `p` | `n` | REAL gradient | K1 (margin permuted, 20 draws) | `z` vs K1 | K3 (geometry only, 20 draws) | `z` vs K3 |
|---|---|---|---|---|---|---|
| 1051 | 1093 | **−17.63** | `−0.79 ± 3.75` | **−4.49** | `−19.97 ± 2.94` | `+0.80` |
| 1669 | 1663 | **−20.37** | `+0.59 ± 4.99` | **−4.20** | `−24.68 ± 5.00` | `+0.86` |
| 2143 | 2089 | **−11.40** | `+0.05 ± 3.46` | **−3.32** | `−5.67 ± 2.17` | `−2.64` |

**Three findings, in order of how well they are supported.**

1. **The departure is margin-dependent — a real localisation.** `z = −3.3 … −4.5` against the
   margin-permutation control, 3/3 primes. The stratification is not manufacturing it.
2. **Its sign is the reverse of the idea's prediction.** The excess is largest **far from** the carry
   boundary and smallest near it. The pre-committed reading enumerated "concentrates at low margin"
   and "flat"; **it did not enumerate this outcome**, so no conclusion is retro-fitted (D5). What can
   be said: the boundary-set idea predicted a boundary event, and the localisation found is interior.
3. **It is reproduced by the geometry-only control.** K3 keeps the exact lift multiset (hence every
   margin and every carry state) and destroys the arithmetic order in `d`. Two primes sit inside K3
   (`z = +0.80, +0.86`); one is at `z = −2.64`, which over three primes with no multiplicity
   correction is not a resolved excess. **At this scope no arithmetic-in-`d` remainder is resolved.**

**And the headline number is an artifact of the estimator, not the curve.** The pooled `G²/df` is
`155.0` at `p=1669` — against `155.6 ± ` from K3, and `85.9` vs `82.3` at `p=2143`. **The entire
apparent "massive departure from the tensor law" is reproduced with the arithmetic destroyed.** It is
the AP-overlap dependence of the estimator plus lift geometry. This is the concrete confirmation of
the spec's §2.0-3 warning and the reason the power claim is withdrawn (D4).

**Companion, reported never as a verdict:** `|λ₂−λ₃|` on the AP-complete object = `0.0142` (`n=1093`),
`0.0097` (`n=1663`), `0.0043` (`n=2089`) — and **real by construction**, since that object is
reversible (D4), so this is not comparable to the `g=1` drill's directed `λ₂,λ₃`.

## 4. What was NOT run

- **Spec ARM 2** (`T₂ = ‖ΠDΠ‖_F²`, hashed calibration, 9 primary + 6 holdout curves of the frozen 37).
- **Spec ARM 3** (exact-vanishing census at composite order).
- **Spec ARM 4** (the parity-legal amicable channel) — the live version of proposal 4, and the one
  place a proposal's underlying frontier is still fully open.
- **ARM B's phase configuration** — the live remainder of §1; run in progress at write-up time.

## 5. Grades

| item | grade |
|---|---|
| DC1–DC4 (`V(a)=V(aλ)`; `t_p+t_n=2`; `φ(n)` vacuous at prime `n`; exact tensor degeneracy) | `[DERIVED — FORCED]`, zero information as evidence |
| All four twisted eigenvalues of weight 1 | `[VERIFIED — p = 13, 43; six unforced cells]` |
| Literal "2 of 4 carry weight-1 mass" | **refuted at those two primes** |
| Forced multiples `=` `Aut(E)` | `[VERIFIED — 19 primes, exhaustive in k]`; the six elements themselves `[DERIVED — FORCED]` |
| `C_T` departure is margin-localised, interior, geometric | `[EMPIRICAL — EXPLORATORY, 3 primes]` |
| "AP-completeness buys 6–30× power" | **withdrawn — it was a premise, not a measurement** (D4) |

**Nothing here closes a frontier.** N1 moves from an unexplained magnitude to a phase question with
the weight explanation eliminated; `C_T`'s §X.6 stays exactly where DRILL 01 left it, with the
addition that the AP-complete estimator is dependence-dominated and must not be used for a bound
until its floor is measured (spec §2.5).
