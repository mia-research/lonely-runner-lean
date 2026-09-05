# RESULT — S-visibility is a SCALAR condition, not a character: `S = λ·lift`, `ℓ` blind ⟺ `ℓ | λ`. The single blind point (211, 13) is forced by the sweep's arbitrary `β`.

**Date 2026-09-01. Grade: `[PROVED — derivation]` for the scalar reduction; `[VERIFIED]` for the
consistency of the record with a `1/ℓ` coincidence model; predictions PR1–PR4 OPEN
(`PREREG_s_visibility_lambda_predictions_v1.md`).**

Ground truth: `anew_sorder_sweep_v1.log` (8 primes), `NOTE_anew_subgroup_structure_map_v1.md`.
Ledger rows: **M39** (the reduction), **SB** (the closure), **SB-owed**. Companion to the ρ_p
retraction (`RESULT_rho_branch_convention_v1.md`) — same defect class.

---

## 1. The claim under audit

The record (`NOTE_anew_subgroup_structure_map_v1.md` §4): S-visibility of `ℓ | M = p²+p+1` is *"an
embedding-sign question in `Q(√p, ζ₃)`"*; the plain Legendre law **fails** (`ℓ=37 @ 211`: symbol `+1`
but seen); *"every `ℓ ≡ 7 mod 12` is seen (6/6); the `ℓ ≡ 1 mod 12` class is mixed (13 blind, 37
seen) — the sign is a finer character, conjecturally a quartic-type character."* `p=1303` was named
the discriminating case and the sweep is grinding toward it.

## 2. The reduction: `S` is multiplication by a scalar

`lift(P) = [(x_P, r) − (x_P, −r)]` with `r² = y_P`, written in the `(x, w)` coordinates of
`C : w⁴ = x³ + B`. The automorphism `ζ₃ : (x, w) ↦ (ωx, w)` **fixes `w`**. Therefore

    lift(φP) = ζ₃*(lift P)     — lift is φ-equivariant.

`A_new(F_p) ≅ Z/M` is **cyclic** whenever `M` is squarefree (`NOTE_anew` §1), so `ζ₃*` acts on it as
multiplication by an integer `c` with `c³ ≡ 1 mod M`. Hence, with the sweep's integer multipliers
`β` and `b₂ = β² mod p`:

> ### `S(P) = Q₀ + b₂·Q₁ + β·Q₂ = (1 + b₂c + βc²)·lift(P) = λ·lift(P)`
> ### **`ℓ` is S-BLIND ⟺ `ℓ | λ`.**

The "two `ζ₃`-eigenplanes and which one contains the `π=1` line" picture is **too coarse**: on a
*cyclic* group the `ℓ`-part is one-dimensional and `S` acts on it by a scalar. Blindness is the
scalar vanishing — an arithmetic event of probability `≈ 1/ℓ`, **not a character**.

## 3. The record is exactly what chance predicts

| | |
|---|---|
| tested `(p,ℓ)` pairs, `ℓ≠3` | **17** |
| expected blind under the `1/ℓ` model | **0.865** |
| observed blind | **1** |
| `P(at least one blind)` | **0.60** |

Class by class:

| class | pairs | `ℓ` values | expected blind | observed |
|---|---|---|---|---|
| `ℓ ≡ 7 mod 12` | 14 | 7, 19, 31, 43, 67, 163, 631, 751, 368551 | 0.759 | 0 |
| `ℓ ≡ 1 mod 12` | 3 | 13, 37, 613 | 0.106 | 1 |

**The `ℓ ≡ 7 mod 12` "6/6 seen" is really 14/14 with 0.76 expected blind** — observing none has
probability `≈0.47`. Unremarkable. And the class split itself was carved *after* seeing where the
single blind point landed. There is no pattern to explain.

## 4. Why `(211, 13)` specifically — and it is a convention, not arithmetic

The sweep picks `beta = next(c for c in range(2,p) if pow(c,3,p)==1 and c!=1)` — the **smallest**
primitive cube root mod `p`. At `p=211` that is `β = 14`. Then:

- `β² = 196 < 211`, so `b₂ = β²` **exactly** (no wraparound mod `p`);
- `β − 1 = 13`, and `13 | M = 3·13·31·37`;
- therefore `β ≡ b₂ ≡ 1 mod 13`, and `λ ≡ 1 + c + c² ≡ 0 mod 13` for **either** primitive cube root.

**Blindness at `(211,13)` is forced independently of the group action.** It is a coincidence of the
arbitrary `β`-pick, not a fact about `A_new`. This is the same defect class as `ρ_p`: an observable
defined through a convention, whose one anomalous value was being chased as a character law.

**Scan** (`p ≡ 7 mod 12`, `13 ≤ p < 4000`, 139 primes): exactly **3** forced-blind cases —
`p = 211, 1459, 2707` — **all at `ℓ = 13`**, rate 2.2%. `p=211` is one of the three.

## 5. Predictions (pre-registered; see the PREREG)

| # | prediction | status |
|---|---|---|
| **PR1** | **`p=1303` is FULLY VISIBLE, not 13-blind**, despite `13 \| M`. `β=95, b₂=1207`; `95≡4`, `1207≡11 mod 13`. **This is the record's own named discriminating case** | OPEN — `anew_sorder_sweep_v2` grinding |
| **PR2** | `p=1459` **IS** 13-blind (forced) | OPEN |
| **PR3** | `p=2707` **IS** 13-blind (forced) | OPEN |
| **PR4** | At `p=211`, `β=14→196` leaves 13 **still blind**; 31, 37 stay visible. Discriminates scalar-λ from the eigenplane model, which predicts the sets **exchange** | OPEN — running |

## 6. Instrument finding — the sweep is the wrong tool

| p | 43 | 163 | 547 | 823 | 1051 | 1303 |
|---|---|---|---|---|---|---|
| time | 104 s | 66 min | 12 h | 23 h | **55 h** | 37 h+ elapsed, **0-byte log** |

Superlinear, and it builds the full function-field Jacobian (`L.places(1)`, divisor arithmetic) to
answer a **one-bit** question. §2 answers the same question in `O(1)` integer arithmetic. **Recommend
retiring the sweep** and testing PR1–PR3 by the λ route. *(Not killed — it is another session's job.)*

## 7. Scope of the closure

**Closed:** the "finer quartic-type character" / `Q(√p,ζ₃)` embedding-sign programme for S-visibility,
and the `ℓ mod 12` pattern (§3 — post-hoc, and priced).
**NOT closed:** the `A_new` structure map itself (M34 — cyclicity, the automatic-`√p` witness `r=1+p`
of order 6, the Smith refinement at `ℓ²`) is untouched and stands. Whether the *transfer* hurdle
matters is a separate question, unaffected.
**Owed (SB-owed) — CLOSED 2026-09-02.** `c` measured directly from the φ-action
(`s_lambda_c_v1.sage`; `S` never used, so non-circular): p=79 → `c = 2027` (ord 2107), `6241` (ord
6321 = M); p=163 → `c = 26569` (ord 26733 = **M**). `gcd(λ, ord) = 1` in every case, so `ℓ=7` is seen
at both — the true `c` is the other cube root, as the model requires. **`c³ ≡ 1 mod ord(D)` at 5/5
points confirms `lift` is φ-equivariant by measurement**, which is the load-bearing step of §2. The
predictor is **validated at 8/8 primes**.

**PR4 CONFIRMED (2026-09-01).** β-swap at p=211: `β=14` and `β=196` both give SEES [3,31,37], BLIND
[13] — **identical, no exchange**. The eigenplane model is REFUTED; the scalar-λ model stands.
