# PREREG — S-visibility under the scalar-λ model: three falsifiable predictions

**Date 2026-09-01, written BEFORE any of the three tests landed.** Companion:
`RESULT_s_visibility_scalar_lambda_v1.md`. Ground truth: `anew_sorder_sweep_v1.log` (8 primes),
`NOTE_anew_subgroup_structure_map_v1.md`.

## The model

`ζ₃ : (x,w) ↦ (ωx, w)` **fixes `w`**, and `lift(P) = [(x_P, r) − (x_P, −r)]` with `r² = y_P` is written
in `(x,w)` coordinates. Hence `lift(φP) = ζ₃*(lift P)` — **`lift` is φ-equivariant**. On the cyclic
group `A_new(F_p) ≅ Z/M` (M squarefree), `ζ₃*` acts as multiplication by some `c` with `c³ ≡ 1 mod M`.
Therefore

> `S(P) = Q₀ + b₂·Q₁ + β·Q₂ = (1 + b₂c + βc²)·lift(P) = λ·lift(P)` — **a scalar.**

> **`ℓ` is S-BLIND ⟺ `ℓ | λ`.**

`β` = the sweep's arbitrary pick (smallest primitive cube root mod `p`), `b₂ = β² mod p`.

**Forced blindness** (independent of the unknown `c`): if `β ≡ b₂ ≡ 1 mod ℓ` then
`λ ≡ 1 + c + c² ≡ 0` for *either* primitive cube root. This happens when `ℓ | gcd(β−1, b₂−1, M)`.

## Predictions

| # | prediction | basis | status |
|---|---|---|---|
| **PR1** | **`p = 1303` is FULLY VISIBLE — NOT 13-blind** — despite `13 \| M = 3·13·19·2293`. `β=95`, `b₂=1207`; `95 ≡ 4`, `1207 ≡ 11 mod 13`, so `λ ≢ 0`. | this is the record's own named discriminating case; the sweep `anew_sorder_sweep_v2` is grinding it now | **OPEN** |
| **PR2** | **`p = 1459` IS 13-blind.** `β=339`, `b₂=1119`, both `≡ 1 mod 13`; `13 \| M = 3·13·193·283`. Forced. | new target, not in any sweep list | **OPEN** |
| **PR3** | **`p = 2707` IS 13-blind.** `β=1327`, `b₂=1379`, both `≡ 1 mod 13`; `13 \| M = 3·13·187963`. Forced. | new target | **OPEN** |
| **PR4** | **At `p=211`, swapping `β=14 → β=196` leaves 13 BLIND** (both `≡ 1 mod 13`), and 31, 37 stay visible. **Discriminates the scalar-λ model from the eigenplane model**, which predicts the visible and blind sets EXCHANGE. | `s_beta_swap_v1.sage` | **✅ CONFIRMED 2026-09-01.** `β=14`: SEES [3,31,37], BLIND [13]. `β=196`: SEES [3,31,37], BLIND [13] — **identical, no exchange.** Eigenplane model REFUTED; scalar-λ model confirmed. (Also reproduces the ground truth on 14 sample points vs the sweep's 80.) |

## Falsifiers

- **PR1 fails** (1303 turns out 13-blind) ⇒ the scalar-λ model is wrong and an `ℓ=13`-specific
  arithmetic law is back on the table.
- **PR4 fails** in the *exchange* direction (13 seen, 31/37 blind) ⇒ `lift` is not φ-equivariant,
  or `S` is not scalar, and the eigenplane picture governs instead.
- **PR2/PR3 fail** ⇒ the forced-blindness derivation is wrong even where `c` cannot matter.

## Standing over-prediction — CLOSED 2026-09-02

Testing *both* primitive cube roots `c` over-predicted blindness at `(79, ℓ=7)` and `(163, ℓ=7)`.
**Resolved by measuring `c` directly from the φ-action** (`s_lambda_c_v1.sage`): `c` is found as the
unique cube root of unity mod `ord(D)` with `c·D = lift(φP)`. `S` is never used, so the subsequent
λ-prediction is **not circular**.

| p | `ord(D)` | `c` | `c³≡1` | `λ = 1+b₂c+βc²` | `gcd(λ, ord)` | ground truth |
|---|---|---|---|---|---|---|
| 79 | 2107 = M/3 (7²·43) | 2027 | ✓ | 1632 | **1** | fully visible ✓ |
| 79 | 6321 = M | 6241 | ✓ | 3739 | **1** | fully visible ✓ |
| 79 | 21 | 4 | ✓ | 1 | **1** | ✓ |
| 163 | 26733 = **M** | 26569 | ✓ | 19132 | **1** | fully visible ✓ |

`λ ≡ 1 mod 7` at p=79, so `ℓ=7` is **seen** — the true `c` is the other cube root, exactly as the
model requires. At p=163 a single lift generates the **whole** group, so visibility reduces to `λ`.

**Consequences:**
1. **`lift` is φ-equivariant — measured, not assumed.** `c³ ≡ 1 mod ord(D)` at **5/5** points. This
   is the load-bearing step of the §2 derivation.
2. **The predictor is validated at 8/8 primes** with `c` determined independently.
