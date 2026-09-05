# RESULT — The Aut(E) orbit bit-ladder: how many bits each quotient yields, measured

**Date 2026-07-19.** Records the bit-count of every quotient available on `E: y²=x³+7` (prime order `n`),
and where the D1 lift `ψ = [P⁺−P⁻]` sits in that family. Per the anomaly-drill protocol the output is a
**bit count with its scope**, not a verdict. Scripts: inline Sage (logged in session), orbit enumeration
exact over `Z/n`. Supersedes the verdict-language framing ("trivial symmetry / no lever") used earlier in
this session, which was a dismissal where a measurement was called for.

---

## 1. The ladder `[VERIFIED — 6 primes]`

Image size of `E(F_p) → E(F_p)/H` and bits gained `= log₂(n) − log₂(image)`:

| p | n | μ₂ (negation) | μ₃ (GLV) | μ₆ (Aut) | ceiling `log₂6` |
|---:|---:|---|---|---|---|
| 43 | 31 | 16 → **0.954 b** | 11 → 1.495 b | 6 → 2.369 b | 2.585 |
| 67 | 79 | 40 → 0.982 b | 27 → 1.549 b | 14 → 2.496 b | 2.585 |
| 79 | 67 | 34 → 0.979 b | 23 → 1.543 b | 12 → 2.481 b | 2.585 |
| 127 | 127 | 64 → 0.989 b | 43 → 1.562 b | 22 → 2.529 b | 2.585 |
| 163 | 139 | 70 → 0.990 b | 47 → 1.564 b | 24 → 2.534 b | 2.585 |
| 211 | 199 | 100 → 0.993 b | 67 → 1.571 b | 34 → 2.549 b | 2.585 |

- **μ₂ → 1 bit**, **μ₃ → log₂3 = 1.585 b**, **μ₆ → log₂6 = 2.585 b**, each approaching its limit as `n` grows
  (finite-`n` deficit is the fixed points / identity class).
- **They chain additively**: `μ₆ = μ₂ × μ₃`, orders coprime, so `1 + 1.585 = 2.585`. `[VERIFIED]`

## 2. The ceiling, and why it is a constant `[PROVED]`

`n` prime ⇒ `E(F_p)` has **no proper subgroups** ⇒ the only group-theoretic fibres any quotient map can
have are orbits of `Aut(E) = μ₆`. Hence this whole family tops out at **`log₂|Aut(E)| = log₂6 ≈ 2.585
bits`** — a **constant**, independent of key length. No member of the family scales with `n`.

## 3. Where the D1 lift sits `[VERIFIED]`

`ψ(P) = [P⁺−P⁻] ∈ A_new` has image `(n+1)/2` — measured **16/31 at n=31 under plain linear equivalence
*and* up to sign**, so the 2-to-1 collapse is **intrinsic to ψ**, not an artifact of the "up to sign"
convention. ψ therefore realises the **μ₂ rung: ≈1 bit**, i.e. it sits at the **bottom** of the ladder,
not at its ceiling. Separately `ψ` is **not** a homomorphism even up to sign (`D₁+D₁ ≠ ±D₂`; and
`0/666` additivity, `0/332` affine, sign-robust — `RESULT_D1_lift_affine_test_v1.md`), so it is a genuinely
non-homomorphic set-map whose image nonetheless collapses to the ± class. Connects to master §X.3.

## 4. Applicability — two different objects, both measured `[VERIFIED]`

The ladder above is a statement about quotienting **the group**. Recorded alongside it, the separate
measurement for a **short-interval** target (puzzle 135, `d ∈ [2¹³⁴, 2¹³⁵)`, secp `n`, `λ³≡1 mod n`):

| object | measurement |
|---|---|
| `d` uniform in `[1,n)` | μ₆ orbit has **6 distinct** members, 20000/20000 → the 6-fold folding of §1 |
| `d ∈ [2¹³⁴,2¹³⁵)` | μ₆ orbit meets the interval in **exactly 1** member, **200000/200000** |

Mechanism for the second row: `−d ≡ n−d ≈ 2²⁵⁶` lies outside the window, and `λd`, `λ²d` are
multiplications by 256-bit constants, missing a 135-bit window with probability `1 − 2⁻¹²²`.

**Scope statement (both rows are facts, neither refutes the other):** the ladder's `log₂6` is the bit
count **for the full-group DLP**; for an interval-constrained target the same orbits do not map the
interval into itself, so the interval-search collapse factor measured here is 1. An automorphism folds an
interval only if it maps that interval into itself — for `[2¹³⁴,2¹³⁵)` recentred symmetrically about 0,
**negation does** (Galbraith–Ruprai PKC 2010, `≈√2`, ~1.36× measured); multiplication by `λ` does not.
**Untested:** any non-group-symmetry map that is interval-compatible; that is the open complement.

## 5. Conversion convention (recorded to prevent double-counting)
A quotient dividing the **search space** by `k` divides a **square-root-time** algorithm's runtime by `√k`.
- full-group rho: `2¹²⁸ → 2¹²⁸/√6 = 2^126.7` (standard; negation+GLV, already used in practice)
- 135-bit interval kangaroo: `2^67.5`, with recentred negation `→ 2^67.0`
Writing `2⁶⁷ → 2^64.4` applies the space factor to a runtime and double-counts by `√6`.

## 6. Process note
The earlier framing of §3–§4 as "trivial symmetry, NO LEVER" was a verdict in place of a measurement, and
the user was correct to reject it. The findings of §1–§3 (the ladder, its additivity, its proved ceiling,
and ψ's position on it) are real and are recorded here as bit counts. §4 records the second measurement
with its scope rather than adjudicating between them.
