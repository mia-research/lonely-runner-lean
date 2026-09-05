# DEVIATIONS — `PREREG_jclass_120deg_discriminator_v1.md`

**Date:** 2026-07-31. **Nothing has been run on any arm.** All entries below were found while
building the instrument, BEFORE any `V` was computed on a non-`j=0` curve, and BEFORE the
`experiment-designer` gate returned. They are recorded here rather than by editing v1, because v1 is
out for audit.

---

## D1 — ★ FATAL to the arm structure: the J1728 arm is EMPTY at `p ≡ 3 mod 4`

**Found by:** direct point-count over `p ∈ {7,19,31,43,11,23,47,59}` and `p ∈ {13,37,61,73}`,
exact Legendre symbols, `A,B ∈ [1,5]`.

`y² = x³ + Ax` (`j = 1728`) is **supersingular for every `p ≡ 3 mod 4`** — `#E = p + 1` for every
`A`, so `n = #E` is even and never prime. v1 §2 froze the prime set as `p ≡ 3 mod 4`, `60 < p < 400`.
**The J1728 arm therefore has no curves at all**, and the J1728 `g₄ = 2` row of the §3 prediction
table — the only *positive* prediction in the design, and the reason the test is more than a null
sweep — is unrunnable as specified.

Measured (`ordinary` = at least one `A` or `B` with `#E ≠ p+1`):

| `p mod 12` | `j = 0` | `j = 1728` |
|---|---|---|
| 1 | ordinary | ordinary |
| 7 | ordinary | **supersingular** |
| 11 | **supersingular** | **supersingular** |

`j = 0` is ordinary iff `p ≡ 1 mod 3`; `j = 1728` is ordinary iff `p ≡ 1 mod 4`.

**⇒ The only residue class in which all three arms exist is `p ≡ 1 mod 12`.**

## D2 — §0a's justification is wrong (its conclusion survives on other grounds)

v1 §0a argued the anchor is not the right test because *"at `p ≡ 11 mod 12` the anchor has `m = 2`,
hence `g = 0`, while every `a≠0` cell at those same primes has `g = 2`."*

**There are no `a≠0` census cells at `p ≡ 11 mod 12`.** By D1, `j = 0` is supersingular there, so
`n = p + 1` is even and the census — which requires `n` prime — is empty. The record's own strata
confirm this: `freeze_n1_120deg_v1.py` selects STRATUM S as `p ≡ 7 mod 12` and STRATUM C as
`p ≡ 1 mod 12`; **`p ≡ 11 mod 12` appears nowhere**, and the D4 correction's "both strata" means
{S, C}, not {`7 mod 12`, `11 mod 12`}. The contrast §0a leaned on does not exist.

**The conclusion (test at `a≠0`, not at the anchor) stands on the correct ground, which was already
on file:** `RESULT_120deg_anchor_from_mlaw_v1.md` §5(i) — `a = 0` is excluded from the census by
construction (`0 ∉ (ℤ/n)^×`) — and §5(ii) — the rigidity-budget row the anchor's value depends on
("each `αᵢ` is `√p` × a root of unity") is the row measured as destroyed by the twist. Neither
requires the `p ≡ 11 mod 12` claim.

**Error class:** a supporting argument invented in the write-up when a correct one was already
recorded three files away — the same "check the artifact family first" failure logged in
`AUDIT_prereg_incomplete_shortscalar_SELFAUDIT_v1.md`.

## D3 — consequence of D1: the closure sign changes, and this is not a free move

At `p ≡ 1 mod 12` we have `p ≡ 1 mod 4`, so `χ₂(−1) = +1`, `V` is **real**, and the closure is
`α ↦ ᾱ` with `e₃ = +p·e₁` (the record's D4 correction). v1 §1 already carries the sign as
`e₃ = χ₂(−1)·p·e₁` and `run_n1_120deg_v1.py:93` implements it, so the machinery is correct — but the
**object changes**: the discriminator now runs in the stratum where `V` is real, not in secp's own
stratum where it is imaginary. Any conclusion is about stratum C.

**This must be stated in the scope section of v2**, and it is a real cost of the repair: secp is
`p ≡ 7 mod 12`, and the arm comparison cannot be run in secp's own class. The J0/JGEN contrast
*can* be run at `p ≡ 7 mod 12` as a secondary, secp-class arm pair (both are ordinary there); only
J1728 is unavailable.

## D4 — `g_k` is choice-independent for `k ∈ {3,4,6}`; it would NOT be for `k ∈ {8,12}`

`deg gcd(L(T), L(ζT))` counts ordered root pairs with ratio exactly `ζ`. If `(α,β)` has ratio `ζ`
then `(β,α)` has ratio `ζ⁻¹`, so `g_ζ = g_{ζ⁻¹}` identically. For `k = 3, 4, 6` we have `φ(k) = 2`
and the two primitive `k`-th roots are mutually inverse, so **`g_k` does not depend on which
primitive root the multi-modular embedding picks.** For `k = 8, 12` (`φ = 4`) there are two distinct
inverse-pairs and the choice would matter; those `k` are **not** used, and must not be added without
pinning the root.

Independently: *"reduction only raises gcd degree, so true `g` = min over `l`"* does not depend on
`k` being prime — it is a statement about reduction mod `l`. That part of v1 §1 is sound for
composite `k`.

## D5 — `primitive_root_of_order()` in `run_n1_120deg_v1.py:56` is wrong for composite `k`

Its comment states *"m prime -> order is exactly m"*, and the code returns the first `b` with
`b^{(l-1)/m} ≠ 1`. For `m = 4` that returns an element of order 4 **or 2** (any `b` whose
`(l−1)/4`-power is `−1` passes the test but may have order 2 after... ) — in any case the code's own
justification is void for composite `m`, so it cannot be reused for `k = 4, 6`. v1 §5 C-ORDER
already requires a replacement with an asserted exact order; **D5 records that the existing function
must not simply be called with `k = 4` or `6`.**

## D6 — ★ the predecessor's negative plant is not generic; it is `ζ₄`-locked by construction

**Found by:** the repaired C-PLANT firing. Building the control at `k = 4` made it fail
(`PLANT-N4 = 2` where 0 was wanted), and the cause is in the inherited plant, not the instrument.

`run_n1_120deg_v1.py:143-144` builds its `want-0` control **PLANT-B** from
`α = 3 + 2i`, `β = 2 + 3i`, both of norm 13, described as a generic quartet
`{α, β, −ᾱ, −β̄}` with no lock. But `i·\barα = i(3−2i) = 2+3i = β` **exactly**, so
`β/\barα = ζ₄` and the quartet carries a `ζ₄` ratio by construction.

**This is structural, not a slip of arithmetic.** `ℤ[i]` has unique factorisation, so any two
elements of the same *prime* norm are related by a unit (`μ₄`) times conjugation. **A negative
control built from two Weil numbers of the same prime norm can never be lock-free.** All eight
elements of norm 13 are associates of `3+2i` or of its conjugate — verified by enumeration.

**Effect on the published result: none.** `RESULT_n1_120deg_exact_v1.md`'s statistic is `k = 3`,
`ζ₄` is not a cube root of unity, and PLANT-B does report `g₃ = 0` correctly. **What is inaccurate
is the control's stated meaning** — it certifies "no `ζ₃` lock in a `ζ₄`-locked quartet", not "no
lock in a generic quartet". The `k=3` census's negative control is therefore weaker than described,
and it **must not be reused at `k = 4`**, which is exactly what this spec proposed to do.

**Repair, implemented:** the negative plant now uses a **composite** norm
(`65 = 5·13`: `g_A = (2+i)(3+2i) = 4+7i`, `g_B = (2+i)(3−2i) = 8−i`), and is **self-validating** —
the code enumerates all 12 ordered root ratios and asserts none has order `≤ 12` before the plant is
used. A hand-picked plant that is silently non-generic cannot recur.

**Post-repair C-PLANT (`F_73`): ALL FIRE** — `g_k = 2` on each of the three positive plants
`k ∈ {3,4,6}`, `g_k = 0` on the lock-free negative plant at all three `k`, and **0 on every
cross-order pair** (a `ζ₃` plant registers nothing at `k=4` or `6`, and so on) — the last being the
check that makes a `g₄` reading on the J1728 arm meaningful.

---

## Instrument status (as of 2026-07-31, pre-gate)

`jclass_120deg_discriminator_v1.py`, `--check` mode. **No arm has been run; the arm runner refuses
to execute without `--i-have-the-gate` and a v2 spec.**

| control | result |
|---|---|
| **C-ORDER** — `root_of_order` exact for `k ∈ {3,4,6,12}` over 5 primes | **PASS** (D5 repaired) |
| **C-PLANT** — 3 positive, 1 lock-free negative, 6 cross-order, over `F_73` | **ALL FIRE** (D6 repaired) |
| **C-REPRO** — generalized pipeline vs `RESULT_n1_120deg_exact_v1.json`, `p = 43,67,79,127` | **PASS, cell-for-cell**: `{2:5}`, `{2:13}`, `{2:11}`, `{2:21}`; `zero=0`, `rep=0`, cell counts exact |
| **C-EXACT** — `check_no_float.py` | **OK** |

C-REPRO is the load-bearing one: the `A`-generalized code path reproduces the published `j = 0`
census exactly, so a difference observed on a new arm is attributable to the curve and not to the
rewrite.

---

## Standing after these deviations

**v1 must be reissued as v2 before any arm runs.** Required changes: prime class `p ≡ 1 mod 12`
(D1); §0a rewritten to the correct justification (D2); scope restricted to stratum C with the
secp-class J0/JGEN pair named as a secondary arm (D3); `k` restricted to `{3,4,6}` with the
choice-independence argument recorded (D4); `root_of_order` replaced and asserted (D5).

**No number from any arm may be read against v1.** The `experiment-designer` audit of v1 remains
useful — every axis except the prime-class selection is unaffected by D1–D3 — and its findings will
be folded into v2 rather than superseded by them.
