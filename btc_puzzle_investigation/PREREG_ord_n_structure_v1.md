# PREREG — the multiplicative orders `ord_n(2)`, `ord_n(p)` in `(ℤ/nℤ)*`

**Date:** 2026-07-24 · **Frozen BEFORE computation.** Object = secp256k1's group order `n` (prime),
base field prime `p`. Deterministic exact-integer arithmetic; no sampling, no floats (project rule).

Target = the ledger item (`OPEN_ITEMS_LEDGER_v1.md §A`, "new"):
`ord_n(p) = (n−1)/6`, `ord_n(2) = (n−1)/64`, `[VERIFIED]` and **never explained**.

---

## 1. What is computed (frozen)

Exact integers only. `n−1` factored; factorization **verified by product and by primality of each
factor** (not taken on trust from the record — see §5).

| # | quantity | note |
|---|---|---|
| Q1 | `ν₂(n−1)`, `ν₃(n−1)`, full factorization of `n−1` | the record asserts `ν₂ = 6` |
| Q2 | `ord_n(2)` and the cofactor `c₂ := (n−1)/ord_n(2)` | record asserts `c₂ = 64` |
| Q3 | `ord_n(p)` and `c_p := (n−1)/ord_n(p)` | record asserts `c_p = 6` |
| Q4 | `t := p+1−n`; check `p ≡ t−1 (mod n)` | forced identity, used as an arithmetic self-test |
| Q5 | power-residue characters of `2` and `p` mod `n` at each prime `ℓ ∣ n−1` | *which* subgroup each lands in |

## 2. The control row (decides whether Q2/Q3 are findings at all)

A cofactor `c` means the base lies in the index-`c` subgroup — a **1-in-`c` event for a random base**.
With many candidate bases, some base having a large cofactor is *expected*. So the claim "2 is special"
is untestable without the baseline. Frozen control:

> **C1.** Compute `c_q = (n−1)/ord_n(q)` for every prime `q < 1000` (168 bases, `2` among them).
> Report the **full distribution** of `c_q`, and `#{q : 64 ∣ c_q}` and `#{q : 6 ∣ c_q}`.

**Pre-committed reading of C1** (fixed now, before seeing it):

- If several other small primes also have `64 ∣ c_q` (expectation ≈ `168/64 ≈ 2.6`), then `c₂ = 64` is a
  **generic draw**, NOT a property of `2`, and the correct output is *"the record's item is a selection
  effect"* — a dissolution, which per the anomaly-drill protocol is a positive result, not a failure.
- If `2` is the **unique** base under 1000 with `64 ∣ c_q`, that is `≈ 1-in-64` seen once among 168
  tries — still **not** significant on its own (`p ≈ 0.93`). It is promoted to a question, not a finding.
- Only a **structural** account (§3) can make either case a theorem. The count alone decides nothing.

Same reading applies to `c_p = 6` with expectation `168/6 = 28`.

**`p` is exempt from C1's selection critique** and is the stronger of the two: `p` is not a base chosen
from a list, it is *the* other distinguished prime, and `c_p = 6` coincides with `|Aut(E)| = 6` for `j=0`.

## 3. The structural hypothesis to be tested against Q5 (frozen)

**H-sextic.** `c_p = 6` is **not** coincidence but forced by CM: `E/F_p` has CM by `ℤ[ω]`, `π π̄ = p`
with `π ≡ 1 (mod n)` on the rational `n`-torsion, hence `p ≡ π̄ (mod n)`. If `n ≡ 1 (mod 3)` both `p`
and `n` split in `ℤ[ω]` and the **sextic residue symbol** `(p/n)₆` is computable by **Eisenstein
reciprocity** from `(n/p)₆`, with `n ≡ 1−t (mod p)`.

- **Confirmed if:** `p^((n−1)/6) ≡ 1 (mod n)` AND the sextic symbol is reproduced by the reciprocity
  computation from `t` alone.
- **Falsified if:** `p^((n−1)/6) ≢ 1`, or the reciprocity value disagrees with the direct one.
- **Scope limit stated now:** even if confirmed, this explains the **6**, and says *nothing* about the
  `2`-part `64`, and has **no leakage/ECDLP consequence** — it is a statement about `p mod n`, and `p`,
  `n`, `t` are all public. It is structure-mapping, not a lever.

## 4. Falsification of the record itself

If Q1–Q3 disagree with `(n−1)/6` / `(n−1)/64` / `ν₂ = 6`, the **record is wrong** and the finding is the
correction. (Precedent: `feedback_verify_root_system_against_defining_polynomial_2026_07_20` — an
inherited "verified" root-system claim was false and was repeated into two files.)

## 5. Integrity

Exact `int` only; `pow(b, e, n)`; no float anywhere. Every asserted prime factor of `n−1` is
Miller–Rabin-tested in-script and the product re-multiplied to `n−1`; the factorization is **not**
inherited from memory. Order computed by descending from `n−1` through each prime factor.

## 6. What this cannot become

No claim about key recovery, and no transfer to the `d`-side. Per
`feedback_no_prng_generation_side_2026_07_14`, the object is curve/field arithmetic only.
