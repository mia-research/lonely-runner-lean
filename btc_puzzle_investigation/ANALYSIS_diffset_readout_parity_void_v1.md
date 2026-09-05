# Odd characters are structurally unusable on a NEGATION-CLOSED index set — `χ₃` is the only readout there

> ## ⚠ SCOPE CORRECTION (2026-07-31, same day, before this file was cited anywhere)
>
> The title and body of the first revision said **"difference set"**. That is too broad and is
> **wrong for the group-law difference.**
>
> The void requires the index set to be **negation-closed in the value**: `x_i − x_j` and
> `x_j − x_i` differ by a sign, which is what makes an odd `χ` ill-posed (unordered) or identically
> zero (symmetrized).
>
> **For the group-law difference the void does NOT apply:**
> `x(P_j − P_i) = x(−(P_i − P_j)) = x(P_i − P_j)` — **negation preserves the `x`-coordinate**, so
> each unordered pair yields ONE canonical value and `χ₂`, `χ₆` are well-posed.
>
> **Measured confirmation, same `β`, same code, two objects** (`run_multireadout_v3b.log`, C-GLV):
>
> | | field difference | group-law difference |
> |---|---|---|
> | `E₃` | 0 exact | 0 exact |
> | `E₆` | **292** — β-closure broken by unordered pairing | **0 exact** — closure intact |
>
> **⇒ Everywhere below, read "difference set" as "FIELD difference set / negation-closed index
> set".** The group-law difference, and any swap-invariant object such as `x(P_i + P_j)`, admits
> the full `χ₂`/`χ₃`/`χ₆` family.
>
> ⚠ The `[parity-void]` tags printed on the **group** arm of `interval_multireadout_v3.py` are
> therefore wrong; the field-arm tags are right. See `RESULT_interval_multireadout_v2.md` §4–§5.

---


**Date:** 2026-07-31. **Grade: `[PROVED — parity, exact]` for §1; `[VERIFIED — exact]` for §2.**
Found while building `interval_multireadout_v3.py`; the C-GLV control refused to pass and the
refusal was correct.

---

## 1. The statement

Let `S` be a set of points, `D = {x_i − x_j}` its pairwise difference multiset, and `χ` a
multiplicative character of `F_P`. The difference multiset is **symmetric**: if `d ∈ D` then
`−d ∈ D`.

> **If `χ(−1) = −1`, then `Σ_{d∈D} χ(d) = 0` identically**, for every `S`, because `d` and `−d`
> pair off and `χ(d) + χ(−d) = χ(d)(1 + χ(−1)) = 0`.
>
> **The unordered-pair version is not a repair — it is ill-posed.** Taking one representative per
> pair (by index order `i<j`) makes the statistic depend on an arbitrary labelling, not on the
> curve.

**Which readouts survive, on secp (`P ≡ 3 mod 4`, `P ≡ 1 mod 3`):**

| readout | `χ(−1)` | on a difference set |
|---|---|---|
| `χ₂` | **−1** | **VOID** — identically 0 symmetrized; index-order-dependent unordered |
| `χ₃` | **+1** | **usable** — even, so `±d` carry the same class; well-posed unordered |
| `χ₆ = χ₂·χ₃` | **−1** | **VOID** |

`χ₃(−1) = 1` follows from `χ₃(−1)² = χ₃(1) = 1` and `χ₃(−1)³ = χ₃(−1)`, forcing `χ₃(−1) = 1`.

> **⇒ Among characters of order dividing 6, the only nontrivial readout available on a difference
> set is `χ₃` (and its conjugate `χ₃²`, which gives the same statistic).** The record's exclusive
> use of `χ₃` on difference-set objects was not an oversight; it is the only choice there is.

**⇒ "Swap the readout to `χ₂` / `χ₆` / sextant" is not a parameter change on this object — it is
a mis-specified axis.** To vary the readout, the index set must stop being symmetric: readouts on
the **points** rather than their differences, or an **oriented** object such as `x(P_i + P_j)`,
where `+` and `−` are genuinely different operations.

## 2. How it was found — the control refused, and the refusal was right

`C-GLV` builds a `β`-closed set (`β³ ≡ 1 mod P`) and asserts the forced value. I asserted
`E₃ = E₆ = 0`. Measured: **`E₃ = 0` exactly, `E₆ = 292`, `E₂ = 15625`.** F-VOID fired and no arm
number was read.

The diagnosis, by exact `Counter` equality on a 90-point `β`-closed set:

| multiset | `β`-closed? | class counts | `E₂, E₃, E₆` |
|---|---|---|---|
| **unordered** differences | **False** | `[691, 642, 692, 644, 693, 643]` | `21609, 0, 12` |
| **ordered** (both signs) | **True** | `[1335]×6` — exactly equal | `0, 0, 0` |

The `x`-multiset **is** `β`-closed, and `β(x_i − x_j) = βx_i − βx_j`, so the *ordered* difference
multiset is `β`-closed and every class is exactly equal. **Unordered pairing breaks the closure**,
because choosing between `d` and `−d` by index order is not a `β`-equivariant choice.

`E₃ = 0` survives the unordered restriction precisely because `χ₃` is even. `E₂` and `E₆` do not.

**The `β` action itself** (independent of parity): `χ₆(β)` has order 3, so a `β`-orbit
`{d, βd, β²d}` hits `μ₆` classes `{j, j+4, j+2}` — the shift is `+4`, computed, not assumed — and
`ζ₆^j(1 + ζ₆⁴ + ζ₆²) = 0`. So on the **ordered** multiset all three statistics vanish; the `E₆`
and `E₂` non-zeros in the measured row are entirely the unordered artifact.

## 3. Why this is the fourth instance, not the first

`btc_puzzle_INDEX.md` (2026-07-30, 5th) records the standing rule and three prior instances:

> *"★ STANDING RULE: check a probe's parity against the oddness of `u` BEFORE running it — even ⇒
> forced zero ⇒ zero information. Has now silently mis-specified three probes."*

Those three were **even index maps against an odd readout**. This is the **mirror image** — an
**odd readout against a symmetric index set** — and the rule as written does not cover it. Proposed
generalization:

> **Compute the parity of the readout AND of the index set. If their product is odd, the statistic
> is identically zero (symmetrized) or ill-posed (unordered). Either way it carries no information,
> and no amount of sample fixes it.**

The prior three were caught after running. This one was caught by a control **before any arm was
read**, which is the only reason it did not become a reported null. `PREREG_interval_cubic_
structure_v1.md` §4's F-VOID clause is what stopped it.

## 4. Effect on the record

- **No published result is corrected.** Every difference-set result on file uses `χ₃`, which is the
  parity-legal readout. `RESULT_diffset_cubic_*`, `RESULT_mu3_diffset_control_repair_v1`,
  `CORRECTION_v32_mu3_diffset_controls_v2` are unaffected.
- **`RESULT_interval_cubic_structure_v1.md` is unaffected** — it used `χ₃` only.
- **What is corrected is a proposed next step** (2026-07-31): "swap the readout to `χ₂`, `χ₆`,
  sextant" on the interval difference-set object. That axis is void as stated and is withdrawn;
  the `M`-scaling and group-law-difference axes are unaffected and proceed.
- **`CORRECTION_v32_mu3_diffset_controls_v2.md` §2's forcing result is confirmed by an independent
  code path** (`E₃ = 0` exactly), and **refined**: the forcing is exact on the *ordered* difference
  multiset for all of `χ₂, χ₃, χ₆`, and survives unordered restriction only for `χ₃`.
