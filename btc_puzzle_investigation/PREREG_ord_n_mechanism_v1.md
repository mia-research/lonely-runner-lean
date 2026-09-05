# PREREG — mechanism of the `(p/n)` small-`p` excess, and its scaling law

**Date:** 2026-07-24 · **Frozen BEFORE the run.** Follow-on to `PREREG_ord_n_structure_v1.md`.
Exact integers only. Object = the `j=0` family `p ≡ 1 mod 3`, `p = a²+3b²`, twist orders
`n = p+1−t`, `t ∈ {±(a+3b), ±(a−3b)}`, `n` prime, `n ≡ 1 mod 3`.

## 0. What is already measured (not re-litigated here)

`(p/n) = +1` rate in the cell `n ≡ 1 mod 8`, prime `n`, matched control clean at every scale:

| bits | 16 | 20 | 24 | 28 | 32 | 64 | 128 | 256 |
|---|---|---|---|---|---|---|---|---|
| excess | `+.0957` | `+.0893` | `+.0297` | `+.0090` | `+.0065` | `+.0017` | `+.0337` | `+.0029` |
| z | `+10.48` | `+9.79` | `+3.25` | `+0.80` | `+0.58` | `+0.12` | `+1.91` | `+0.15` |

## 1. The mechanism being tested (stated before the run)

`n = p+1−t`. **Two branches:**
- **SMALL branch** (`t ≥ 2`): `n < p`, so `p mod n = t−1 =: u`, and `0 < u ≤ 2√p` — a **small** number.
- **LARGE branch** (`t ≤ 0`): `n > p`, so `p mod n = p`, a generic residue.

The cell is `n ≡ 1 mod 8` **and** the family filter is `n ≡ 1 mod 3`, hence **`n ≡ 1 mod 24`**.
Write `u = s²·m` with `m` squarefree. Then `(u/n) = (m/n)`, and for `n ≡ 1 mod 24`:

- `(2/n) = +1` (since `n ≡ 1 mod 8`); `(3/n) = (n/3) = +1` (since `n ≡ 1 mod 4`, `n ≡ 1 mod 3`).
- So **`m | 6 ⇒ (u/n) = +1` is FORCED**; any `m` with a prime factor `≥ 5` leaves `n mod q` free ⇒ `1/2`.

**H-mech:** the entire excess is the forced sub-population of the SMALL branch, i.e.

> **(i)** LARGE branch rate `= 0.500`.
> **(ii)** SMALL branch, `sf(u) | 6` ⇒ rate **exactly `1.000`** (not "high" — exactly, all instances).
> **(iii)** SMALL branch, `sf(u) ∤ 6` ⇒ rate `= 0.500`.
> **(iv)** therefore `excess = ½ · P[ SMALL ∧ sf(u) | 6 ]`, with **no free parameter**.

## 2. Falsification (pre-committed)

- H-mech is **FALSE** if any `sf(u) | 6` instance has `(p/n) = −1` (a single counterexample kills it), or
  if cells (i)/(iii) deviate from `0.5` beyond the control's own scatter.
- H-mech is **INCOMPLETE** if (i)–(iii) hold but the **predicted** excess (iv) does not reproduce the
  observed excess at every bit size — that would mean a second mechanism carries the remainder.

## 3. The scaling claim, and why it is analytic rather than extrapolated

`#{u ≤ U : sf(u) | 6} = Σ_{m|6} √(U/m) ≈ 2.69√U`, and `u` ranges over `~2√p`, so
`P[sf(u)|6] ≍ 2.69/√(2√p) ∝ p^{−1/4}` ⇒ **`excess ∝ p^{−1/4}`, decaying, with an explicit constant.**

**Pre-committed scaling test:** compare predicted (iv) against observed excess at every bit size in
§0. If they agree, the decay is a *theorem about the parametrization*, not a fitted curve, and the
`256`-bit null is **derived**, not merely measured — which is the one thing that answers global caveat
**#5** (the `~239 binary orders of magnitude` banner) for this question.

## 4. Scope, stated before the result

Whatever the outcome: this is a statement about `p mod n` where `p`, `n`, `t` are **public**. It has
**no leakage/ECDLP content** and no `d`-side content. It is a structure map, and if H-mech confirms,
the honest output is that the ledger's `c_p = 6` item is **explained away**, not opened.
