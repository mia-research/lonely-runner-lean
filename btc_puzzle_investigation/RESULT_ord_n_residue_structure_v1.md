# The `ord_n(p)` / `ord_n(2)` item: an exact forced-sign law, its `p^{−1/4}` density, and two dissolutions

**Date:** 2026-07-24 · Pre-registered: `PREREG_ord_n_structure_v1.md`, `PREREG_ord_n_mechanism_v1.md`
(both frozen before their runs). Scripts: `scratchpad/ord_n_structure_v1.py`, `ord_n_family_v1.py`,
`ord_n_family_v2.py`, `ord_n_quad_oos_v1.py`, `ord_n_secp_scale_v1.py`, `ord_n_mechanism_v{1,2}.py`.
Exact integers throughout; no float in any signal path. **Controls fire in every table reported here.**

Target = the ledger item (`OPEN_ITEMS_LEDGER_v1.md §A`): *`ord_n(p) = (n−1)/6` and `ord_n(2) = (n−1)/64`,
`[VERIFIED]` and never explained.*

---

## 0. What is new here (positive first)

Two objects were built that did not exist in the record, both **proved**, plus a derivation that the
record had been using without stating:

| object | grade |
|---|---|
| **(L1) Forced-sign law.** For a `j=0` curve `/F_p` with prime order `n ≡ 1 mod 8`: `(p/n) = +1` is **forced** whenever the squarefree part of `\|t−1\|` divides 6. | **`[PROVED]`** + `1546/1546`, 0 violations |
| **(L2) Density law.** The forced population has density `≍ 2.69/√(2√p) ∝ p^{−1/4}`. | **`[PROVED asymptotic]`** + `[VERIFIED 20–48 bits]` |
| **(L3)** `3 ∣ n−1` is **forced** for every prime-order `j=0` curve — hence the cubic character mod `n` is always nontrivial. | **`[PROVED]`** + `4977/4977` |

## 1. `ord_n(2) = (n−1)/64` — DISSOLVED as a selection effect

`ν₂(n−1) = 6` exactly. So "the cofactor's 2-part is the full 2-part of `n−1`" **is** just "2 has odd
order" — a 1-in-64 event, not a 6-bit coincidence needing explanation. Control (frozen in the prereg,
all primes `q < 1000`, 168 bases):

```
#(64 | c_q) = 5   (expected 168/64 = 2.62)   bases: [2, 79, 137, 199, 367]
```

**2 is not distinguished** — four other small primes do the same thing, at the rate chance predicts.
The prereg's pre-committed reading for this outcome was *"selection effect, a dissolution."* Recorded
as such. (`c_q = 1`, i.e. primitive root, for 47 of the 168 — the distribution is unremarkable
throughout.)

## 2. `ord_n(p) = (n−1)/6` — the "6" is structural; `p`'s membership in it is not

**H-sextic** (prereg §3: CM forces `p` into the index-6 subgroup via Eisenstein reciprocity) is
**FALSIFIED**. Over 6790 family instances (`p < 3·10⁵`, `n` prime):

```
p is a cube  mod n : 2274/6790 = 0.3349   z = +0.27      CONTROL cube  : 0.3325
p is a 6th power   : 1188/6790 = 0.1750   z = +1.83      CONTROL square: 0.4890
```

Cube residuacity of `p` mod `n` is **flat at chance**, so CM does not force the factor 3.

What *is* forced is **(L3)**: writing `p = a²+3b²` (always solvable for `p ≡ 1 mod 3`), the odd-order
twists have `t = ±(a±3b)`, so `n ≡ 2−a (mod 3)`; since `3 ∤ a`, the case `a ≡ 2` gives `3 ∣ n` and
cannot be prime. Hence **prime order ⇒ `n ≡ 1 mod 3`** — verified `4977/4977`. This is the standard
reason GLV applies to secp, here derived rather than assumed. Both the quadratic and cubic characters
mod `n` are therefore always nontrivial: the "6" is *available* by structure. **Which** subgroup `p`
lands in is a free `1/6` draw.

## 3. The one real signal — and it is a finite-size effect (L1, L2)

The quadratic half was **not** flat: conditioned on `n ≡ 1 mod 8`, `(p/n)=+1` ran at `0.6073`
(`z = +8.64`) for `p < 3·10⁵`, replicating out-of-sample on disjoint `p ∈ [3·10⁵, 9·10⁵]` at `0.5660`
(`z = +6.69`) — control clean at `0.494`/`0.504`. It is fully explained:

**(L1), derived before the confirming run.** `n = p+1−t ⇒ p ≡ t−1 (mod n)` **always**. The family
filter gives `n ≡ 1 mod 3` (L3) and the cell gives `n ≡ 1 mod 8`, so **`n ≡ 1 mod 24`**, whence
`(−1/n) = +1` and `(p/n) = (\|t−1\|/n)`. Writing `\|t−1\| = s²m` with `m` squarefree, `(2/n) = +1`
(as `n ≡ 1 mod 8`) and `(3/n) = (n/3) = +1` (as `n ≡ 1 mod 4`, `n ≡ 1 mod 3`), so

> **`m ∣ 6 ⇒ (p/n) = +1`, forced.**

Measured, cell `n ≡ 1 mod 8`, `n` prime, 16→48 bits:

| bits | 16 | 20 | 24 | 28 | 32 | 40 | 48 |
|---|---|---|---|---|---|---|---|
| **forced cell rate** | `1.0000` | `1.0000` | `1.0000` | `1.0000` | `1.0000` | `1.0000` | `1.0000` |
| free cell rate | `.4924` | `.5151` | `.4875` | `.5148` | `.4703` | `.4796` | `.5046` |
| control | `.4970` | `.5072` | `.4850` | `.5024` | `.5030` | `.5227` | `.4875` |

**0 violations in 1546 forced instances.** The free cell sits at `0.5` within the control's own scatter.
Predicted excess `½·P[sf(\|t−1\|) ∣ 6]` vs observed: `+.0892/+.0830`, `+.0649/+.0780`, `+.0343/+.0227`
at 16/20/24 bits — agreement within the observed excess's own `sd ≈ 0.008`, **no free parameter**.

**(L2), and this is the part that answers caveat #5.** `#{u ≤ U : sf(u) ∣ 6} = Σ_{m∣6}√(U/m) ≈ 2.69√U`,
and `\|t−1\| ≤ 2√p+1`, so the forced density `∝ p^{−1/4}` — a **halving per 4 bits**. Measured forced
fraction: `17.9%, 13.0%, 6.9%, 2.8%, 1.55%, 0.33%, 0.083%, 0` at 16/20/24/28/32/40/48/64 bits; ratios
per 4 bits from 20 bits up are `0.53, 0.41, 0.55` and per 8 bits `0.21, 0.25` against a predicted
`0.50`/`0.25`. (The 16-bit point saturates, as expected where the density's error term is not small.)

## 4. secp itself

`t = p+1−n = 432420386565659656852420866390673177327`; `\|t−1\|` is **129 bits**, and none of
`\|t−1\|/m` for `m ∈ {1,2,3,6}` is a perfect square ⇒ **secp is not in the forced population**.
`n ≡ 1 mod 24` and `(p/n) = +1` both hold, but at `p ≈ 2²⁵⁶` the forced density is `≈ 10^{−19}`, so
`(p/n) = +1` at secp is a free draw. Likewise `\|t−1\|` is not a perfect cube.

Direct measurement at secp's own bit size (prime `n`, matched control, cell `n ≡ 1 mod 8`):

```
 bits      N     rate      ctl   z(rate)   z(ctl)
   16   3000   0.5957   0.5110    +10.48    +1.20
  ...
  128    800   0.5337   0.5050     +1.91    +0.28
  192    700   0.5286   0.5029     +1.51    +0.15
  256    700   0.5029   0.4886     +0.15    -0.60
```

**Net on the ledger item: `c_p = 6` at secp is a `1/6` draw** — `[VERIFIED]`, and **scoped**: this says
the two mechanisms examined (small-residue quadratic forcing; the cubic character) do not force it. It
is not a claim that no mechanism does.

## 5. Sampler integrity (a scare that was resolved, recorded so it is not re-run)

Mid-run I suspected the `4p = L²+27M²` parametrization had silently restricted the family to primes
where 2 is a cubic residue. **It had not.** `4p = L²+27M²` is *always* solvable for `p ≡ 1 mod 3`:
of the three representations `4p = t²+3v²`, the values `v ∈ {2b, a−b, a+b}` satisfy `b mod 3 ∈ {0,a,−a}`
with `3 ∤ a`, so **exactly one** has `3 ∣ v`. (The classical cubic-residue criterion is about
`p = L²+27M²`, not `4p`.) An independent Cornacchia sampler on `p = a²+3b²` reproduced the family
**instance for instance** — 6790 both times, identical counts — which is the check that settled it.

## 6. What stays open (this drill does not close a frontier)

- **A cubic analogue of (L1).** (L1) works because `(2/n)`, `(3/n)` are fixed by `n mod 24`. The cubic
  character `χ₃(2)`, `χ₃(3)` mod `n` is **not** fixed by `n` mod anything — it needs the ℤ[ω]
  representation of `n` (cubic reciprocity). Whether a corresponding forced population exists is
  **untested**; the bound from §2 is only that any such effect is below `z = +0.27` at `p < 3·10⁵`.
- **The free cell is bounded at `0.5`, not proved `0.5`** — resolution here is `≈ ±0.015` at 16–28 bits
  and `≈ ±0.04` at 256 bits (`N = 700`).
- **`ord_n(2)`'s dissolution is about `2`, not about `n`.** The cofactor distribution over `q < 1000`
  was not tested for structure beyond the two counts the prereg froze.
