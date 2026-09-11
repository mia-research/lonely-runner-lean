# The prime bound fails — and the reason names the real obstruction

2026-09-11. Scripts `experiments/n8/ok_prime_bound_v1.py`, `ok_crowding_v1.py`. Exact
arithmetic. Answers the two items left open at `DENOMINATOR_TOWER_v1.md` §6.

---

## 1. All three prime hypotheses fail  `[PROVED — counterexample]`

`q(E)` = smallest prime dividing no `e_j`; `p₂` = the second such prime.

| | H1 `dmin ≤ q` | H2 `dmin ≤ 2q` | H3 `dmin ≤ p₂` |
|---|---|---|---|
| complete Case-2 residual `[1..18]`, 6250 | **fails** (+12) | **fails** (2.09×) | **fails** (+8) |
| `lcm(1..D)` adversaries, `D = 6..39` | **fails** (+18) | **fails** (2.64×) | **fails** (+16) |
| smooth adversaries (maximise `q`) | **fails** (+12) | holds (2.00×) | **fails** (+5) |
| random residual `[1..3000]`, 4000 | **fails** (+12) | **fails** (2.09×) | **fails** (+9) |

Worst witness: `E = (1,2,3,4,5,7,840)`, `dmin = 29`, `q = 11`, `p₂ = 13`.

## 2. Why no prime statistic can work  `[PROVED]`

Let `ρ(d)` be the per-runner safe fraction at modulus `d`:
`ρ(d) = |{r ∈ ℤ/d : ‖r/d‖ ≥ 1/8}|/d = (d − 2⌈d/8⌉ + 1)/d`. Then

> **`ρ(d) = 3/4 + 1/d` exactly when `8 | d`, and `ρ(d) < 3/4 + 1/d` otherwise.**
> `max_{d ≥ 8} ρ(d) = 7/8`, attained only at `d = 8`, and `ρ ↓ 3/4`.

Verified for all `8 | d < 2000` and by direct maximisation over `d < 2000`. So **a larger
modulus is strictly worse per runner**; the only gain from large `d` is that `φ(d)` grows,
against `ρ^7` decaying to `(3/4)^7`. Primes are not privileged — they are *penalised*
(`ρ(11) = 8/11 = 0.727`, `ρ(17) = 12/17 = 0.706`, against `ρ(16) = 13/16 = 0.813`). The right
moduli are **small multiples of 8**, which is why a statistic built from primes cannot bound
`dmin`, and the null of §1 is structural rather than a matter of the constant.

## 3. What the case split actually is  `[PROVED — 0 disagreements over 31 788]`

Apply the `gcd` bound of `DENOMINATOR_TOWER_v1` §1 at `d = 2^k`: a runner is automatically
safe iff `2 ≤ 2^k/gcd(e,2^k) ≤ 8`, i.e.

> **`v₂(e) ∈ [k−3, k−1]`** — a window of width `3 = log₂ 8`.

All seven fit some window iff `max_j v₂(e_j) − min_j v₂(e_j) ≤ 2`, and `gcd(E) = 1` forces
`min v₂ = 0`. Hence

> **Case 1 ⟺ the 2-adic valuations fit inside the window; Case 2 ⟺ they span more than it.**

Checked against "some speed is a multiple of 8" over all 31 788 primitive 7-tuples in
`[1..18]`: **0 disagreements**. The n=8 case split is not a convention — it is the 2-adic
span measured against `log₂ 8`, and §2 says no choice of `d` repairs it.

## 4. The crowding duality, transported  `[PROVED — exact]`

GECT audit C15 confirms `ℓ_i c_i = 0` identically, `L` peaking at isolation and `C` at
non-coprime times, with conservation failing pointwise and `S = L + C` reframed as an order
parameter. Transporting the one-sided form —
`c_j(t) = max(0, 1 − 8‖e_j t‖)`, `ℓ_j(t) = max(0, 8‖e_j t‖ − 1)` — gives:

- **`ℓ_j c_j = 0` identically.** Verified, 11 800 exact draws, 0 violations.
- **`∫₀¹ c_j = 1/8` and `∫₀¹(ℓ_j + c_j) = 5/4`, for every speed.** Exact, checked at
  `e = 1,2,3,5,7,8,12,13,14`. So `∫C = 7/8` and `∫S = 35/4` are **speed-free invariants** —
  the conservation transports here as an exact integral identity.
- `LRC(8)` for `E` ⟺ `∃t : C(t) = 0`.

**Where it lands, stated plainly.** `∫C = 7/8 < 1` does not bound `|{C > 0}|`, because `c` is
a tent and not an indicator: the same first moment read through indicators is
`Σ|B_j| = 7/4 > 1`. Measured exactly:

| `E` | `∫C` | `\|{C > 0}\|` |
|---|---|---|
| `T₁ = (1,…,7)` | `7/8` | `1` |
| `T₃ = (1,4,5,6,7,11,13)` | `7/8` | `1` |
| `E* = (2,6,7,8,10,13,14)` | `7/8` | `14467/14560` |

So the crowding conservation **is** the first moment, which `WHERE_THE_PROOF_IS_v2` §3 already
records as the common cause of every dead route ("soft analytic methods have 6.8% of room and
need 95%"). It is an exact and correct transport that lands on a documented wall. Its value
here is diagnostic, not probative — as the audit itself says, `S` is a tolerance-free
*detector*.

**Independent cross-check.** The computation gives `|G(E*)| = 93/14560`, hence
`∫X = 8|G| = 93/1820` — reproducing the project's recorded Case-2 target exactly, by a route
(crowding integral over exact breakpoint cells) that does not use the `X` reformulation.

## 5. My own error in this file's first run  `[recorded]`

The first pass reported `ℓ_j c_j = 0` as **False**. That was a bug — `ℓ` and `c` were
evaluated at two independently drawn times. At a common `t` the identity is exact, as §4
records. No claim was published from the faulty line.

## 6. Ledger

`[PROVED — counterexample]` §1, all three prime hypotheses, witnesses exhibited.
`[PROVED]` §2 the `ρ(d) = 3/4 + 1/d` identity for `8 | d` and `max ρ = 7/8` at `d = 8`;
§3 the 2-adic window and the case-split equivalence (0 disagreements, complete enumeration).
`[PROVED — exact]` §4 the transported invariants `∫c_j = 1/8`, `∫(ℓ_j+c_j) = 5/4`,
`ℓ_j c_j = 0`, and the three measured `|{C>0}|` values.
`[recorded]` §5.

`n = 8` is **not proved**, and nothing here moves a grade.
