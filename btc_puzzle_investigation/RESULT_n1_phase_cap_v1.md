# RESULT — N1 explained as a symmetry type: the `½` is the phase-pairing cap `2√p`

*2026-07-24. Script: `n1_phase_cap_sweep_v1.py` (pre-committed readings R1/R2/R3 frozen in its
docstring before the sweep). Predecessor: `RESULT_xdomain_ports_v2.md` §1, which established the
weight and the pairing at `p = 13, 43` and named this as the open question.*

**No leakage, key-recovery or ECDLP claim. `p = 2²⁵⁶−2³²−977` is not enumerable; nothing here
transfers to it — the scale banner (§XI.5) governs every row.**

---

## 1. The result

`V(a) = Σ_{P} χ₂(y_P) e_n(a·d_P)`, `S(p) := max_{a≠0} |V(a)| / √p`.

> **`[EMPIRICAL — 193 primes, 402,718 distinct μ₆ configurations]`
> `S_y(p) ≤ 2` with ZERO violations, and `S_y(p) → 2`.**

| `p` range | primes | mean `S_y` | max | min |
|---|---|---|---|---|
| 1 000 – 3 000 | 14 | 1.97911 | 1.99979 | 1.95158 |
| 3 000 – 10 000 | 57 | 1.98563 | 1.99937 | 1.94173 |
| 10 000 – 30 000 | 103 | **1.99189** | 1.99975 | 1.97542 |

The deficit decays: `mean(2 − S_y) = 0.01034` for `p > 3000`, with `log(2−S_y)` regressing on
`log p` at slope **`−0.448`** — i.e. `S_y = 2 − O(p^{−1/2})`.

**Pre-committed outcome R2 fires** (`S ≤ 2` everywhere **and** `S → 2`): the `½` **is** the
phase-pairing constraint, the true cap is `2√p`, and it is attained asymptotically. R1 (any
violation ⇒ the cap is false) had a falsifying instance available at every one of 193 primes and
did not fire once.

## 2. Why this explains N1

Chain, with each link's grade:

1. **All four twisted eigenvalues have modulus exactly `√p`** `[VERIFIED p=13,43]` — so N1 is **not**
   eigenvalue starvation, and `MASTER_v4:189`'s "effectively only 2 of 4 carry weight-1 mass" is
   refuted read literally as a weight claim.
2. **The multiset is closed under `α ↦ −ᾱ`** `[DERIVED — FORCED]`: `χ₂^{(k)}(−1) = (−1)^{(p^k−1)/2}`
   alternates with `k` at `p ≡ 3 mod 4`, so `p_k = (−1)^k \overline{p_k}`. Confirmed here as a forced
   readout check at all 193 primes: `V` is purely imaginary at `p ≡ 3 mod 4` and real at
   `p ≡ 1 mod 4`, worst deviation **`9.5×10⁻¹⁶`**.
3. **Hence four complex unit vectors collapse to two real parameters** `[DERIVED]`:
   `|V(a)| = 2√p·|sin θ₁ + sin θ₂|` (`p ≡ 3 mod 4`), `2√p·|cos θ₁ + cos θ₂|` (`p ≡ 1 mod 4`).
4. **And those two parameters obey `|sin θ₁ + sin θ₂| ≤ 1`** `[EMPIRICAL — this run]`.

> **So `χ₂(y)` saturates `½` of its `4√p` ceiling because its actual cap is `2√p`. The record's
> "2 of 4" intuition is right in form and wrong in mechanism: not two eigenvalues starved, but four
> phases locked into two antipodal-conjugate pairs.** N1 is a **symmetry type**, which is exactly the
> branch `NEXT_DIRECTIONS_v1.md §3 #1` pre-committed as "N1 is explained".

This also closes the loop with `RESULT_N1_reframed_2sqrtp_cap_v1.md`, which observed that `χ₂(y)`
and `χ₂(x)` "both land in `[3.66, 3.98]` — the same absolute magnitude `≈2√p`" at 6 primes. That
observation is now carried out to 193 primes **and given its mechanism.**

## 3. The discriminating comparison — `χ₂(x)` is NOT capped at `2√p`

Same estimator, same primes, same code path:

| readout | `> 2` at how many of 193 primes | max excess |
|---|---|---|
| **`χ₂(y)`** (dim 4, ceiling `4√p`) | **0** | — |
| `χ₂(x)` (dim 2, ceiling `2√p`) | **51 (26%)** | +0.0203 |
| random unit-modulus target | routinely | mean `S` 3.22 at `p>10⁴` |

`χ₂(x)`'s excursions are consistent with a `2√p + 1` bound (allowance `1/√p`), and `χ₂(x)` has no
`−ᾱ` pairing available — `x_{−d} = x_d` makes it **even** in `d`, a different structure. **The point
is that the same statistic on a sibling readout crosses 2 routinely while `χ₂(y)` never does**, so
the cap is not an artifact of the estimator, of the max-over-configurations, or of the `+1` term.

## 4. What is NOT established

- ⚠ **`|sin θ₁ + sin θ₂| ≤ 1` is EMPIRICAL, not proved.** It is not automatic — two unit sines can
  sum to 2. **Deriving it is now the sharp open question**, and it is well posed: what constrains the
  two surviving phase parameters of a weight-1, `−ᾱ`-paired Weil quadruple? The natural attack is the
  integrality of the twisted `L`-polynomial's coefficients in `ℤ[ζ_n]`.
- The eigenvalue facts (§2.1–2.2) rest on `p = 13, 43` — **six unforced cells**. This sweep extends
  the *consequence* (§2.4) to 193 primes, not the eigenvalue computation itself.
- Nothing about `p ≈ 2²⁵⁶`. `S_y → 2` is measured on `p ≤ 30 000`.
- **No security or extraction consequence is claimed.** A tight cap on `|V|` is a statement that the
  readout is *less* concentrated than its dimension permits.

## 5. ⚠ A bug in this script's own first run, caught before any reading

The first pass had **no Hasse guard**. `curve_orbit` returns `ord(G)`, **not** `#E`; when the first
point `G` lands in a small prime-order subgroup, `ord(G)` is prime and the primality filter accepts
it. That admitted rows like `p=1951 → n=5`, `p=11833 → n=61`, `p=2113 → n=163` — impossible for `#E`
by Hasse, and a **different object entirely** (a small subgroup, not the curve group).

Effect: those rows have small `S` and **dragged every mean down** — the pre-fix means were
`1.5556 / 1.6477 / 1.5506` by `p`-range, which would have read as "`S` plateaus well below 2",
i.e. **outcome R3 instead of R2.** Fixed by requiring `|n − (p+1)| ≤ 2√p`, which forces `n = #E` and
`G` a generator; 193 valid primes remain. **No reading was taken before the fix.**

This is the same class as the four instrument bugs already on this record (the off-by-one group
order, the cube-root exponent, the power-residue index, the unconditional print) and the fifth this
session. The tell was an arithmetic impossibility in a printed column, not a re-read.

## 6. Status

- **Frontier §XI.10 / N1** moves from *"the one measured anomaly with no account"* to a named
  symmetry type with one empirical inequality left to prove.
- **Open, and now sharp:** prove `|sin θ₁ + sin θ₂| ≤ 1`.
- Unchanged: the eigenvalue computation's own scope (2 primes), and the scale banner.
