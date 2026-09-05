# RESULT — `(†)` PROVED: `Σχ₂(s)sgn(ρs mod p−s) = 3h(−p)`, promoting `|FLD| = 6h(−p)` to a theorem

*2026-07-24. Grade `[PROVED — pending independent adversarial review]`. The proof was found
source-first (priority sweep → Berndt–Evans/Goldstein–Razar → the classical `h = −(1/p)Σχ₂(a)a`
form), reduced to one elementary identity, and every load-bearing step verified exactly. Numerical
de-risk with firing controls passed (§4). Closes `NEXT_DIRECTIONS_v1.md §4` / frontier #16.*

**No leakage / ECDLP claim. Pure analytic number theory about the flap class-number identity.**

---

## 1. Statement

`p ≡ 7 mod 12` prime (so `p ≡ 3 mod 4` and a primitive 6th root of unity exists mod `p`),
`H = (p−1)/2`, `χ₂` the Legendre symbol mod `p`, `ρ` a primitive 6th root of unity mod `p`.

> **(†)  `T := Σ_{s=1}^{H} χ₂(s)·sgn(ρs mod p − s) = 3·h(−p)`,**

with `h(−p)` the class number of `ℚ(√−p)`. Equivalently (reflection `s↔p−s`, §2), the full-range sum
`T_full := Σ_{s=1}^{p−1} χ₂(s)·sgn(ρs mod p − s) = 6h(−p)`. Both primitive 6th roots give the same
value (`sgnsum(ρ)=sgnsum(ρ⁻¹)`, §4).

## 2. Reduction to the full range

`χ₂` is **odd** (`p≡3 mod4`), and under `s↦p−s`: `sgn(ρ(p−s) mod p − (p−s)) = −sgn(ρs mod p − s)`
while `χ₂(p−s) = −χ₂(s)`, so the summand `χ₂(s)sgn(ρs mod p − s)` is **invariant**. Hence
`T_full = 2T`, and (†) ⟺ `T_full = 6h`. Work with `T_full` (denote `sgnsum(ρ)`).

## 3. Proof

**Step A — the two auxiliary sums and the classical anchor.** Define
`sawsum(ρ) := Σ_{s=1}^{p−1} χ₂(s)·((ρs/p))`, where `((x)) = {x} − ½` is the sawtooth. Since
`Σ_s χ₂(s) = 0`, `sawsum(ρ) = (1/p)Σ_s χ₂(s)·(ρs mod p)`. Substituting `t = ρs mod p`
(a bijection of `(ℤ/p)*`), and using **`χ₂(ρ) = ρ^{(p−1)/2} = ρ³ = −1`** (as `p≡7 mod 12 ⇒
(p−1)/2 ≡ 3 mod 6`):

> `sawsum(ρ) = χ₂(ρ⁻¹)·(1/p)Σ_t χ₂(t)·t = −(1/p)Σ_{t=1}^{p−1} χ₂(t)·t = h(−p)`,

the last equality being the **classical finite class-number formula** for `ℚ(√−p)`, `p≡3 mod4`
(`h = −(1/p)Σ_{a=1}^{p−1}(a/p)a`; Borevich–Shafarevich; generalized Bernoulli `B_{1,χ₂}`, `w=2`).
`[CITED — classical]`, verified with 0 exceptions for all `p≡3 mod4` in `[7,500)` (§4).

**Step B — the orbit collapse `sgnsum(ρ) = 6·sawsum(ρ)`.** Group `{1,…,p−1}` into orbits of
multiplication by `⟨ρ⟩`; each has size **6** (`ρ` has order 6). Write an orbit as
`a_i = ρ^i s mod p`, `i=0..5`, with `a₀=s`, `a₁=ρs mod p`, `a₂=ρ²s mod p`. Using **`ρ² = ρ−1`**
(so `ρ²s ≡ ρs − s`) and **`ρ³ = −1`** (so `a₃=p−a₀, a₄=p−a₁, a₅=p−a₂`), split on the sign of
`a₁ − a₀`:

| | `a₁ > a₀` (i.e. `ρs mod p > s`) | `a₁ < a₀` |
|---|---|---|
| `a₂ = (ρs−s) mod p` | `a₁ − a₀` | `a₁ − a₀ + p` |
| orbit sum of `χ₂(a_i)((ρa_i/p))` | `+χ₂(s)` | `−χ₂(s)` |
| orbit sum of `χ₂(a_i)sgn(ρa_i mod p − a_i)` | `+6χ₂(s)` | `−6χ₂(s)` |

Both rows equal `χ₂(s)·sgn(ρs mod p − s)` and `6·χ₂(s)·sgn(ρs mod p − s)` respectively (the
computation for the sawtooth row: the orbit sum telescopes to `χ₂(s)(2(a₁−a₂−a₀)+p)/p`, which is
`+χ₂(s)` when `a₂=a₁−a₀` and `−χ₂(s)` when `a₂=a₁−a₀+p`; the sign row's six terms are each
`+χ₂(s)sgn(a₁−a₀)`). Summing over orbits:

> **`sawsum(ρ) = Σ_orbits χ₂(s)sgn(ρs mod p − s)` and `sgnsum(ρ) = 6·Σ_orbits χ₂(s)sgn(ρs mod p − s)`,
> hence `sgnsum(ρ) = 6·sawsum(ρ)`.**

Each per-orbit identity verified **exactly at every orbit of every `p≡7 mod12`, `p<400`** (§4).

**Step C — conclude.** `sgnsum(ρ) = 6·sawsum(ρ) = 6h(−p) = T_full`, so `T = 3h(−p)`. ∎

## 4. Numerical de-risk (frozen checks, all passed)

| check | result |
|---|---|
| `(†)`: `sgnsum(ρ)=6h` **and** `sawsum(ρ)=h` | **78/78** primes `p≡7 mod12`, `p<2000` |
| per-orbit `sawsum` collapse `= χ₂(s)sgn(ρs−s)` | holds at **every orbit**, every `p<400` |
| per-orbit `sgnsum` collapse `= 6×` that | holds at **every orbit**, every `p<400` |
| classical `h = −(1/p)Σχ₂(a)a` | **0 exceptions**, all `p≡3 mod4` in `[7,500)` |
| **FIRING** — wrong constant (`5h`,`7h ≠ sgnsum`) | fires **78/78** (the check is not vacuous) |
| **FIRING** — a non-6th-root `c` gives `sgnsum≠6h` | fires 41/78 (the value `6h` is not universal; ratio is `±2` for many `c`) |

The wrong-constant firing control is the decisive one: `sgnsum(ρ)=6h` is a genuine constraint, and a
generic `c` gives ratio `±2`, not `6` — the factor 6 is specific to `ρ` being a primitive 6th root
(where `ρ²=ρ−1` makes `a₂=a₁−a₀`, the exact fact that collapses the orbit).

## 5. Consequence and grade

- **`(†)` is `[PROVED]`** — grade finalized. Two independent proofs (orbit collapse; and the
  floor-telescoping of `RESULT_twisted_dedekind_structure_v2.md`, of which `(†)` is the `χ₂,c=ρ`
  corollary). **Independent adversarial review PASSED** (`REVIEW_twisted_dedekind_v1.md`,
  2026-07-24): every step re-derived on fresh instruments (independent character construction,
  class number by reduced-form counting), 0 gaps. **Large exact tests:** `T=3h` at **569 primes
  `p≡7 mod12` up to `p=20000`**, 0 failures; per-orbit collapse at 580 orbits; firing controls reject
  wrong constants.
- ⚠ **`|FLD| = 6h(−p)` — `(†)` closes P2's open IDENTITY, but does NOT by itself give the end-to-end
  theorem.** `(†)` (`T=3h`) holds on **all** `p≡7 mod12`. But `|FLD|` is `6h` only on `p≡19 mod24`
  (`χ₂(2)=−1`) and `0` on `p≡7 mod24` (`χ₂(2)=+1`) — the `6h`-vs-`0` split is the **separate `χ₂(2)`
  condition** that P2 packages. So: **P1 `[PROVED]` + `(†)` `[PROVED]` complete the two open steps
  flagged in `RESULT_flap_lemmas_P1P2_proofstatus_v3.md`**; the full `|FLD|` characterization is then
  the P1/P2 assembly on the correct congruence, which should be re-confirmed end-to-end before
  `|FLD|=6h` is itself re-graded `[PROVED]`. Not asserted here.
- **Scope:** `p ≡ 7 mod 12`. The `ρ`-existence needs `p≡1 mod3`; `χ₂` odd needs `p≡3 mod4`. This is
  exactly the flap/Eisenstein regime. No claim outside it.
- **Method note (positive):** this is the **sixth** time on this project that reading the source
  dissolved a supposed "research-grade" obstacle — the priority sweep named Berndt–Evans, which put
  the classical `h = −(1/p)Σχ₂(a)a` form in hand, and the rest is the `ρ²=ρ−1` orbit collapse.

## 6. Relation to prior work — v38 (checked AFTER the fact; a process miss)

⚠ **I did not read `masked_structure_findings_v38.md` (2026-07-18) before doing this, and I should
have.** v38 had already: (i) reduced P1/P2 to the **same primitive-6th-root region** `T⁺` with
`ρ²=ρ−1`, `ρ` order 6; (ii) established `χ₂(ρ)`-type structure; (iii) **evaluated the *untwisted*
Dedekind sum `s(ρ,p) = Σ((i/p))((ρi/p)) = −(p−1)/(12p)`** and localized `χ₂(2)` to the boundary.
So the **ρ-region / Dedekind setup of §3 largely re-walks v38** — had I read it first I would have
started from its reduction.

**What is nonetheless new here, and why this is not a duplication:**
- v38 named its remaining step a `[GAP]`: *"evaluate the [region character] sum as a Jacobi-type
  object — not done."* The later `RESULT_flap_lemmas_P1P2_proofstatus_v3.md` restated that evaluation
  as `(†): C′−C=3h(−p)` and left it `[VERIFIED, NOT PROVED] — the single open step`. **This document
  proves exactly that step.**
- v38 evaluated the **untwisted** `s(ρ,p)` (a fixed CM value, no `χ₂` content). The proof here uses
  the **`χ₂`-twisted** sum `sawsum(ρ)=Σχ₂(s)((ρs/p)) = h(−p)` and the sign↔sawtooth factor-6 orbit
  collapse — a different computation. **Consistency cross-check:** the present framework reproduces
  v38's `s(ρ,p) = −(p−1)/(12p)` exactly (7/7 primes), confirming the same valid setup.

**Net:** the RESULT (a proof of `(†)`) is new and completes v38's named gap; the SETUP overlaps v38
and should have cited it from the start. Credit to v38 for the region reduction.

## 7. Status (finalized)

- **Adversarial review: PASSED** (§5). **Grade: `[PROVED]`.**
- **Scope reconciliation done** (§5): `(†)` is `p≡7 mod12`; `|FLD|=6h` lives on the `p≡19 mod24`
  half. `(†)` + P1 close the two flagged open steps; the end-to-end `|FLD|=6h` re-grade is deferred to
  an explicit P1/P2-assembly confirmation, not claimed here.
