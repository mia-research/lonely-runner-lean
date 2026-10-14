# The n=8 obstruction, reduced to a floor-state count and an equidistribution step

2026-09-07. Working inside the `lrc_proof_v10_21.md` framework (§5.1 definitions).
Target: the `n = 2^k` branch of Corollary 11.0 — Case 2, Unit-Complete, `k = 3`.
Nothing here verifies LRC(8); its truth is known and is not the question.

## 1. Setting

`n = 8`, `E` = 7 distinct positive integers, `gcd = 1`, `E_div ≠ ∅` (so `8 | L`).
Unit-Complete: the two residue classes of `{1,…,7}` absent from `R_non` are both
non-units, so `R_non` = `{1,3,5,7}` together with exactly one `ρ₀ ∈ {2,4,6}`.
Floor state `t_e(b) = ⌊eb/L⌋`; `bad(e,t,8)` as in §5.1; `b` is safe if the bad sets
of `E_non` do not cover `ℤ/8`.

## 2. The pair rule  `[PROVED]`

Every unit of `ℤ/8` is its own inverse, so for a unit runner `e ≡ ρ (mod 8)`

    bad(e,t,8) = { −tρ, −(t+1)ρ }.

The two elements differ by `ρ`, which is odd, so **one is odd and one is even**. Writing
`o` for the odd one:

> **Pair rule.** A unit runner of residue `ρ` blocks exactly the pair `(o, o + ερ)` with
> `o` odd and `ε = +1` if `t` is even, `ε = −1` if `t` is odd.

**This depends only on `ρ` and on `t mod 8` — not on the actual speed `e = 8q + ρ`.**
That is what removes the representative-speed restriction: the quotient `q` enters only
through the floor value.

For a non-unit runner, `g = gcd(e,8) ∈ {2,4}`, `H₂ = {0,4}`, `H₄ = {0,2,4,6}`, both
inside the even residues; `bad(e,t,8)` is a single coset of `H_g` or empty, hence lies
**entirely within one parity class**.

## 3. The counting is exactly break-even, and that is the whole difficulty  `[PROVED]`

`ℤ/8` has 4 odd and 4 even residues. Unit-Complete supplies exactly `φ(8) = 4` unit
residue classes, each blocking exactly one odd and one even. So the units have **zero
slack in both parities simultaneously**. This is `2φ(n) = n`, which holds for `n = 2^k`
and for no other `n`: for odd prime powers `2φ(p^k)/p^k = 2(1−1/p) ≥ 4/3`. It is the
same break-even that `lrc_proof_v10_21.md:936` needs and does not have, its density
identity `2φ(n)/n = ∏_{p|m}(1−1/p)` being stated for `n = 2^a m` with `m` odd `≥ 3`.

## 4. The obstruction set, counted exactly  `[PROVED — finite enumeration]`

The bad sets depend on the floor vector only through `(t₁,t₃,t₅,t₇,t_{ρ₀}) mod 8`.
Enumerating all `8⁵ = 32768` states:

| | four unit runners alone (`8⁴ = 4096` states) |
|---|---|
| block all of `ℤ/8` | **16** (0.39%) |
| leave a **mixed-parity** gap — unfillable by any single non-unit, since a non-unit blocks one parity | **3344** (81.6%) |

The 16 total-blocking states all have parity signature `(t₁,t₃,t₅,t₇) ≡ (0,1,0,1)` or
`(1,0,1,0)` mod 2 — the units must **alternate** in floor parity. Equivalently, in the
relaxation where the odd blocks `o_ρ` and the signs `ε_ρ` are treated as free, exactly
16 of the 384 configurations cover both parities bijectively, and all 16 have
`ε₁ = ε₅ = −ε₃ = −ε₇`.

Adding the single non-unit runner, the full-obstruction set is

| `ρ₀` | 2 | 4 | 6 |
|---|---|---|---|
| obstructing states of 32768 | 1152 (3.52%) | 1600 (4.88%) | 1152 (3.52%) |

So **at least 95% of floor states are safe**, for every `ρ₀`.

## 5. What remains, stated exactly

As `b` runs through `B_div` the floor vector moves by a `0/1` increment at each step
(coordinate `ρ` advances when `b` crosses a multiple of `L/e_ρ`). If the obstruction set
were left by every increment, a single jump inside `B_div` would finish the proof. It is
not: the obstruction set is closed under some increments, and the subgraph of *single*
increments **contains cycles**, for all three `ρ₀`. So the state-space relaxation alone
does not close the case, and saying otherwise would be wrong.

What the relaxation discards is the **rate**: coordinate `ρ` advances at rate `e_ρ/L`,
so the five coordinates advance in the fixed ratio `e₁ : e₃ : e₅ : e₇ : e_{ρ₀}`. A cycle
in the obstruction graph returns every coordinate to its value mod 8, so its increment
multiset has every entry `≡ 0 (mod 8)`; a trajectory staying obstructed therefore forces
the speed ratios to match that cycle's frequency vector.

> **Remaining step.** Show that the line `b ↦ (e_ρ b / L)_ρ mod 8` cannot remain inside
> the ≤4.88% obstruction set for all `b ∈ B_div`. Equivalently: rule out the cycle
> frequency vectors as speed ratios, or obtain the equidistribution directly.

This is where the two lineages meet: the obstruction set is a `v10` residue/floor-state
object, and the step needed is a `v11` equidistribution statement (§5.1 Weyl, Theorem
5.1). The synthesis is the point — but note the hazard: `v11`'s Conjecture 5.2-H became
circular at its own edge case, so any equidistribution input here must be checked
against that failure mode before it is relied on.

## 6. Grades

- Pair rule, parity of non-unit cosets, the `2φ(8) = 8` break-even: **PROVED**.
- The state counts (16/4096, 3344/4096, 1152 and 1600 of 32768), the alternating parity
  signature, and the presence of cycles in the single-increment subgraph: **PROVED by
  finite enumeration** over a state space of size `8⁵`, exact integer arithmetic.
- The remaining step: **OPEN**, stated above.
