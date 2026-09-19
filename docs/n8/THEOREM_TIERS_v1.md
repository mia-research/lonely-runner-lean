# Walking the theorems: three tiers, one extension proved, one boundary found

A pass over all 56 declarations, comparing statements rather than recalling them. The comparison
sorts them into three tiers by *how much of the order 8 they actually use* — and two of the three
were not what I expected.

## Tier 1 — the order never appears

`ReachRule` (13), `GapRule` (3), `ArithForm` (2), `EdgeWitness` (4), `SolutionPair` (3) — **25
declarations** — carry the order as a free variable or not at all. `GapRule.gap_eq` is
`{n s s' m m' : ℤ}`; `ArithForm.near_iff_int` likewise; `ReachRule` and `EdgeWitness` never mention
an order in any form.

**They already hold at every order.** Nothing needs restating or reproving. Checked for
`EdgeWitness`/`SolutionPair` at orders `7, 8, 9, 11, 13` (991 profiles each, 0 failures); the rest is
visible in the statements.

## Tier 3 — special to `n ∣ 24`, and this is the boundary I had not found

`Guard.klein_self_inverse` is `∀ r : ZMod 8, IsUnit r → r * r = 1`. **Every unit of `ℤ/n` is
self-inverse exactly when `n ∈ {2,3,4,6,8,12,24}`** — the divisors of 24. Computed for `n < 60`, an
exact match.

`TwoPatterns.unit_on_both` rests on `u² ≡ 1 (mod 8)`. So:

> **The AP's four-coincidence structure is a fact about `n ∣ 24`, not about order 8 as an order.**

| `n` | 7 | 8 | 9 | 11 | 12 | 13 | 24 |
|---|---|---|---|---|---|---|---|
| all units self-inverse | no | **yes** | no | no | **yes** | no | **yes** |

At `n = 7, 9, 11, 13` the units are not self-inverse, so `x = u` does **not** sit on the `+1` pattern
via reading `u`, and the two patterns do not coincide there. Any attempt to carry the coincidence to
the general-`n` programme is carrying a property of `24`.

This also explains, retrospectively, why the coincidence failed to generalise *within* order 8
(`AP_GENERALISATION_v1`): it is not a robust feature but an arithmetic accident of the modulus.

## Tier 2 — stated at order 8, general in substance, now proved general

`Guard.odd_clear_of_not_dvd` is `¬(8 ∣ s) → Odd R → ¬(8 ∣ s·R)`. At order 8, "odd" is exactly
"coprime to 8" — and **the proof uses only that `R` is invertible mod the order**, no Klein structure
at all.

> **`GeneralOrder.clear_of_not_dvd`** (Lean, axioms `[propext]` only): `IsCoprime R n → ¬(n ∣ s) →
> ¬(n ∣ s·R)`.
> **`GeneralOrder.spine_all_or_nothing`**: if no reading is divisible by `n`, then **every** `R`
> coprime to `n` is clear of every reading.

**This is Branch A at every order.** Verified across `n = 4..15`, ~94,000 Branch A profiles: `R = 1`
fails **0** times.

Branch A was the strongest proved result at order 8 — proved for arbitrary reading magnitudes. It now
holds at arbitrary **order** as well, and the two new declarations carry the lightest axiom footprint
in the whole development.

## What the tiers say about the remaining work

- Anything built on **Tier 1** transfers to the general-`n` programme of §8 unmodified. That is 25 of
  56 declarations, including the entire reduction to `ℤ` and both witness-normalisation results.
- Anything built on **Tier 3** does not transfer past `n ∣ 24`, and should not be attempted there.
  The Klein group, the four coincidences, and `blocked_reflect`'s `{1,7}`/`{3,5}` pairing are all in
  this tier.
- **Tier 2 is where the value is**: results stated at 8 whose proofs use less. `odd_clear_of_not_dvd`
  was one, and the general version fell out in two lines. The others in this tier are not yet
  identified, and finding them is a mechanical exercise — compare each statement's hypotheses against
  what its proof consumes.

## Status

`GeneralOrder` is **`[PROVED]`**, axiom-clean on `[propext]`. The `n ∣ 24` boundary is
**`[VERIFIED — exact]`** by computation over `n < 60`, not formalised. Witness file now 56
declarations. Existence at order 8 is unchanged.
