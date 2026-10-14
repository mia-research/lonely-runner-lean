# Never a singleton — proved, and the residue named

Next on the list: the one structural fact measured everywhere and never explained — **the solution
count is never 1.** Minimum 2 across all 51,295 divisor-closed profiles.

## The measurement, sharpened to an exact law

When the reflection `q ↦ m − q` acts — `Involution.clear_reflect`, i.e. every modulus and `m` has
residue mod `8` outside `{0,1}` — the parity of `|S|` is **completely determined**:

> **`|S|` is odd if and only if `m/2 ∈ S`.**  6,728 profiles, **0 exceptions.**

The accounting closes exactly: of those 6,728, `6,701` have `|S|` even and `27` have `|S|` odd — and
the 27 are precisely the ones with a fixed point in `S`. Nothing is left over.

The reflection's fixed points on `ℤ/m` are `q = 0` and `q = m/2`. **`0` is never a solution**, since
every clear interval has `L(b) = ⌈(b−1)/8⌉ ≥ 1` for `b ≥ 2` — measured `0 ∈ S` in 0 of 19,880
profiles, and proved below. So `m/2` is the only fixed point that can occur.

## The proof, and it needs no parity argument

Once the fixed points are identified, the statement falls out directly:

**`SolutionPair.two_of_reflect`** — if the solution set is closed under `r ↦ m − r`, any solution `q`
with `2q ≠ m` yields two distinct solutions, `q` and `m − q`.

**`SolutionPair.not_singleton`** — hence a non-empty solution set containing anything other than the
centre contains two distinct points.

**`SolutionPair.zero_not_sat`** — `q = 0` fails any constraint with a positive lower bound, which
every modulus `b ≥ 2` has.

All three Lean, axiom-clean, and on only `[propext, Quot.sound]` — a strict subset of the usual
three. No `Finset.card` parity machinery was needed: **a solution off the centre brings its mirror
image with it, and the two are distinct.** That is the whole argument.

## The residue, named

`S = {m/2}` is **not excluded**. The theorem says "two distinct solutions unless every solution is
the centre". That case was never observed — 0 singletons in 19,880 profiles — and is not proved
impossible.

It is a small, sharp, and genuinely open sub-question: *can the centre be the unique solution?*
Unlike the frontiers, it concerns a single explicitly named point.

## Scope

The parity law and the proof both require the reflection to act, which holds for **6,728 of 19,880**
profiles (33.8%). Where a modulus has residue `0` or `1` mod `8` the reflection is obstructed
(`reflect_fails_zero`, `reflect_fails_one`) and `|S|` is even only 59.85% of the time — no parity
argument is available there. Those 13,152 profiles still have `|S| ≥ 2` empirically, by some other
mechanism, which is not identified.

So: "never a singleton" is **proved on a third of the category and measured on the rest**, with the
obstruction to extending it already named and understood.
