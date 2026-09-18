# How the laps grow: they are the disparity times the nearest runner's reading

2026-09-18. Artefacts: `experiments/n8/lap_growth_v1/`. Follows `RETURN_G_GE_1_v1`, which left the
question: can the laps in a window be bounded below? The owner's intuition — laps grow with the
disparity between the speeds — is correct, and sharpens to an identity.

---

## 1. The law  `[VERIFIED — exact, 0 violations in 3,454 moves]`

Write `m = min ds`, `ρ_j = d_j/m` (the **disparity**, the setter's ratio to the slowest), and
`τ_j = m·t_j` (the nearest runner's reading). Then for the setter of move `j` at lap `Q_j`:

    Q_j = ρ_j · τ_j ± 1/n                                    the lap IS disparity × reading
    τ_{j+1} = τ_j + (1/n − δ_j)/ρ_j,      1/n − δ_j ∈ (0, 2/n)

Both hold with **zero violations** over 3,454 moves. The second is the memo's `s' = s + (2 − 8δ)`
read against the nearest runner instead of the setter.

**Consequences.** A setter's lap is proportional to its disparity, with `τ` the common scale. Since
`(Q + 1/n)/(Q − 1/n)` decreases in `Q`, **fast runners supply little growth**. And `τ` climbs slowly —
each move adds at most `2/(n·ρ)`.

**The crude lower bound this gives**, `Q > (ρ − 1)/n`, holds (0 violations, ~7,000 moves) but is loose
by a median factor of **5.6** — which is exactly `τ_typical/τ₀ ≈ 0.7/0.125`. It is the identity
evaluated at the start, and it loses precisely the growth of `τ`.

## 2. `τ` cancels: the return condition is scale-free  `[VERIFIED — 201 returns, 0 failures]`

A return from lap `P` to `P+1` costs `(3/4)/(P + 1/8)`; a setter at lap `Q` supplies
`(1/4)/(Q − 1/8)`. Substituting `Q_j = ρ_j τ` and `P = ρ_x τ`, **`τ` cancels**:

    3/ρ_x  <  Σ_{j ∈ window} 1/ρ_j

Measured as need/supplied: median **0.565**, 90th 0.667, max **0.706**, no failures — including both
named hard cases (max 0.629 and 0.650).

**This is the substantive finding.** The return structure does not depend on the trajectory, on time,
or on scale. It is a condition on the seven ratios alone. A question about a cascade has become a
question about seven numbers.

## 3. Two structural predictions of mine, both refuted

Recorded because each looked plausible and each was wrong.

- **"Returns must be paid for by slow setters."** False. Median `ρ` inside return windows matches the
  median over all setters: 5.84 vs 5.84 (§6.7 climb), 5.30 vs 5.30 (§6.9 row), 7.85 vs 8.45 (random).
  §2 explains why — `τ` cancels, so the condition couples `ρ_x` to the window's ratios, not to
  absolute smallness.
- **"The nearest runner is never in the way at a cascade instant."** False. This was the weakened,
  framework-legitimate form of the `n = 4` window invariant — not *"`τ ≤ 7/8`"* (which is not a
  framework requirement, and which fails because `τ` can jump **over** the blocked band), but *"the
  nearest is clear at every instant"*. **Both named cases have the nearest runner in the way, and
  setting, exactly once.** So this fails too.

## 4. The sampler warning, now confirmed three times

`TERMINATION_ROUTES_v1` §2 recorded it; §3 above is the third instance in one sitting.

| invariant | sampler verdict | truth |
|---|---|---|
| nearest stays in first window | 4,000/4,000 hold; 60,000 spread-biased, 0 violations | **false** — both named cases |
| nearest never in the way | 40,000 spread-biased, 0 violations | **false** — both named cases |
| tight configurations | "3431 tight, 0 loose" | **forced statistic**, the search could not return anything else |

The control fires in each case (e.g. the second-slowest runner is in the way in 290/4,000 cascades),
so the tests are not blind — the **sampler** cannot reach the hard region. Test invariants against
`{(27,70,107,137,159,188,344,393), subject 393}` and `{(1,31,75,97,128,160,176,225), subject 1}`
first, always.

## 5. Where this leaves work item B

Standing, and proved: `ChainBounds.return_needs_growth` — a return is paid for by the window's
growth, with no hypothesis on the window.

Standing, and measured exactly: the lap law of §1 and the scale-free return condition of §2.

Not standing: any invariant asserting the nearest runner stays clear.

## 6. That question is now answered, and the answer closes the route  `[REFUTED]`

I proposed: a cascade that never terminates must satisfy `3/ρ_x < Σ_{window} 1/ρ_j` at every return
forever, drawing windows from a fixed set of seven values — so perhaps no infinite setter word can.

**It can.** If letter `x` has frequency `f_x`, consecutive occurrences are `≈ 1/f_x` apart, so the
window supplies `≈ A/f_x` with `A = Σ_y f_y/ρ_y`. The condition becomes `f_x/ρ_x < A/3` for every `x`
— but `Σ_x f_x/ρ_x = A` exactly. Seven non-negative terms summing to `A`, each required below `A/3`:
satisfiable whenever four or more letters carry weight. **No contradiction is available.**

Explicit witness: the round-robin word on `ρ = (1, 1.1, 1.2, 1.3, 1.4, 1.5, 1.6)` satisfies it at
every return, margins 1.5 to 3.0 (`infword.out`). The condition does bite once the ratios spread past
about `[1, 3]`, and LRC must hold for clustered ratios too, so that does not rescue it.

So the scale-free condition is a true necessary condition and is too weak to force termination.

## 7. Status of termination, stated without a successor route

`CascadeCapped` was put to Lean directly (`try_cap.lean`): `exact?` cannot close it and `aesop` fails
after exhaustive search. That only confirms nothing already in the tree suffices — Lean checks
proofs, it does not find them.

**The residue cannot be usefully restated.** `nearest_reading_recurrence` gives
`τ_N ≤ (1/n)·∏ (Q_j + 1/n)/(Q_j − 1/n)`, so a bounded lap product implies `CascadeCapped`; and if
capped, `exists_fixed_of_capped` gives finitely many moves, so the product is finite. The two are
**equivalent**. Recasting the obligation in terms of the laps is not a refinement.

Termination is **open**. No route in this document is one, and none is offered.

**A correction to how I had been framing this.** I wrote elsewhere that termination "is equivalent to
`ExistenceAt8`, hence to LRC(8), settled in 2025 by computer verification", in a position where it
read as a bar — as though a proof here had to reach the shape or the scale of that search. **That
inference is invalid.** Equivalence of *statements* says nothing about equivalence of *proof
methods*: a true statement can carry both a long computational proof and a short analytic one, and
which exist is not settled by the fact that one does.

What Rosenfeld 2025 legitimately supplies is that the statement is **true** — which helps, since it
means no route here is hunting something false. It supplies no constraint on proof shape whatever.

And the record in this tree runs the other way. Every order settled before 8 has a **published
analytic proof**, formalised here: `TerminationThree` and `TerminationFour` are the framework's own,
Bienia–Goddyn–Gvozdjak–Sebő–Tarsi 1998 covers 4 and 5, BHK 2001 covers 6, Barajas–Serra 2008 covers
7. None is a computer search. So "order 8 needs a computation" is a claim about publication history,
not about the problem.

None of the refutations in this document or in `LONG_RETURN_CIRCLE_v1` used that fact as a premise.
They are self-contained — a forcing argument, a frequency argument, and measurements against named
arrangements. The error was in the framing, and the framing was doing the deflationary thing the
project instructions name: converting an absence in my own information into a deficiency in the
thing.
