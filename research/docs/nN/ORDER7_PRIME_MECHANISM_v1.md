# Order 7: the mechanism found, and proved

2026-09-21, version 1. The owner asked what happens with the 119 failures at order 7 and said
the mechanism would make them provable. It did — but the other way round: the mechanism proves
the **complement**, and the 119 are exactly what it leaves.

Artefacts: `LonelyRunner/LRC/Spec/ResonanceN.lean` (13 declarations, axiom-clean, no `sorry`) ·
`experiments/n8/resonance_axioms_v1.{lean,out}` · `experiments/nN/n7_frontier_v1.{py,out}` ·
`n7_why_v1.{py,out}` · `n7_mechanism_v1.{py,out}` · `prime_flank_proof_v1.{py,out}` ·
`n7_tight_v2.{py,out}`

---

## 1. The theorem  `[PROVED — axiom-clean]`

> **At a prime order `n`, if `n` divides neither the flank `e` nor any disparity, then `e` hosts
> a lonely opening — at the explicit index `j = (e·s − 1)/n`, where `e·s ≡ 1 (mod n)`.**
>
> `LRC.Resonance.flankWorks_of_prime`, `lonely_flank_of_prime`, `lonely_flank_of_prime_image`

**The proof, in one line.** With `n·j + 1 = e·s`, every disparity reads
`d·(n j + 1) = e·(d·s)`, whose residue mod `n·e` is `e·((d·s) mod n)` — inside the band
`[e, (n−1)e]` exactly when `n ∤ d·s`.

**Why it is about primality and not size.** That last step is Euclid's lemma: `n ∤ d` and
`n ∤ s` give `n ∤ d·s` only when `n` is prime. At a composite order it fails, and the failures
are explicit — at `n = 8` the pairs `(2,4)`, `(4,2)`, `(4,4)` have `8 ∣ d·s` with `8 ∤ d` and
`8 ∤ s`; at `n = 9`, `(3,3)`, `(3,6)`, `(6,3)`; at every prime order there are **none**.

Verified before formalising on 78,182 non-resonant sets at `n = 5, 7, 11, 13` — the construction
clears every one.

This upgrades `CoprimeLargestFlank` from `[EMPIRICAL]` to **proved at prime orders**, and gives
more than was conjectured: **every** flank, not only the largest.

---

## 2. What that leaves at order 7

Card 6 (the diagonal), primitive subsets of `[1,18]`:

| | count | status |
|---|---|---|
| non-resonant (no multiple of 7) | 7,979 | **PROVED** — §1, every flank |
| resonant (some multiple of 7) | 10,500 | the frontier |
| of those, largest flank fails | **119** | the open part — 1.13% of the frontier |

So the 119 are precisely the sets the construction cannot reach, because it needs `n ∤ d` for
every `d`. They are not an anomaly inside the proved region; they are its complement.

---

## 3. What the 119 are like

**They are marginal, not caused by one runner.** Deleting *any* blocker fixes all 119 — both a
7-multiple (119/119) and a non-multiple (119/119). No single disparity is the culprit.

**Every one is settled at the second-largest flank.** Best working flank rank is **2** for all
119. So `DoorTwoLargest` — already in the Lean, with the ladder to the target — is the order-7
candidate, the same door as order 6.

**The aggravating factor is `gcd(d, e)`, not `gcd(d, n)`.** The trace shows the over-blockers:
in `(1,2,3,5,7,14)` the disparity 7 blocks 7 of 14 openings against a generic 4, because
`gcd(7,14) = 7` leaves a 2-point lattice. But that is aggravation, not cause —
(`n7_mechanism_v1.out`, `[1,20]`, card 6):

| n-resonant? | `gcd(d,e) ≥ 3`? | sets | failures | rate |
|---|---|---|---|---|
| no | no | 7,743 | **0** | 0 |
| no | yes | 10,736 | **0** | 0 |
| yes | no | 9,529 | 10 | 0.00105 |
| yes | yes | 10,541 | 138 | 0.01309 |

**Non-resonance is decisive on its own**: zero failures at *every* value of `max gcd(d,e)`, up to
10. Within the resonant class, a large `gcd(d,e)` raises the rate twelvefold. Order-resonance is
necessary; flank-resonance only makes it worse.

---

## 4. Is the order-7 tight family bounded?

The `DoorTwoLargest` tight family (at most one working opening across the two largest flanks):

| range | [1,20] | [1,24] | [1,28] | [1,32] |
|---|---|---|---|---|
| primitive sets | 38,549 | 133,644 | 373,653 | 897,973 |
| tight | 39 | 45 | 46 | **48** |
| with **zero** openings | 0 | 0 | 0 | **0** |

The family grows 39 → 48 while the population grows 23-fold, so it is decelerating; but the
maximum element still tracks the range (20, 23, 28, 30), so it is **not** established as bounded
— unlike order 5 (57 sets, all `≤ 15`, stable to `[1,200]`) and order 6 (26 sets, all `≤ 30`,
stable to `[1,80]`).

---

## 5. Grades

| claim | grade |
|---|---|
| the prime-order flank construction | `[PROVED — flankWorks_of_prime, axiom-clean, no `sorry`]` |
| it gives **every** flank, not only the largest | `[PROVED]` |
| Euclid's lemma is the step that fails at composite `n` | `[PROVED — explicit witness pairs at 8, 9, 10, 12; none at 5, 7, 11, 13]` |
| every order-7 failure is resonant | `[PROVED for the non-resonant side — §1; the count is exhaustive measurement]` |
| all 119 are settled at rank 2 | `[VERIFIED — exhaustive]` |
| removing any blocker fixes all 119 | `[VERIFIED — exhaustive]` |
| `gcd(d,e)` aggravates but does not cause | `[VERIFIED — 18,479 non-resonant sets, 0 failures at every `gcd(d,e)`]` |
| the order-7 tight family is bounded | **not established** — still tracking the range |
| `DoorTwoLargest` at order 7 | **not proved** — 0 counterexamples to `[1,32]` |

**Scope.** Whole-number difference sets, exhaustive over the stated ranges. §1 is a theorem over
the reals for any list of whole-number disparities at any prime order.

---

## 6. Where this leaves the programme

**Order 7 is now split cleanly**: 43% of the diagonal proved outright by §1, the rest reduced to
resonant sets of which ~1% fail the largest flank and all of those yield to rank 2.

**Order 8 gets nothing from §1** — `8` is not prime, and the proof's final step is exactly what
composite orders break. That is the same conclusion as `RESONANCE_LEAN_v1.md` §3(a), now with a
proof rather than a measurement behind it: the gap at composite orders is Euclid's lemma.

**The next question for 8** is whether the construction has a composite analogue: at `n = 8` one
would need `s` with `8 ∤ d·s` for every disparity `d`, which is possible only when no disparity
is `≡ 0 mod 8` *and* the `d` avoid the zero-divisor pairs with `s`. Whether a suitable `s`
exists is a finite condition on the residues `d mod 8` — checkable, and not yet checked.
