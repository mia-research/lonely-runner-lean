# What Lean actually requires, and what I added on top

An audit of my own framing, prompted by the right question. **The answer is that I have been
describing the last step of one strategy applied to one case as though it were the remaining
hurdle for Lean Existence. It is not.**

---

## 1. The obligation, exactly

```lean
def LonelyRunnerAt8 : Prop :=
  ∀ v : Fin 8 → ℝ, Function.Injective v → ∀ k : Fin 8, LonelyForSubject v k
```

with `LonelyForSubject v k := ∃ t : ℝ, 0 < t ∧ LonelyAt v k t` and
`LonelyAt v k t := ∀ i ≠ k, (8:ℝ)⁻¹ ≤ circDist (sep v k i t)`.

`doors_agree` proves `DoorFlank ↔ DoorArrives ↔ DoorCapped ↔ DoorFAM ↔ LonelyForSubject`, per
arrangement and per subject, and `lonelyRunnerAt8_of_doorX` converts any of them. **`Spec/` and
`Cascade/` contain zero `sorry`.** The infrastructure is finished. **No door is proved.**

Everything is over `ℝ`. The target quantifies over real speeds and asks for a real time.

## 2. What I added, and none of it is required

| layer | status | required by the obligation? |
|---|---|---|
| restrict to **commensurable** (integer) differences | a case split I chose | **no** — the target is over `ℝ` |
| the **candidate / opening** normal form `(8q+1)/(8e)` | `witness_normalised`, `finite_check` | **no** — a normal form for a witness; existence needs any real `t` |
| the **divisor-closed** structure | a sub-case | **no** |
| **order-6 + rounding** | one proof strategy | **no** |
| the **four residue exclusions** at `b ∈ {2,3,8,9}` | a consequence of the strategy above | **no** |

So the "single remaining step" of `SYNTHESIS_v1`, `FourResidues` and `GAP_THRESHOLD_v1` is the
last step of **one strategy** applied to **one case**. Closing it would not produce
`LonelyRunnerAt8`.

## 3. What is genuinely missing, in two parts

**(a) No door is established for real arrangements.** `DoorThreeLargest` is `[EMPIRICAL]`,
exhaustive to `[1,40]` but unproved. `DoorLargestFlank` is `[REFUTED]`. The others are open.

**(b) There is no bridge from integer results to the real target.** `Spec/` **never mentions**
`intLRC`. `Target.lean:246–251` records the position: the congruence (integer) form and
`ExistenceAt8` "are equivalent on whole-number differences and **not otherwise**", so adopting
the integer form as the target "would **drop the real case**" — which is *"mathematically
comfortable (margins 1.6× to 3.7× once any ratio is irrational) but expensive to formalise, since
it needs a dense-orbit theorem on the `k`-torus that mathlib does not carry."*

So even a complete proof of `intLRC 8` would not close `LonelyRunnerAt8` in this tree. The
bridge is unbuilt, and it is a **formalisation** obligation against mathlib rather than a
mathematical one.

## 4. What the arc did buy, stated without inflation

The proved results stand and are useful, but they are fragments of case (a), not progress on the
door:

* `CardSix.lonely_at_eight_of_six` — loneliness at order 8 whenever the differences collapse to
  `≤ 6` distinct values, **built on `intLRC_seven`**. This is the one result of the arc that
  delivers `LonelyAt` itself rather than a statement about candidates.
* Everything else — `LastClass`, `MinusSeven`, `Openings`, `FirstLap`, `CoverCount`,
  `DivisorOrder6`, `SmallModuli`, `CanonicalCandidate`, `WindowGeometry`, `Derestricted`,
  `ReducedOpen`, `FourResidues`, `OddSublattice`, `IsolatingPair`, `GapThreshold` — is about the
  candidate normal form over `ℤ`. Sound, axiom-clean, and inside layer 2 of §2's table.

## 5. The correction

I said, repeatedly, that Existence "reduces to one statement" and that there is "one line item".
That was true **within the chosen strategy and case** and I did not say so. Read as a claim about
the Lean obligation it overstates: closing that step leaves (i) the rest of the commensurable
strategy, (ii) the other cases, and (iii) the real bridge of §3(b).

The honest ledger: **the Lean hurdle is to prove one door for all real arrangements, and nothing
in the tree does that.** The nearest thing to a door-level result is `CardSix`, which covers
arrangements whose subject is the midpoint of two others.

Existence at order 8 remains open.
