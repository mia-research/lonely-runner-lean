# The requirements for a proof of Existence — audited, then fixed

2026-09-17, at the owner's instruction: *"we have been here before, create a list and then the goal posts
move. But I think they move because at the end we ask is this proof again and then import something
else."*

That is exactly the mechanism, and the record below shows it seven times in one session. **§1 is the
audit. §2 is the fix, and the fix is that the target is now a Lean `Prop`, so the question is decidable
rather than judged.** §3 is the ledger of what is owed.

---

## 1. The audit: seven requirements, in order, each replaced when the previous was found imported

| # | stated requirement | where | what it actually was | how it fell |
|---|---|---|---|---|
| 1 | a bound on the **return correction** (Lemma C) | inherited, `LADDER_BOUND_v1` §4 | a bound | superseded by 2 |
| 2 | **`sup R < n − 1`** | the certificate line | `R = n·u`, so this is `u < 7/8` — the **first window**, register item 15 | §1.3 disavows it; and it is false at order 8 (`R = 10.31`) |
| 3 | **`R < ∞`**, i.e. `∏λ_j` finite | `EXISTENCE_ARITHMETIC_v1` §2 | still a bound, but true and equivalent | not false — but §4 replaced it while chasing how to prove it |
| 4 | an **amortised bound on the depths** `δ_j` | `EXISTENCE_MAP_v1` Link 4, `WHAT_IS_STOPPING_IT_v1` §5 | the repair to `n > 2k`, which is `k·(2/n) < 1` — a **union bound**, register items 4 and 27 | owner's challenge; G3 reduction |
| 5 | **a flank with `j ≥ 4` non-integer ratios has a lonely opening** | `WHAT_IS_STOPPING_IT_v1`, `DEEP_REVIEW_v1` §5 | §6.9's description of where Props 6.10–6.11 stop — a **lemma-coverage boundary** | owner's challenge; measured, flanks fail at every `j` from 2 |
| 6 | **not every flank can be shadowed at once** | §6.9's own words | the framework's own, equivalent to Existence | stands |
| 7 | **a rule assigning each arrangement a pair `(D, a)` plus its verification** | `WHAT_A_PROOF_IS_v1` §4 | the framework's own *mode*, derived from §0 | stands |

**The mechanism, stated plainly.** Each replacement happened at the moment a target was found to be an
import. The correct response at that moment is to **return to the frozen target**. What happened instead
was to invent a new one on the spot — and a target invented on the spot is invented from the general
mathematical habit, which is where the imports come from. The movement was not carelessness about the
goal; it was the absence of a goal that could not be moved.

Note that 6 and 7 are not rivals: **6 is what must be true, 7 is what form a proof must take.** They are
the first two entries that were derived rather than reached for.

## 2. The fix: the target is a Lean `Prop`, and the question is decidable

`LonelyRunner/LRC/Spec/Target.lean` — **outside** `LRC/Cascade/`, so the gate's check [4] keeps its
meaning. Nothing is claimed there; they are `Prop`s.

```
def ExistenceAt8 : Prop :=
  ∀ ds : Finset ℝ, (∀ d ∈ ds, 0 < d) → ds.card ≤ 7 → ∃ s : ℝ, 0 < s ∧ Lonely 8 ds s
```

and §6.7's own wording, `ExistenceAt8_cascade` (the determinator from the bound reaches a fixed point),
and the flank wording, `ExistenceAt8_flank`.

**`target_forms_agree : ExistenceAt8 ↔ ExistenceAt8_cascade`** is proved, axiom-clean, and
`target_flank_agrees` gives the third. So no wording can be substituted for another as a redefinition of
the goal — a route that shifts between them shifts nothing.

### The requirements, fixed

| | requirement | how it is checked |
|---|---|---|
| **R1** | **The target is `LRC.Spec.ExistenceAt8`.** Done ⟺ a term of that type exists and the gate passes with it imported | `#print axioms` + `scripts/cascade/gate.sh` |
| **R2** | Any claim of progress is a **Lean theorem with a complete statement**. Its hypotheses are either proved in the tree or listed in §3 as owed | the term type-checks; the hypotheses are named |
| **R3** | Empirical results are tagged `[EMPIRICAL]` with the artefact named, and never upgrade to `[PROVED]` except by R2 | the artefact runs |
| **R4** | **Tools free; targets and statements native** (owner, 2026-09-15). Test: does the statement exist in the framework's vocabulary alone | `PROVENANCE_MAP_v1` gate G1–G7 |
| **R5** | **Does the route end in a pair `(D, a)`?** If it ends in an inequality, a density, a count, or an impossibility, it is not a proof here | one line, answerable before the work |
| **R6** | **R1 may not be replaced.** A target found to be an import sends the work back to R1 — it does not license a new target. Amending R1 needs the owner's recorded decision, with a date and a reason | this file |

**R6 is the fix to goalpost movement.** R5 is the fix to importing. R1 is what makes both enforceable,
because it is the thing they refer back to.

## 3. The ledger: what is owed, as of 2026-09-17

Stated so that "how far along are we" is also not a matter of judgement.

**Proved in the tree** (gate: 4,669 theorems, axiom-clean, zero `sorry`):

- the determinator and its two equivalences — `lonely_iff_run_ends`, `lonely_iff_exists_flank`;
- the clearing test as integer arithmetic — `clear_of_residue_band` (Prop 2.1);
- the `U`/`K` calculus — `class_killer_int`, `circDist_periodic_of_lattice`,
  `lonely_opening_of_free_off_lattice`, `lonely_of_flank_unkillable`, `lonely_of_some_flank_unkillable`;
- Existence for `card ≤ 4` (`stops_when_twice_card_lt`, `four_diffs_stop_ge_eight`), the §4.5 and §6.9
  families, the eighth family, and **4,475 census families** (4,413 fully pinned + 62 with a free
  parameter).

**Owed, and named** — each is a hypothesis of something above, not a vague gap:

| | owed | why it is owed |
|---|---|---|
| A | the **8 intersection families** | `lonely_of_some_flank_unkillable` exists; its hypotheses are not discharged for them |
| B | census families with **`e/P > 1`** | the emitter's `hkill` assumes the free parameter ranges over the integers |
| C | **no-mixing** — every minimal shadowing set is confined to one modulus | validated at `c ≤ 14` and `c ≤ 15`; `RESEARCH.md`: *"its proof is the structural target"* |
| D | the census beyond **`M ≤ 60`** | the per-`M` census is finite; the wall is `M ≈ 100–150` per run |
| E | **R1 itself** | A–D together do not give it; they give the census, not the theorem |

**E is not a formality.** Even with A–D discharged, what exists is a verified finite census plus a
calculus, not a term of type `ExistenceAt8`. The gap between them is the uniform argument, and under R5
it must end in a construction of `(D, a)` — per `WHAT_A_PROOF_IS_v1` §7, most likely by taking the
shadowing of six flanks as *data* and constructing the opening of the seventh.

## 4. What to do when a route is found to be an import

The procedure, so the next occurrence does not cost a day:

1. **Stop.** Do not invent a replacement target.
2. Record the import against `OBJECT_REGISTER_v1`, with the G-gate row that catches it.
3. **Return to R1.** The target has not changed.
4. Ask R5 of any proposed next route *before* starting it.
