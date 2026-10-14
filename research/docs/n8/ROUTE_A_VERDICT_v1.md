# Route A: the verdict — uniqueness of the eighth pattern is false, and the mechanism generalises

2026-09-16. Answers the owner's Route A instruction (make uniqueness a rigidity argument, not a census)
and its named highest-value check (does `exists_clear_step` force shadowing covers to have an integer
free parameter). Scripts: `experiments/n8/largest_flank_rigidity_v1.py`,
`largest_flank_minimal_covers_v1.py`, `largest_flank_c10_witness_v1.py`, `largest_flank_other_flanks_v1.py`.

**Order 8 is not closed by anything in this document.** It remains open, and the cascade gate still
reports it unstated.

---

## 1. The named check: what `exists_clear_step` does force  `[PROVED — argument below, not yet in Lean]`

It does bite, but not in the form the instruction anticipated. The correct statement is about *essential*
ratios, not the free parameter.

> **Essential-ratio rationality.** Let a set of ratios shadow a flank at threshold `1/n`, `n ≥ 4`. Suppose
> every ratio but `ρ` is rational, with common period `L`, and that those leave some residue class
> `k ≡ r (mod L)` uncovered. Then `ρ·L ∈ ℤ`.

*Proof.* On `k = r + Lj` the phase of `ρ` is `ρ(r + 1/n) + (ρL)·j`. If `ρL ∉ ℤ`, put `f = Int.fract (ρL) ∈ (0,1)`
and `c = ρ(r + 1/n)`; `Flanks.exists_clear_step` gives a `j` with `1/n ≤ circDist (j·f + c)`, and
`j·ρL − j·f ∈ ℤ`, so `circDist (ρ(r + Lj + 1/n)) ≥ 1/n` — `ρ` is clear there. No other ratio blocks that
class, so the flank has a free opening and is not shadowed. ∎

So **a cover cannot consist of rationals plus exactly one irrational**: covers are forced towards
commensurability. What the argument does *not* reach is two or more irrational ratios sharing a class, where
`exists_clear_step` (a one-ratio lemma) has nothing to say. That gap is real and is the honest limit of the
rigidity available today.

The instruction's stronger hope — that shadowing forces the *free* parameter to be an integer, collapsing
Route A onto the formalised integer table — does not hold, for a simpler reason: at the largest flank the
five fixed ratios shadow *on their own*, so the free parameter is unconstrained there. It is constrained at
the `7/8` flank, and that is precisely the eighth-family theorem already proved.

## 2. Uniqueness is false  `[REFUTED — exact, minimal, verified witness]`

The census reproduces `FLANK_SIGNATURES_v1` §6 exactly where they overlap: at `c ≤ 8` there is **one**
minimal cover, `{1/8, 3/8, 1/2, 5/8, 7/8}` — the eighth pattern. That agreement is what makes the
disagreement above it meaningful.

Minimal covers of the largest flank, by ratios with denominator dividing `c`:

| `c` | size | count | example |
|---|---|---|---|
| 4–7 | — | none of size ≤ 6 | — |
| **8** | 5 | **1** | `{1/8, 3/8, 1/2, 5/8, 7/8}` — the eighth pattern |
| 9 | 6 | 2 | `{1/9, 2/9, 1/3, 5/9, 7/9, 8/9}` |
| **10** | 5 | **4** | `{1/10, 1/5, 3/10, 1/2, 7/10}` |
| 11 | 6 | 2 | `{1/11, 2/11, 5/11, 6/11, 7/11, 8/11}` |
| 12 | 5 | 8 | `{1/12, 1/4, 1/3, 5/12, 7/12}` |
| 16 | 5 | 6 | `{1/16, 3/16, 1/4, 5/16, 7/16}` (the eighth pattern also appears, as `c = 8 ∣ 16`) |

**The witness, checked in full.** `{1/10, 1/5, 3/10, 1/2, 7/10}` — differences `{1, 2, 3, 5, 7}` at
`d_max = 10`, a realisable eight-runner set `{1,2,3,5,7,x,10}`. Every opening `k mod 10` is blocked
(`k=1` by `1/10`, `k=2` by `1/2`, `k=3` by `3/10`, `k=5` by `1/5`, `k=7` by `7/10`, evens by `1/2`), and it
is minimal: each member holds private openings (`1/10`: {1,9}; `1/5`: {5}; `3/10`: {3}; `1/2`: {2,6,8};
`7/10`: {7}). It is not the eighth pattern.

**Consequence.** *"If the eighth-pattern is unique at all denominators, Existence at order 8 is proved
outright"* rests on a premise that is false. Uniqueness fails at `c = 9, 10, 11, 12, 16`. No amount of
census extension recovers it, and no rigidity argument can prove it. **Route A is closed as stated.**

An aside worth keeping: at `c = 9` and `c = 11` the minimal covers have size **six**, consuming all six
non-flank differences. Those are not families with a free parameter — they are rigid points.

## 3. What survives, and it is the better target  `[EMPIRICAL — every case checked]`

The eighth-family *mechanism* generalises. For every minimal cover found at `c = 8, 10, 12, 16`, some
**other** flank has an uncovered residue class — the same situation the eighth-family theorem exploits at
the `7/8` flank, where `exists_clear_step` then clears the free parameter:

- `c = 8` (eighth pattern): flank 4 free at `k ≡ 2 (mod 4)`, flank 5 at `k ≡ 4 (mod 5)`, flank 7 at
  `k ≡ 1, 3 (mod 7)` — the theorem already proved.
- `c = 10`, `{1,2,3,5,7,10}`: flank 3 free at `k ≡ 1`, flank 5 at three residues, flank 7 at three.
- `c = 12`, `{1,3,4,5,7,12}`: flanks 3, 4, 5 each free at one residue, flank 7 at two.
- Every other cover in the table: at least two flanks with uncovered residues.

So the classification explosion does not matter. **The target is not "the pattern is unique" but "no
difference set has every flank shadowed at once"** — and that is already native: `lonely_iff_exists_flank`
says the subject is lonely exactly when some flank has a lonely opening, so *not all flanks shadowed* **is**
Existence. The eighth-family theorem is the first instance; the general statement is the goal.

## 4. Where this leaves the two routes

- **Route A (uniqueness / rigidity): closed.** Its premise is refuted. The essential-ratio lemma of §1 is
  the part worth keeping — it is native, it follows from a lemma already in the artefact, and it is not yet
  in Lean.
- **Route B (bounded overhang): now the live route**, by the owner's own conditional. Not started, and not
  formalised — per instruction, no formalisation runs until the route is chosen.
- **The reframed target** (§3) is the one this document recommends: some flank is always free. It subsumes
  both routes' purposes and is stated in the framework's own vocabulary.

**Scope, verbatim and to be carried into every derived document:** this closes the family that shadows the
largest flank; **Existence at order 8 remains open and the gate still reports it unstated.**
