# What it actually takes to prove Existence — the chain, step by step, each link checked

2026-09-17, at the owner's instruction. Every link below is either **quoted from a Lean theorem in our
own tree**, **quoted from the manuscript with a line reference**, or marked **OPEN**. Each carries its
`PROVENANCE_MAP_v1.md` gate result. Where a step re-derives something the project already owns, it says
so — a re-derivation is not a finding.

**Nothing here closes Existence.** The value of the map is that it shows precisely which link is open
and what the known obstruction to it is.

---

## Link 0 — the scope  `[PROVED — Lean, axiom-clean]`

`MomentIterationN.lonely_iff_run_ends` (`LRC/Cascade/Iteration.lean:624`):

    (∃ s, 0 < s ∧ Lonely n ds s)  ↔  ∃ N, move n ds ((move n ds)^[N] (1/(n*m))) = (move n ds)^[N] (1/(n*m))

**The subject has some lonely instant ⟺ the cascade reaches a fixed point.** An `↔`, both directions,
in our own tree.

Three consequences, and they should be stated before any work is planned:

- **Existence is exactly LRC(8) for that runner.** Not a weaker stepping stone. §9 says as much; this
  theorem is why.
- **§6.6's "Existence needs some lonely instant, not the cascade's" is this theorem**, left-to-right. Any
  lonely instant anywhere forces the cascade to stop.
- **So no reformulation makes it easier.** What the framework buys is not a reduction in difficulty; it
  is that the object is *determinate* — one path per arrangement, each step arithmetic — instead of a
  search over instants. That is a change of handle, not of weight.

*Gate: G1 pass, G2 pass (target is §6.7 verbatim), G4 — target **is** Existence, equivalence not merely
sufficiency.*

## Link 1 — failure needs unbounded instants  `[PROVED — Lean]`

`exists_fixed_of_capped` (`LRC/Cascade/SmallOrders.lean:452`): if `∀ N, move^[N] b ≤ U` then a fixed
point exists. Contrapositive: **no fixed point ⟹ the instants are unbounded ⟹ `R = ∞`.**

*Gate: G3 — the bound is `U`, an instant. Not a lap boundary, not a window. Pass.*

## Link 2 — `R` is a product of step factors  `[PROVED — §6.2; VERIFIED exactly]`

§6.2: a step multiplies **every** reading by one factor `λ_j = (8N_j+1)/s_{x_j}`, the setter's reading
`s_{x_j} ∈ (8N_j−1, 8N_j+1)`, the setter landing exactly on `8N_j+1`. With `R = d_min/D_final`:

> `R = ∏_j λ_j`,  `1 < λ_j ≤ (8N_j+1)/(8N_j−1) ≤ 9/7`

Verified exactly on both named climbs (`scale_recursion_check_v1`, `r_bounded_seeded_v1`): the product
equals `R`, 6000/6000 agreement between the time and scale coordinates.

**So: Existence ⟺ `∏λ_j` is a finite product.** This is the target — *not* `∏λ_j < n − 1`, which
`RETURN_CORRECTION_v3` refutes outright (`R = 10.31` at `S = 7.467`).

## Link 3 — how the count and the size constrain each other  `[re-derivation of a known wall]`

Writing readings at step `j` as `σ_i·R_j` with `σ_i = d_i/d_min` the original readings:

- the setter's reading `σ_{x_j}R_j ∈ (8N_j−1, 8N_j+1)`, so `8N_j ≳ R_j`, hence
  **`λ_j − 1 ≤ 2/(8N_j−1)`** and `R_{j+1} ≲ R_j + 2`: `R` grows by at most about 2 per step;
- a runner's reading only increases (scales only decrease), so **each runner sets at most once per `N`
  value**, giving at most about `σ_i·R/8` settings for runner `i` up to `R`;
- combining, with `M` steps: `M ≲ (R/8)·Σσ_i` and `R ≲ R_0 + 2M`, so `M(1 − Σσ_i/4) ≲ R_0Σσ_i/8`.

**This is bounded only when `Σσ_i < 4`, and `Σσ_i ≥ 7` always at order 8.** So the counting closes
nothing here.

**This is not new and must not be reported as a finding.** It is the wall already recorded at
`ORDER5_GROWTH_v2` §5 — *"Charge every setting its worst case, `term ≤ 2/s` … `A ≤ (2k/n)A + 2Σ1/s_x`"* —
which reproduces §8's condition **`n > 2k`**. With `k = 7` differences that wants `n > 14`; we have
`n = 8`. §6.7's *"the number of moves is at most `(7/8)·S·R + 7`"* is the same relation. Re-deriving it
independently confirms the map is on the right object and confirms nothing else.

*Gate: G5 — the only premise is that scales decrease and readings increase, both §6.2. G6 — checked
against `framework_cases_v1.py`: the 23-step case has `Σσ_i = 59/2 = 29.5`, `R = 165/16`, `M = 23`; the counting bound gives `M ≲ (R/8)Σσ_i = 38.0` and the growth bound `R ≲ R_0 + 2M = 47` against the actual `10.31` — both hold, both loose, which is the wall.*

## Link 4 — the open link, stated exactly  `[OPEN]`

The worst-case charge `2/s` per step is what fails. The true per-step term is
`(2 − n·δ_j)/s_j` (`ORDER5_GROWTH_v2` §2), where `δ_j ∈ (0, 2/n)` is the setter's **depth** — how far
into its zone it sat. Charging `δ_j = 0` every step is what produces `n > 2k`.

> **The open statement.** Show the depths `δ_j` cannot all be near zero along a cascade — equivalently,
> that the setters cannot repeatedly enter their zones at the very edge — for enough steps to let
> `∏λ_j` diverge.

This is where the framework's existing machinery bears, and it should be **read before anything is
invented** (§5 of the project rules, and the source-first rule):

| lemma | where | what it forbids |
|---|---|---|
| `no_four_alternation` | `SmallOrders.lean:549`, needs `4 ≤ n` | two runners alternating as setters across four openings |
| `no_return_after_few_faster` | `FourDifferences.lean:113`, needs `2g+2 ≤ n` — so `g ≤ 3` at `n = 8` | a runner returning across `g` faster moves |
| `nearest_reading_recurrence` | `SmallOrders.lean:638` | bounds the nearest runner's reading along the run |

Each is a **return** restriction, and returns are exactly what a divergent product needs: a runner must
come back into the way over and over. `no_return_after_few_faster` at `n = 8` covers `g ≤ 3`; the gap is
returns across **four or more** faster moves.

## Link 5 — the two directions that are actually open to work

1. **Extend the return restrictions past `g = 3`.** `no_return_after_few_faster` needs `2g + 2 ≤ n`; at
   `n = 8` that is `g ≤ 3`. Whether the hypothesis is tight, or an artefact of how it is proved, is a
   question about an existing proof — readable, not speculative. **Read the proof first.**
2. **More families.** §4.5 and §6.9 are proved; the eighth-family line is this. Families do not close
   Existence but they are the only thing on the board that has been closing.

**What not to do, with the reason:** do not open a route whose target is `R < c` for any constant `c`.
G3 catches every one of them — `R = n·u`, so any such bound is a statement about *when* the instant
falls, and §1.3 says no bound on when is a requirement of any result. The cap, the ladder, and Lemma
A/B/C were all this route.

## Link 6 — what would settle it in the other direction

A single arrangement whose cascade provably never stops would refute Existence, and by Link 0 would
refute LRC(8). Nothing suggests one exists: §6.7's exhaustive sweep is 18,564,316 arrangements and
148,514,528 runner-instances with a lonely instant for every runner. **That sweep is in the pinned frame
`v_1 = 0`**, which §6A's first row does not describe — the manuscript states this itself and gives the
argument that carries the counts across (a common shift leaves every difference unchanged).

## Appendix — the gate results in one line each

| link | G1 | G2 | G3 | G4 | G5 | G6 | G7 |
|---|---|---|---|---|---|---|---|
| 0 scope | ✓ | ✓ | n/a | ✓ equivalence | ✓ | n/a | ✓ |
| 1 capped ⟹ stops | ✓ | ✓ | ✓ bound is an instant | ✓ | ✓ | n/a | ✓ |
| 2 `R = ∏λ` | ✓ | ✓ | n/a | ✓ | ✓ scales decrease only | ✓ 4/4 named | ✓ forward |
| 3 counting | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ consistent on the 23-step case | ✓ |
| 4 depths | ✓ | ✓ | ✓ `δ` is §6.2's | ✓ | — OPEN | — | ✓ |
