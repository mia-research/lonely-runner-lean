# The n=8 dropped-unit leaf, closed for representative speeds

2026-09-07. Full proof and per-cell certificates: `reports/n8_dropped_unit.md`
(806 lines); scripts `experiments/n8/du2_*.py`. Independently produced, then
spot-checked here. Companion to `UNITCOMPLETE_THEOREM_v1.md` and
`TWIN_CASE_THEOREM_v1.md`, which close the other leaf.

## Theorem  `[PROVED]`

`E` = 7 distinct positive integers containing a multiple of 8, `|R_non| = 5` with at
least one absent residue class a **unit**, representative speeds (`e = ρ_e`). Then a
loneliness witness exists. No bound on `m₁, m₂`; `gcd(E) = 1` is not used.

## Why it closes cleanly: the union bound settles all 18 pairs

The gap lemma is never needed here. Exact safe measures of the five non-divisible
runners, verified independently:

- **13 of the 18** absent-pairs give `S = [0,1)` — no `x` is blocked at all;
- four more give `5/6, 5/6, 5/6, 13/15`;
- the extremal case is absent `(3,4)`, `E_non = {1,2,5,6,7}`, with `|S| = 19/35`.

`min |S| = 19/35 ≈ 0.5429 > 1/2 > |B_{m₁} ∪ B_{m₂}|` by the B-lemma, surplus `3/70`.
Integrality then yields an integer `b`, and any uncovered `r` gives `k = b + rL`.

## Your boundary/averaging warning, paying off exactly once  `[PROVED]`

Requirement (ii) — *track every uncovered residue, never a single representative one* —
is load-bearing at precisely one place, and without it this leaf fails.

Window `W₂ = [3/7, 4/7)` of the `(3,4)` case has **no residue valid throughout**:

    x ∈ [3/7, 1/2)  →  uncovered {2}
    x ∈ [1/2, 4/7)  →  uncovered {5}

*Verified here.* A tracker following one residue drops `W₂` entirely, reports
`|S| = 2/5 < 1/2`, and the union bound then **fails** — the leaf would look open. This
is the same failure mode that produced the false cover at `(e′,m) = (11,4)` in the twin
case, and it is exactly the hazard in preferring an averaged or representative value to
the true entry-and-exit behaviour of an interval.

## Controls, and the one that shows the test is not forced

- **Boundary exactness:** 0 interior breakpoints, 0 entry/exit floor mismatches, 0
  entry-vs-exit covered-set differences across 246 cells — asserted inside the
  certificate generator so it aborts on failure. No cell centre is ever evaluated.
- **The union-bound test is not vacuous.** Over all 21 absent-pairs exactly one fails
  `|S| > 1/2`: the Unit-Complete pair `(2,6)` with `|S| = 5/14`. So the criterion
  discriminates, and it discriminates precisely at the case that needed Lemma D.
- **Independent reproduction of my own theorem.** The same code recomputes
  `UNITCOMPLETE_THEOREM_v1.md` §4 exactly — `22/35`, `5/14`, `6/7`. *Confirmed here.*
- Independent integer recount of `|S|` over `b ∈ [0,L)` with no `Fraction` arithmetic:
  agrees 18/18. Two independent `B_m` implementations agree for `m ≤ 30`.
- End-to-end: 1638 tuples (18 pairs × all `m₁ < m₂ ≤ 14`), 0 failures, minimum slack
  exactly `1/8`.
- **Inclusion direction measured:** 30 910 floor-built witnesses against 31 428 true
  witnesses, and **0** floor-but-not-true — the floor-built bad set is a superset, so
  `S` is conservative, as required.

## The refuted manuscript routes, resolved

`Lemma 11.3c`'s counterexample `E = (1,2,3,4,6,8,24)` **lies in this leaf**, and the
direct argument delivers a witness where the lemma failed: `b = 3`, `r = 1`, `k = 27`.
*Verified here:* `min_e ‖e·k/(8L)‖ = 1/8` exactly. `Lemma 11.3a′` Case III's
`E = (1,2,3,4,5,6,64)` is **outside** this leaf (six classes present, `|E_div| = 1`).

## Without representativeness

Every structural ingredient transfers verbatim — bridge, pair rule, `B_m`, B-lemma,
integrality, boundary discipline. Only the value of `|S|` must be recomputed. Sweeps:
56 250 exhaustive (`q ≤ 4`), 16 807 (`q ≤ 6`, absent `(1,7)`), 7 000 random to `q ≤ 40`,
plus 67 500 end-to-end tuples — **0 failures**, with

    min |S| = 1/2 exactly, at E_non = {2,3,5,12,14}, where S = {x : ‖x‖ < 1/4}

*(verified here).* At `|S| = 1/2` the crude union bound is exhausted and the
**sharpened** B-lemma is what closes it; the margin is attained at
`E = {2,3,5,12,14,8,48}`, surplus `1/24 = gcd(1,6)/24`.

> **(NR)** `|S| ≥ 1/2` for every non-representative `E_non` in this leaf.
> `[EMPIRICAL / VERIFIED-INSTANCE — not proved]`

**And it cannot be proved in the obvious generality.** The companion Unit-Complete leaf
has `|S| = 5/14` at `ρ₀ = 4`, so any argument establishing `|S| ≥ 1/2` for *all*
five-class `E_non` is necessarily wrong. The true statement must exclude that tuple.
Two natural strengthenings were tested and are **false**: the quarter-neighbourhood
containment, and any fixed-residue union bound.

## Grades

The theorem and all measures: **PROVED**. (NR): **OPEN**, and stated with its own
counterexample-to-over-generalisation attached.
