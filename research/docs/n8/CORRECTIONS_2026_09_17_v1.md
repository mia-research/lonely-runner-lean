# Corrections: four documents of 2026-09-17 assert framings refuted later the same day

Written after a hedge audit. Supersedes the named sections; the documents are kept as the record.
**Nothing here is new mathematics** — it is the correction backlog, discharged in one place instead of
being offered repeatedly while new work was added on top.

---

## 1. The covering / union-bound framing  `[REFUTED — register items 4, 27]`

`n > 2k` reduces to `k·(2/n) < 1`: a runner in the way occupies an arc of width `2/n`, so the condition
says **the k arcs cannot cover the circle**. That is a union bound — register item 4 (covering, NOT
APPLICABLE) and item 27 (union bounds, NOT APPLICABLE); §6.1 requires proofs be pointwise. At
`n = 8, k = 7` the total width is `7/4`, so the arcs cover 1.75 times over and the route was never going
to reach us.

**Affected, and wrong in each:**

| document | section | what it says | correction |
|---|---|---|---|
| `EXISTENCE_ARITHMETIC_v1` | §3 | frames `n > 2k` as the wall to beat | it is a union bound; beating it is not our obligation |
| `EXISTENCE_ARITHMETIC_v1` | §5 item 1 | "bound the `N = 1` steps" as the next step | that is the covering repair — showing the arcs overlap |
| `EXISTENCE_MAP_v1` | Link 3 | derives the same wall, marked "re-derivation" | correct as arithmetic, wrong as a description of our obstruction |
| `EXISTENCE_MAP_v1` | Link 4 | "show the depths `δ_j` cannot all be near zero" as **the** open statement | a repair to the union bound, not the framework's obligation |
| `WHAT_IS_STOPPING_IT_v1` | §1, §3, §4, §5 | the whole answer built on "every bound charges `δ = 0` ⇒ `n > 2k`" | same import throughout |

**What replaces it.** The framework's instrument is the clearing test — exhibit `(D, a)` with
`D ≤ (a·e mod nD) ≤ (n−1)D` for every difference, an integer comparison, pointwise. In flank
coordinates: find an opening at which every ratio's residue lands in the clear band.

## 2. The `j ≥ 4` framing  `[REFUTED — by measurement, owner's challenge]`

Claimed: the open case is flanks with four or more non-integer ratios, "85% of arrangements".

Measured (`flank_what_blocks_v1`, 6,000 arrangements): live flanks fail at **every** `j` from 2 up —
`{2: 13, 3: 44, 4: 147, 5: 285, 6: 561}`. So `j` does not predict failure. `j ≥ 4` is §6.9's description
of **where Props 6.10–6.11 stop applying**, and it was converted into "where the difficulty is". The
failures at `j = 2, 3` also refute the claim, made without checking, that those propositions cover `j ≤ 3`.

And **0 of 6,000 arrangements had no flank with a lonely opening** — individual flanks fail routinely
(2.6% of live ones), all seven never did.

| document | section | correction |
|---|---|---|
| `DEEP_REVIEW_2026_09_17_v1` | §5 | the table and the "85%" describe lemma coverage, not difficulty |
| `WHAT_IS_STOPPING_IT_v1` | §5 | same |

**What replaces it.** §6.9's own second open item: *"not every flank of a runner can be shadowed at
once, which is Existence read at flanks"* — a statement about the arrangement, not a per-flank count.

## 3. The hedge audit itself

`feedback_no_credibility_hedges` records that these words are a **diagnostic**, not a style fault: the
rule is to stub-test the adjacent claim, then delete the word, never delete only. Four occurrences across
29 files of 2026-09-17:

| where | adjacent claim | test | outcome |
|---|---|---|---|
| `EXISTENCE_ARITHMETIC_v1` §4 "the honest scope" | "§6.7's line **is** LRC(8) for the runner" | `lonely_iff_run_ends`, an `↔` in Lean | **claim holds**; the word sat beside §3/§5, which do not — §1 above |
| `RETURN_CORRECTION_v2` "genuinely returns" | "if some word exceeds 7, the nearest returns and the framing needs rework" | the named cases: nearest sets at steps 19 and 24, `R = 10.31` | **already fact, not hypothesis**; corrected in `v3` |
| `NATIVENESS_AUDIT_v2` "explains the infeasibility honestly" | "the word space is 7.25×10²⁶ **because** it is not the framework's object" | not measured — a causal claim asserted | **unverified**; the checkable part is that the cascade is deterministic (`move` is a function), so one arrangement has one path. The "because" is rhetoric and is withdrawn |
| `NO_RETURN_TIGHTNESS_v1` §2 "a genuine strengthening" | a `P`-dependent restatement strengthens the lemma | §3 of the same document: 0 extra returns excluded | **strengthens the lemma, not its reach** — say both, not "genuine" |

Three of four sat next to the backlog in §1–§2. The diagnostic worked; it was not acted on at the time.

## 4. What is not affected

The Lean work of 2026-09-17 (`class_killer_int`, `circDist_periodic_of_lattice`,
`lonely_opening_of_free_off_lattice`, `lonely_of_flank_unkillable`, `lonely_of_some_flank_unkillable`
and their `stops_` corollaries, gate 189/189 axiom-clean); `RETURN_CORRECTION_v3`;
`NATIVENESS_AUDIT_v3`; `PROVENANCE_MAP_v1`; `NO_RETURN_TIGHTNESS_v1` §§1, 3–5; `DEEP_REVIEW_v1` §§1–4,
6–8; and every measurement artefact. None of those rests on §1 or §2's framings.
