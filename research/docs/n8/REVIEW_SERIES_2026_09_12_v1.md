# Review — the n = 8 AP/grid exploration, 2026-09-10 to 2026-09-12

2026-09-12. Independent review of the 94 notes and 98 scripts committed in the window
(103 commits, `7ecb1f1`..`d2a6309`). Scope: provenance, grade discipline, and reproduction of
the headline figures. New artifact: `experiments/n8/ok_method_control_v1.py`.

Findings are ordered by consequence. Every defect claim below quotes the sentence it is about,
with file and line.

---

## 1. What reproduced

Four checks were run against the series rather than read out of it.

**(a) The three-way method control reproduces.** `METHODS_AUDIT_2026_09_12` §2 records
`[VERIFIED]` — 495 primitive constraint sets, A vs B vs C, 0 disagreements, 0 BSM cell
anomalies — and names no script (see §2 below). The three implementations were extracted from
`resolution_law.py` (A), `bsm_transit.py` (B) and `bsm_fast.py` (C) and run against each other
over a fresh population:

| comparison | disagreements |
|---|---|
| A vs B | 0 |
| B vs C | 0 |
| A vs C | 0 |
| BSM cell anomalies | 0 |

`[VERIFIED — 495 primitive sets, sizes 2/3/5/7, spans 10..70, seed 20260912]`
Artifact: `experiments/n8/ok_method_control_v1.py`. The population landing on 495 is a
coincidence of the generator, not a reproduction of the original 495 — **the law reproduces,
the tally is not recoverable.**

**(b) The grid-distance table reproduces, including the entry I first thought was wrong.**
An independent run over 5,716 distinct reduced configurations gave min count 4 at `k = 0` and
2 at `k = 1,2,3`, matching `AUDIT_2026_09_12` §2, but **4** at `k = 4` where the table says 2.
A sampled minimum can only overshoot, so this was searched rather than reported: exhaustive
over `[0..17]` (19,440 distinct reduced configurations) produces `k = 4`, min count **2**, at
`(0,1,3,4,9,11,12,16)`. The published entry is correct.

**(c) The floor holds in the only regime where parity does not already force it.**
`PROOF_CANDIDATE_v3` §2 (P1) proves the count is odd ⟺ every `d` is odd, so `count = 1`
survives only when all seven differences are odd. That regime was tested directly: 63,431
all-odd primitive difference sets (odd values ≤ 39), **minimum count 9**, and every count odd —
which also re-derives P1 mechanically. `[VERIFIED — 63,431 sets, odd values ≤ 39]`
This closes, empirically and at that scope, the open item at
`WN_grid_distance_2026_09_12.md:73`.

**(d) The proof line is reported correctly.** `PROOF_CANDIDATE_v3` §6 grades P1–P4 `[PROVED]`
and §4's lemma `[OPEN]`, "the only step between this chain and a proof";
`MEASURE_LEMMA_ATTEMPT_v2` §5 then retracts §4 as viable and tags `[NOT PROVED]` n = 8. The
terminal record closes "**n = 8 is not proved. Nothing above bounds any count below.**" That
chain is intact and self-consistent.

---

## 2. The structural defect: 36 documents assert verification with no artifact

`METHODS_AUDIT_2026_09_12` is titled "exactness and BSM conformance **across the series**" and
its §1 tabulates which implementation produced which result. That mapping cannot be
reconstructed, because **36 of the 94 notes carry a `[VERIFIED]` or `[EMPIRICAL]` tag and name
no script** — 100+ tags in total. Among them are the series' load-bearing documents:

| note | tags | what rests on it |
|---|---|---|
| `METHODS_AUDIT_2026_09_12` §2 | `[VERIFIED]` | the exactness claim for the whole series |
| `AUDIT_2026_09_12` §4 | `[VERIFIED — exhaustive]` | 1.6M-instance collision retest |
| `AUDIT_2026_09_12` §1 | `[VERIFIED — constructed]` | the entire `k = 6` row |
| `WB_interaction_structure` | 9 tags | observations 31–36 |
| `AP_GRID_SUMMARY_v1` | 11 tags | the popcorn result |
| `WN_grid_shape_space` | 4 tags | observations 10, 11 |

This is the `COMPENDIUM_v1` failure mode: a document standing as its own witness. It is a
**provenance** defect, not a correctness one — §1(a) above shows the §2 control's claim is
substantively right. But nothing in the series could have shown that, and the check that
settles it had to be written from scratch.

The reasoning notes in that count (`PROOF_CANDIDATE_*`, `LOCALITY_v1`, `FRAMEWORK_REASONING_v1`,
`MECHANISM_REVIEW_v1`) legitimately run no code and are not at issue.

---

## 3. Scope qualifiers lost at the consolidation step

`OBSERVATIONS_2026_09_12` retains **all five** open items from `AUDIT_2026_09_12` §5 as its
own items 40–44. Frontier retention is clean — the H3→H4 liquidation did not recur.

What did not survive is the scope on three observed items. In each case the qualifier is
present upstream and absent in the banked record:

| # | source | banked |
|---|---|---|
| 10 | "Enumerating `q ∈ {0,1,2}⁸` **normalised to `min q = 0`** gives 6,305 grid shapes" (`WN_grid_shape_space:13`) | "Exhaustive over 6,305 grid shapes `q ∈ {0,1,2}⁸`" (`OBSERVATIONS:10`) |
| 21 | "reserve conserved under a move \| 3,657 runners, **sampled** \| moderate" (`AUDIT:51`) | "Reserve across a move, for 3,657 runners that kept the spine: up 30.4%…" (`OBSERVATIONS:21`) |
| 33 | "max-S coalition usually ≠ spine set \| **exhaustive `[0..14]`**, 2,032 cases" (`AUDIT:53`) | "Of 2,032 configs with `k ≥ 2`…" (`OBSERVATIONS:33`) |

Item 10 matters most: as banked it names a population of 6,561, and the stated count is 6,305.
The difference is exactly `3⁸ − 2⁸ = 256`, which is the normalisation — recoverable only by
arithmetic on a figure the reader is not told is normalised.

**One open item was dropped outright.** `WN_grid_distance_2026_09_12.md:73` flags:

> "Whether the `k = 0` and `k = 5` floors of 4 are stable in larger boxes; `k = 5` has only 56
> configurations here."

`AWAY_FROM_GRID_v1.md:42` puts the same row at 106 configurations. Neither `AUDIT` §5 nor
`OBSERVATIONS`' Open list carries it, and `OBSERVATIONS` item 16 presents the `k = 5` entry
flat in the "Complete map", beside entries backed by hundreds of thousands of instances.
Independent exhaustive search over `[0..17]` reaches min count **6** at `k = 5`, not 4 — no
contradiction, since high `k` forces the minimiser outside that box, but it does confirm the
entry is not checkable at accessible scale. The `k = 5` and `k = 0` cells of the complete map
rest on ~10³ times less evidence than their neighbours and should carry that on the table.

---

## 4. The popcorn constant: right number, unreproducible label, over-general explanation

`AP_GRID_SUMMARY_v1` §2 reports the measure at `r1 = 1` as **0** and at `r1 = 1.001` as
**0.13021**, "Varying r1 continuously from the AP".

Read as written — the runner at speed 1 in the AP `{0,…,7}`, measuring its own good set — the
values are **0.0875** and **0.12693**. The published figures reproduce exactly under a
different reading: the varied runner is an **endpoint** of the AP (speed 7), and the quantity
is that moved runner's own good-set measure. Then `r1 = 7` gives 0 and `r1 = 7.001` gives
**0.13021**, to five figures. The number is right; the note does not contain the specification
needed to get it.

The explanation attached to it does not survive its own test. `AP_GRID_SUMMARY_v1:53`:

> "The generic value is **0.1302**, not `(3/4)⁷ = 0.13348`; the seven differences of eight
> speeds are not fully independent."

Any seven distinct positive integers are the difference set of eight speeds (take `v_i = 0`).
Over 60 such generic sets drawn from `[900, 4000]` the measure has **mean 0.13347, median
0.13346** — `(3/4)⁷ = 0.133484` to four figures. The deficit to 0.1302 is a property of the
AP-with-one-endpoint-moved family, where six of the seven differences stay at the consecutive
integers 1..6; it is not a property of eight speeds. `AP_GRID_SUMMARY_v1` §8 already lists
"whether the generic measure 0.1302 has a closed form" as untested — the sentence at :53
answers it in passing, and answers it too widely.

---

## 5. Smaller items

**Notation collision in the banked record.** `OBSERVATIONS` defines `k` as grid distance, then
uses `k` as the eighth-lattice numerator in item 3 ("`t = k/8` requires `dk ≢ 0 mod 8`, so
`k=4` (all `d` odd) ⟹ `k=2,6`"). The mathematics is right; the two meanings collide inside a
document written to be the reference.

**Nine self-certifying words**, each a standing audit trigger. Load-bearing instances:
`WHERE_THE_PROOF_IS_v2:92` ("a genuinely strong bound" — attached to a numerical claim),
`DENOMINATOR_TOWER_v1:39` ("genuinely box-free", tagged `[PROVED]`), and
`COLLAPSE_v2_NULL_v1:35` ("the decisive test"). `CASE_TREE_AUDIT_v1:89` ("genuinely the
hardest") is also a difficulty verdict.

**Three of the nine design retractions have no `[RETRACTED]` tag at origin.** "the adversary
chooses halves", "crashed runners land on sixteenths" and "worst permutation reconstitutes an
AP" appear in `METHODS_AUDIT` §4's table, but their source notes were corrected in place
(`f9ccb56`, `063c68d`) rather than superseded. Nine window notes were revised after commit.
The retraction lines inside the revised files preserve the record, so nothing is lost — but a
tag grep does not find them, and a tag grep is how the other six are found.

---

## 6. What this review did not cover

- The 09-10/09-11 half of the window (`U_REFORMULATION`, `CASE2_ATTACK`, `ODD_RUNNER_COLLAPSE`,
  `INTERFERENCE`, `TILING_AND_BLOCKS`, and the `α` line) was audited only for grade tags and
  retraction hygiene, not re-derived. The reproduction work in §1 is confined to the AP/grid
  mapping series.
- No citation was checked against its source; nothing in the window rests on a new citation.
- `k = 6` remains reached by construction only. A second generator was not run here either, so
  `OBSERVATIONS` item 44 stands open as written.

## 7. Status

`[VERIFIED — new artifact]` §1(a)'s three-way control, 495 sets.
`[VERIFIED — exhaustive, [0..17]]` §1(b)'s `k = 4` entry, and the `k = 5` figure in §3.
`[VERIFIED — 63,431 all-odd sets, values ≤ 39]` §1(c)'s count-1 regime.
`[DEFECT — provenance]` §2, 36 notes.
`[DEFECT — scope]` §3, three items plus one dropped open item.
`[DEFECT — reproducibility]` §4's parametrisation label.
`[RETRACTED]` `AP_GRID_SUMMARY_v1:53`'s explanation of the 0.1302 deficit, as stated for
eight speeds generally. The measurement itself stands.

**n = 8 is not proved, and nothing in this review bears on that.**
