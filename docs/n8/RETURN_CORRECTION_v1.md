# Lemma C: the return correction measured at order 8, and what it costs the ladder argument

2026-09-17. `LADDER_BOUND_v1.md` §4 names three lemmas for the ladder argument and leaves **Lemma C**,
a bound on the return correction, open. This document measures that correction at order 8 and
**corrects §4's figure for it**. The measurement was already on disk when v1 was written — the beam run
finished at 18:33 on 2026-09-16, four hours after the document — so this is a reading of an existing
artefact, not a new computation.

**Order 8 is not closed by anything here, and nothing here refutes the ladder structure.** What changes
is the size of the gap Lemma C has to close: §4 estimated it at 4% of a wide margin; it is in fact the
entire margin.

Artefacts: `experiments/n8/ladder_return_beam_w2500_v1.out` (the beam run),
`experiments/n8/ladder_cap_word_check_v1.py` / `.out` (this document's own re-derivation, independent
of the beam and of the code path that produced it).

---

## 1. What the beam run found  `[VERIFIED — exact rational arithmetic]`

At order 8, ratio bound `S = 8`, the beam (width 2500, depth 14) reports `max R = 7` — **exactly the cap
`n − 1`** — on the 14-move word

    (1,1) (2,1) (3,1) (4,1) (5,1) (6,1) (3,2) (4,2) (1,4) (5,2) (3,3) (2,4) (6,2) (1,6)

Re-derived here prefix by prefix from `order_n_certificate_v1.py`'s own LPs:

| len | move | max τ | min u | R |
|---|---|---|---|---|
| 1 | (1,1) | 1/8 | 7 | 9/7 = 1.2857 |
| 2 | (2,1) | 1/8 | 49/9 | 81/49 = 1.6531 |
| 3 | (3,1) | 1/8 | 343/81 | 729/343 = 2.1254 |
| 4 | (4,1) | 1/8 | 2401/729 | 6561/2401 = 2.7326 |
| 5 | (5,1) | 1/8 | 16807/6561 | 59049/16807 = 3.5134 |
| 6 | (6,1) | 1/8 | 117649/59049 | 531441/117649 = 4.5172 |
| 7 | (3,2) | 1/8 | 343/81 | 1377/343 = 4.0146 |
| 8 | (4,2) | 1/8 | 1715/459 | 7803/1715 = 4.5499 |
| 9 | (1,4) | 13/236 | 7 | 33/7 = 4.7143 |
| 10 | (5,2) | 13/236 | 35/11 | 187/35 = 5.3429 |
| 11 | (3,3) | 71/2207 | 805/187 | 935/161 = 5.8075 |
| 12 | (2,4) | 71/2207 | 49/9 | 297/49 = 6.0612 |
| 13 | (6,2) | 71/2207 | 245/99 | 1683/245 = 6.8694 |
| **14** | **(1,6)** | **71/2207** | **7** | **7 = 7.0000** |

Two things this table settles, and they are the reason the word counts:

- **Every prefix is realisable**: `max τ > 0` throughout, down to `71/2207` at the end. This is not a
  closed-relaxation artefact of the kind §2 of `ORDER5_CERTIFICATE_v2` disposed of — that word carried
  `max τ = 0` exactly and was discarded. This one does not.
- **Every proper prefix is below the cap.** So the word is a legitimate *first exceedance* candidate in
  the sense of `ORDER5_CERTIFICATE_v2` §1 — precisely the object the cap argument quantifies over, not
  a word that wandered past the cap earlier and kept going.

**Lemma A is confirmed on the way.** Rungs 1–6 are `7, 49/9, 343/81, 2401/729, 16807/6561, 117649/59049`
— the closed form `(n−1)·((n−1)/(n+1))^(k−1)` to the last digit, and `R` at depth 6 is the ladder value
`4.5172` exactly. §2 of `LADDER_BOUND_v1` reproduces here independently. It remains `[EMPIRICAL]`.

## 2. Which side of the boundary  `[VERIFIED]`

The value lands exactly on the threshold, so the standing rule applies: say which side, explicitly.

Minimising the final reading subject to `τ ≥ ε` rather than on the `τ = 0` face gives `min u = 7 + 8ε`
exactly:

| τ ≥ | min u | R | R < 7 |
|---|---|---|---|
| 0 | 7 | 7.0000000 | no |
| 1/10⁶ | 875001/125000 | 6.9999920 | yes |
| 1/1000 | 876/125 | 6.9920091 | yes |
| 1/100 | 177/25 | 6.9209040 | yes |

So `R = 49/(7 + 8ε) < 7` for every `ε > 0`. **The supremum is not attained.** Every strictly realisable
configuration of this word has `R < 7`; `R → 7` only as the margin vanishes. The cascade, on this word,
does not *reach* the cap.

That is the favourable side, and it is worth being exact about how little it buys. It rescues the
pointwise statement and nothing else. What order 5 had was a **uniform** gap — `sup R = 31/9 < 4`, flat
across every ratio bound from 10 to 26 — and any argument that consumes a gap (iterating, bounding step
counts, absorbing a later error term) needs the uniform version. At order 8 the uniform gap is zero.

## 3. What this corrects, and what it does not

`LADDER_BOUND_v1` §4 item 2 reads: *"at order 8, `4.5172 → 4.7143` (+4%). Both stay well under their
caps."* That is a **depth-7 reading** — it is the value in the beam's own depth-7 row. The run continued
for another 6000 seconds. At depth 14 the correction is `7/4.5172 = 1.5496×`, and §4's own next line,
*"there is no bound on this correction"*, is the one that survives.

Restating the corrected position in the terms §4 set up:

| | `LADDER_BOUND_v1` §4 | measured, depth 14 |
|---|---|---|
| order 5 correction | `27/8 → 31/9`, +2%, margin 0.625, consumed 0.07 | unchanged (that run was exhaustive) |
| order 8 correction | `4.5172 → 4.7143`, +4% | `4.5172 → 7`, **×1.5496 — the whole margin** |
| the ratio a proof must control | 0.07 / 0.625 at order 5 | 1.0 at order 8 |

**Not refuted:** the ladder structure, Lemma A's closed form, Lemma B, the order-5 certificate, or the
claim that order 8 has more room than order 5 in the sense §3 of v1 meant it (the ladder value sits
further below the cap). **Refuted:** that the measured correction at order 8 is small, and with it the
reading of §4 on which Lemma C looks like a tightening of a comfortable inequality.

## 4. The consequence for the exhaustive run  `[the operational point]`

A complete order-8 enumeration at `S = 8` was launched on 2026-09-16 and abandoned at length 5. If it is
relaunched, it will return **NOT PROVED**, and the reason is now known in advance rather than after
2.4 hours: the enumeration takes a maximum over realisable words, a realisable word attains `7`, and the
script's own verdict line tests `best < CAP`. Beam search is heuristic and gives a *lower* bound on that
maximum, which is the direction that settles this — the exhaustive run cannot come in below what the
beam already found.

So the order-5 instrument does not transfer to order 8 as it stands. Three ways forward, stated so they
can be chosen between rather than drifted into:

1. **Tighten the relaxation.** The word LPs drop two necessary conditions — *the setter has the latest
   opening* and *the others are clear* (`ORDER5_CERTIFICATE_v2` §1). The bound is therefore an upper
   bound over a superset, and `sup R = 7` may be a fact about the superset alone. Restoring either
   condition is the first thing that could push the value back below the cap. **This is the test with
   the best ratio of information to cost**, and §5 is why it has to be run rather than assumed.
2. **A different cap.** `n − 1` is far above the ladder value `4.5172` and, per `LADDER_BOUND_v1` §1,
   that slackness is what makes the enumeration prune nothing. A cap nearer the truth would prune —
   but it has to be earned from the reduction, not chosen to fit.
3. **Lemma C directly**, as a bound on returns rather than a measurement of them. §4 of v1 already says
   no bound exists. What is new is that any such bound must be tight at the boundary at order 8, so a
   slack argument will not do.

## 5. One link in §1 of `LADDER_BOUND_v1` has no artefact I can find  `[flag, not a finding]`

v1 §1 states: *"Taking each LP-realisable word's own witness readings and running the actual cascade —
latest-next-opening rule and all — reproduced the claimed word in 100% of cases at every length
tested."* The scripts v1 names are `order8_tree_census_v1.py` and `order_n_certificate_v1.py`; neither
implements a cascade replay, and a search of `experiments/` for one found nothing that replays order-8
LP words. The check may well have been run inline without being saved.

Stating this conditionally: **no artefact for it was located**, which is not the same as its not having
been run. It matters here specifically, because the faithfulness of the word space is exactly what
decides whether the depth-14 word is a real cascade or a relaxation artefact — that is, whether §4's
route 1 is a repair or a dead end. The depth-14 word is longer than anything v1's census reached, so it
would be outside the tested range in any case.

**The check to run:** take the `τ = 71/2207` witness readings for the 14-move word, run the actual
cascade with the latest-next-opening rule, and see whether it produces that word. That answers route 1
for the one word that matters, and it is cheap.
