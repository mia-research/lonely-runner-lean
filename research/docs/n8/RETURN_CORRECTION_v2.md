# Lemma C at order 8: the correction is the whole margin, the extremal word is a real cascade, and the uniform bound is false

2026-09-17. Supersedes `RETURN_CORRECTION_v1.md` (written earlier the same day). Everything v1
established is carried forward; **two of its sections are overtaken by measurement** and are marked
`[OVERTAKEN]` where they appear — v1 §4 route 1 and v1 §5. Both were flagged there as things to test;
they have now been tested, and the answers point the other way from what v1 expected.

Corrects `LADDER_BOUND_v1.md` §4, whose order-8 return-correction figure is a depth-7 reading.

Artefacts, all exact rational arithmetic:
`experiments/n8/ladder_return_beam_w2500_v1.out` (the beam run, from 2026-09-16),
`ladder_cap_word_check_v1.py` / `.out` (re-derivation and the boundary question),
`ladder_cap_word_replay_v1.py` / `.out` (the cascade replay),
`ladder_cap_word_extend_v1.py` / `.out` (terminality).

---

## 0. The finding in one paragraph

At order 8, ratio bound `S = 8`, there is a realisable word whose value is exactly the cap `n − 1 = 7`.
It is **not** a relaxation artefact: the actual cascade, run on witness readings from inside its own
polytope, reproduces it move for move, including at configurations with `R = 6.999992`. The cascade
**terminates lonely** at every witness, and the word admits no extension, so the cap is approached as a
terminal value and not crossed. Consequently **`sup R < n − 1` is false at order 8 for `S ≤ 8`** — the
statement the order-5 certificate proves, and the statement Lemma C was being asked to deliver. The
pointwise statement `R < n − 1` survives, holds at every strictly realisable configuration, and is what
Existence actually needs. Order 8 remains open; nothing here threatens Existence, and the cascade gate
still reports it unstated.

## 1. What the beam run found  `[VERIFIED]`  `[unchanged from v1]`

The beam (width 2500, depth 14) reports `max R = 7` — exactly the cap — on the 14-move word

    (1,1) (2,1) (3,1) (4,1) (5,1) (6,1) (3,2) (4,2) (1,4) (5,2) (3,3) (2,4) (6,2) (1,6)

Re-derived prefix by prefix from the certificate's own LPs:

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

Every prefix is realisable (`max τ > 0` throughout, down to `71/2207`) and every **proper** prefix is
below the cap, so the word is a legitimate *first exceedance* candidate in the sense of
`ORDER5_CERTIFICATE_v2` §1. It is not the closed-relaxation artefact that document's §2 disposed of —
that word carried `max τ = 0` exactly and was discarded; this one does not.

**Lemma A is confirmed on the way.** Rungs 1–6 are the closed form `(n−1)·((n−1)/(n+1))^(k−1)` to the
last digit, and `R` at depth 6 is the ladder value `4.5172` exactly. `LADDER_BOUND_v1` §2 reproduces
here independently. It remains `[EMPIRICAL]`.

## 2. Which side of the boundary  `[VERIFIED]`  `[unchanged from v1]`

The value lands exactly on the threshold, so the standing rule applies: say which side, explicitly.
Minimising the final reading subject to `τ ≥ ε` rather than on the `τ = 0` face gives `min u = 7 + 8ε`
exactly, hence `R = 49/(7 + 8ε) < 7` for every `ε > 0`.

**The supremum is not attained.** Every strictly realisable configuration has `R < 7`; `R → 7` only as
the margin vanishes. Keep the two statements apart, because the whole of §4 turns on the difference:

| statement | at order 5 | at order 8, `S ≤ 8` |
|---|---|---|
| pointwise `R < n − 1` | true | **true** |
| uniform `sup R < n − 1` | true (`31/9 < 4`, flat for `S` = 10…26) | **false** (`sup R = 7`) |

## 3. The extremal word is a real cascade  `[VERIFIED]`  `[OVERTAKES v1 §4 route 1 and v1 §5]`

v1 §5 flagged that `LADDER_BOUND_v1` §1's faithfulness claim named no artefact that implements a cascade
replay, and v1 §4 named "tighten the relaxation" as the highest-value next test on that basis: the word
LPs drop two necessary conditions — *the setter has the latest opening* and *the others are clear* — so
`sup R = 7` might have been a fact about the superset alone.

It is not. `ladder_cap_word_replay_v1.py` runs the actual cascade — threshold `1/n`, start at `t = 1/n`,
advance to the latest exit among the runners in the way — on witness readings taken from inside the
word's own polytope:

| witness | τ | R | cascade | reproduces the word |
|---|---|---|---|---|
| max-margin | 71/2207 | 49/8 = 6.1250 | LONELY after 14 steps, `t = 49/64` | **yes** |
| R-optimal, τ ≥ 1/100 | 1/100 | 6.9209 | LONELY after 14 steps | **yes** |
| R-optimal, τ ≥ 1/1000 | 1/1000 | 6.9920 | LONELY after 14 steps | **yes** |
| R-optimal, τ ≥ 1/10⁶ | 1/10⁶ | 6.999992 | LONELY after 14 steps | **yes** |

The R-optimal rows are the ones that carry the weight. Faithfulness at the max-margin witness alone
would not license the cap value, because the cap value lives at `τ → 0`; these show the word is
reproduced along the very sequence that drives `R` to 7.

**So route 1 is closed.** Restoring either dropped condition cannot push the value back below the cap,
because the configurations attaining values arbitrarily close to it already satisfy both.

**Two further facts, and they make the picture coherent rather than alarming.**

- **The word is terminal.** All 17 legal one-move extensions are unrealisable
  (`ladder_cap_word_extend_v1.out`). The cap is a terminal value, approached and not crossed — which
  matches the replay reporting LONELY, and means the finiteness framing of `ORDER5_GROWTH_v2` §4 is not
  disturbed.
- **The `τ = 0` corner degenerates.** At the exact corner (`u = 7, 49/9, 805/187, 119/31, 35/11, 119/47`)
  the cascade runs for **0 steps**: `u₁·t = 7/8` at the opening instant `t = 1/8`, so `circDist = 1/8`,
  which is *not* `< 1/8`. Zones are open, the first setter is clear, and the configuration is lonely
  immediately. The boundary point is not a counterexample to anything; it is not the word at all. This
  is the `4.125` phenomenon of `ORDER5_CERTIFICATE_v2` §2 recurring one level up, and it is the third
  result this convention has decided.

## 4. What this means for Lemma C  `[the operational point]`

`LADDER_BOUND_v1` §4 item 2 reads: *"at order 8, `4.5172 → 4.7143` (+4%). Both stay well under their
caps."* That is a **depth-7 reading** — the beam's own depth-7 row. The run continued for another 6000
seconds. At depth 14 the correction is `7/4.5172 = 1.5496×`, and §4's own next line, *"there is no bound
on this correction"*, is the one that survives.

| | `LADDER_BOUND_v1` §4 | measured |
|---|---|---|
| order 5 correction | `27/8 → 31/9`, +2%, margin 0.625, consumed 0.07 | unchanged (that run was exhaustive) |
| order 8 correction | `4.5172 → 4.7143`, +4% | `4.5172 → 7`, **×1.5496 — the whole margin** |
| the ratio a proof must control | 0.07 / 0.625 at order 5 | 1.0 at order 8 |

**Lemma C as posed is asking for a false statement.** It was framed as a bound on the return correction
sufficient to keep `sup R` below the cap. At order 8 with `S ≤ 8` no such bound exists, because
`sup R = n − 1` exactly. This is worth stating plainly rather than as a setback: it explains why the
lemma resisted, and it redirects the work rather than stopping it. Three consequences.

1. **A uniform-gap proof of Existence at order 8 is unavailable by this route.** Any argument that
   spends a margin — iterating, bounding step counts, absorbing a later error term — has nothing to
   spend. The order-5 certificate's shape does not transfer, and the reason is a fact about order 8, not
   a weakness of the instrument.
2. **The pointwise statement is intact and is what Existence needs.** Every strictly realisable
   configuration has `R < n − 1`; equivalently, by `ORDER5_GROWTH_v2` §3, the nearest runner never
   returns and the cascade terminates. It terminates in all four witnesses, at `t → 7/8⁻`. A proof must
   establish `R < n − 1` configuration by configuration, with the strictness coming from `τ > 0`, not
   from a gap below the cap.
3. **The relaunch is settled.** A complete order-8 enumeration at `S = 8` would return **NOT PROVED**:
   it maximises over realisable words and tests `best < CAP`, a realisable word attains 7, and beam
   search bounds that maximum from below. The abandoned 2.4-hour run should not be relaunched at `S = 8`
   expecting a certificate.

## 5. The next test, and what would overturn this

**Highest value now: does any realisable word strictly exceed the cap at `S ≤ 8`?** The beam stopped on
reaching 7 and never asked. This word is terminal, so it does not answer the question for the space. If
some word exceeds 7 with `τ > 0`, the nearest runner genuinely returns at order 8 and the first-exceedance
framing of `ORDER5_GROWTH_v2` §4 needs rework — a much larger consequence than anything in this document.
If none does, then `sup R = n − 1` exactly, attained nowhere, and §4 item 2 becomes the statement to
prove.

**What would overturn the finding.** Three things, in the order they should be checked:

- an error in the LP encoding, so that the word's rows are not the conditions claimed. Checked against
  `ORDER5_CERTIFICATE_v2` §1's stated inequalities and re-derived here, but the check is mine and shares
  a code path with the beam;
- an error in the replay's cascade rule — in particular the latest-exit tie-break, which is the rule
  `LADDER_BOUND_v1` §1 names but no artefact on disk implemented before now. The replay is an
  independent implementation, not a check of the beam against itself, but it has not been cross-checked
  against the Lean cascade in `LonelyRunner/LRC/Cascade/`;
- a scope error: everything here is at ratio bound `S = 8`. Nothing is claimed for larger `S`, and the
  order-5 result that `sup R(S)` is flat rather than climbing does not transfer by assumption.
