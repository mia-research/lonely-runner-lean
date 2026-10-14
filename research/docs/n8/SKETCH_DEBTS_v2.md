# What the sketch rests on, and what it owes (v2)

2026-09-13. Companion to `SKETCH_v6.md`. Its purpose is to make every debt explicit before a
lemma pass, so that nothing gets formalised that is either an import or unearned.

**Change in v2**: `D2` is struck as a standing debt — owner's call, checked below. Three
compounding reasons, and a caveat kept.

Three separations are kept throughout, because conflating them is what this line of work keeps
paying for: **proved** vs **verified**; **owner's** vs **mine**; and **owed to the outside** vs
**owed to ourselves**.

---

## 1. What the sketch establishes, section by section

| § | statement | grade | rests on |
|---|---|---|---|
| 1 | `Σ g_k = 1` at every instant | `[PROVED]` | the circle |
| 2 | adjacency is adjacency mod `n`; labels are ranks; runner lonely iff both flanking gaps `≥ 1/8` | `[PROVED]` | the cyclic order |
| 3 | `#lonely = |A| − c(A)`; `#lonely ≥ max(8−2b, 0)` | `[PROVED]`, `[VERIFIED — 180,000]` | §1, §2 |
| 4 | all eight lonely ⟺ every gap exactly `1/8` | `[PROVED]` | §1, §2 |
| 4 | **global isolation forces commensurable speeds** | `[PROVED]`, `[VERIFIED — 400,000]` | §4 |
| 4 | the instants are `r/n`, `gcd(r,n)=1`, and there are `φ(n)` | `[CITED]` | **debt D1** |
| 5 | `d_min` local and exact; nothing before `1/(8·d_min)`; one window; location vs time | `[PROVED]` | sortedness |
| 6 | lap count and phase of all **six** others read off | `[PROVED]` | arithmetic |
| 7 | displacement by `e_k·r/d` eighths; survival iff whole eighths and a bijection | `[PROVED]`, `[VERIFIED — 12,135]` | `k ↦ kr (mod n)` |
| 7a | the AP of step `d` holds the other seven over `8d ± (n−2)d/(n−1)`; dilates free by scaling | `[PROVED]` | §5, §7 |
| 7b | the four instants at each runner's own scale name ~72% of runners, ~8% of configurations | `[VERIFIED]` | §5, §7 |
| 7c | **ceiling**: no step above `7·d_min(i)` clears `i` | `[PROVED]`, `[VERIFIED — 32,000]`, attained | the nearest difference |
| 7c | **closed form**: dead lattices are the divisors of `M(i)`; `L_0 = min(ℤ⁺ \ Dead)`; prime bound | `[PROVED]`, `[VERIFIED — 32,000/32,000]` | `8D∣d ⟺ 8∣d ∧ D∣d/8` |
| 7c | cascade rates; clearing step `= L_0` in 78.6% | `[VERIFIED — descriptive]` | `PREREG_DSWEEP_v1` §2.3 |
| 7c | a configuration no admissible step clears | `[VERIFIED — exact]`, one case | exhibited |
| 7d | window-widening: `m ≤ 3h/4` ⟹ lonely in the first window | `[PROVED, given nonemptiness]` | nonemptiness exhibited per case; see the `D2` note |
| 7d | at integer speeds the second trigger collapses to the `gcd ≥ 2` case | `[PROVED]`, `[VERIFIED — 26/26 of 32,000]` | integrality |
| 8 | the moment is always an **opening** `(8k+1)/(8d)`, never a closing | `[PROVED]`, `[VERIFIED — 12,672]` | closedness of the reading |
| 9 | a permutation disturbs only `{mover} ∪ {departure pair} ∪ {arrival pair}` | `[VERIFIED — 1,376/1,376]` | **not proved** |
| 10 | the Claim | `[CLAIMED]` | **debt D3** |

**Lean.** `LonelyRunner/LRC/Construction8/Parts.lean` — `gaps_all_eq` (§4), `nearest_below`,
`nearest_above`, `before_floor` (§5), `displacement` (§7). Zero `sorry`, no `native_decide`,
all five `[propext, Classical.choice, Quot.sound]`, all stated at general `n`.

## 2. Owed to the outside

| | debt | where | status |
|---|---|---|---|
| **D1** | `lrc_ap_phi_n_law_v1` Theorem 3.1(a)–(b) — the `φ(n)` instants and their count | §4 | the owner's own prior work; the construction's only intended external debt |
| ~~D2~~ | ~~LRC(7), for nonemptiness of the six-constraint reading~~ | §7d | **struck — legacy.** See below |

**Why `D2` is not a debt of this sketch.**

1. **Not new.** At integer speeds §7d collapses to the `gcd ≥ 2` case — `[PROVED]`, and measured
   26/26 of 32,000 firings. §7d borrows `LRC8_ANALYTIC_v2` §6b's citation rather than incurring
   one; the debt is already recorded there.
2. **Not outside.** LRC(7) is axiom-clean in this project's own Lean tree — `intLRC_seven`,
   `[propext, Classical.choice, Quot.sound]`, zero `sorry`. That places it with `D1`, the owner's
   own prior work.
3. **Not load-bearing.** LRC(8) over the reals reduces to integer speeds, and at integer speeds
   §7d *is* §6b — so the sketch's route to the theorem does not pass through §7d. §7d earns its
   place on the prediction side, explaining the near-collision delays of `DELAYED_ISOLATION_v1`.

And it is not cited in practice: `[VERIFIED — 4,000/4,000]` an instant exhibited directly for six
random positive integers, `D ≤ 9` every time.

**Caveat kept.** The statement needed is weaker than LRC(7) — six speeds at `1/8`, not `1/7` — but
the margin is thin at the extremal point: `w = (1,2,3,4,5,6)` tops out at exactly `1/7`, which is
LRC(7)'s own tight case. "Weaker" is true; "comfortably weaker" is not.

Nothing else in the sketch cites anything. In particular: no measure, no covering, no
equidistribution, no Weyl, no induction on `n`, no Rosenfeld, and Proposition 4.1 of the `φ(n)`
paper is not used.

## 3. Owed to ourselves — the open items

**D3 — the Claim.** The owner's statement, `PROOF_CANDIDATE_v3` Step 7:

> For every arrangement and every runner, the procedure of Steps 3–5 — form `m` from the two
> neighbours, form the window, read the other six inside it — **returns the moment**.

`[VERIFIED — 21,600 runner-instances across seven populations; every integer arrangement with
0 = v_1 < … < v_8 ≤ 20 and gcd 1, being 77,400 arrangements and 113,145 distinct profiles; and
2,432 runner-instances of the single-mover sweep]`.

**D4 — §9 is measured, not proved.** The locality of a permutation through crossings holds
1,376/1,376 on the AP base with one mover. No argument is given.

**D5 — §7a's second half.** Whether an enlarged step can be chosen so that its range contains the
runner actually present. Measured: a step giving such a range exists for two of three irregular
bases tested, and in neither case does the range contain the eighth runner the configuration has.
**This item is mine, not the owner's** — see §5 below.

## 4. Owed as corrections — outstanding

| | correction | where | raised |
|---|---|---|---|
| **C1** | "verify the other **five**" → **six**. `d_min` comes from the nearer neighbour; the second neighbour is read like everyone else. Counterexample `V = (4,12,29,37,101,121,176,196)`, runner r4 — five-only returns `1/8`, the reading gives `9/64`; differs in 3,276 of 48,000 | `NEIGHBOUR_INTERVAL_v1` §1 step 3 | handover 2026-09-13 §7 item 1. **Still not made** |
| **C2** | `SKETCH_v6` §10 carries the **carrier** — "every *grant* falls on lap 0", "which runner grants it", and the `k = 0` reframing, which is the existence quantifier the owner removed in `PROOF_CANDIDATE_v3` change (iii). Replace the section with the Step 7 sentence and the counts, delete the three paragraphs | `SKETCH_v6` §10 | this session. **Owed** |
| **C3** | The open item is restated in banned vocabulary in three files: `NEIGHBOUR_INTERVAL_v1:72` *"a proof that the **good set** always meets the first neighbour interval"*; `OWNER_PROCEDURE_v1:104` *"the lap lines … never **cover** the whole window"*; `GAP_FRAME_v1:97` *"is there a `t` at which runner `i`'s junction is interior to a **run of A(t)**"*. Register items 8 and 4 | three files | this session. **Owed** |
| **C4** | The disturbed-runner attainment rate is a step-size artefact, not a constant near one half: 0.4641 / 0.4135 / 0.3800 / 0.3735 at steps 1/10, 1/100, 1/1000, 1/10000. The reported 0.4812 and 0.497 are the two coarsest points; the cause is the small-denominator bias of handover 2026-09-12 §2 item 12 | `SCALE_RULE_v1` §3 §6, `TWO_MOVER_PREDICTION_v1` §4 §6, `RANDOM_PREDICTION_v1` §2 §5 | this session. **Owed** |
| **C5** | `SKETCH_v6` §7a uses **window** for a range of *speeds*, while every other file uses it for the runner's time interval `[1/(8·d_min), 7/(8·d_min)]`. Same word, different object, never flagged. Rename or cut | `SKETCH_v6` §7a | this session. **Owed** |

## 5. Provenance — whose is what

This matters because a lemma pass must not formalise an import.

**The owner's, and load-bearing:** the gap frame and the two-gap criterion; adjacency mod `n` and
rank labelling; `d_min` local and exact; the one window; the reading of the others by lap and
phase; the eighths and the displacement; the `φ(n)` spine; the all-or-nothing property of the four
spine instants at integral `s`; the first live lattice and the dead-lattice criterion
(`WHY_IT_PREDICTS_v1` §2); the `gcd ≥ 2` theorem; the AP-of-1 range for the eighth runner; the
three regimes and the grand return; the Claim itself.

**Mine, and marked as such:** the closed form for `L_0` and the two bounds (§7c) — a formalisation
of the owner's own criterion, not a new mechanism; the ceiling `7·d_min` (§7c); the unification of
the `gcd ≥ 2` case and the near-collision case as one lemma (§7d); the exact endpoints `8d ±
(n−2)d/(n−1)` (§7a); the crossing extension of the disturbance rule (§9); the commensurability
proof in §4; the opening/closing statement (§8); **and D5, which is a question about an object I
introduced.**

**Imports that were removed after being introduced by me, this session:** bad sets and coverage;
Helly; lap vectors chosen rather than read; annealing; a span bound; the 2-adic ladder
(a route the owner had already closed, `DYADIC_DEPTH_RESULT_v1`); slots; the carrier; "residue"
used for a leftover fraction. The register at handover 2026-09-13 §6 lists fourteen such items;
seven were re-imported in this session before being caught.

## 6. What a lemma pass can take

Ordered by independence — each of these is proved in the sketch and needs nothing from the items
above it.

1. §4 global isolation forces commensurability — pure arithmetic on `(1/8)ℤ`.
2. §7c the ceiling — one inequality on the nearest difference.
3. §7c the closed form and the prime bound — `8D ∣ d ⟺ 8 ∣ d ∧ D ∣ d/8`, then a divisor-closed set.
4. §8 the opening — the reading is closed, its components' left endpoints are the openings.
5. §7a the endpoints `8d ± (n−2)d/(n−1)` — two band conditions at `p = 7`.
6. §7d window-widening — periodicity plus an interval of at least one period, with nonemptiness
   supplied per case rather than cited.
7. §3 the run identity — adjacency counting on a cyclic set.

Not available to a lemma pass: §9 (measured only), §10 (the Claim), D5.

---

`[PROVED]` §1 of this document reproduces the sketch's grades; nothing is promoted here.
**n = 8 is not proved by the sketch, and this document does not change that.**
