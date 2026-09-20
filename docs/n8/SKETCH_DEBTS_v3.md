# What the sketch rests on, and what it owes (v3)

2026-09-15. Companion to `SKETCH_v7.md`. Its purpose is to make every debt explicit before a
lemma pass, so that nothing gets formalised that is either an import or unearned.

**Change in v3**: the five corrections outstanding at v2 §4 — **C1–C5** — are all made, each as a
new version rather than in place. §4 below becomes the record of what was done and where. Three
new items are opened, **C6–C8**. Nothing in §§1, 2, 3, 5, 6 of v2 changes, and no grade moves.

Three separations are kept throughout, because conflating them is what this line of work keeps
paying for: **proved** vs **verified**; **owner's** vs **mine**; and **owed to the outside** vs
**owed to ourselves**.

---

## 4. Corrections — discharged

| | correction | made in | note |
|---|---|---|---|
| **C1** | "verify the other **five**" → **six** | `NEIGHBOUR_INTERVAL_v2` §1 | The counterexample `V = (4,12,29,37,101,121,176,196)` r4 and the 3,276-of-48,000 divergence are stated at the point of use. v1 left the in-place-or-v2 call to the owner; taken as **v2**, per the standing versioning rule. |
| **C2** | `SKETCH_v6` §10 carries the carrier | `SKETCH_v7` §10 | Section is now Step 7's own sentence plus the counts. The `k = 0` reframing and the "what to work up first" paragraph are gone. The handover 2026-09-12 §5 trap is **kept** — deleting it would have lost a recorded warning, which is not what C2 asked for. |
| **C3** | the open item restated in banned vocabulary, three files | `NEIGHBOUR_INTERVAL_v2` §4 §5, `OWNER_PROCEDURE_v2` §4, `GAP_FRAME_v2` §3 | Register items 8 and 4. `GAP_FRAME`'s is now §0's two-gap criterion asked of the trajectory; `OWNER_PROCEDURE`'s is stated positively. No claim altered. |
| **C4** | the attainment rate is a step-size artefact | `SCALE_RULE_v2` §3, `TWO_MOVER_PREDICTION_v2` §4, `RANDOM_PREDICTION_v2` §2 | The 0.4641 / 0.4135 / 0.3800 / 0.3735 curve is recorded inline at each reported figure. The two "why is the rate near one half" open questions are **struck** — the premise is false. |
| **C5** | `SKETCH_v6` §7a uses **window** for a range of speeds | `SKETCH_v7` §7a | Renamed **speed band**, with a note at the point of use and the ledger line changed. |

## 4a. Corrections — opened 2026-09-15

| | correction | where | note |
|---|---|---|---|
| **C6** | `C1_STATUS_v1` §1 puts the settled share at **31.4%** and §4 says nothing is closed on the mixed branch. Both were already superseded by the owner's own files *before* v1 was written: `SKETCH_v6` §7b measures the four instants at **~72% of runners**, and `C1_MIXED_CONSTRUCTION_v1` §2 reports **97.5%** settled, stating the comparison against 31.4% explicitly | `C1_STATUS_v1` §1 §4 §6 | Recorded in `C1_STATUS_v2` §0. **Made.** v1 is left standing; the retraction lives in v2 with the sentences quoted. |
| **C7** | Mine, this session: I re-measured the spine against mixed readings, got 77.6%, and reported it as a correction nobody had made. It is `SKETCH_v6` §7b's result. The re-measurement is a confirmation at five spans on 12,000 instances and nothing more | `C1_STATUS_v2` §0 | **Made**, in the same file, before anything was built on the wrong framing. |
| **C8** | Mine, this session: I claimed `GAP_FRAME_v1`'s run identity over-predicts at 685 of 46,204 instants and proposed it be qualified to lonely *positions*. Wrong. My check built `k` gaps from `k` distinct positions; `GAP_FRAME_v1` §0 says **eight** gaps with zeros permitted. Re-run in the file's own convention: **0 violations** in the same 46,204 instants | `C1_STATUS_v2` §3, `GAP_FRAME_v2` header | **Made.** `GAP_FRAME_v1` needed no change and got none; `GAP_FRAME_v2` exists for C3 and for the new Corollary 1a. |

**What C6–C8 have in common.** All three are the same failure: a result already in the owner's
files was re-derived and presented as new, or the owner's convention was replaced with mine and the
mismatch read as a defect in their work. This is the fourth, fifth and sixth instance in this
session; v2 §5's list of imports records the earlier ones. The check that would have caught all
three is the same one, and it is cheap: **before reporting a finding, grep the file set for the
object it concerns.** §7b was one `grep` away throughout.

## 4b. What was added rather than corrected

Not debts. Recorded here so the ledger of this session's output is in one place.

| | statement | where | grade |
|---|---|---|---|
| | `d_max ≤ 7·d_min` ⟹ `u = 1/8` clears the subject; sharp at `s = 1` and `s = 7` | `C1_STATUS_v2` §1 | `[PROVED]` |
| | hence all four spine points shut ⟹ `d_max > 7·d_min`; the ratio condition is a subset of the spine's reach, not an addend | `C1_STATUS_v2` §1 | `[PROVED]` |
| | a single `s` shuts all four spine points iff `dist(s, 8ℤ) < 1/7` | `C1_STATUS_v2` §2 | `[PROVED]`, 1,396/1,396 |
| | the lonely count is never 7; it is 8 only at the barycentre | `GAP_FRAME_v2` §1 Cor. 1a | `[PROVED]`, exhaustive to 12,870 |
| | the spine and the window-widening lemma are complementary on §7d's worked case | `SKETCH_v7` §7d | `[VERIFIED — exact, 400-digit]` |
| | the shut-pattern depends only on `f = dist(s, 8ℤ)` signed; every spine point has shut-density exactly `1/4` | `SPINE_PATTERNS_v1` §1 | `[PROVED]` |
| | nine shut-patterns are achievable and six subsets of `{1,3,5,7}` are not; there are exactly **eleven** minimal ways to shut the whole spine, none using more than four readings | `SPINE_PATTERNS_v1` §2 §3 | `[PROVED — finite]` |
| | first clearance is at lap 0 — 12,000 instances at five spans, plus 12,800 on a second seed | `NEIGHBOUR_INTERVAL_v2` §2 | `[VERIFIED]`, joins the file's 21,600 for 46,400 total |

The last of these is **the owner's claim**, `NEIGHBOUR_INTERVAL_v1` §2, confirmed twice more and
not newly found.

---

`[PROVED]` §1 of `SKETCH_DEBTS_v2` reproduces the sketch's grades and is carried forward unchanged;
nothing is promoted here. §§2, 3, 5, 6 of v2 likewise stand.

**n = 8 is not proved by the sketch, and this document does not change that.**
