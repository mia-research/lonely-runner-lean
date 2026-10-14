# Object register — what the framework owns, and what has been imported against it

**Status:** append-only. Supersedes `HANDOVER_2026_09_13_v1.md` §6 as the register's home;
that section's fourteen rows are carried here **verbatim** and reclassified, never edited.
Nothing on this list may be deleted. Items that turn out to be wrong get a retraction row,
not a removal.

**Date opened:** 2026-09-14. **Author:** T. Palelei's framework; register maintained against it.

**v3, 2026-09-18.** v2 is carried **verbatim**; v3 appends **§7, indices that measure the wrong
object** — three instances found in one session, all at the mathematical rather than the tooling
level. Nothing in v2 is edited.

**v2, 2026-09-18.** v1 is carried **verbatim**: not one row is edited, reclassified or removed.
v2 adds two things and nothing else — the banner below and the supersession table after §0's list.
**Reason:** §0 describes the construction as it stood on **2026-09-14**, a rule-based procedure over
lattice instants with integer scales. Read as current it reintroduces **candidates**, the **ceiling**
and the **`(D, a)` output** — three of the things §2 and §3 exist to keep out. This is the retraction
row the Status line above prescribes, applied to §0 rather than to a numbered item.

---

## 0. The framework's own objects

A register of imports is unreadable without the positive list it is measured against. These are
the objects the construction actually has. Everything in §2 and §3 is an outside thing that was
laid over one of them, or laid over nothing at all.

> ### ⚠ READ BEFORE THE TABLE — this list is a snapshot of 2026-09-14
>
> On 2026-09-14 the construction was a **rule-based procedure over lattice instants** `p/(8D)` with
> **integer** scales `D = k·d_min`, and the cascade was `SKETCH_v7` §7c's **three tiers**.
>
> The present cascade has **no candidates**. Its scales are **real**, `D_{j+1} = D_j·s/(8N+1)`, and
> they **decrease** from `d_min`, so the ceiling `D ≤ 7·d_min` never binds. Its output is **an
> instant**. Four rows below therefore describe a superseded procedure, and the supersession table
> after the list says which and what replaced each.
>
> **Nothing below is deleted, and nothing below is a licence to reintroduce candidates.** If a plan
> step needs a candidate set, a loop over `D` or `a`, a ceiling, or an output pair, it is reading
> this table as current. The current objects are in
> `docs/n8/N8_FRAMEWORK_CHEATSHEET_v1.md` §2.

| object | what it is |
|---|---|
| **Gaps** | the eight cyclic gaps between runners **on the track**, summing to 1. Theorem 4.1: a runner is lonely ⟺ both its flanking gaps are `≥ 1/8` |
| **`d_min`** | the nearest speed difference, taken from the two speed-neighbours |
| **Laps** | `u = d_min·t`; readings `s_j = d_j/d_min`; phase `s_j·u mod 1` |
| **The six readings** | `d_min` comes from the nearer neighbour; the second neighbour is read like everyone else — six, not five |
| **The clearing test** (`coord_iff`, Prop 2.1) | at `t = a/(nD)`, difference `e` is clear ⟺ `D ≤ (a·e mod nD) ≤ (n−1)D`. An integer comparison |
| **The cascade** (SKETCH_v7 §7c) | three tiers: AP (`D = g`), grid (`D = d_min`), enlarged (the gap varies) |
| **Candidates** | `t = p/(8D)`; `4D` of them at gap `D` (odd `a` mod `8D`) |
| **The output** | the pair `(D, a)` |
| **The ceiling** | no step above `7·d_min` clears **for `p ∈ {1,3,5,7}`**, since `p·d_min ≤ 7·d_min < D` |
| **The free test** | `e` cannot block at gap `D` ⟺ `m = 8D/gcd(e,8D)` is even and `≤ 8` |
| **All-or-nothing** | if `D` divides every difference, every candidate at that gap gives the same verdict |

**The identity that governs §3 items 22–24:** at gap `D` the candidates are `t = p/(8D)`, so
`D = p/(8t)`. **The gap and the instant are the same datum in two coordinates.** Choosing the gap
*is* choosing the instant. Any apparatus that treats the gap as an input to be searched for is
re-asking the construction's output as its input.

### 0a. Supersession table (added v2, 2026-09-18)

Which rows above are superseded, which are only dated in their wording, and which stand unchanged.
The distinction is deliberate: §6 of this register and the owner's ruling of 2026-09-15 both warn
that **over-refusal is now the live risk**, so a row is marked superseded only where the object
itself is gone, never on the strength of a word.

| row | status | what is current |
|---|---|---|
| **Candidates** — `t = p/(8D)`, `4D` at gap `D` | **SUPERSEDED — the object is gone** | there is no candidate set. The runners in the way at `t` **fix** the move; it goes to the largest of their next openings (`move_eq_self_or_opening`). Nothing is picked |
| **The cascade** — three tiers, AP / grid / **enlarged** | **SUPERSEDED** | one recursion on the scale, `D_{j+1} = D_j·min{s/(8N+1)}`. The enlarged tier is not renamed but **retired, provably**: every factor `s/(8N+1)` is below 1, so scales decrease and never enter `d_min < D ≤ 7·d_min`. `[PROVED — from the factor; VERIFIED — 0 of 2,488 shuffled arrangements reach a scale above d_min]` |
| **The ceiling** — no step above `7·d_min` clears, for `p ∈ {1,3,5,7}` | **SUPERSEDED as a constraint** | it binds at the AP tier only, and the cascade's scales decrease, so it never binds at all. Carrying `p ∈ {1,3,5,7}` onto the cascade is register item 16 |
| **The output** — the pair `(D, a)` | **SUPERSEDED** | the output is **an instant**. Register item 19 already classifies the lap-in-the-contract version as an import |
| **The six readings** | **CORRECTED — seven** | all seven are evaluated, the `d_min` reading included (v8.2 → v9 audit, finding C5). §4 row (a) of this register already carried the five-versus-six correction; the count moved again |
| **The free test** — "`e` cannot **block** at gap `D` ⟺ …" | **dated wording; content stands for integer scales** | the integer form is `dead_iff` / `dead_downward` / `exists_live`. The real-valued form is the **band identity**: at `1/(8D)` a reading `s` is in the way ⟺ `\|s − 8N\| < 1` for some `N`, every real `D > 0`. Say **in the way** / **clear**, not *block* |
| **All-or-nothing** — "every **candidate** at that gap" | **dated wording; content stands** | this is Theorem 4.10, `spine_all_or_nothing`: at integral readings, the **spine instant** indexed by any unit `p` clears `s` ⟺ `8 ∤ s`. Read "spine instant" for "candidate" |
| **Gaps**, **`d_min`**, **Laps**, **The clearing test** | **stand unchanged** | still exactly the framework's objects |
| **The identity governing items 22–24** (`D = p/(8t)`) | **stands** | still the reason a loop over the gap re-asks the output as its input. Only the word *candidate* in it is dated |

**The one sentence a future session needs.** §0 is a **historical positive list**. Items 22–24 refuse
a search over gaps and numerators; reading §0 as current supplies exactly the apparatus those items
refuse, by a door the register itself left open. Current objects: `N8_FRAMEWORK_CHEATSHEET_v1.md` §2.

---

## 1. The three classifications

Both of the owner's words are used, and they mean different repairs.

| tag | meaning | the repair |
|---|---|---|
| **NOT APPLICABLE** | the framework poses no question here at all. There is no object under the import | **deletion.** Nothing takes its place |
| **MISPLACED** | the framework *has* an object here, and the import is the wrong name, wrong shape, or wrong scope for it | **substitution.** Name the framework's object instead |
| **REFUTED BY THE FRAMEWORK'S OWN CASE** | the import contradicts a worked example already on file in these documents | **withdrawal**, citing the case |

The distinction matters because a misplacement is the more dangerous of the two: it survives every
audit that checks whether a foreign *word* appears, because the word is the framework's own.

---

## 2. The original fourteen, reclassified

Wording of columns 2–4 is `HANDOVER_2026_09_13_v1.md` §6 unaltered. Column 5 is new.

| # | import | how it entered | why it is out | classification |
|---|---|---|---|---|
| 1 | **Lemma 6** — "for any six reals `s ≥ 1` there is a `u` …" | I reduced the problem to the classical seven-difference form | It is LRC(8) restated. The construction's objects are gaps and laps, not a list of six reals | **NOT APPLICABLE.** It is a different problem's statement, not a tool |
| 2 | **Blocking** | described constraints as "blocking" the floor | Owner: *"I didn't say anything about blocking, that's not a brick."* There is no walk, so nothing blocks | **MISPLACED.** There is an object — whether a difference clears at a candidate. It is a residue comparison, and the free test names it |
| 3 | **The jump chain**, its "handover" and "cycling" | `MOMENT_ITERATION_v1`, which `NEIGHBOUR_INTERVAL_v1` had already superseded | The owner's procedure reads one window; it never takes a minimal step. The obstruction was an artefact of the walk | **NOT APPLICABLE** |
| 4 | **Covering** | "the lap lines never cover the window" | Owner: *"Is cover something my framework or someones needs?"* Covering forms a complement; the construction forms none | **NOT APPLICABLE.** §6.1 requires proofs be pointwise |
| 5 | **Measure / `min\|G\|` / zero-measure branch** | a whole afternoon of it | The construction never measures anything. Also a dead frame at n = 8 | **NOT APPLICABLE.** The AP's reading is four points, length 0, and the framework still names `t = 1/8` there |
| 6 | **Witness** | "a witness always exists…" | Owner, twice: *"My work does not need a witness."* Every case that closes, closes by computing the point | **MISPLACED.** A point is produced; it is computed, not witnessed. The object is the pair `(D, a)` |
| 7 | **Carrier** | "which constraint is tight at the moment" | Owner: *"My work doesn't need a carrier?"* The procedure never asks which one was last to clear | **NOT APPLICABLE** |
| 8 | **Set emptiness** | "is the determined set ever empty" | Owner: *"You keep importing these things."* Good-set language in a new coat | **NOT APPLICABLE** |
| 9 | **Weyl equidistribution** | closed the incommensurable case | A real result, but an outside debt. **Excluded from the candidate** | **NOT APPLICABLE.** Also unnecessary: irrational differences are read directly, `√2/100` exact |
| 10 | **LRC(7) / induction on `n`** | closed the `gcd ≥ 2` case | Owner: *"Im not sure about needing the n=7 framework."* **Excluded** | **NOT APPLICABLE** |
| 11 | **`p` and primes** | my index notation | Owner: *"I dont use primes either?"* Rosenfeld's method is a prime search; this is not. `r` is the units mod 8 | **MISPLACED**, and it did downstream damage — see §3 item 16. The index object is `r`, the units mod 8, and the numerator `a`, odd mod `8D`. The letter `p` came in first and the restriction followed it |
| 12 | **A stationary first runner** | normalised `s`-profiles, "the AP's `s` run 1…7" | Owner: *"I don't like to use a stationary first runner."* `v₀` only rotates; part 6 is now frame-free | **NOT APPLICABLE.** Standing ban: never pin any runner at 0 |
| 13 | **Slots** | my word for an eighth | Flagged at handover. Use eighths | **MISPLACED.** The object is an eighth |
| 14 | **Prop 4.1** | cited as established | It is a Proof Sketch in its source, and it is a measure statement | **NOT APPLICABLE** as cited — it is item 5 arriving under a citation |

---

## 3. New entries, 2026-09-14

Each was introduced by me during the generalisation work and rejected, refuted, or dissolved.

| # | import | how it entered | why it is out | classification |
|---|---|---|---|---|
| 15 | **The first window `u ∈ [1/8, 7/8]`** | §1.3 flags it as a **choice**; §7.1 bakes it into the procedure; §7.4 makes it the claim | Owner: *"I never thought the first window/cycle was a requirement and think it keeps getting introduced from context loss and revert to training data."* | **MISPLACED.** The object is the reading's opening; the framework never demands the **first** one. Consequence: every coverage figure quoted at me — 81.9%, 66.0%, 86.8% — is a statement about the first window, not about reach |
| 16 | **`p ∈ {1,3,5,7}` carried onto the enlarged tier** | inherited from item 11's letter, then from the ceiling proof, which genuinely needs `p ≤ 7` | The ceiling argument is `p·d_min ≤ 7·d_min < D`. It binds at the AP tier. With the numerator free it does not bind at all | **MISPLACED.** §7c's own exhibited failure clears at `D = 5, a = 9` |
| 17 | **`a ≡ 1 (mod 8)`** | my normalisation of the numerator | §7d's own worked case is `t = 71/8`, and `71 ≡ 7 (mod 8)`. My form would have missed the framework's own example | **REFUTED BY THE FRAMEWORK'S OWN CASE** |
| 18 | **`D ∈ ℤ`** | my parametrisation of the lattice step | The gap is a **scale**, `k·d_min`, not an integer. Integer-`D` produced 82 false failures on irrational configurations; with the framework's own scales, 0 | **MISPLACED** |
| 19 | **The lap in the output contract** | I wrote the procedure as returning a lap | The output is `(D, a)`. Laps are the currency of the prediction work, not the deliverable | **MISPLACED** |
| 20 | **The interior / no-interior split** | I classified arrangements by whether the clear set has interior | Owner: *"My framework doesn't need an interior to work."* The split classifies by whether a **density** argument applies | **NOT APPLICABLE.** Item 5 arriving by a new route. The framework produced in 472 of 472 empty-interior cases |
| 21 | **"Gap" used for the lattice step `D`** | my own usage, sustained across many exchanges | In the framework, **gaps are the eight cyclic gaps on the track**, summing to 1, and Theorem 4.1 is the only gap condition it has. I attached the word to the lattice step | **MISPLACED — the sharpest entry on this list.** Every question I asked about "whether a gap clears" read as a question about loneliness and was not one. This is the failure mode §1 warns about: a foreign structure wearing the framework's own word, invisible to any audit that greps for outside vocabulary |
| 22 | **A loop over the gap index `k`** | my model of §7c | §7c names **three tiers**, not a loop. Owner: *"What step do you mean the variability in the AP gap size? That is the cascade."* | **NOT APPLICABLE.** By `D = p/(8t)`, searching for the gap is re-asking the construction's output as its input |
| 23 | **A loop over the numerator `a`** | same model | Same root as 22 | **NOT APPLICABLE** |
| 24 | **"Return the first candidate that passes"** | same model | Nothing in §7c says first | **MISPLACED.** It is the first-instant demand (`SMUGGLED_MECHANISMS_v1` §1) in control-flow costume, and it re-imports item 15 through the back door |
| 25 | **Termination** | I raised it as a blocker | Nothing runs. Each step is finite: `4D` candidates at gap `D`. Owner: *"Termination is not required in my framework"* | **NOT APPLICABLE.** It is a property of my loop (22, 23), not of the cascade |
| 26 | **Rule coverage read as reach** | I quoted 81.9% / 66.0% as the framework's success rate | Those are how often a **named rule** fires. The framework produced 12,000 of 12,000 | **MISPLACED.** The object is production; I measured explanation |
| 27 | **Union bounds over the candidates** | my counting work, which reached 86.8% | Owner: *"are we proving our framework or someone elses?"* | **NOT APPLICABLE.** Item 4 by a new route; §6.1 requires pointwise. A bound reaching 86.8% produced nothing |
| 28 | **The global clock / simultaneity** | assumed in how I framed "an instant" | Demonstrated dead: speeds `(3,7,12,20,29,31,44,50)` give eight runners, five distinct times, and **zero** instants at which all eight are lonely together | **NOT APPLICABLE** |

---

## 4. Misplacements inside the framework's own objects

Distinct from §2 and §3: nothing foreign entered, but one of the framework's own objects was used
at the wrong scope. These are corrections, not exclusions, and they stay on the list because the
same slip has recurred.

| | error | correction | status |
|---|---|---|---|
| a | **Five readings instead of six** | `d_min` comes from the nearer neighbour; the **second neighbour is read like everyone else**. Counterexample `V = (4,12,29,37,101,121,176,196)`, runner r4: five-only returns `1/8`, the truth is `9/64`. Differs in 3,276 of 48,000 | standing rule |
| b | **Grid and AP conflated** | Grid ⊋ AP. `(1,2,3,4,5,6,15,16)` is a grid and not an AP. Part 6 decomposes against an **AP**; part 2 is about **grids** | standing rule |
| c | **Octant labelling at exactly `1/8`** | `int(p*8)` puts `7/8` in "octant 7", but `7/8` is allowed — the distance is exactly `1/8`. 16.7% of positions sit exactly on the boundary. BSM: evaluate boundary points separately, never merge touching zones | standing rule |
| d | **Measure-zero read as a difficulty** | A reading that is four isolated points is an AP, possibly based elsewhere. In `(8,9,10,11,15,16,17,18)`, r4 and r5 have differences `1…7`: pure APs based at 11 and 15. They are the *easy* cases | standing rule |

---

## 5. Cross-references

- **False blockers I raised and the owner rejected:** `OBJECTION_LEDGER_v1.md` Part 4. Items 25,
  26 and the "gcd rule does not survive incommensurability" claim are recorded there in full.
- **Retracted claims:** `CLAIM_REFUTED_v2.md` retracts `v1`. `COUNTING_AT_A_GAP_v1`'s bounds are
  retracted as wrong-shape (item 27).
- **The firewall as a stated discipline:** `SMUGGLED_MECHANISMS_v1.md` §5 records that the
  manuscript states no bans, so a reader cannot tell the framework's exclusions from its
  omissions. That is still true of `MANUSCRIPT_v7`, and is the standing argument for §0 of this
  file being restated in the manuscript itself. **No manuscript change is to be made without
  explicit approval.**

## 6. The generator, stated once

Twenty-eight entries, and the pattern behind almost all of them is one move: an absence in my own
model of the construction is converted into a requirement on the construction. I could not see
what named the enlarged tier's gap, so I built a loop; the loop then needed a bound, a
termination proof, and a coverage figure, and each of those became an objection to the framework.
None of the three was about the framework. The check that catches this is §0 — name the object
before naming the problem, and if the object is not on the positive list, the problem is mine.

---

## 7. Indices that measure the wrong object  (added v3, 2026-09-18)

§§2–3 record foreign constructs laid over the framework's objects. This section records something
different and, on the evidence of one session, commoner: **a quantity of the framework's own, used
as an index, that does not vary with the thing it is taken to index.** Nothing foreign enters. The
number is correct; what it counts is not what was claimed.

This is the mathematical form of the rule CLAUDE.md §2b states for tooling — *name the object you
track and check that object, never a correlate.*

| # | the index | what it was taken to measure | what it actually measures | how it was caught |
|---|---|---|---|---|
| 29 | **`k` unbounded** (`bounded_k_attack_v1`, `k = 369`) | that the flank route cannot be bounded, hence cannot close | **search length.** The witness has `S = d_max/d_min ≈ 14,125`; all eight of its subjects resolve in at most **3** cascade moves at `R ≤ 1.17`, and the cascade reaches that `k = 369` opening **in one move**, computed not searched | asking the question never asked — *is `k` bounded GIVEN `S`?* Adversarially: 6 at `S ≤ 20`, 7 at `S ≤ 30`. The ledger's Part 4 test already names search length a **false blocker** |
| 30 | **`j`, the count of non-integer ratios at a flank, as difficulty** | where shadowing becomes possible | nothing predictive. §6.9 already recorded that live flanks fail at every `j` from 2 up | the effective step `ĝ = min(f, 1−f)` does predict it: every shadowing configuration found exhaustively to denominator 7 has `max ĝ ≥ 1/3`, and all-`ĝ ∈ {1/5,1/6,1/7}` configurations were tested and none shadow |
| 31 | **`j` as coverage** — Theorem 6.9 (`j = 1`) and Proposition 6.10 (`j = 2`) | a decomposition of the flank problem by walker count | **about one flank in sixty.** Walkers per flank over 84,000: `6: 65,734 · 5: 10,423 · 4: 2,874 · 3: 1,127 · 2: 391 · 1: 77 · 0: 854`. Six walkers is 78%; `j ≤ 2` is 1.6% | measuring the distribution instead of assuming it. Coverage comes from the **band condition at small `k`** (Thms 6.12/6.14), not from the walker theorems |

**The generator.** In all three the index came from **how the theorem was written**, not from how the
object varies. A statement proved "for one non-integer ratio" invites `j` as the axis; a search over
opening indices invites `k` as the axis. Neither was checked against the data before being used to
decide where the difficulty lies or what was covered.

**Two sub-patterns worth separating, because the check differs.**

- **Wrong index.** The quantity does not co-vary with the difficulty. *Check:* before indexing by
  anything, measure whether the hard cases concentrate at particular values of it. If they are spread
  uniformly, it is not the index.
- **Wrong population.** The quantity is measured where the phenomenon cannot occur. Two instances the
  same session: `ghat_index_v1` sampled random rationals at denominator 1000 and found **0**
  shadowing configurations in 60,000 — shadowing needs *exact* rational coincidences, so the sample
  had nothing to discriminate; and bad-interval coverage measured **~56%** on random arrangements
  while the hard cases already on file reach **98.9%**. *Check:* ask whether the extremal object can
  appear in the population at all. If it is measure-zero or adversarial, sample adversarially or
  enumerate exhaustively.

**What this section is not.** It is not an argument that `j` or `k` are bad objects — both are the
framework's own and both are correct. `k` is bounded given `S`; `j` counts what it says. The error is
in the second step, where a correct count was used to locate difficulty or to claim reach.

**Standing check, before a count decides anything:** write down what the number counts, then write
down the claim it is about to support, and confirm they are the same object. Where they differ, say
which is being measured.
