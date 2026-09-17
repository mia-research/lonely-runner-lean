# Corrections: four documents of 2026-09-17, and the withdrawal of Propositions 6.10-6.11

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
| `NATIVENESS_AUDIT_2026_09_17_v2` "explains the infeasibility honestly" | "the word space is 7.25×10²⁶ **because** it is not the framework's object" | not measured — a causal claim asserted | **unverified**; the checkable part is that the cascade is deterministic (`move` is a function), so one arrangement has one path. The "because" is rhetoric and is withdrawn |
| `NO_RETURN_TIGHTNESS_v1` §2 "a genuine strengthening" | a `P`-dependent restatement strengthens the lemma | §3 of the same document: 0 extra returns excluded | **strengthens the lemma, not its reach** — say both, not "genuine" |

Three of four sat next to the backlog in §1–§2. The diagnostic worked; it was not acted on at the time.

## 4. What is not affected

The Lean work of 2026-09-17 (`class_killer_int`, `circDist_periodic_of_lattice`,
`lonely_opening_of_free_off_lattice`, `lonely_of_flank_unkillable`, `lonely_of_some_flank_unkillable`
and their `stops_` corollaries, gate 189/189 axiom-clean); `RETURN_CORRECTION_v3`;
`NATIVENESS_AUDIT_2026_09_17_v3`; `PROVENANCE_MAP_v1`; `NO_RETURN_TIGHTNESS_v1` §§1, 3–5; `DEEP_REVIEW_2026_09_17_v1` §§1–4,
6–8; and every measurement artefact. None of those rests on §1 or §2's framings.

---

## 5. Propositions 6.10-6.11  `[WITHDRAWN — register items 4, 27; and the manuscript's own ban]`

Owner's question, 2026-09-17: *"Were counts and or pidgeonholes added as part of a reference to
other's needs rather than our own frameworks need?"*  Answer: yes.  §1 above caught this shape at
`n > 2k` and did not carry it through to the flanks, where the same shape sits inside two numbered
propositions.

**(a) The framework already ruled on the conclusion form.**  `FRAMEWORK_CONJECTURE_v1` §3:

> "A covering or counting argument cannot prove this conjecture, however strong, because such an
> argument concludes *'a candidate survives'* and the conjecture asks *which*."

and, in the line after, the register's banned items are *"inapplicable rather than forbidden ...
measure, density, covering, set emptiness and witnesses all conclude existence, and existence is not
what is being asked."*

**(b) Both propositions are that shape.**  6.11's step 3 is *"For every residue to be covered:
`1 ≤ Σ(ℓ + 1/c_j)`"* — a union bound over capacities, concluded by contradiction from an assumed
cover.  6.10's rational-pair step is the same move over two candidates: *"the two shares must add to
at least 1."*  Register item 4 (covering) and item 27 (union bounds), both NOT APPLICABLE, at flanks
instead of at candidates.

**(c) They violate the manuscript's own ban table.**  §6.10 of `MANUSCRIPT_v9_2` lists the framework's
bans, including *"**No covering or emptiness language** — The construction forms no complement and no
set to be shown empty; it runs a cascade to a named instant."*  The paragraph after that table records
**two** violations in earlier drafts (the first-instant demand; the pinned frame).  6.10-6.11 are a
third, and were not recorded as one.

**(d) The operative criterion is the index bound, not constructivity.**  This correction states the
test wrongly if it says the native results are constructive and these are not: `exists_clear_step` is
proved `by_contra` in Lean, like 6.11.  The difference that matters is whether the argument **bounds
where the opening is**:

| result | bound on the index | native |
|---|---|---|
| `exists_clear_step` (Thm 6.9) | `~1/min(f, 1-f)` (`census_batch_verify_v1.py:31`) | yes |
| `class_killer_int`, `circDist_periodic_of_lattice` | inherit that bound | yes |
| `n > 2k` via the potential `Ψ` (§8.2) | caps the instants (`exists_fixed_of_capped`) | yes, ruled 2026-09-17 |
| 6.10's rational-pair count | none | **no** |
| 6.11, the flank sum criterion | none; `q = q'L`, `q' ≤ Q^m`, `Q → ∞` | **no** |

The manuscript admits 6.11's failure itself: *"the criterion names an opening without bounding when"*,
with `k = 1, 5, 45, 442, 4420` as `ε → 0`.  A bounded search names an instant.  An unbounded existence
claim does not.  `n > 2k` survives the same test because a cap **is** a bound, which is why its
covering-threshold coincidence is a coincidence and not the argument.

**(e) They do not have the reach they are credited with.**  `MANUSCRIPT_v9_2:708` carries "Flanks with
four or more non-integer ratios, where Proposition 6.11 does not apply" as the open case.  That is
register item 26 (**rule coverage read as reach**, MISPLACED) — §2 above refutes it twice over: `j ≥ 4`
is where the propositions stop applying, not where the difficulty is, and live flanks fail at `j = 2`
(13) and `j = 3` (44), so they do not cover `j ≤ 3`.  Measured independently from the other side
(`flank_sum_reach_v1`, every 8-subset of `[1,20]`, 958,256 live flanks): the criterion fires 19,736
times, **all at `|J| ≤ 1`**, which Theorem 6.9 already decides without a count.  0 firings at `|J| ≥ 2`.

**(f) They are aimed at the wrong object.**  §6.9's other open item is the obligation: *"not every
flank of a runner can be shadowed at once"* — about the arrangement.  6.10-6.11 are per-flank, and
per-flank freeness is false in general (2.6% of live flanks are shadowed) while **0 of 6,000
arrangements** had no free flank.  A per-flank criterion cannot reach an arrangement-level statement,
however far it is pushed.

**(g) There is a ceiling regardless.**  At order 8 every term of `Σ(2/n + 1/c_j)` is at least
`2/n = 1/4` before any denominator is read, so `|J| ≥ 4` gives `Σ ≥ 1` outright.  6.11 can never reach
four or more non-integer ratios.  Not a gap in its proof — a ceiling of the method.

**What is withdrawn:** Proposition 6.11 entirely; Proposition 6.10's final counting step; the `j ≥ 4`
framing of §6.9's open item; and the pending counting ruling, which after the above has nothing left to
decide.

**What survives, and why:** 6.10's mixed pair and the reduction of its rational pair to `c₁ = c₂`.
Both run on `class_killer_int` / `exists_clear_step`, which bound the index, and both were formalised
axiom-clean on 2026-09-17 (`lonely_opening_of_lattice_and_free`, `shadowing_pair_cross_lattice`).
Neither needs the withdrawn ruling.  The arithmetic of 6.11 is not wrong; it is inapplicable as a
discharge, and its credited reach is refuted.

---

## 6. The sweep for others of the same kind

Owner asked whether anything else hangs in the manuscript this way.  Then, on being shown a
keyword sweep: *"I wonder if grepped search for key words is enough?  If it was it would have
caught 6.10-11?"*

**It is not enough, and it would not have.**  The keyword sweep found 6.10-6.11 only because their
grade tags *self-declare* — they literally read "residue count" and "pigeonhole".  An import that
does not use the banned vocabulary passes straight through.  This is CLAUDE.md §2b's recorded
failure exactly: a tag-count audit that was *"mechanical and wrong"* because it *"measured a
proxy"*.  Vocabulary is a correlate.  The object is the **conclusion form**.

**There is no mechanical discriminator, and the evidence is inside this document.**  §5(d) shows
`exists_clear_step` is native and proved `by_contra`; 6.11 is not native and proved `by_contra`.
Same tactic, same vocabulary, opposite verdicts.  Worse for the vocabulary test:
`exists_fixed_of_lonely` **uses pigeonhole** (`not_injective_infinite_finite`) and is native.
Counting and pigeonhole were never the problem and the register never banned them.

**The object-level test.**  For each claim that asserts something exists: *is the witness bounded by
something computable from the arrangement?*  Applied to all 35 structural existence-form theorems of
the cascade artefact (the 4,653 census-family theorems are `decide`-discharged, so they compute the
instant outright):

| claim | the bound | verdict |
|---|---|---|
| `exists_clear_step` | `~1/min(f, 1-f)` (`census_batch_verify_v1.py:31`) | native |
| `exists_fixed_of_lonely` | `N ≤ Σ_d (⌈d·s⌉ + 1)`, the size of `openingsUpTo n ds s` | native |
| `stops_when_twice_card_lt` (§8.2 `n > 2k`) | explicit cap `B = b^n·((lapProd n 3)^n)^{|ds|}·(∏_x (x + 1/b))^2`, via `exists_fixed_of_capped` | native |
| the other 32 | inherit one of the three above, or are `↔` statements carrying no existence conclusion | native |
| 6.10's rational-pair count, 6.11 | **none** | **not native** |

Every structural claim in the Lean tree bounds its witness.  The only two that do not are the two
withdrawn in §5.

**Why no automated check caught them: they were never in Lean.**  The cascade gate reads
"coverage 4688 of 4688 on disk" — that is coverage of the **Lean tree**, not of the manuscript's
claims.  A prose-only result is invisible to the gate, to `#print axioms`, and to every scan we run.
6.10-6.11 were prose-only.  So were Prop 6.7, §6.2's dilation, §6.6's spine pattern and H1 until
2026-09-17, and those four turned out sound only because they were later formalised and checked.

**The maintainable fix** is a tripwire on that hole rather than a wider grep: every numbered result
in the manuscript must either name a Lean declaration, or be listed as prose-only **with its index
bound stated**.  A prose-only result with no stated bound is the signature, and it is decidable from
the §7 crosswalk table without reading any mathematics.

**The keyword sweep, kept for what it is worth.**  It establishes the absence of the *obvious*
form — it does not establish the absence of the subtle one, and did not find either withdrawn
proposition on its own merits:


| ban / item | result |
|---|---|
| No search (item 22) | honoured. Every "search"/"candidate" mention is a **superseded** method being retired (§6.2's enlarged tier, `SKETCH_v7` §7b's mixed reading), or `MANUSCRIPT_v9_2:387` "There is no set of candidates" |
| No measure or density (items 5, 9) | honoured. Zero live uses of Weyl, Kronecker, equidistribution or density; §6.9 states its three facts are *"about openings and denominators, not about measure"* |
| No window / first lap (item 15) | honoured, and actively withdrawn at `:330` — *"that bound is the first-window restriction withdrawn in revision-list items 1-3, and is not part of the obligation here"* |
| Witness (item 6), set emptiness (item 8) | honoured. Every "witness" is a named counterexample arrangement, which produces a point rather than asserting one |
| Global clock (item 28) | honoured. Zero live uses |
| Slots (item 13) | honoured, distinctly: `:428` defines a slot as an AP position (`d/D ∈ 8ℤ`), a different object from an eighth of a lap. Worth a one-line note in the vocabulary section, not a correction |
| The four remaining `[OPEN]` items (`:159`, `:330`, `:534`, `:849`) | all native — the fit between AP locations, the gap-frame obligation, Existence itself, five differences at `n = 6…10` |
| §8.2 `n > 2k` | ruled 2026-09-17, and survives §5(d)'s test independently: it caps the instants |
| §9 "ruled admissible as tools" vs "pending" | **not** a contradiction. `:366` distinguishes the 2026-09-15 tools ruling from the pending question of whether they sit inside the framework. §5 answers the pending one |

**Stale in our favour, not imports** — three `[not formalised]` rows overtaken by the Lean work of
2026-09-17, to be corrected in `v9_3`:

| row | now |
|---|---|
| `:788` Prop 6.7; §6.6 spine pattern; §6.2 dilation — *"derived and verified, not formalised"* | all three formalised, axiom-clean |
| `:791` Props 6.10-6.11 — *"proved in the text, not formalised"* | superseded by §5; what survives is formalised |
| `:1034` H1 / Appendix C item 4 — *"[PROVED — the two lines above; not formalised]"* | formalised (`Together.lean`) |
