# PAPER v7 — Section Map, v2

*Version 2, 2026-09-22. Supersedes `PAPER_v7_SECTION_MAP_v1.md`, which was built on an outline the
author has since corrected. A placement document, not a draft: no prose rewritten, no abstract or
introduction, no grade moved, no result dropped.*

**What changed from v1.** v1 organised the paper around reaching an existence obstruction, and its
Part D.1 treated a boxed blocker equivalence as the paper's destination. That conflated two
statements. The correction, from the author:

> **Equivalence/localisation** — characterising loneliness exactly by the framework's certificates,
> openings and cascade — is *already established, in both directions, unconditionally*.
> **LRC existence** is not a missing direction in that equivalence. It is the **universal quantifier
> over configurations**.

The map is therefore rebuilt in **two layers**, and the boundary between them is the most important
structural decision in the document.

---

## Part A — the two layers

### Layer 1 — the framework

Complete and unconditional. Each arrow is an equivalence, not a sufficient condition.

```
    loneliness  ⟺  lonely opening  ⟺  certificate  ⟺  cascade outcome
```

The substantive direction throughout is the *forward* one: **any lonely instant necessarily induces
a lonely opening.** The converse — certificate ⇒ opening ⇒ loneliness — is immediate once the
certificate is defined correctly. Stating the pair as an equivalence is the result.

### Layer 2 — the existence analysis

For a fixed configuration, Layer 1 settles what loneliness *is*. The conjecture asks:

```
    for every admissible disparity configuration, does such an (e, j) exist?
```

Layer 2 goes **inside** the equivalent condition — reparameterising it and constraining its
satisfying set — and does not revisit the equivalence.

```
LONELINESS
    │ exact equivalence
LONELY OPENING
    │ exact arithmetic form
CERTIFICATE
    ├───────────── end of Layer 1 ─────────────
    │ reparameterisation
R / CLEAR-SET FORM
    ├── structural symmetries      ├── rescaling
    ├── self/non-blocking          ├── edge witnesses
    ├── reflection                 └── candidate/blocker structure
    │
UNIVERSAL EXISTENCE  — for every disparity set
```

### Target sections

| § | title | layer | source |
|---|---|---|---|
| 1 | The problem and the framework | — | written last |
| 2 | Loneliness is a closed condition, and its boundary | 1 | P §3, §4 |
| 3 | The precursor: global isolation and `φ(n)` | 1* | P §3.1, §3.2 |
| 4 | One runner, one scale | 1 | P §5 |
| 5 | Localisation: every lonely instant is represented by an opening | 1 | P §6 |
| 6 | The certificate: the exact arithmetic form | 1 | P §6 |
| 7 | The cascade: constructing the certificate | 1 | P §7, §8 |
| 8 | **The framework stated** — the equivalence chain in one place | 1 | consolidation |
| 9 | **The existence question** — the universal quantifier | 2 | new, short |
| 10 | Structural certificate rules | 2 | P §10, §11 |
| 11 | What the rules cover: the trichotomy | 2 | P §12 |
| 12 | The middle is self-similar, but mixed | 2 | P §12 |
| 13 | The certificate condition reparameterised: `R` and the clear set | 2 | **M §11** |
| 14 | Candidate geometry: rescaling, blocking, reflection, edge witnesses | 2 | **M §13, §14, §15** |
| 15 | What the universal question has been reduced to | 2 | **M §15** |
| 16 | General `n` | both | P §13 + **M §16** |
| 17 | Verification | — | P §14 + M §7 |
| 18 | What remains to prove | — | assembled from grades |
| 19 | Glossary / references | — | P §15 |

*§3 is a **precursor**, not a link in the equivalence chain. It is Palelei (2026) and motivates the
framework; §8's chain does not pass through it. Flagged so it is not mistaken for a dependency.

**§8 and §9 are the hinge.** §8 closes Layer 1 by stating the equivalence chain as a finished object.
§9 opens Layer 2 by stating, in one short section, that the remaining question is the universal
quantifier and not a missing direction. Everything that has gone wrong in previous drafts happened
because these two jobs were done by the same prose.

---

## Part B — disposition of every result now in `PAPER_v6`

Unchanged in content from map v1; renumbered to the two-layer targets.

| result in v6 | v6 § | goes to | layer | note |
|---|---|---|---|---|
| Definition (lonely at `t`) | 3 | **2** | 1 | closedness is the mechanism |
| Theorem 3.1 (two flanking gaps) | 3 | **2** | 1 | |
| Theorem 3.2 (regular `n`-gon) | 3 | **2** | 1 | |
| Corollary 3.3 (never exactly `n−1`) | 3 | **2** | 1 | |
| §4 boundary discipline (unnumbered) | 4 | **2** | 1 | **Palelei 2026 §2.2** |
| Theorem 3.4 (`φ(n)` law) | 3.1 | **3** | 1* | **Palelei 2026** — precursor |
| Theorem 3.5 (displacement) | 3.2 | **3** | 1* | shorten |
| Theorem 3.6 (survival criterion) | 3.2 | **3** | 1* | shorten; the reason the problem goes runner-by-runner |
| Theorem 5.1 (earliest possible instant) | 5 | **4** | 1 | the framework proper begins |
| Theorem 5.2 (ratio condition) | 5 | **4**, restated at **10** | 1, 2 | a scale fact in Layer 1; rule R1 in Layer 2 |
| Definition (opening) | 6 | **5** | 1 | |
| **Theorem 6.1** (lonely ⟺ flank has lonely opening) | 6 | **5** | 1 | the paper's hinge; see F.8, F.10 |
| Theorem 6.2 (modular criterion, Beatty form) | 6 | **6** | 1 | split from 6.1 — form, not localisation |
| Definition (in the way / next opening / move) | 7 | **7** | 1 | |
| §7.1 worked example | 7.1 | **7** | 1 | keep entire |
| Theorem 8.1 (Construction) | 8 | **7** | 1 | |
| Theorem 8.2 (Localisation) | 8 | **7** | 1 | |
| **Theorem A** (`doors_agree`) | 8 | **7**, consolidated at **8** | 1 | stated in 7; §8 draws the chain together |
| Observation 9.1 (cascade length, order five) | 9 | **13** — see E.1 | 2 | |
| Rules R1–R7 | 10 | **10** | 2 | regrouped by mechanism |
| §10.1 failure conditions of the rules | 10.1 | **15** | 2 | the re-framing that makes 15 work |
| §11 `φ(n)` and primality | 11 | **10** | 2 | the totient belongs with the rules it governs |
| §12 trichotomy (`M`, `c`) | 12 | **11** | 2 | |
| §12 the middle is self-similar | 12 | **12** | 2 | |
| §12 the `{1,2,3,5}` example | 12 | **12** | 2 | the centre of §12 |
| §12.1 reach of the rules | 12.1 | **11**, as a remark | 2 | caveat load-bearing — F.4 |
| §13 general `n` | 13 | **16** | both | |
| §14 formal verification | 14 | **17** | — | |
| §15 glossary | 15 | **19** | — | |

### Rules regrouped by mechanism (target §10)

| target | rule | condition |
|---|---|---|
| 10.1 Scale control | R1 | `d_max ≤ (n−1)·d_min` |
| 10.2 Band control | R2 | every disparity in the band ladder |
| 10.3 Non-resonant structure | R3 | `gcd(e,n) = 1`, no disparity divisible by `n` |
| 10.4 Resonant structure | R4, R5 | divisible flank (`n` prime); self-similar reduction |
| 10.5 Divisibility | R6 | some `q ≤ n` divides no disparity |
| 10.6 Free disparity / real case | R7 | one disparity off the `P`-lattice of the rest |
| 10.7 The totient behind them | — | v6 §11 |

---

## Part C — the import from `MANUSCRIPT_v20`

Listed by subsection so a miss is visible individually rather than absorbed into a count. Placement
changed from map v1; contents and grades unchanged.

### Into target §13 — the reparameterisation (M §11)

| M subsection | results | status |
|---|---|---|
| 11 The ratio `R` | 11.1, 11.2 | `[PROVED]` |
| 11.1 What Existence reduces to | the `s_i·R mod 8 ∈ [1,7]` equivalence | **reformulation — F.1** |
| 11.2 The frontier, where the maximum sits | measurements | `[EMPIRICAL]` |
| 11.3 The AP is extremal, and the cage says why | 11.3 | `[PROVED]` + `[EMPIRICAL]` |

### Into target §14 — candidate geometry (M §13, §14, §15)

| M subsection | results | n |
|---|---|---|
| 13A–13E The covering scan as a rule | 13.1–13.11 | 11 |
| 14A The rescaling family | 14.1–14.4 | 4 |
| 14B The `n−1` constant, again | 14.5 | 1 |
| 14C Who can block | 14.6–14.8 | 3 |
| 14D One symmetry at four levels | 14.9–14.13 | 5 |
| 14E Two inverted patterns | 14.14–14.16 | 3 |
| 14F The unique degenerate modulus | 14.17–14.19 | 3 |
| 14G The witness is tight somewhere (edge witness) | 14.20–14.26 | 7 |
| 15A The spine at every order | 15.1–15.3 | 3 |
| 15B The split law | 15.4–15.7 | 4 |
| 15C Reflection at general order | 15.8–15.14 | 7 |
| 15D Flanks and candidates are one language | 15.15–15.20 | 6 |
| 15E Small-denominator flanks | 15.21–15.22 | 2 |
| 15F The last class and the denominator boundary | 15.23–15.30 | 8 |
| 15G The −7 opening | 15.31–15.35 | 5 |
| 15H A flank has exactly `e` openings | 15.36–15.39 | 4 |
| 15I First-lap clearance | 15.40–15.46 | 7 |
| 15J The covering count | 15.47–15.50 | 4 |
| 15L The small end, reach of one candidate | 15.51–15.56 | 6 |
| 15M The anatomy of `q = L(m)` | 15.57–15.62 | 6 |
| 15N The window geometry | 15.63–15.67 | 5 |
| 15O Hypotheses removed | 15.68–15.70 | 3 |
| 15P Small moduli forbid at most two residues each | 15.71–15.73 | 3 |

*`MANUSCRIPT_v20`'s own lettering skips `15K`, `15Q` and `15R` — verified, zero occurrences. The
theorem numbers run contiguously `15.1`–`15.73`, so no subsection is missing.*

**M §13 is a dependency, not an option.** §15 opens: *"§13 made the covering question exact over `ℤ`
and §14 described its symmetry."* Map v1 listed §13 as an orphan; it is placed here.

**Grades, from M §14I and §15S, carried unchanged.** 14.1–14.26 and 15.1–15.73 are `[PROVED]`, Lean,
axiom-clean, zero `sorry` / `native_decide` / `unsafe` / `admit`. Measurements beside them are
`[EMPIRICAL]`, bound to script, sample and range. 14.20–14.26 hold at every order; 14.9–14.19 are
stated at order 8, with 14.11–14.13 and 14.17–14.19 having general-`n` analogues **by computation,
not by proof**.

### Into target §16 — general `n` (M §16)

16A order-free obligation · 16B order five, move-count shape false · 16C `φ(n)` is the discriminator
· 16D three further `φ(n)` sites · 16E rules with exact conditions · 16F trichotomy and where the
rules stop · 16G the flank index · 16H instants not indexed by the arrangement · 16I incommensurable
disparities · 16J Branch B, one regularity forced · 16K refuted and withdrawn in v20 · 16L what is open.

---

## Part D — target sections with no existing written material

**D.1 — Target §9, the existence question.** Short, and the most important new writing in the paper.
It must state that Layer 1 is closed, that the conjecture is the universal quantifier over
configurations, and that what follows constrains that quantifier rather than completing an
equivalence. **No new mathematics is required** — this is a statement of what the existing theorems
do and do not say. Under map v1 this section did not exist and its job was being done badly by
several others.

**D.2 — Target §8, the framework stated.** A consolidation of Theorems 6.1, 6.2, 8.1, 8.2 and
Theorem A into the single chain. No new mathematics.

**D.3 — The blocker equivalence, formerly map v1's Part D.1.** The boxed
`existence ⟺ ∃(s,m) B_s(m) = ∅` **is still not a theorem anywhere in `MANUSCRIPT_v20`**, and the
ingredients remain as v1 recorded them: the candidate family (14.1–14.4), who can block
(14.6–14.8), the edge witness (14.20–14.26), the clear set (§11.1).

**What changed is its weight.** Under the two-layer framing it is no longer the paper's destination.
§15's job is to state what the universal question has been *reduced to and constrained by*, which the
existing `[PROVED]` results already support. The box is now **optional**. If it is wanted it still
needs a citation, a proof, or a `[OPEN]` grade with no `⟺` asserted — but the paper no longer depends
on it.

**D.4 — Target §1 and the abstract.** Deferred by instruction: abstract last, introduction
second-last.

---

## Part E — orphans

**E.1 — Observation 9.1, cascade length unbounded at order five.** `[VERIFIED — exact rational
arithmetic, 3 ≤ κ ≤ 100; not formalised]`. Its companion fact is that `R` stays bounded (`→ 3/2`)
while the length grows. That pairing is a statement about `R`, so its home is **§13**, as the reason
for working with `R` rather than with cascade length. Moved from v1's recommendation only in
numbering.

**E.2 — M §12, depth as a function on the profile space.** Still unplaced. `R`-adjacent; belongs with
§13 or §14 if kept.

**E.3 — M §6A the firewall, M §5 no external dependency, Appendix A routes closed.** The
manuscript's self-discipline apparatus. A submission paper may omit them, but that is deletion of
recorded content and needs the author's word. **Note F.2 makes part of §6A load-bearing for §13.**

---

## Part F — caveats that must survive the move

A `compile-diff` run before promotion should check each by name.

**F.1 — M §11.1 is a reformulation.** It says, in italics: *"This is a reformulation, not progress
toward a proof."* No bound is established; `R < 12` rests on 12.2 million profile evaluations and
`R < 16` on those plus Theorem 11.2; the counting gives a factor of 1.5 against. Keeping the sentence
is compatible with following the reformulation with its structural consequences.

**F.2 — M §11.1 is admitted by a ruling, not by the firewall.** It argues by covering, which §6A's
row bans in terms. It is admitted by the author's ruling of 2026-09-18 that the ban prevents covering
being *imported*, and that an argument from the framework's own objects is not that. Readers who
reject the ruling read §13 as conditional. **Theorems 11.1–11.2 do not depend on it.** All three
sentences travel together.

**F.3 — "No result in §14 bears on Existence."** §14I says exactly this. §14's material moves into
target §14, inside Layer 2. **The move is of position, not status.** Under the two-layer framing this
is easier to honour than under v1's: Layer 2 is explicitly the analysis of the universal question,
and constraining a question is not bearing on it.

**F.4 — Reach figures are not progress.** A count over an enumeration measures that enumeration; the
domain carries no canonical measure; the same rule scores differently under different schemes. Must
not be shortened when §12.1 becomes a remark.

**F.5 — Theorem 15.20 is vacuous and must not be cited as a route.** §15S: a true implication whose
hypothesis is refuted by `[-4, 0, 1, 3, 4, 5, 7, 8]`, subject `0`, flank `e = 8`. It sits inside
15.15–15.20, imported wholesale into target §14.

**F.6 — The `φ(n)` law is Palelei (2026).** Precursor, not a result. Restored in v6; must not regress
when it becomes §3. It is also **not a link in the §8 chain**.

**F.7 — Theorem numbering.** Everything in Parts B and C is renumbered. The §17 crosswalk must be
rebuilt against declarations, not against old numbers.

**F.8 — The chain is equivalences, not sufficient conditions.** The paper must not read as *"here is
a method which might find loneliness"*. It says *"loneliness has this exact structural form"*. The
forward direction — any lonely instant necessarily induces a lonely opening — is the substantive one;
the converse is immediate once the certificate is defined correctly.

**F.9 — Existence is the universal quantifier, not a missing direction.** Layer 1 has no gap. Any
sentence implying the equivalence is incomplete, or that Layer 2 finishes it, is wrong.

**F.10 — Two sentences invert the claim and must be reversed.** Verified by enumeration —
`PAPER_v6.md` uses "search" four times:

| line | text | verdict |
|---|---|---|
| 90 | "so nothing is searched or ranked" | **correct** — leave |
| 310 | "So a search for lonely instants may be confined to this countable family without loss" | **reverse** — this is F.8's failure in one sentence |
| 323 | "so the search `0 ≤ j < e` decides the question" | **reverse** — it is a finite check, not a search |
| 352 | "Three facts make this well defined and free of search" | **correct** — leave |

Lines 90 and 352 already carry the right framing and must not be "corrected" along with the other two.

---

## Part G — decisions the map cannot make

1. **Where Layer 1 ends.** The map places the boundary after the certificate and the cascade, at §8.
   The alternative is to end Layer 1 at §6 and treat the cascade as the first item of Layer 2, on the
   grounds that it *constructs*. The author's framing — "the cascade gives a deterministic way of
   reaching such a certificate" — and Theorem A's status as an equivalence both favour §8. Confirm.
2. **Is the `R`-form Layer 1 or Layer 2?** It is an *exact* reparameterisation, so it does not weaken
   the chain; but its work is entirely in service of the universal question. Placed at the head of
   Layer 2 (§13). Confirm.
3. **E.1** — Observation 9.1 to §13 as recommended, or to §18.
4. **E.2** — M §12 kept or dropped.
5. **E.3** — whether the firewall, M §5 and Appendix A appear at all.
6. **D.3** — whether the blocker box is wanted at all now that it is optional.
7. **Scale.** ~120 imported numbered results against the paper's present 14. Either §14 states the
   structural lemmas in groups and cites the manuscript for individual statements, or the paper
   becomes long. The map assumes grouping.
8. **Title.** Unchanged and still under objection from three reviewers. Out of scope here.

---

## Part H — defect carried forward, and gates owed

**Defect in `PAPER_v6`, uncorrected.** The abstract says *"eight arithmetic conditions"* and §1 says
*"§10 the eight conditions"*. **Only R1–R7 exist — seven.** Confined to the abstract and
introduction, which are by instruction untouched, and it resolves when §10 is rebuilt from the
mechanism grouping. Recorded so it is not lost.

**Gates owed before promoting a v7 draft:**

* `compile-diff` — mandatory before promoting a consolidated document. Checklist is Part F; inventory
  is Parts B and C.
* The §17 crosswalk regenerated against declarations (F.7).

---

## Part I — checks run on this map

| # | claim | check | result |
|---|---|---|---|
| 1 | Part C's theorem ranges are contiguous, total 73 | cumulative sum of §15S module counts | `15.1`–`15.73` — matches |
| 2 | no §15 subsection dropped | grep `### 15K`, `### 15Q`, `### 15R` | 0 — the lettering itself skips |
| 3 | `PAPER_v6` contains none of M §§11–15 | grep `clear set`, `blocker`, `8m+1`, `reflection`, `rescal`, `edge witness` | 0, 0, 0, 0, 0, 0 |
| 4 | seven rules exist, not eight | enumerate bolded rule labels | `R1`–`R7` — seven |
| 5 | §14 grades and the "bears on Existence" sentence | read §14I | `[PROVED]` 14.1–14.26; sentence verbatim |
| 6 | §11.1's reformulation and ruling caveats | read §11.1 | both verbatim |
| 7 | Theorem 15.20 vacuity | read §15S | present, with the refuting arrangement |
| 8 | **F.10's four "search" sites** | grep `search` in `PAPER_v6.md` | lines 90, 310, 323, 352 — two to reverse, two correct |
