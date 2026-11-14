# PAPER v7 — Section Map

*Version 1, 2026-09-22. A placement document, not a draft. It says where every existing result goes
under the dependency structure the author set out, and names what is missing, what is orphaned and
what must not be changed in the move. No prose is rewritten here, no abstract or introduction is
written, no grade is moved, and no result is dropped.*

**Constraints this map operates under, as given:**

1. Reorganise existing material into the dependency structure. 2. Invent no connective claims.
3. Strengthen no proof status. 4. Write no abstract and no introduction. 5. Delete no result merely
because it does not fit the narrative.

---

## 0. The two sources, and why the map spans both

| | file | numbered results | role |
|---|---|---|---|
| **P** | `PAPER_v6.md` | 14 numbered + Theorem A + 3 definitions + rules R1–R7 | the current submission draft |
| **M** | `MANUSCRIPT_v20.md` | §§11–16 carry ~109 further numbered results | the manuscript of record |

The decisive fact for this restructure: **`PAPER_v6` contains none of `MANUSCRIPT_v20` §§11–15.**
Checked by name, not by impression — `clear set`, `blocker`, `8m+1`, `reflection`, `rescal` and
`edge witness` each return matches in `MANUSCRIPT_v20.md` and **zero** in `PAPER_v6.md`.

So the target sections 10–12 are not a re-ordering of the paper. They are an **import** from the
manuscript of record, and they roughly double the paper's mathematical content. That is the change
of centre of gravity; the map treats it as such.

---

## Part A — the target spine

```
LRC
 ├── circle geometry ─── closed loneliness ─── open obstruction zones
 ├── subject-relative ── disparities ── d_min scaling ── readings s_i·u
 ├── boundary localisation ── openings (j+1/n)/e ── certificate ── modular criterion
 ├── cascade ── deterministic construction ── localisation ── halting ⟺ certificate ⟺ lonely
 ├── certificate rules ── explicit sufficient structures
 └── existence reduction ── R ── clear set ── candidates (8m+1)/s ── non-blocking
                                 ── rescaling ── reflection ── endpoints ── edge witness
                                 └── remaining obstruction: can all admissible candidates be blocked?
```

| § | title | source |
|---|---|---|
| 1 | The problem and the framework | new, written last with the intro |
| 2 | The geometric starting point: isolation and its boundary | P §3, §4 |
| 3 | One runner, one scale | P §5 |
| 4 | The boundary reduction: openings and certificates | P §6 |
| 5 | The cascade: construction, not search | P §7, §8 |
| 6 | The certificate is the object of existence | P §6, §8 consolidated |
| 7 | Structural certificate rules | P §10 |
| 8 | What the rules actually cover | P §12 |
| 9 | The middle is self-similar, but mixed | P §12 |
| 10 | The ratio / candidate formulation | **M §11** |
| 11 | Candidate geometry and edge witnesses | **M §14, §15** |
| 12 | The actual existence obstruction | **M §15** — see Part D.1 |
| 13 | The rules revisited as partial solutions | P §10, §12 re-framed |
| 14 | General `n` | P §13 + **M §16** |
| 15 | Verification | P §14 + M §7 |
| 16 | What remains to prove | new, assembled from grades |
| 17 | Glossary / references | P §15, references |

---

## Part B — disposition of every result now in `PAPER_v6`

Every numbered result, every definition, every rule. Nothing omitted.

| result in v6 | v6 § | goes to | note |
|---|---|---|---|
| Definition (lonely at `t`) | 3 | **2.1** | leads; the closedness is the mechanism, not an aside |
| Theorem 3.1 (two flanking gaps) | 3 | **2.1** | |
| Theorem 3.2 (regular `n`-gon) | 3 | **2.2** | |
| Corollary 3.3 (never exactly `n−1`) | 3 | **2.2** | |
| Theorem 3.4 (`φ(n)` law) | 3.1 | **2.3** | **Palelei 2026** — precursor, not a result of this paper |
| Theorem 3.5 (displacement) | 3.2 | **2.4** | shorten |
| Theorem 3.6 (survival criterion) | 3.2 | **2.4** | shorten; keep as the reason the problem goes runner-by-runner |
| §4 boundary discipline (unnumbered) | 4 | **2.1** | **Palelei 2026 §2.2** — attribution added in v6 |
| Theorem 5.1 (earliest possible instant) | 5 | **3** | this is where the framework proper begins |
| Theorem 5.2 (ratio condition) | 5 | **3**, restated at **7.1** | it is both a scale fact and rule R1 |
| Definition (opening) | 6 | **4** | |
| Theorem 6.1 (lonely ⟺ some flank has a lonely opening) | 6 | **4** | the localisation theorem; the paper's hinge |
| Theorem 6.2 (modular criterion, Beatty form) | 6 | **4** | |
| Definition (in the way / next opening / move) | 7 | **5** | |
| §7.1 worked example | 7.1 | **5** | keep entire; it is the only place the reader watches the machine run |
| Theorem 8.1 (Construction) | 8 | **5** | |
| Theorem 8.2 (Localisation) | 8 | **5** | |
| **Theorem A** (`doors_agree`) | 8 | **5**, consolidated at **6** | stated in 5, its meaning drawn out in 6 |
| Observation 9.1 (cascade length unbounded at order five) | 9 | **see Part E.1** | no clean home in the spine |
| Rules R1–R7 | 10 | **7.1–7.6** | re-grouped by mechanism, below |
| §10.1 failure conditions of the rules | 10.1 | **13** | this is the re-framing that makes 13 work |
| §11 `φ(n)` and primality | 11 | **7.7** | the totient belongs with the rules it governs |
| §12 trichotomy (`M`, `c`) | 12 | **8** | |
| §12 the middle is self-similar | 12 | **9** | promoted from "what is open" to the object of a section |
| §12 the `{1,2,3,5}` example | 12 | **9** | the centre of 9, as the author directs |
| §12.1 reach of the rules | 12.1 | **8**, as a remark | see Part F.4 — the caveat is load-bearing |
| §13 general `n` | 13 | **14** | |
| §14 formal verification | 14 | **15** | |
| §15 glossary | 15 | **17** | |

### Rules regrouped by mechanism (target §7)

| target | rule | v6 condition |
|---|---|---|
| 7.1 Scale control | R1 | `d_max ≤ (n−1)·d_min` |
| 7.2 Band control | R2 | every disparity in the band ladder |
| 7.3 Non-resonant structure | R3 | `gcd(e,n) = 1`, no disparity divisible by `n` |
| 7.4 Resonant structure | R4, R5 | divisible flank (`n` prime); self-similar reduction |
| 7.5 Divisibility | R6 | some `q ≤ n` divides no disparity |
| 7.6 Free disparity / real case | R7 | one disparity off the `P`-lattice of the rest |
| 7.7 The totient behind them | — | v6 §11 |

---

## Part C — the import from `MANUSCRIPT_v20`

Listed by subsection with the numbered results each carries, so that a miss is visible individually
rather than absorbed into a count.

### Into target §10 — the ratio formulation (M §11)

| M subsection | results | grade |
|---|---|---|
| 11 The ratio `R` | 11.1, 11.2 | `[PROVED]` |
| 11.1 What Existence reduces to | the `s_i·R mod 8 ∈ [1,7]` equivalence | **reformulation — see Part F.1** |
| 11.2 The frontier, where the maximum sits | measurements | `[EMPIRICAL]` |
| 11.3 The AP is extremal, and the cage says why | 11.3 | `[PROVED]` + `[EMPIRICAL]` check |

### Into target §11 — candidate geometry (M §14, §15)

| M subsection | results | n |
|---|---|---|
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
theorem numbers run contiguously `15.1`–`15.73`, so no subsection is missing from the table above.*

**Grades, from M §14I and §15S, carried unchanged.** Theorems 14.1–14.26 and 15.1–15.73 are all
`[PROVED]`, Lean, axiom-clean, zero `sorry` / `native_decide` / `unsafe` / `admit`. Every measurement
quoted beside them is `[EMPIRICAL]`, bound to its script, sample and range. 14.20–14.26 hold at every
order; 14.9–14.19 are stated at order 8, with 14.11–14.13 and 14.17–14.19 having general-`n` analogues
**by computation, not by proof**.

### Into target §14 — general `n` (M §16)

16A order-free obligation · 16B order five, move-count shape false · 16C `φ(n)` is the discriminator
· 16D three further `φ(n)` sites · 16E rules with exact conditions · 16F trichotomy and where the
rules stop · 16G the flank index · 16H instants not indexed by the arrangement · 16I incommensurable
disparities · 16J Branch B, one regularity forced · 16K refuted and withdrawn in v20 · 16L what is open.

---

## Part D — target sections with no existing written material

**These must be written from existing results or dropped. They must not be filled by invention.**

**D.1 — Target §12, "the actual existence obstruction", and its boxed statement.**
The outline gives, explicitly as a schematic,

```
    B_s(m) = { s' ∈ S : s'(8m+1)/s lies in a forbidden band }
    existence  ⟺  ∃ (s, m) with B_s(m) = ∅
```

The **ingredients** are all present and proved: the candidate family `(8m+1)/s` (14.1–14.4), who can
block (14.6–14.8, blocker count `≤ n−3`), the edge witness forcing a candidate to be tight
(14.20–14.26), and the clear set (§11.1). **The equivalence itself is not stated as a theorem
anywhere in `MANUSCRIPT_v20`.** Writing the box therefore requires one of:

* locating it in the Lean tree or the experiments and citing the declaration; or
* proving it, with the edge witness supplying `⟸` and §11.1 supplying `⟹`; or
* stating it as a *definition plus a conjecture*, graded `[OPEN]`, with no equivalence asserted.

The third is the only one available without new work. **Until one of the first two is done, §12 must
not carry an `⟺`.**

**D.2 — Target §1 and the introduction.** Deferred by instruction.

**D.3 — Target §16, "what remains to prove".** The five `Proved` headings the outline lists are
assembled from existing grades and need no new mathematics. The final `Remaining` heading depends
entirely on D.1.

---

## Part E — orphans: existing results with no home in the spine

**Nothing here may be dropped without an explicit decision.**

**E.1 — Observation 9.1, cascade length unbounded at order five.** `[VERIFIED — exact rational
arithmetic, 3 ≤ κ ≤ 100; not formalised]`. It fits nowhere in the dependency graph because it is not
a step toward the certificate; it is a *negative structural fact* — it kills the move-count shape,
and its companion fact is that `R` stays bounded (`→ 3/2`) while the length grows. That pairing is
precisely a statement about `R`, so its natural home is **target §10**, as the motivation for working
with `R` rather than with cascade length. Recommended placement: §10, opening. Alternative: §16.

**E.2 — M §12, depth as a function on the profile space.** Not in the outline at all. It is
`R`-adjacent and belongs with §10 or §11 if kept.

**E.3 — M §13, the covering scan as a rule (13.1–13.11).** The outline's §11 draws on §14 and §15,
both of which build on §13 — §15's own opening says *"§13 made the covering question exact over `ℤ`
and §14 described its symmetry"*. So §13 is a **dependency of the import, not an optional extra**. It
has no slot in the outline. Recommended: fold into §11 as its first subsection.

**E.4 — M §6A, the firewall; M §5, no external dependency; Appendix A, routes closed.** Not in the
outline. These are the manuscript's self-discipline apparatus. A submission paper may legitimately
omit them, but that is a deletion of recorded content and needs the author's word.

---

## Part F — caveats that must survive the move

These are the statements most likely to be lost, because each one *limits* a result that the new
structure puts in a more prominent position. A `compile-diff` run before promotion should check each
by name.

**F.1 — §11.1 is a reformulation.** `MANUSCRIPT_v20` §11.1 states, in italics: *"This is a
reformulation, not progress toward a proof."* No bound is established; `R < 12` rests on 12.2 million
profile evaluations and `R < 16` on those plus Theorem 11.2; the counting gives a factor of 1.5
against. The outline directs that §10 not stop at the reformulation but follow it with structural
consequences. **That is compatible with keeping the sentence, and the sentence must be kept.**

**F.2 — §11.1 is admitted by a ruling, not by the firewall.** §11.1 argues by covering, which §6A's
row bans in terms. It is admitted by the author's ruling of 2026-09-18 that the ban exists to prevent
covering being *imported*, and that an argument built from the framework's own objects is not that.
Readers who reject the ruling read §11.1 as conditional. **Theorems 11.1–11.2 do not depend on it.**
All three sentences must travel with the section.

**F.3 — "No result in §14 bears on Existence."** §14I says exactly this. The outline promotes §14's
material into the existence architecture (§11). **The promotion is of position, not of status.** §15
is the section titled *"and what Existence now reduces to"*; §14 supplies structural lemmas it uses.
Presenting §14 as bearing on Existence would be a strengthening of proof status and is forbidden.

**F.4 — Reach figures are not progress.** v6 §12.1 already carries this: a count over an enumeration
measures that enumeration, the domain carries no canonical measure, and the same rule scores
differently under different schemes. The caveat must not be shortened when §12.1 becomes a remark.

**F.5 — Theorem 15.20 is vacuous and must not be cited as a route.** §15S: a true implication whose
hypothesis is refuted by the arrangement `[-4, 0, 1, 3, 4, 5, 7, 8]`, subject `0`, flank `e = 8`. It
sits inside 15.15–15.20, which target §11 imports wholesale.

**F.6 — The `φ(n)` law is Palelei (2026).** Precursor, not a result. Restored in v6; must not regress
when §3 becomes §2.3.

**F.7 — Theorem numbering.** Every result in Parts B and C is renumbered by this move. The crosswalk
in target §15 must be rebuilt against declarations, not against old numbers.

---

## Part G — decisions the map cannot make

1. **D.1** — which of the three routes §12's boxed statement takes. This is the single largest open
   question in the restructure, and it determines whether the paper has a destination or a horizon.
2. **E.1** — Observation 9.1 to §10 as recommended, or to §16.
3. **E.3** — M §13 folded into §11 as recommended, or imported as its own section.
4. **E.4** — whether the firewall, §5 and Appendix A appear at all.
5. **Scale.** The import is ~109 numbered results against the paper's present 14. At full detail the
   body would be three to four times its current length. Either §11 states the structural lemmas in
   groups and cites the manuscript for the individual statements, or the paper becomes long. The
   author's call; the map assumes grouping.
6. **Title.** Unchanged from v6 and still under objection from three reviewers. Out of scope here.

---

## Part H — defect found while mapping, and gates owed

**Defect in `PAPER_v6`, uncorrected.** The abstract says *"eight arithmetic conditions"* and §1 says
*"§10 the eight conditions"*. **Only R1–R7 exist — seven.** Verified by enumerating the bolded rule
labels in the file. The error is confined to the abstract and the introduction, which are by
instruction not being touched, and it disappears when §7 is rebuilt from the mechanism grouping. It
is recorded here so it is not lost.

**Gates owed before any promotion of a v7 draft:**

* `compile-diff` — mandatory before promoting a consolidated document. Its checklist is Part F, plus
  Parts B and C as the inventory of what must arrive.
* The verification crosswalk must be regenerated against declarations (F.7).

---

## Part I — checks run on this map

Each claim the map makes about the sources was checked against the files, not recalled.

| # | claim | check | result |
|---|---|---|---|
| 1 | Part C's theorem ranges are contiguous and total 73 | cumulative sum of §15S's module counts | `15.1`–`15.73`, total 73 — matches |
| 2 | no subsection dropped from §15 | grep `### 15K`, `### 15Q`, `### 15R` | 0 — the lettering itself skips |
| 3 | `PAPER_v6` contains none of M §§11–15 | grep `clear set`, `blocker`, `8m+1`, `reflection`, `rescal`, `edge witness` | 0, 0, 0, 0, 0, 0 |
| 4 | seven rules exist, not eight | enumerate bolded rule labels in `PAPER_v6` | `R1 R2 R3 R4 R5 R6 R7` — seven |
| 5 | §14 grades and the "bears on Existence" sentence | read §14I | `[PROVED]` 14.1–14.26; sentence present verbatim |
| 6 | §11.1's reformulation and ruling caveats | read §11.1 | both present verbatim |
| 7 | Theorem 15.20 vacuity | read §15S | present, with the refuting arrangement |

Check 3 is the one the restructure turns on: it is what makes target §§10–12 an import rather than a
re-ordering.
