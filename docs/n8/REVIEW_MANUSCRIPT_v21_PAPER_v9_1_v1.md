# Review: MANUSCRIPT_v21 and PAPER_v9_1

2026-09-25. Read in full: `MANUSCRIPT_v21.md` §0–§17 and the references; Appendices A–D skimmed at their
boundaries only. `PAPER_v9_1.md` read in full. Neither file was edited. Line numbers refer to those two files.

Grades follow the project scheme. "Checked" means a script or grep on disk; each one is named.

---

## Part 1. MANUSCRIPT_v21

Findings are ordered by whether they affect a grade. M1–M4 do. M5–M8 are presentation, stale figures and
gate hygiene.

### M1. The Existence grade rests on a premise the manuscript does not supply

**Where.** Abstract l.473–477 ("**Closed** … it follows from an outcome this manuscript proves"); §6.7
l.1108–1131; §9 l.2013–2021; §6.9 l.1469; §11.3 l.2518; the v17 record l.228.

**What the text says.** §6.7 l.1129–1131: *"Loneliness at eight runners holds. By the equivalence, so does
Existence … That is a consequence of Localisation, which this manuscript proves, and it needs nothing else."*

**The defect.** `doors_agree` proves `DoorFlank v k ↔ LonelyForSubject v k`. That is correct and axiom-clean.
An equivalence moves truth from one side to the other; it does not supply truth to either side. The step
therefore needs the premise "loneliness at eight runners holds". The only source for that premise anywhere in
the document is Rosenfeld's computer verification (abstract l.457). Nothing in §§1–17 proves it. So the
`[PROVED]` tag on Existence is a `[CITED — Rosenfeld 2025]` tag in substance.

**Where this contradicts the manuscript itself.**
- §5 l.889: "Nothing else is cited."
- Abstract l.458: "The account below is analytic throughout."
- l.1130–1131: "it needs nothing else."
- v21's own §9 l.2180 and §17C l.3549–3550 grade the same content `[OPEN]`. §17C says `existenceAt8_iff_residual`
  makes `ExistenceAt8` equivalent to the `EightResidual` statement, and grades that statement `[OPEN]`.
  `ExistenceAt8` is equivalent to `LonelyRunnerAt8` (see M2), so one statement carries `[PROVED]` in §6.7 and
  `[OPEN]` in §17C.

§1.3 l.544 tries to separate the two by saying "obligation" refers to the derivation, never to the statement.
That separation does not rescue the tag, because the `[PROVED]` tag sits on the statement.

**Owner ruling needed.** There are two consistent readings, and the text currently asserts both:
- (a) The statement is true because Rosenfeld proved it. Then grade it `[CITED — Rosenfeld 2025]`, grade the
  framework's derivation `[OPEN]`, and remove "nothing else is cited", "analytic throughout" and "needs nothing
  else".
- (b) Only the framework's own derivation counts. Then the grade is `[OPEN]`, matching §17C.

The owner's ruling of 2026-09-24 ("the obligation is equivalent to loneliness in both directions … = proof")
covers the *form* of a proof: exhibiting `(e, k)` on a condition proves that case. It does not assert that the
cases are exhausted. PAPER_v9_1 §9 states this correctly.

### M2. The §17B standing question has a short mathematical answer (positive)

**Where.** §17B l.3476–3481 ("Finding 1"), §17G; §6.7 l.1234–1236; Appendix D, final paragraph.

**The fact.** `Spec/Target.lean` l.436–441 already states the argument. Every set `ds` of distinct positive
reals with `4 ≤ card ≤ 7` arises from an injective arrangement. Put the subject at `0`, a runner at `+d` for
each `d ∈ ds`, and a runner at `−d` for `7 − card` of them. The `+d` are distinct and positive, the `−d` are
distinct and negative, and `7 − card ≤ card` holds exactly when `card ≥ 4`. The case `card ≤ 3` is
`exists_lonely_of_card_le_three` `[PROVED]`. So `LonelyRunnerAt8 → ExistenceAt8`, and with
`lonelyRunnerAt8_of_existence` the two are **equivalent**. Via `existenceAt8_iff_residual`, the `EightResidual`
statement is therefore equivalent to the conjecture at eight, not merely sufficient for it.

**Defects this exposes.**
- §6.7 and `Target.lean` grade the realisation `[EMPIRICAL — 20,000 sets, no failure]`. It is a direct
  construction and could be a short Lean theorem, `existenceAt8_iff_lonelyRunnerAt8`. It is currently graded
  below what it is.
- Appendix D's scope line, "a 7-subset need not arise from eight real speeds", is false. `(0, d₁, …, d₇)`
  realises every set of seven distinct positive reals.

**What stays open.** The logical half of Finding 1 is answered. The proof-shape half is still the owner's call:
the realising arrangement is a special one (subject at `0`, runners placed symmetrically), so a proof of the
residual cannot use cross-subject structure of a *general* arrangement.

### M3. Theorem 11.3: the statement holds; one proof step is false

**Where.** §11.3 l.2493–2500, graded `[PROVED — in the text]`.

**The false step.** *"`i = 1` forces `R mod 8 ∈ [1,7]` and `i = 7` forces `7R mod 8 ∈ [1,7]`, and those two alone
leave only the odd integers in `[1,15]`."* This is false. `R = 3/2` and `R = 9/7` pass both conditions. On an
exact grid of denominator 840, 7,214 points in `[1,7] ∪ [9,15]` pass `i = 1` and `i = 7`. With all seven
readings, the clear set is exactly `{1, 3, …, 15}`, so the statement is right.
Checked by `experiments/n8/thm11_3_proof_step_check_v1.{py,out}`.

**Repair, from the manuscript's own tools.** The readings `1, …, 7` are the pairwise differences of
`0, R/8, 2R/8, …, 7R/8`. If every reading is clear, those eight points are pairwise at least `1/8` apart. By
Theorem 4.3 (`grid_of_pairwise`) they then form the regular 8-gon, so `R/8 = a/8` with `gcd(a, 8) = 1`, and `R` is
an odd integer. Until the text carries this argument or an equivalent one, the grade should be `[VERIFIED]`.

### M4. §14C overstates `unit_never_blocks`

**Where.** §14C l.2759–2762, and the "blocker count ≤ n−3" summary in §9 l.2089–2090.

**The mismatch.** The manuscript says "the unit reading never blocks **any** candidate" and "the blocker count at
**any** candidate is at most `n − 3`". The Lean theorem carries the band hypothesis `sk ≤ A ≤ 7·sk`
(`experiments/n8/BlockerCount_v1.lean:40`). The docstring there also says "any candidate". PAPER_v9_1 §14.3
states it correctly: the band hypothesis is required, and without it the bound is `n − 2`. The manuscript and
the docstring should both adopt the paper's wording.

### M5. The abstract is stale against v21

- It does not mention §17: orders three to seven proved inside the framework for real speeds, and order eight
  reduced to `EightResidual`.
- l.481–482 say "**Three** Lean 4 artefacts", name two, and continue "**Both** have no `sorry`". `Spec` is missing.
- l.486–488 list the general-`n` difference counts but omit the v21 closures (five differences at
  `n = 6 … 10`, and at most six disparities at every `n ≥ 7`).

v20's record (l.60–63) describes this defect class: a figure changed in one place and not in the abstract,
which is outside gate check [6].

### M6. The Spec gate prints a false banner

`scripts/nN/spec_gate.sh:271` prints *"LRC is NOT proved at any order."* The tree it gates contains
`lonelyRunnerAtN_five`, `_six` and `_seven`. Each is stated as `LonelyRunnerAtN n` (checked in `DoorsN.lean:393`
and `RealFiveN/RealSixN/RealSevenN.lean`), and each appears in its axiom witness. The witness v21 cites,
`LonelyRunner/experiments/nN/spec_gate_small_resolution.out`, carries this now-false line. A suggested
replacement: "proved in Lean at orders 3–7; not proved at order 8".

### M7. The manuscript carries two incompatible tests for what discharges a case

- **§0** (v20, owner 2026-09-24) says a case is discharged by `∃ (e, k)` "by any means — pigeonhole,
  contradiction, induction, construction", and that a closed form is more than is owed.
- **§6A** l.1765–1769 and **§6.7's amendment** l.1223–1228 say the *argument* must bound the witness. They keep
  Propositions 6.10–6.11 withdrawn because those conclude that a lonely opening exists "without naming or bounding
  one".

Under §0, the stated ground for that withdrawal no longer applies. §6.9 l.1367 says their arithmetic is "not in
question", so the two propositions look reinstatable as proved cases. Their measured reach is still small: the
sum criterion fires only at `|J| ≤ 1`, l.1372–1374. PAPER_v9_1 §2.2 carries both tests side by side
(l.223–228 and l.247–252). **Owner ruling needed.** Which test governs, and do 6.10–6.11 return?

### M8. Presentation and stale figures

1. l.1407: the Theorem 6.14 blockquote starts in the middle of a paragraph, so it will not render as a block.
   This is the same defect class as v20's §8 heading.
2. §9 l.2115–2118: a truncated sentence ("§15 carries 81 axiom-clean declarations across 17") runs into
   "**Three corrections carried in v14.**". There is also "…and The figure". The 81/17 figures are v14's; §15S
   gives 73 across 15 after v15.
3. §10.4 still lists `DivisorOrder6_v1.lean` and `CardSix_v1.lean`, which v15 removed from §15.
4. l.2885 repeats itself: "locates the witness, and locates the witness."
5. Appendix order: "Routes 15–20" and "A note on two sampled minima" sit inside Appendix B after B.12, and B.9 sits
   after Appendix C.
6. l.1397 begins with a lowercase letter, and its claim "the required `k` is unbounded" has no grade. §6.10's
   heading "The index is bounded given the ratio" states as fact what its body grades as measured.

### What was checked and holds

- The `(a, q)` / band / residue criteria (Prop 2.1, Thm 6.12, Thm 6.14, Thm 6.19) agree with each other and
  with PAPER Theorem 10.
- Theorem 6.25's bound `λ < (8M+1)/(8M−1) ≤ 9/7`. Theorem 11.2's band argument.
- The disparities, distances and certificate `(7, 1)` in the §7.1 example, recomputed by hand.
- The §17 artefacts exist on disk: `spec_gate_small_resolution.out` ends `GATE PASS … 1522 … EXIT 0`, and
  `real_five_axioms.out`, `order_six_real_axioms.out`, `order_seven_axioms.out`, `real_eight_axioms.out`,
  `order_eight_cases_axioms.out` and `eight_residual_count_v1/v6.out` are all present.

**Not checked.** Gates were not re-run. The §12–§17 measurements were not reproduced, apart from M3. Appendices
A–C were not read in full.

---

## Part 2. PAPER_v9_1 — what v21 makes out of date

The paper is the more careful of the two documents on Existence. §9 and §18 state that the universal
quantifier remains. The paper should not take over the manuscript's "Closed" wording (M1).

### Content v21 adds that the paper lacks

1. **Orders three to seven inside the framework** (v21 §17A), for every real arrangement, axiom-clean. Order six is
   BHK with Proposition 11 and §5 converted to named instants. Order seven is Barajas–Serra with primality reduced
   to `φ(7) = 6` and no `gcd` hypothesis. Real speeds follow from whole numbers through the any-row merge and
   stepping. The paper's §1 still says that `n ≤ 7` is "settled … by arguments particular to each order".
2. **§16's order-five paragraph is stale.** "Four disparities are settled at orders six and seven and not at
   five … order five is the hard one" and "Order five reduces to `card = 4` exactly" describe a case that
   `OrderFiveN.lonelyRunnerAtN_five` has since closed.
3. **The trichotomy's upper end is closed at order eight, not only reduced** (§11 table, §15.1, §18). R5 leaves
   `M` with at most six disparities at threshold `1/8`, and native order seven clears any at most six at
   `1/7 ≥ 1/8`. Similarly, at order eight the cost count of §12 is the `descent` case,
   `lonely_eight_of_descent`. So the §17 sentence "the one statement proved in the text and not formalised is the
   cost count of §12" needs a scope qualifier. I did not check whether the general-`n` cost count is formalised.
4. **The order-eight case list and the reduction to one statement** (v21 §17B–§17C): `existenceAt8_iff_congruence`,
   `lonely_eight_or_residual`, `existenceAt8_iff_residual`, and the fourteen-row case table. The paper's Layer 2
   has only the seven general-`n` rules.
5. **§15's "sufficient conditions not among the rules of §10" is partly wrong at order eight.** v21 §17C proves the
   last-class results are R1 there (`lastClass_is_spread`), and so is the `−7` opening at the largest flank.
   First-lap clearance is **provisional** by the author's ruling of 2026-09-25, and the paper should carry that
   qualification.
6. **Lower orders are native** (author, 2026-09-25). This matters for how the paper states R5's reduction and the
   "nothing depends on" sentence in §1.

### The paper's own defects

- **P1.** §2.2 l.216–221 and §3 l.307–311 justify "the extremal configuration any general argument must cover" by
  Theorem 2. Theorem 2 is about all `n` runners being lonely at once. The fact needed is per-runner: the end
  runner of the progression is lonely only at isolated instants (manuscript §1.2). Also, l.219–220 give the
  `n = 8`, `d = 1` instants inside a paragraph stated for general `n`.
- **P2.** §10.7 l.881–883 and §16 l.1190–1191 say "which is why even orders are harder. Order eight is `2³`, and
  that — not its size — is the difficulty." No result in the paper supports this. The paper's own data runs
  against it: `φ(6)/6 = 1/3 < φ(8)/8 = 1/2`, yet order six is proved. It is a difficulty verdict of the kind the
  project bans. Restate it as the specific fact, R4's budget `|L| < φ(n)`, or delete it.
- **P3.** Missing hypotheses. R6 (§10.5 and the table) needs whole-number disparities, since divisibility is
  otherwise undefined. R7 needs `n ≥ 4` (manuscript §16I, `IrrationalN.lonely_of_one_free`).
- **P4.** The abstract's "seven structural conditions" counts R3, which the paper itself shows R6 subsumes
  (§10.8), and R5, which it calls a reduction (§10). The count is correct only with that reading stated.
- **P5.** References differ between the two documents. The paper cites Rosenfeld 2025b and Trakulthongchai 2025;
  the manuscript does not. The arXiv identifiers were not verified in this review.

### What was checked and holds

- The proofs of Theorems 1, 2, 3, 4, 5, 6, 7, 9, 10 (including the Beatty form), 11, 12 and 13, and the arguments
  for R3, R4, R5 and R6, read line by line. Details checked include R4's `a = ke + 1` residue computation and its
  `{0, n−1}` exclusion, and R5's three-shift argument for `n ≥ 3`.
- The worked examples: §7.1, including that `1/6` is not an opening and that Theorem 9 returns `9/56` from it; and
  `{1,2,3,5}` at `(5,1)` and `(3,2)`.
- All 56 declarations named in the §17 table resolve in `LonelyRunner/LonelyRunner/LRC/` (a grep over
  `(theorem|lemma|def) <name>`; no misses).

---

## Owner decisions this review surfaces

1. M1: grade Existence as (a) `[CITED — Rosenfeld]` for the statement plus `[OPEN]` for the derivation, or
   (b) `[OPEN]`.
2. M2: prove `ExistenceAt8 ↔ LonelyRunnerAt8` in Lean. Then §17B's question reduces to its proof-shape half.
3. M7: which discharge test governs, §0 or §6A, and whether Propositions 6.10–6.11 return.
4. Whether to cut PAPER v10 now, absorbing Part 2 items 1–6 and P1–P5, or after the §17B ruling.
