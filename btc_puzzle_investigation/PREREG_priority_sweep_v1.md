# PREREG — Priority / Literature Sweep of the §2 "undocumented elsewhere" list

**Frozen 2026-07-24. NO SEARCH HAS BEEN RUN. This file is the protocol only.**
Source of the 10 claims: `NEXT_DIRECTIONS_v1.md` §2 (read verbatim, lines 46–65).
Nothing below may be edited after the first query is issued; deviations go in a
separate `PREREG_priority_sweep_v1_DEVIATIONS.md`, never by editing this file.

This is a **review protocol, not a statistical test.** Two framings are held fixed
per the task:
- **"power" = search coverage** = (query variants × databases) actually executed.
- **"matched control" = the positive controls** = known-published results the
  instrument must recover, or the sweep is VOID.

The sweep's product is a **citation map** (per claim: grade + citation(s) + delta +
coverage). It is **never** a "these are all novel" conclusion. The single word
**"novel" is banned from every output.** The strongest statement any claim may
earn is: *"no prior located under the frozen protocol P (variants V, databases D,
date)."*

---

## 1. OBJECT

What we are measuring: for each of 10 claims, **does a paper in the mathematical
literature state the same theorem** (same mathematical object, same conclusion),
a strictly more/less general or adjacent one, or none locatable under a frozen
search.

**Tautology / mis-framing risk, stated before the run.** The §2 list is explicitly
a claim about **this record's originality** ("Stated as a claim about *this
record's* originality, not about the literature"), not a claim that the literature
is empty. Several items are named in **project-internal vocabulary** (Cap Law,
flap, FLD, Claim S, Claim F, "quantum number", k_den). Searching the *name* of an
internal object will return nothing **by construction** and that null is
uninformative — it measures a proxy (the name), not the object (the mathematical
statement). The object is the **mathematical content**, stated in standard terms;
the grade attaches to the content, never the name. See §6 for the per-claim
classification into term-searchable vs concept-only.

---

## 2. STATISTIC — the per-claim grade (exactly one, three levels, pre-committed)

For each claim, exactly one grade, decided by the rule below and by nothing added
later:

- **FOUND-IN-LIT** — a located paper states the **same theorem**: same object, same
  conclusion. REQUIRED to record: full citation, and the **delta** (what is
  identical, what differs — generality, field, hypotheses). "Same" is frozen now as
  *"a competent reader would say the two assert the same mathematical fact"*; the
  delta makes the reader the adjudicator, not the executor.
- **PARTIAL** — a located result is **strictly more general**, **strictly special**,
  or **adjacent** (shares mechanism/object but not the exact statement). REQUIRED:
  state **which of the three**, the citation, and the exact relationship (what
  specializes/generalizes to what).
- **NO-PRIOR-FOUND** — not located under protocol P. This is a **bounded, negative
  statement**: "not located under protocol P," explicitly **NOT** "novel," a
  statement about coverage, not about the world. REQUIRED: the coverage actually
  run (which variants × which databases) AND the **nearest related work found**, so
  the bound is legible.

The bar for "same" and for "strictly more/less general" is **frozen now**. The
executor may not, after seeing hits, relax "same" to "vaguely related" to earn
FOUND, nor tighten it to earn NO-PRIOR. Any borderline call is written up as PARTIAL
with the relationship stated, and the reader adjudicates.

---

## 3. MATCHED CONTROL / POSITIVE-CONTROL GATE (the firing check — MANDATORY, runs FIRST)

The instrument is only informative if it CAN surface results that ARE published.
These are frozen as positive controls and are searched **before** any of the 10
claims. Each must be recovered by the same protocol (same database set, ≤3 query
variants).

- **PC-1 — Silverman–Stange 2011**, *"Amicable pairs and aliquot cycles for
  elliptic curves"*, Experimental Mathematics 20(3). Framework behind claim 6.
  Query seeds: `silverman stange amicable pairs aliquot cycles elliptic curves`;
  `amicable pair elliptic curve #E(F_p)=q #E(F_q)=p`; `aliquot cycle elliptic
  curve experimental mathematics 2011`.
- **PC-2 — Kohel–Shparlinski 2000**, ANTS-IV, *"On exponential sums and group
  generators for elliptic curves over finite fields."* On disk
  (`kohel_shparlinski_ants4_2000.pdf`). Adjacent to claims 8/9. Query seeds:
  `kohel shparlinski exponential sums group generators elliptic curves`;
  `exponential sums elliptic curve 4 sqrt p group generator ANTS 2000`;
  `character sums points elliptic curve finite field bound Shparlinski`.
- **PC-3 — one of Waterhouse 1969** (*"Abelian varieties over finite fields,"*
  Ann. Sci. ENS 2) **or Honda–Tate**. Adjacent to claims 5/7. Query seeds:
  `Waterhouse abelian varieties over finite fields Weil numbers`;
  `Honda Tate theorem abelian variety finite field isogeny`;
  `supersingular Weil number characteristic polynomial Frobenius classification`.

**GATE RULE (pre-committed):** If **any** of PC-1, PC-2, PC-3 is NOT recovered under
the protocol, the sweep is **VOID**: it reports *"search instrument uninformative
under protocol P"* and **issues no grades on the 10 claims** — a null on the 10 is
then unreadable (cannot distinguish "not in literature" from "instrument cannot
find things that are"). All three must fire. A partial recovery (found under a
looser query than frozen) is recorded as a coverage note but still counts as fired
only if recovered within the ≤3 frozen variants.

---

## 4. PLANTED CONTROL

The positive controls in §3 double as planted controls: three results **known to be
published** are injected into the search queue and the instrument must return each.
This is the "inject a known effect of known size; the test must fire" check adapted
to a review. If the plant does not fire, the null is uninformative — full stop (§3
GATE). No separate synthetic plant is possible for a literature search; the three
real published papers are the plant.

**Secondary calibration plant (claims 6 & 8, see §5):** claim 6's *framework* and
claim 8's *headline* are known non-independent. They are planted expecting
FOUND/PARTIAL. If the protocol grades either as NO-PRIOR-FOUND, that is an
instrument failure signal (the search missed a result known to exist), and the
coverage for that claim is treated as deficient and re-run, not accepted.

---

## 5. PRE-COMMITTED HANDLING OF THE TWO KNOWN NON-INDEPENDENT CLAIMS

Decided before the run; these are the framework-vs-instance calibration:

- **Claim 6 (secp is an amicable pair).** The **Silverman–Stange framework is
  published** (= PC-1). Pre-committed: the framework component is graded **FOUND-IN-LIT
  by construction** (cite PC-1). The **instance** ("secp256k1 *specifically* is an
  amicable pair, with the sextic-twist selection named as the unforced part") is a
  **separate** search, graded independently by §2's rule. The protocol must **print
  both** — framework grade and instance grade — so it is on record that the sweep
  **distinguishes framework from instance** and does not let a published framework
  auto-grade the instance, nor let a NO-PRIOR instance masquerade as full priority.
- **Claim 8 (three conservations of U; headline Σ_a|U(a,b,c)|² = n(n−1)).** The
  headline was shown this session to be **Parseval/Plancherel for a unit-modulus
  sequence** (holds for ANY unit-modulus target, not curve-special). Pre-committed:
  the headline Σ|U|²=n(n−1) is graded **FOUND-IN-LIT or PARTIAL by construction**
  against the standard Plancherel identity on a finite abelian group (cite a
  standard harmonic-analysis reference located by the search). The **other two
  conservations** are searched and graded **separately**; a FOUND on the headline
  may **not** be extended to them. The protocol must print all three
  sub-grades separately.

---

## 6. SCOPE / ORDERING — term-searchable vs concept-only, and execution order

**Execution order is frozen:** (i) run the §3 positive-control gate; if VOID, STOP.
(ii) Then the 10 claims **in numeric order 1→10, none skipped.** The executor may
NOT search only an easy subset; every claim gets its full §7 query budget or a
recorded coverage gap (database unavailable), never a silent drop. A claim with an
unavailable database is documented, not omitted.

**Classification (which literature the object lives in):**

| # | Object | Class | Search mode |
|---|---|---|---|
| 1 | Cap Law / flap / carry ε region = `\|u∓v\|>½` of ℤ[ω] | project-internal NAME; content = a rounding-carry = hexagonal-lattice region fact | **concept-only** (name returns nothing by construction) |
| 2 | H1: `(−1)^{flap/6}=χ₂(2)=(−1)^{(p²−1)/8}` | mixed: `(−1)^{(p²−1)/8}` is the classical 2nd supplement; "flap/6" is internal | **concept-only** for the bridge; term-based for the classical target |
| 3 | `\|FLD\|=6·h(−p)` | mixed: `h(−p)` standard; FLD internal | **concept + term** |
| 4 | Claim S (isotypic selection rule / character-sum zeros), Claim F (j=0 field/curve split) | mixed: isotypic decomposition & sextic twist standard; Claim S/F naming internal | **concept-only** |
| 5 | `A_new` (Jac. of `w⁴=x³+b`) supersingular ∀ p≡3(4), via μ₄ cover not CM | standard AG/NT (superelliptic/cyclic-cover Jacobians) | **term-based** |
| 6 | secp is an amicable pair | standard (Silverman–Stange) framework + instance | **term-based** (see §5) |
| 7 | `m=b₂/p` names 4 Frobenius eigenvalues; charpoly `t⁴+mpt²+p²`; = one Jacobi sign | standard (quartic Weil polynomials, Jacobi sums) | **term-based** |
| 8 | three conservations of `U`; headline Σ`\|U\|²`=n(n−1) | headline standard (Plancherel); other two mixed | **term-based** headline (see §5); **concept** for the other two |
| 9 | bilinear closure: `\|S\|/n²=O(p^{−1/2})` via two-point Fourier factorization | standard (bilinear character/exponential sums) | **term-based** |
| 10 | `k_den` level sets = primitive Farey comb (d-side only, no curve) | mixed: Farey structure standard; k_den mapping internal | **concept + term** |

**Concept-only flag (pre-committed consequence):** for a concept-only claim, a
NO-PRIOR-FOUND on the internal NAME is EXPECTED and is recorded as *uninformative
about the concept*. The grade must be earned by searching the **mathematical
statement in standard terms** (the concept queries in §7), not the name. If only the
name was searched, the claim is marked **coverage-incomplete**, not graded.

---

## 7. POWER = SEARCH COVERAGE (per-claim query budget, ≥3 variants × databases)

**Database set (frozen), D = {D1…D5}:**
- D1 Google Scholar
- D2 arXiv (math.NT, math.AG, math.NA)
- D3 zbMATH Open
- D4 MathSciNet — if unavailable, the frozen substitute is Semantic Scholar +
  Crossref, recorded explicitly as a coverage substitution (not a silent swap)
- D5 on-disk sources (`grep` the two PDFs and the `*.txt`/`*.md` corpus in this
  directory — already present: `kohel_shparlinski_ants4_2000.pdf`,
  `lange_shparlinski_jmc_2007.pdf`)

**Minimum coverage per claim:** **≥3 distinct query variants, each run across D1–D4**
(≥12 executed queries), plus a D5 on-disk check. A NO-PRIOR-FOUND is only admissible
if **all ≥3 variants were run across all available databases** and the nearest
neighbor is named. A single-query null is **not** a NO-PRIOR-FOUND; it is
coverage-incomplete.

**Frozen query variants (≥3 each; executor may ADD but not SUBTRACT):**

- **C1 (concept):** (a) `Eisenstein integers rounding fundamental domain carry
  region`; (b) `hexagonal lattice nearest point rounding \|u−v\|>1/2 ℤ[ω]`;
  (c) `reduction modulo Eisenstein integer carry region hexagonal Voronoi`.
- **C2 (concept + term):** (a) `lattice point count mod 6 quadratic character 2
  Eisenstein`; (b) `Dedekind sum second supplement quadratic reciprocity lattice
  count`; (c) `(2/p)=(−1)^{(p²−1)/8} geometric lattice-point proof`.
- **C3 (concept + term):** (a) `class number imaginary quadratic field lattice
  point count region`; (b) `h(−p) equals 6 times counting formula difference set
  Eisenstein`; (c) `geometric class number formula sawtooth sign sum sgn(ρs mod
  p − s)`.
- **C4 (concept):** (a) `character sum vanishing isotypic component selection
  rule`; (b) `j=0 elliptic curve sextic twist decomposition field part curve
  part`; (c) `μ₆ isotypic decomposition Gauss/Jacobi sum zeros`.
- **C5 (term):** (a) `superelliptic curve w^4=x^3+b Jacobian supersingular p≡3
  mod 4`; (b) `cyclic cover degree 4 supersingular abelian variety Newton
  polygon`; (c) `Jacobian μ4 cover supersingular not CM separable cubic`.
- **C6 (term):** (a) `secp256k1 amicable pair elliptic curve`; (b) `#E(F_p)=n and
  #E(F_n)=p amicable elliptic curve instance`; (c) `Silverman Stange amicable
  secp256k1 sextic twist b=7` (framework grade = PC-1, §5).
- **C7 (term):** (a) `characteristic polynomial Frobenius t^4+mpt^2+p^2
  supersingular abelian surface`; (b) `Jacobi sum determines Frobenius eigenvalue
  superelliptic curve`; (c) `quartic Weil polynomial p≡3 mod 4 supersingular
  eigenvalue √p root of unity`.
- **C8 (term + concept):** (a) `Plancherel Parseval exponential sum finite abelian
  group n(n-1)` (headline, §5); (b) `twisted exponential sum elliptic curve
  conservation identity Σ|U|^2`; (c) `Σ_a |Σ_d e_p(bx+cy)e_n(ad)|^2 = n(n-1)
  additive character` (the other two conservations searched separately by their
  own statements).
- **C9 (term):** (a) `bilinear exponential sum elliptic curve points p^{-1/2}
  bound`; (b) `two-point character sum Fourier factorization elliptic curve`;
  (c) `Bourgain Garaev Shparlinski bilinear sums elliptic curve group`.
- **C10 (term + concept):** (a) `Farey sequence denominator level sets structure`;
  (b) `primitive Farey fractions comb denominators Stern-Brocot`; (c) `Dirichlet
  hyperbola denominator equivalence classes Farey dissection`.

**Coverage ledger (mandatory output):** the executor records, per claim, a table:
`query string | database | date | # hits scanned | top relevant hit`. This table
IS the power number; a claim's grade is inadmissible without it. A shallow search
cannot be dressed as exhaustive because the ledger exposes the executed variant×
database count.

---

## 8. EXACTNESS

No numerical signal path exists in this task: the sweep produces discrete citation
grades, not key-derived arithmetic. The no-float rule (`btc_puzzle_investigation/
CLAUDE.md`) has **no signal-path surface here** — no key, (n,k,D), target, or
feature is computed. Carve-out: none needed; there is no float in any decision.
Grades are labels {FOUND-IN-LIT, PARTIAL, NO-PRIOR-FOUND} plus text.

---

## 9. FALSIFICATION / VOID CONDITIONS

- **Sweep VOID (no grades issued):** any of PC-1, PC-2, PC-3 not recovered under the
  protocol (§3 GATE). Report "search instrument uninformative under protocol P."
- **Per-claim inadmissible (regraded coverage-incomplete, not NO-PRIOR):** fewer than
  3 variants run, or the name-only search on a concept-only claim, or a missing
  coverage ledger.
- **Calibration failure (re-run required):** claim 6 framework or claim 8 headline
  graded NO-PRIOR-FOUND (both are known-published; a NO-PRIOR there means the search
  missed a result known to exist).
- **The hypothesis under test** ("§2's 10 are undocumented elsewhere") is
  **abandoned for a given claim** the moment a FOUND-IN-LIT paper is located for it.
  It is **weakened to PARTIAL** when a strictly-more-general/special/adjacent result
  is located. It is **neither confirmed nor called novel** by NO-PRIOR-FOUND —
  absence of evidence is recorded as a bounded coverage statement only.

---

## 10. PRE-COMMITMENT — what each outcome earns, per claim

Filled in BEFORE the run. For every one of the 10 claims, each possible grade yields
exactly:

- **FOUND-IN-LIT** ⇒ record the citation and delta; the §2 originality assertion for
  that claim is **retracted** (priority belongs to the located paper); the item moves
  to "Tie-ins to what is known."
- **PARTIAL** ⇒ record the citation and the exact more-general / more-special /
  adjacent relationship; the §2 assertion is **narrowed** to the residual delta (state
  precisely what, if anything, the record adds beyond the located result).
- **NO-PRIOR-FOUND** ⇒ record coverage (variants × databases) + nearest neighbor; the
  §2 assertion is **rephrased** from "undocumented elsewhere" to *"no prior located
  under protocol P (date, coverage)"* — a bounded statement, **never** "novel," never
  a priority certificate.

**Aggregate product (frozen):** a **citation map** — a table with columns
`claim | grade | citation(s) | delta/relationship | coverage ran | nearest neighbor`.
The maximal allowed aggregate statement is: *"k of 10 have no prior located under
protocol P; nearest neighbors listed."* The sweep may **never** conclude "these are
all novel." The two calibration items (6 framework, 8 headline) are printed as
FOUND/PARTIAL-by-construction and demonstrate the map distinguishes framework from
instance.

---

## 11. ANTI-GAMING LOCKS (summary of the freezes above)

1. All 10 claims attempted, numeric order, none dropped (§6).
2. ≥3 frozen query variants × D1–D4 per claim; the coverage ledger is a required
   output (§7).
3. "Same theorem" bar frozen now; borderline ⇒ PARTIAL with stated relationship,
   never post-hoc relaxed to FOUND or tightened to NO-PRIOR (§2).
4. Positive-control gate runs FIRST; VOID if any of three fails (§3).
5. Concept-only claims graded on the mathematical statement, not the internal name;
   name-only null = coverage-incomplete, not NO-PRIOR (§6).
6. Claims 6 & 8 pre-graded by construction on framework/headline; instance/other
   conservations searched separately (§5).
7. "Novel" banned; strongest statement = "no prior located under protocol P" (§1, §2).
8. Product is a citation map, not a novelty verdict (§10).
