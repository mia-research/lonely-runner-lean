# ScholarEval Evaluation — LRC Preprint v7.6

**Framework:** ScholarEval (Moussa et al. 2025, arXiv:2510.16234)
**Input file:** `lrc_proof_v7_6_preprint.md`
**Journal-submission context:** `reports/matsengrp/journal-submission-check-v7_6.md`
**Evaluator:** Claude (claude-sonnet-4-6) with mandatory Qwen prescreening
**Qwen prescreening verdict:** FLAG — see auditor note below
**Date:** 2026-03-14
**Scale:** 1 = Poor | 2 = Needs Improvement | 3 = Adequate | 4 = Good | 5 = Excellent
**Pass threshold (project standard):** ≥ 3.5 on all 8 dimensions

---

## Auditor Note (Post-Qwen Checkpoint)

Qwen says: VERDICT FLAG — preprint fails evaluation readiness due to missing AMS MSC codes, absent keywords, version mismatch, uncited references (Kuipers-Niederreiter; Tao 2018 orphaned), incomplete Lemma 9.3d/e proofs, and abstract exceeding the 150-word arXiv limit.

Decision: Accepting — the flag accurately catalogues the known pre-submission issues. These are evaluated as weaknesses in the appropriate dimensions below. The Qwen flag does not indicate mathematical incorrectness; it reflects presentation and completeness gaps. The evaluation proceeds.

---

## Dimension 1: Problem Formulation & Research Questions

**Score: 5 / 5**

### Strengths

1. The conjecture is stated with full precision in §1.1: the definition of loneliness ($\|v_j t\|_{\mathbb{R}/\mathbb{Z}} \geq 1/n$), the speed conditions (distinct nonzero integers), and the range ($n \geq 3$) are all explicit. The Theorem A box is clear and unambiguous.
2. The contribution is correctly and honestly scoped. The abstract and §1.1 distinguish between the full Tier 1 result ($x_0 \geq 1$ for all $n \geq 3$) and the partial Tier 2 result ($x_0 \geq \varphi(n)$, proved on the prime branch, dropped-unit composite branch, and odd dropped-two composite branches). There is no overclaiming.
3. The significance is well-explained. §1.1 recounts the problem's origins (Wills 1967; Cusick 1973), the state of prior partial proofs ($n \leq 7$), and the open status of the general case. The arithmetic normalisation in §1.2 (the safe-point count $x_0(E)$ and the integer-lattice reformulation) is elegant and makes the problem computationally tractable. The §2.4 blueprint table provides a structured proof roadmap visible to the reader from the outset.

### Weaknesses / Suggestions

1. The boundary inclusion note (§1.2) — that $\|e_i t\| \geq 1/n$ is a weak inequality and hits at exactly $1/n$ count as safe — is correct but deserves a one-sentence remark on why this does not trivially guarantee solutions (to forestall a potential referee objection).
2. The abstract currently conflates the statement of the result (Tier 1) with quantitative bonus results (Tier 2) in a way that may confuse a first reader. Splitting these more cleanly — one sentence for the main theorem, one for the quantitative upgrade — would sharpen the contribution claim.
3. The case partition in §1.3 is given as a two-branch split ($E_{\rm div} = \emptyset$ vs $E_{\rm div} \neq \emptyset$) without immediately signalling that the $E_{\rm div} \neq \emptyset$ branch itself splits into at least five sub-branches. A brief forward-reference to §2.4 at this point would reduce navigation burden.

### Critical Issues

None.

---

## Dimension 2: Literature Review

**Score: 4 / 5**

### Strengths

1. The canonical prior results are all cited correctly in §1.1: Bienia et al. (1998) for $n \leq 5$, Bohman-Holzman-Kleitman (2001) for $n = 6$, Barajas-Serra (2008) for $n = 7$. These are the directly relevant predecessors and they are all present.
2. The Weyl (1916) equidistribution theorem — the single most important external mathematical result used in the proof — is cited inline in §3 with journal title and a secondary reference to Kuipers-Niederreiter §1.4. The conceptual context for Weyl's theorem is briefly explained before use.
3. The reference list correctly provides journal names, volume numbers, and page ranges for all entries it contains, indicating care about bibliographic completeness.

### Weaknesses / Suggestions

1. Kuipers-Niederreiter is referenced in the proof of Theorem 3.1 (by section number §1.4) but does not appear in the reference list. This is a missing citation and is a blocking issue for any submission. The full reference is: Kuipers, L. and Niederreiter, H. (1974). *Uniform Distribution of Sequences*. Wiley.
2. Tao (2018) appears in the reference list but is cited nowhere in the body. A paper of Tao's on the conjecture should either be cited in §1.1 as background (e.g., to discuss density results or connections to other problems) or removed. An orphaned reference weakens the bibliography.
3. The Chebyshev prime distribution result used in Lemma 9.3f-LCM is cited only as "elementary; a consequence of Chebyshev's theorem" without a specific reference. For a journal submission, a pointer to Hardy-Wright Theorem 414 or a comparable number-theory text is required.
4. There is no discussion of related approaches (e.g., topological or measure-theoretic approaches to LRC) beyond the historical chain. A brief paragraph in §1.1 on why arithmetic and coverage arguments appear natural for this problem — and why earlier attempts for $n \geq 8$ failed — would situate the methodology more clearly.

### Critical Issues

Kuipers-Niederreiter must be added to the reference list before any submission (arXiv or journal). This is a named citation with a section number that has no corresponding bibliography entry.

---

## Dimension 3: Methodology & Research Design

**Score: 4 / 5**

### Strengths

1. The case partition is complete and non-overlapping. The top-level split (Case 1: $E_{\rm div} = \emptyset$ vs Case 2: $E_{\rm div} \neq \emptyset$) is exhaustive by definition. Within Case 2, the sub-splits (prime/composite, $|E_{\rm div}|=1$ vs $\geq 2$, dropped-unit vs Unit-Complete, multi-prime vs prime-power) are systematically enumerated in the §13 summary table, which cross-references every branch to a theorem or lemma. No branch appears to be omitted.
2. The Coverage Insufficiency Principle (§2.3) provides a unified conceptual frame. The four failure modes (unit dropout, floor-reset handoff failure, transparency, prime-power misalignment) are a clean taxonomy that motivates the case structure rather than presenting it as ad hoc. This is a major structural strength.
3. The use of certified exhaustive enumeration for finite exceptional sub-cases (prime $n \leq 30$, composite $n \leq 12$) is methodologically sound: the analytic argument bounds the scope of enumeration (Lemmas 10.3-10.4 for the prime branch; the $L < n(n-1)(\varphi(n)+1)$ bound for the composite branch), and the enumeration then provably covers that bounded scope. The architecture of "analytic spine + certified finite exceptions" is rigorous.

### Weaknesses / Suggestions

1. The irrational speeds case (§3) is treated by Weyl equidistribution and relies on the integer cases (§§4-12) as a sub-argument for the rational sub-case within Step 4a-4b. This creates a logical dependency that is stated but not fully unrolled: the reader is told that Step 4b reduces to Case 1 / Case 2, but the boundary between irrational and rational cases is not stated as a formal lemma. A clean "if all speeds are rationally commensurate, reduce to the integer case" lemma would strengthen the logical pathway.
2. The proof blueprint table (§2.4) maps sections to failure modes correctly, but it does not explicitly state that the sub-branches within §11 (Sub-cases B1, B2, B3, PP(i), PP(ii)) are exhaustive within the composite $|E_{\rm div}|=1$ case. The reader must reconstruct this from §11's local exposition. A completeness note in the blueprint table (e.g., "B1/B2/B3/PP(i)/PP(ii) are exhaustive by parity and prime-power factoring") would close this gap.
3. Sub-case B1 ($n$ even, both dropped runners non-units) relies on Sub-case B1 sending the reader to Theorem 9.2c for the quantitative conclusion, but the even-$n$ inequality $2\varphi(n)/n < 1$ (the residue-count argument showing a unit residue is always uncovered at floor 0) is not itself proved in the text — it is stated as a displayed equation. Adding a one-line proof that this ratio is $< 1$ for all even $n \geq 4$ would close the gap.

### Critical Issues

None, but the completeness of Sub-cases B1/B2/B3 within the composite even branch should be made explicit.

---

## Dimension 4: Data Collection & Sources (Computational Verification Evidence)

**Score: 3 / 5**

### Strengths

1. The computational certificates are clearly scoped and motivated analytically. In both key certified branches — prime $n \leq 30$ (Appendix A.4) and composite $n \leq 12$ (Appendix A.5) — the analytic argument establishes a finite upper bound on the search space (Lemma 10.3: $M < M_0 < n^2$; the $L$-bound in Proposition 11.3) before the enumeration begins. The enumeration is therefore not open-ended; it is a finite check.
2. The enumeration schemas in A.4 and A.5 are stated in enough pseudocode detail that an independent verifier could reproduce them. The companion Python files (`lrc_certified_A4_prime_n_le30.py`, `lrc_certified_A5_composite_n_le12.py`) are named explicitly.
3. The Coverage Criterion cross-check (Appendix A.6: 6,123 cases, zero discrepancies) provides independent verification that Lemma 9.2a (the CG1/CG2 formula) is implemented correctly in any computational tools used elsewhere. This is good computational hygiene.

### Weaknesses / Suggestions

1. There is no data availability or code availability statement. The companion files are referenced by name but no repository location (GitHub, Zenodo, arXiv ancillary files) and no SHA-256 hash is given in the manuscript body. A.4 and A.5 both say "SHA-256: see companion manifest" — but there is no manifest in the manuscript or in the reference list. This is a significant gap: independent verification requires access to the actual code.
2. Appendix A.1 (the $L = 2n$ table) lists $n \in \{3,4,5,6,8,9,10,12\}$ and skips $n=7$ and $n=11$. The caption does not explain that prime $n$ values are covered by the prime branch rather than the table. A referee will notice and question the omission.
3. Appendix A.3 claims independent verification of Theorem 9.3f for prime powers $n \leq 100$, but the table lists only five values ($n \in \{4,8,9,25,49\}$). For $n \in \{25,49\}$ the $B_{\rm safe}$ value is given as a lower bound ($\geq 2300$, $\geq 9870$) without stating how that bound was obtained computationally. This is weaker than the exhaustive claims in A.4 and A.5.

### Critical Issues

The absence of a code/data availability statement with SHA-256 hashes and a repository location is a blocking issue for verifiability. A journal referee cannot verify "36,847 cases enumerated" without access to the code.

---

## Dimension 5: Analysis & Interpretation

**Score: 4 / 5**

### Strengths

1. The main analytic lemmas are all proved with proofs ending in $\square$. The Coverage Gate conditions (Lemma 9.2a), the Dropped-Runner Targeting theorem (Theorem 9.2c), the Sole Cover bijection (Lemma 5.2), and the quantitative bounds (Theorems 9.3b, 9.3f, Proposition 10.5) are the load-bearing results, and all are proved in detail. Theorem 9.2c in particular — the most novel result — has a fully written-out proof that identifies the specific index $m$ algebraically, verifies $\gcd(d, e_u)=1$, disposes of CG1 by invertibility, and identifies the unique CG2 runner.
2. The quantitative bounds are tight where claimed. Theorem 9.3b proves $B_{\rm safe} \geq \varphi(n)(n-2)/2$ via a $U_n$ lower-bound argument that is careful about the lcm factors across primes; the explicit verification for the five small values of $n < 45$ is a credible way to handle the base cases. The polynomial inequality check at $n=45$ is verified by evaluation and monotone derivative.
3. The distinction between Tier 1 (existence, $x_0 \geq 1$, proved for all branches) and Tier 2 (quantitative, $x_0 \geq \varphi(n)$, proved for some branches) is consistently maintained throughout §§9-13. The §13 summary table makes the precise scope of each result transparent. This intellectual honesty strengthens the paper.

### Weaknesses / Suggestions

1. Lemmas 9.3d (Dangerous-Fibre Count) and 9.3e (Unit Bijection at Dangerous Floors) are stated without proofs. They are referenced in the proof of Theorem 9.3f (and the remark preceding it). For a journal submission these bare statements are unacceptable; proof sketches or explicit citations are required.
2. The bound in Theorem 9.3b uses $B_{\rm safe} \geq L/(n(n-1)) - 1$ from a chamber-width argument, then bounds $L \geq n U_n$ by the unit lcm. The gcd product bound "63 bounds the product of the six pairwise gcds" in the $n \geq 45$ case is an important arithmetic claim that is stated but whose verification for general odd $n$ (as opposed to specific small cases) relies on the reader tracking six pairwise gcd upper bounds. Expanding this two-line argument into a sub-lemma would improve readability and self-containedness.
3. Theorem 8.3 references "Theorem~8.2" and "Proposition~10.5" within its proof using LaTeX tilde notation, which does not render correctly in Markdown. The logical content is correct, but the cross-references must be verified to compile in the final TeX source. Similarly, Lemma 9.3f-LCM is referenced using a compound identifier that must map cleanly to a LaTeX label.

### Critical Issues

Lemmas 9.3d and 9.3e lack proofs. These are not auxiliary remarks; they feed into the prime-power quantitative branch (Theorem 9.3f). Adding proof sketches is required for journal submission.

---

## Dimension 6: Results & Findings

**Score: 4 / 5**

### Strengths

1. Theorem A ($x_0(E) \geq 1$ for all $n \geq 3$ and all gcd-1 tuples) is clearly stated in §1.1 and the proof in §13 explicitly dispatches every branch in a structured table. The proof synthesis is clean: every case in the §1.3 partition appears in the §13 table with a named theorem or proposition.
2. The five main proof branches — irrational (Theorem 3.1), Case 1 (Theorem 4.1), prime $n$ (Lemma 7.1 + Proposition 10.5 + Theorems 8.2, 8.3), composite dropped-unit (Lemma 5.2 + Proposition 11.3), and composite Unit-Complete (Theorems 9.2c, 9.3b, 9.3f, 12.1) — are all dispatched. Each yields $x_0 \geq 1$ for its respective parameter range.
3. The supplementary chamber-persistence material (Supplementary Program 9.2d, Appendix A.7) is clearly labelled as not used in Theorem A. This prevents confusion about which results constitute the proof and which are bonus findings. The "not used in Theorem A" disclaimer appears consistently throughout §§9-11 and the Appendix.

### Weaknesses / Suggestions

1. The quantitative Tier 2 result ($x_0 \geq \varphi(n)$) is not proved for the even-$n$ dropped-two sub-case (Sub-case B1). The manuscript notes that Theorem 9.2c gives $B_{\rm safe} \geq 1$ for $n = 2^k$, and Theorem 9.3b gives the quantitative bound for odd multi-prime $n$, but for even $n$ in the dropped-two sub-case the quantitative bound is not explicitly stated as a theorem. The §13 summary table omits this branch from the quantitative column. This is an honest omission, but it should be stated explicitly as an open direction.
2. Theorem 11.5 (Late Bottleneck Window) provides a second independent route to Tier 1 for the prime-power dropped-two case ($n = p^k$, $k \geq 3$), but it does not appear in the §13 summary table. The omission is intentional (the remark at line 503 explains this), but a brief footnote in §13 acknowledging the auxiliary result would prevent a referee from questioning its absence.
3. The claim in Proposition 5.1 that $x_0 \geq n-1$ for $n \leq 20$ and $L = 2n$ is stated as a computational result (Appendix A.1), but the table in A.1 contains only 8 values of $n$ (composite $n \leq 12$, plus 3, 4, 5). Values $n \in \{13, 14, 15, 16, 17, 18, 19, 20\}$ are missing from the table. This creates a discrepancy between the proposition's stated range and the evidence provided.

### Critical Issues

The Appendix A.1 table does not cover all $n \leq 20$ as stated in Proposition 5.1. If the statement claims $n \leq 20$, the table must cover that range or the proposition must be corrected. This is a falsifiability gap in the certified evidence.

---

## Dimension 7: Scholarly Writing & Presentation

**Score: 4 / 5**

### Strengths

1. The paper is exceptionally well-organised for a proof of this complexity. The §2.4 blueprint table is one of the strongest structural features: it maps sections to branches and failure modes, allowing a reader to navigate the 13-section paper without losing the thread. The Coverage Insufficiency Principle (§2.3) serves as a conceptual anchor that ties together the four failure modes before they are analysed individually.
2. Notation is highly consistent throughout. The v7 naming conventions (Unit-Complete, CG1/CG2, floor-reset event, Sub-case G(i)/G(ii), PP(i)/PP(ii)) are used without reversion to earlier terminology. The absence of "U-FORCE," "Cond 1/2," "GG1/GG2," and "z=0 event" throughout confirms that earlier naming inconsistencies have been resolved.
3. The abstract's first paragraph is an excellent plain-English statement of the result and the core mechanism. It is accessible to a mathematical reader who has not yet read the paper. The separation of "main result" (Tier 1) from "stronger bound status" in the abstract, though currently too long, shows care for communicating scope honestly.

### Weaknesses / Suggestions

1. The abstract is approximately 215 words — significantly over the 150-word arXiv guideline. The third paragraph of the abstract introduces notation ("Sole Cover bijection," "Dropped-Runner Targeting theorem," "Unit-Complete," "floor-reset event," "CG1/CG2," "Chamber Persistence," "Appendix A") that is undefined at point of use. This paragraph should be moved to the introduction or condensed to one accessible sentence.
2. The theorem and lemma labelling uses three distinct systems simultaneously: sequential section-based numbering (Theorem 9.2c), alphabetic-name labels (Lemma G-PRES, FLOOR0, R1-SWEEP, T3), and compound suffixes (Theorem 9.2d-I, Theorem 9.2d-II, Theorem 9.2d-III, Lemma 9.3f-LCM). While internally consistent, this mixed system will require careful mapping to LaTeX theorem environments during conversion (the latex-document-skill step). The Coverage Insufficiency Principle (§2.3) is also not formally numbered as a theorem, which weakens its cross-referenceability.
3. There is no dedicated conclusion section. While §13 functions as an adequate synthesis for a preprint, a journal submission typically benefits from a 3-5 sentence conclusion that (a) affirms the main result, (b) states the quantitative scope gap honestly, and (c) lists open directions (e.g., the even-$n$ Tier 2 gap, the full chamberwise program of Supplementary Program 9.2d).

### Critical Issues

None blocking. The abstract over-length and jargon issues are arXiv-blocking, but do not affect mathematical content.

---

## Dimension 8: Citations & References

**Score: 3 / 5**

### Strengths

1. All major prior partial proofs are cited with correct bibliographic information: Bienia et al. (1998), Bohman-Holzman-Kleitman (2001), Barajas-Serra (2008), Cusick (1973), Wills (1967). Each entry in the reference list provides journal title, volume, and page range.
2. Weyl (1916) is cited inline in the proof of Theorem 3.1 with the German journal title (Math. Ann. 77) and a secondary reference (Kuipers-Niederreiter §1.4). This shows awareness that Weyl's theorem requires attribution even when used as a standard tool.
3. Czerwinski (2012) on random speeds is included as contextual background — a result not directly needed for the proof but relevant to the reader understanding the state of the field.

### Weaknesses / Suggestions

1. Kuipers-Niederreiter (1974) is referenced in Theorem 3.1's proof by section number but absent from the reference list. This is a clear error and must be corrected before any submission.
2. Tao (2018) is in the reference list with full bibliographic information (*Contrib. Discrete Math.* **13**, 1–29) but has no inline citation. It must either be cited (e.g., "for an overview of recent approaches, see Tao (2018)") or removed from the reference list.
3. Chebyshev's theorem — used explicitly in Lemma 9.3f-LCM for the bound $\mathrm{lcm}(1,\ldots,m) \geq 2^{m-1}$ — has no formal citation. For a journal submission a reference to Hardy-Wright (2008, Theorem 414) or Apostol's *Introduction to Analytic Number Theory* would be required.
4. AMS Mathematics Subject Classification (MSC 2020) codes are entirely absent. arXiv submissions in mathematics require at least one primary MSC code. Suggested primary: 11B75 (Other combinatorial number theory). Relevant secondary codes: 11K60 (Diophantine approximation, metric theory); 11J13 (Simultaneous homogeneous approximation).
5. A keywords line is absent. This is recommended for both arXiv discoverability and journal indexing.

### Critical Issues

Three items are blocking for arXiv submission: (1) Kuipers-Niederreiter missing from reference list; (2) AMS MSC codes absent; (3) no keywords. Items (2) and (3) are absent entirely; item (1) is a citation present in the body with no bibliography entry.

---

## Summary Scores

| Dimension | Score | Status vs 3.5 threshold |
|---|---|---|
| 1. Problem Formulation & Research Questions | 5 / 5 | PASS |
| 2. Literature Review | 4 / 5 | PASS |
| 3. Methodology & Research Design | 4 / 5 | PASS |
| 4. Data Collection & Sources | 3 / 5 | FAIL (below threshold) |
| 5. Analysis & Interpretation | 4 / 5 | PASS |
| 6. Results & Findings | 4 / 5 | PASS |
| 7. Scholarly Writing & Presentation | 4 / 5 | PASS |
| 8. Citations & References | 3 / 5 | FAIL (below threshold) |

**Overall score: 3.875 / 5** (31 / 40 raw, average of 8 dimensions)

Equivalent on 10-point scale: **7.75 / 10**

---

## Major Strengths (Top 5)

1. **Complete proof architecture.** The §13 summary table demonstrably dispatches every branch of the case partition with a named theorem or proposition. No branch is left dangling. The proof of Theorem A is structurally complete.

2. **Coverage Insufficiency Principle as a unifying framework.** The four failure modes (§2.2) and the §2.4 blueprint table transform what could be a sprawling case analysis into a coherent narrative. This is a significant expository achievement for a proof of this length.

3. **Theorem 9.2c (Dropped-Runner Targeting) is fully and rigorously proved.** This is the most novel result in the paper. The construction of the index $m$ via $x \equiv -nd^{-1} \pmod{e_u}$, the proof that $\gcd(d, e_u) = 1$, and the dispatch of both CG1 and CG2 are all algebraically explicit. This theorem carries the Unit-Complete composite branch entirely.

4. **Honest scoping of the quantitative results.** The manuscript never overclaims. The distinction between Tier 1 ($x_0 \geq 1$, proved for all $n$) and Tier 2 ($x_0 \geq \varphi(n)$, proved for a subset of branches) is maintained consistently throughout the paper, the abstract, and the §13 summary table.

5. **Analytic bounding of certified enumeration scope.** The design of Appendices A.4 and A.5 — where an analytic argument first bounds the search space to a finite range, then an exhaustive enumeration covers that range — is methodologically clean. This approach eliminates the risk of unbounded computational claims.

---

## Critical Weaknesses (Top 5)

1. **Lemmas 9.3d and 9.3e are stated without proofs.** These are not remarks or supplementary observations — they feed directly into Theorem 9.3f (the prime-power quantitative bound). A journal submission cannot contain bare lemma statements on the main theorem path. Proof sketches or explicit citations are required.

2. **Appendix A.1 table does not cover the full stated range.** Proposition 5.1 claims $x_0 \geq n-1$ for all $n \leq 20$, but the supporting table in A.1 contains only 8 values of $n$ (up to $n=12$ composite, plus a few small values). Values $n \in \{13, 14, 15, 16, 17, 18, 19, 20\}$ are absent. This is a falsifiability gap.

3. **No code/data availability statement with SHA-256 hashes.** Appendices A.4 and A.5 reference companion Python files and claim "36,847 cases enumerated; zero failures" (A.4) and a similar scope for A.5. Without a repository URL, SHA-256 hashes, or any way to access the code, these claims cannot be independently verified. The phrase "SHA-256: see companion manifest" has no corresponding manifest in the manuscript.

4. **Three blocking citation issues for arXiv submission.** Kuipers-Niederreiter (cited in body, missing from bibliography), Tao (2018) (in bibliography, never cited in body), and no MSC classification codes. All three must be resolved before upload.

5. **Abstract exceeds arXiv word limit and contains undefined notation.** At approximately 215 words with terms like "Sole Cover bijection," "Dropped-Runner Targeting theorem," "Unit-Complete," and "CG1/CG2" used without definition, the abstract violates arXiv's 150-word guideline and is inaccessible to a general mathematical reader. This is an arXiv-blocking formatting issue.

---

## Priority Recommendations (Ranked)

**Priority 1 — Blocking for any submission (fix immediately):**

1. Add proof sketches for Lemma 9.3d (Dangerous-Fibre Count) and Lemma 9.3e (Unit Bijection at Dangerous Floors). These are on the main theorem path for Theorem 9.3f and cannot be bare statements.
2. Extend Appendix A.1 to cover all $n \leq 20$ as stated in Proposition 5.1, or revise the proposition to state the correct verified range. Missing evidence for a stated result is a correctness gap.
3. Add Kuipers-Niederreiter (1974) to the reference list. Either cite Tao (2018) inline in §1.1 or remove it from the bibliography.
4. Add AMS MSC 2020 classification codes (primary: 11B75; secondary: 11K60, 11J13) and a keywords line.
5. Trim the abstract to ≤ 150 words, removing undefined technical terms (move elaboration to §1 or a new §1.0 "Overview").

**Priority 2 — Required for journal submission (fix before adversarial review target of 90):**

6. Add a data/code availability statement with SHA-256 hashes and repository location for companion files A4 and A5.
7. Add a citation for Chebyshev's theorem in Lemma 9.3f-LCM (Hardy-Wright Theorem 414 or Apostol).
8. Add a note to Appendix A.1 caption explaining that prime $n$ values ($n=7$, $n=11$, etc.) are handled by the prime branch, not this table.
9. Correct the version header from "v7.5" to "v7.6" (one line change; flagged as a confirmed bug).
10. Add "(defined formally in §9.4)" on first operational use of "Unit-Complete" in §5.2.

**Priority 3 — Strongly recommended for journal readiness:**

11. Add a brief conclusion section (3-5 sentences) after §13 noting: (a) the main theorem is proved; (b) the quantitative Tier 2 gap in the even-$n$ dropped-two branch; (c) the supplementary chamber-persistence program as future work.
12. Assign the Coverage Insufficiency Principle (§2.3) a formal theorem number (suggest Theorem 2.1) to enable clean cross-referencing.
13. Add a consolidating notation table at the start of §11 listing all sub-case labels (B1, B2, B3, PP(i), PP(ii)) with their defining conditions.
14. During LaTeX conversion (latex-document-skill), map named lemmas (G-PRES, FLOOR0, R1-SWEEP, T3) to `\begin{lemma}[G-PRES]` etc. and ensure all tilde cross-references compile correctly.

---

## Publication Readiness Verdict

**Near-ready (minor fixes)**

The proof architecture is complete, the main theorem is dispatched across all branches, and the core technical contributions (Theorem 9.2c, the Coverage Gate framework, the period decomposition counting bridge) are fully and rigorously presented. The paper achieves an overall ScholarEval score of 3.875 / 5 (7.75 / 10 equivalent), meeting the project threshold of ≥ 3.5 on 6 of 8 dimensions.

The two failing dimensions — Dimension 4 (Data Collection & Sources, score 3.0) and Dimension 8 (Citations & References, score 3.0) — are driven entirely by addressable presentation and completeness gaps: missing code availability statements, a citation list with two errors, missing MSC codes, and a table that does not cover its stated range. None of these weaknesses are mathematical; all are fixable without changing any theorem or proof.

The paper is **not yet arXiv-ready** as submitted because of the five blocking items listed in Priority 1. Once those items are resolved, it will meet the arXiv standard. Once the Priority 2 items are also resolved, it will meet the project's adversarial review threshold of 90 and the journal-submission standard.

Recommended next steps in pipeline order:
1. Apply Priority 1 fixes to produce v7.7.
2. Re-run adversarial review (proof-adversarial-review) targeting score ≥ 90.
3. Run matsengrp sweep (math-pr-summarizer + journal-submission-checker) on v7.7.
4. LaTeX conversion (latex-document-skill) with attention to theorem environment mapping.
5. Final ScholarEval re-run targeting ≥ 4.0 / 5 on all 8 dimensions.

---

*Evaluation generated by Claude (claude-sonnet-4-6) with Qwen 3.5:4b prescreening — 2026-03-14*
*Framework: ScholarEval (Moussa et al. 2025, arXiv:2510.16234)*
