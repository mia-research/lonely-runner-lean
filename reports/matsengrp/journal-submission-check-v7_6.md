# Journal Submission Checklist — LRC Preprint v7.6

**Agent:** journal-submission-checker (matsengrp-plugins)
**Input file:** `lrc_proof_v7_6_preprint.md`
**Date:** 2026-03-14
**Reviewer model:** haiku

---

## Summary verdict

The manuscript is substantially complete and mathematically well-organised. It is close to arXiv-ready. The items flagged below are mostly minor but should be resolved before submission. The most significant issues are: (1) the version number in the header metadata reads "v7.5" while the file is v7.6; (2) the abstract exceeds 150 words; (3) AMS subject classification and keywords are absent; (4) the Tao (2018) reference is listed but never cited inline; and (5) two cross-references use LaTeX tilde-notation (`Theorem~9.2c`, `Lemma~9.3f-LCM`) that will not render in Markdown/plain-text output and must be verified in the final TeX source.

---

## A. Structure and Completeness

**A1. Abstract**
- Status: ⚠ Needs attention
- The abstract is present and conceptually clear. However, it is written in three paragraphs spanning approximately 215 words — well above the 150-word arXiv limit (see D3 below). The third paragraph ("For prime n…") contains technical nomenclature ("Sole Cover bijection", "Dropped-Runner Targeting theorem", "Unit-Complete", "floor-reset event", "Appendix A") that may be opaque to a general reader unfamiliar with the paper's notation. These terms should either be briefly glossed or moved to the introduction.
- Fix: Trim the abstract to ≤150 words. The first paragraph (lines 13–15) is the clearest and most accessible; consider making it the core of a revised, shorter abstract.

**A2. Introduction**
- Status: ✓ Complete
- §1.1 motivates the problem with historical context (Wills 1967, Cusick 1973, Bienia et al. 1998, Bohman–Holzman–Kleitman 2001, Barajas–Serra 2008), states the main theorem (Theorem A), and the case partition (§1.3) previews the proof structure. §2.4 provides an explicit proof blueprint table. The introduction is thorough.

**A3. Section cross-references**
- Status: ⚠ Needs attention
- The proof blueprint table (§2.4) references sections §3–§13 correctly.
- In §8.3 (Theorem 8.3) the proof refers to "Proposition~10.5" using a LaTeX tilde. In §9.3b the proof refers to "Lemma~9.3f-LCM" and "Theorem~9.3f". These appear correctly in context, but the tilde notation must be verified to compile correctly in the final `.tex` source; they will not render as links in Markdown.
- Sub-case B1 (line 485) refers to Theorem 9.2c correctly.
- The §13 proof summary table cross-references all branches to their respective theorems/lemmas — complete and consistent.
- One note: Theorem 11.5 is referenced in its own proof ("Quantitative status" remark at line 503) but does not appear in the §13 summary table. It is described as "an auxiliary late-window result providing a second independent route to Tier 1," so its omission from the summary table is intentional; consider a brief footnote to this effect in §13 for clarity.

**A4. Conclusion/summary**
- Status: ⚠ Needs attention
- There is no dedicated conclusion section. §13 (Proof of the Main Theorem) serves as the synthesis and summary, with a complete branch table. For a journal submission this is acceptable if the journal does not require a separate conclusion section. For arXiv, it is fine. However, adding a brief (3–5 sentence) concluding remark after the §13 proof block — noting open questions, the quantitative status gap in even-composite branches, and the supplementary chamber-persistence program — would strengthen the manuscript for a journal audience.

---

## B. Mathematical Standards

**B1. All theorems have proofs or citations**
- Status: ✓ Complete
- Every theorem and lemma is followed by a proof ending with $\square$, or is explicitly marked as a corollary with a proof pointer. Items listed as "supplementary" (Supplementary Program 9.2d, Appendix A.7) are clearly scoped as not used in Theorem A.
- Lemma 10.3 references "Lemma 10.4" for the $M_0 < n^2$ bound — and Lemma 10.4 follows immediately, so forward reference is acceptable and is explicitly managed.
- Lemma 9.3d (Dangerous-Fibre Count) and Lemma 9.3e (Unit Bijection at Dangerous Floors) are stated without proofs. They are referenced in context but have no "Proof." blocks.
  - Fix: Add proof sketches or explicit "Proof omitted; follows from [source]" notes for Lemma 9.3d and Lemma 9.3e. For a journal submission these must not appear as bare statements.

**B2. Lemmas stated before use**
- Status: ✓ Complete (with one minor note)
- All lemmas used in proofs are introduced in the same or an earlier section. The Coverage Criteria (Lemma 9.2a) is used in Theorems 9.2b, 9.2c, 9.2d-I through 9.2d-III, and all uses follow the statement.
- Lemma T3 (§5.4) is stated in §5 and used later in §8 (Theorem 8.2 implicitly) and in the proof of Lemma 10.2. The reference is implicit in §8.2's "leaves ≥ 2 unit residues uncovered" argument. Consider an explicit citation "by Lemma T3" in the §8.2 proof.

**B3. Definitions given before use**
- Status: ✓ Complete
- Key definitions are introduced in §1.2 ($x_0(E)$, safe-point count), §5.1 (bad sets, floor state, fibre), §9.1 (floor-reset event), §9.2d (chamber). The Coverage Insufficiency Principle (§2.3) uses "bad set" before its formal definition in §5.1 — but §2 is explicitly a blueprint/orientation section and warns the reader they may return later; this is acceptable.
- "Unit-Complete" is defined in §9.4, after being used informally in §2 and §5.2. The §2 uses are in a blueprint context with forward-reference intent; §5.2 uses it operationally in Sub-case B. Consider adding a parenthetical "(defined formally in §9.4)" on the first use in §5.2.

**B4. Notation consistency**
- Status: ✓ Complete (minor observations)
- The notation is highly consistent throughout. "CG1"/"CG2" (Coverage Gate 1/2) is introduced in §2.2 and used correctly everywhere. "UC" is never used; "Unit-Complete" is spelled out each time — good.
- "$B_{\rm safe}$" vs "$x_0$": the manuscript sometimes uses $B_{\rm safe}$ (number of safe fibres) and sometimes $x_0(E)$; the relationship is explained in §1.2. Both are used appropriately in context.
- "Sub-case B1/B2/B3" and "Sub-case PP(i)/PP(ii)" and "Sub-case G(i)/G(ii)": these are introduced informally in §11 and §9 respectively. A consolidating notation table at the start of §11 listing all sub-case labels would help readers navigate.
- "GG1/GG2" does not appear in v7.6 (correctly replaced by Sub-case G(i)/G(ii) per v7 conventions). ✓
- The distinction between $L_0 = \mathrm{lcm}(E_{\rm non})$ and $L = \mathrm{lcm}(E)$ introduced in §5.1 is used correctly in §10.

---

## C. Citations and References

**C1. Named results cited**
- Status: ✓ Complete (one issue — see C3)
- Weyl (1916): Cited inline in §3, Step 3 with journal title "Weyl 1916; see Kuipers–Niederreiter §1.4". The Weyl citation appears in the reference list. ✓
- Kuipers–Niederreiter: Referenced by section number (§1.4) in the proof of Theorem 3.1. However, this reference does NOT appear in the reference list.
  - Fix: Add Kuipers, L. and Niederreiter, H. (1974). *Uniform Distribution of Sequences.* Wiley, to the reference list.
- Chebyshev's theorem: Referenced in Lemma 9.3f-LCM ("a consequence of Chebyshev's theorem on prime distribution"). Not cited to a specific reference. For a journal submission, either cite a standard number-theory text (e.g., Hardy–Wright) or note it as elementary.
  - Fix: Add a citation such as "see, e.g., Hardy, G.H. and Wright, E.M. (2008). *An Introduction to the Theory of Numbers*, 6th ed., Oxford, Theorem 414" or similar.
- Wills (1967), Cusick (1973), Bienia et al. (1998), Bohman et al. (2001), Barajas–Serra (2008), Czerwiński (2012): All cited in §1.1 and all appear in the reference list. ✓

**C2. Reference list present and complete**
- Status: ⚠ Needs attention
- The reference list is present (§References, lines 552–562) with 8 entries. It is properly formatted with journal names, volume numbers, and page ranges.
- Missing: Kuipers–Niederreiter (see C1 above).
- Missing: A Hardy–Wright or comparable standard reference for Chebyshev's theorem (see C1 above).
- The Tao (2018) entry is listed but not cited anywhere in the main text (see C3 below).

**C3. Uncited external results**
- Status: ⚠ Needs attention
- Tao (2018) appears in the reference list but has no inline citation in the manuscript body. Either cite it (e.g., in §1.1 for context on progress toward the conjecture, or as a remark on the connection to the present work) or remove it from the reference list.
- No other uncited external results were identified. All theorems proved in the manuscript are original to the author or are properly attributed.

---

## D. arXiv Submission Standards

**D1. Title and authors**
- Status: ⚠ Needs attention
- Title: "A Proof of the Lonely Runner Conjecture" — present. ✓
- Author: "Trent Palelei" — present. ✓
- Affiliation: "MI Research Foundation" — present. ✓
- Date: "March 2026" — present. ✓
- Version: The header metadata reads **"Version: v7.5"** but this file is v7.6 (per filename `lrc_proof_v7_6_preprint.md` and the project memory record of v7.5 being the previous version).
  - Fix: Update header line 6 from `**Version:** v7.5` to `**Version:** v7.6`.

**D2. AMS subject classification**
- Status: ✗ Issue found
- No AMS Mathematics Subject Classification (MSC 2020) codes are present in the manuscript. arXiv submissions in mathematics require at least one primary MSC code.
  - Fix: Add MSC 2020 codes to the header or a dedicated "MSC classification" line. Suggested codes:
    - **11B75** (Other combinatorial number theory) — primary
    - **11K60** (Diophantine approximation, metric theory)
    - **05C15** (Coloring of graphs and hypergraphs) — if the combinatorial framing is emphasised
    - **11J13** (Simultaneous homogeneous approximation, linear forms) — for the Diophantine angle

**D3. Keywords**
- Status: ✗ Issue found
- No keywords line is present. Most journals and arXiv submissions benefit from a keywords field.
  - Fix: Add a "Keywords" line to the header, e.g.: "Lonely Runner Conjecture; Diophantine approximation; equidistribution; Weyl theorem; covering systems; residue arithmetic"

**D4. Abstract word count**
- Status: ✗ Issue found
- The abstract (lines 13–17) is approximately 215 words — significantly over the arXiv 150-word guideline.
  - Fix: Condense to ≤150 words. The first paragraph alone (lines 13–15, approximately 60 words) provides a clean, plain-English statement of the result and could serve as the complete abstract with one or two additional sentences on method. The technical elaboration in lines 15–17 can be moved to the introduction (§1 or a new §1.0 "Overview") where length is unconstrained.

---

## E. Language and Style

**E1. Abstract accessibility (no proprietary jargon)**
- Status: ⚠ Needs attention
- The first paragraph of the abstract is accessible and plain-English. ✓
- The second and third paragraphs introduce "Sole Cover bijection," "Dropped-Runner Targeting theorem," "Unit-Complete," "floor-reset event," "CG1/CG2 arithmetic conditions," "Chamber Persistence," and "Appendix A." These are all defined within the paper but are undefined in the abstract, making it inaccessible to a general mathematical reader. arXiv best practice is to keep the abstract free of undefined terms.
  - Fix: As part of the abstract trim (see D4), remove or paraphrase these terms. Example: "a floor-reset event" can become "a specific arithmetic moment"; "Unit-Complete" can become "the case where all units modulo n are retained."

**E2. Verb tense consistency in proofs**
- Status: ✓ Complete (minor observations)
- The proofs consistently use present tense ("we have," "the map sends," "the floor state is"). No systematic tense mixing was observed across the sections read. The word "satisfies" is used consistently; "satisfied" does not appear in proof bodies. ✓
- One minor observation: §9.3b (line 369) uses "reduces to" and "holds throughout" (present), while the same proof uses "verified for $n \in \{25, 27\}$" (past, appropriate for computations). This is standard style and is not an error.

**E3. Theorem/Lemma/Proof environment label consistency**
- Status: ⚠ Needs attention
- The manuscript uses a mixture of label styles:
  - Sequential numbering: Theorem 3.1, Lemma 5.2, Proposition 5.1, Corollary 5.3, Lemma 9.1, etc.
  - Alphabetic/named: Lemma G-PRES, Lemma FLOOR0, Lemma R1-SWEEP, Lemma T3.
  - Compound with suffixes: Theorem 9.2d-I, Theorem 9.2d-II, Theorem 9.2d-III, Lemma 9.3f-LCM.
  - Descriptive names inline: "Coverage Insufficiency Principle," "Sole Cover Bijection," "Dropped-Runner Targeting" — these are stated as bold-faced definitions within sections rather than numbered theorem environments.
  - This multi-style system is functional and internally consistent within the manuscript, but will require careful mapping to LaTeX theorem environments during conversion. Specifically:
    - Lemma G-PRES, FLOOR0, R1-SWEEP, T3 should become `\begin{lemma}[G-PRES]` etc. in LaTeX.
    - "Coverage Insufficiency Principle" should be a formal `\begin{theorem}` or `\begin{principle}` environment with a number.
    - The "Supplementary Remark" label (9.3a) is used once; use a `\begin{remark}` environment.
  - Fix: During LaTeX conversion (latex-document-skill), map all bold-faced named results to proper numbered theorem environments. Assign the Coverage Insufficiency Principle a theorem number (suggest Theorem 2.1) for cross-reference clarity.

**E4. General prose quality**
- Status: ✓ Complete
- The prose is mathematically precise and well-structured. Section headers are descriptive. The proof blueprint (§2.4) is a clear and useful navigational aid. Supplementary material is cleanly separated from the main theorem path with consistent "not used in Theorem A" disclaimers. No grammatical errors were identified in the sections reviewed.

---

## F. Additional Pre-Submission Items

**F1. Companion files referenced but not described**
- Status: ⚠ Needs attention
- Appendix A.4 references companion file `lrc_certified_A4_prime_n_le30.py` and "SHA-256: see companion manifest." Appendix A.5 references `lrc_certified_A5_composite_n_le12.py` similarly. Neither a "companion manifest" file nor a data availability statement is present in the manuscript body.
  - Fix: Add a "Data Availability" or "Code Availability" statement (either in the appendix or as a separate section) that lists the companion files, their SHA-256 hashes, and their repository location (e.g., GitHub or Zenodo). arXiv allows code to be submitted as ancillary files; this is the recommended approach.

**F2. Scope of Appendix A.1**
- Status: ⚠ Needs attention
- The appendix A.1 table covers only $n \in \{3,4,5,6,8,9,10,12\}$ — it skips $n=7$ and $n=11$. Proposition 5.1 states the bound for $n \leq 20$. The missing values should either be included in the table or the table caption should note that only composite $n$ are listed (since prime $n = 7, 11$ are handled by the prime branch).
  - Fix: Add a note to A.1 clarifying which values of $n$ are included and why prime $n$ values are omitted from the table.

**F3. Version number in header**
- Status: ✗ Issue found (duplicate of D1 — flagged for emphasis)
- Line 6 reads `**Version:** v7.5`. Must be corrected to `v7.6` before submission.

---

## Checklist Summary Table

| Item | Category | Status |
|---|---|---|
| Abstract present and conceptually clear | A1 | ⚠ Over word limit; technical jargon in paragraphs 2–3 |
| Introduction motivates problem, states result, outlines proof | A2 | ✓ Complete |
| Section cross-references correct | A3 | ✓ (minor: Theorem 11.5 absent from §13 table) |
| Conclusion/summary present | A4 | ⚠ §13 serves as summary; no separate conclusion section |
| All theorems have proofs or citations | B1 | ⚠ Lemma 9.3d and 9.3e lack proofs |
| Lemmas stated before use | B2 | ✓ (minor: implicit Lemma T3 use in §8.2) |
| Definitions given before use | B3 | ✓ (minor: Unit-Complete used in §5.2 before §9.4 definition) |
| Notation consistent throughout | B4 | ✓ Complete |
| Named results cited (Weyl, Chebyshev, Kuipers–Niederreiter) | C1 | ⚠ Kuipers–Niederreiter and Chebyshev need formal references |
| Reference list present and complete | C2 | ⚠ Two missing references; Tao (2018) uncited |
| No uncited external results | C3 | ⚠ Tao (2018) listed but not cited in body |
| Title and authors present | D1 | ⚠ Version number in header reads v7.5 (should be v7.6) |
| AMS subject classification | D2 | ✗ Absent — required for arXiv |
| Keywords | D3 | ✗ Absent — recommended for arXiv |
| Abstract ≤150 words | D4 | ✗ Approximately 215 words — exceeds arXiv guideline |
| Abstract plain-English accessible | E1 | ⚠ Paragraphs 2–3 contain undefined technical terms |
| Consistent verb tense in proofs | E2 | ✓ Complete |
| Theorem/Lemma/Proof environment labels consistent | E3 | ⚠ Mixed numbering styles; needs mapping to LaTeX environments |
| Companion file data availability statement | F1 | ⚠ No data/code availability statement present |
| Appendix A.1 table scope note | F2 | ⚠ Missing values (n=7,11) unexplained |
| Version number correction | F3 | ✗ Header says v7.5; correct to v7.6 |

---

## Priority Action List (ordered by urgency for arXiv submission)

1. **Fix version number** in header metadata: `v7.5` → `v7.6`. (1 line change)
2. **Add MSC 2020 classification codes** (primary 11B75, secondary as appropriate).
3. **Add keywords line**.
4. **Trim abstract to ≤150 words** — remove technical terms from abstract body; move elaboration to introduction.
5. **Add Kuipers–Niederreiter to references** and a Chebyshev citation (Hardy–Wright or similar).
6. **Either cite Tao (2018) inline or remove it from the reference list**.
7. **Add proof sketches for Lemma 9.3d and Lemma 9.3e** (two bare statements without proofs).
8. **Add a data/code availability statement** with SHA-256 hashes for companion files A4 and A5.
9. **Add note to Appendix A.1** explaining omission of n=7 and n=11.
10. **Add "(defined formally in §9.4)"** on first operational use of "Unit-Complete" in §5.2.
11. **Consider adding a brief conclusion section** (3–5 sentences) after §13.

Items 1–6 are blocking for arXiv submission. Items 7–11 are strongly recommended for a journal submission and should be resolved before the adversarial review target of ≥90 can be considered met for a journal-ready draft.

---

*Report generated by journal-submission-checker (matsengrp-plugins) — 2026-03-14*
