# Referee Review Response — `eleven_lonely_runners.tex`

Date: 2026-03-30

---

## Overall Verdict (Reviewer)

> "Narrative structure: strong. Section ordering: strong. Conceptual through-line: strong.
> Referee readability: much improved. Main remaining task: harden a few load-bearing
> transitions, not redesign the paper."

The reviewer identifies three **pressure points** requiring targeted hardening. Everything else is commended or needs only minor one-sentence clarifications. This document catalogues all action items by severity and section.

---

## Priority 1 — Three Referee Pressure Points

### P1.1 — Sign-Range Containment (§5.1)

**Reviewer concern:** The lemma is "mostly an appeal to Appendix A.1–A.8." For a load-bearing lemma, the body should contain a one-paragraph meta-proof skeleton *before* the appendix reference so the reader is not left with the impression that the proof is "appendix by delegation."

**Required fix:** Add one paragraph in §5.1 body that:
1. States the geometric reason why an out-of-range shift necessarily dislodges one of the outer slot boundaries.
2. Explains why only finitely many fillers need be checked (finite sign classes × bounded k-index).
3. Then delegates the exhaustive arithmetic to Appendix A.1–A.8.

**Draft paragraph:**
> For each of the $2^8$ sign classes, the bad interval $B_{j,k}(a_j)$ covering the
> right edge of $I_9$ is determined by a single index $k$; the value of $k$ is bounded
> because $B_{j,k}[\text{right}]=(11k+\text{const})/(11a_j)$ must lie in $[0,1]$ and $a_j$
> is bounded below by 1.  Any speed $a_j$ shifted outside its feasibility range pushes
> $B_{j,k}[\text{right}]$ strictly past the slot boundary, uncovering a positive-width
> interval regardless of the remaining configuration.  The $2^8 \times K_{\max}$ cases
> are exhaustively verified in Appendix A.1–A.8.

---

### P1.2 — Phase-Uniform Transport (§7, Second Phase-Independence Lemma)

**Reviewer concern:** The lemma asserts that all engine hypotheses/conclusions depend only on speed ranges and on which runner covers the right gap of $I_9$, and are independent of the cycle index $m$. This is "the most load-bearing sentence in the whole draft." The reviewer asks explicitly:
- Are all relevant endpoint comparisons truly identical in cycle-relative coordinates?
- Are there hidden dependencies on which $B_{j,k}$ index is serving as the local primary branch?
- Does "which runner covers the right gap" suffice to identify the full local geometry needed by PSM/Chain A/Chain B?

**Required fix:** Add half a paragraph (or a short remark block) immediately after the lemma statement making explicit:
1. All slot boundaries $I_s$ are defined in cycle-relative coordinates $[t - \lfloor t\rfloor]$, so the comparison arithmetic is literally identical in every cycle.
2. The branch index $k$ of $B_{j,k}$ shifts by a fixed integer each cycle; the *residual* bad interval in cycle-relative coordinates equals $B_{j,0}$ in cycle 0. Hence the $k$-index is invisible to the slot comparison.
3. "Which runner covers the right gap of $I_9$" determines the branch (Chain A, Chain B, PSM, UB), and within each branch the constraints are speed-range inequalities only.

**Draft remark:**
> **Remark (cycle-coordinate independence).** All slot intervals $I_s$ and good-fraction
> widths are expressed in the fractional coordinate $\{a_j t\}$, which is periodic of period
> $1/a_j$ in $t$.  In the $m$-th pacemaker cycle the relevant coverage condition on
> runner $j$ is $\{a_j t\} \in B_{j,k_m}$ where $k_m = k_0 + m$.  The residual fractional
> position $\{a_j t - k_m\} = \{a_j t\} - k_m/a_j$ coincides with the cycle-0 residual up
> to an integer shift, so the slot-comparison inequalities are numerically identical in every
> cycle.  In particular, the choice of branch (PSM / Chain A / Chain B) is determined
> entirely by which speed ranges hold, and these are independent of $m$.

---

### P1.3 — Irrational Perturbation (§8)

**Reviewer concern:** The sentence "In either case the defining rational relations are unchanged, so $y \in T_e$" is doing a lot of work. The construction of the rational approximating vector $v$ within the same rational-relation class needs to be stated more formally. Also, "positive-measure witness set" may be stronger than needed and could create a proof burden.

**Required fix — two changes:**

**(a) Formal precision on torus membership.** Replace or augment the sentence with:
> The rational approximant $v = (v_1,\dots,v_{n-1})$ is constructed so that the
> integer relation $\sum c_i v_i = 0$ (resp.\ $c_i v_i = c_j v_j$) holding for the
> original speed vector $u$ continues to hold for $v$, since we only perturb within
> the rational hyperplane defined by those relations.  Consequently the orbit closure
> of $v$ under the flow $(t v_1 \bmod 1,\dots, t v_{n-1} \bmod 1)$ lies in $T_e$,
> the same rational sub-torus as the orbit closure of $u$.

**(b) Weaken "positive-measure" to "open witness."** Replace every occurrence of "positive-measure witness set" with "open witness set $\mathcal{S}$" unless positive measure is explicitly required downstream. Since $\mathcal{S}$ is open and the orbit is dense, strict existence suffices and is easier to defend.

---

## Priority 2 — One-Sentence Clarifications (low effort, high referee goodwill)

| Section | Issue | Fix |
|---|---|---|
| §1 Intro | "AP ownership persists literally" misread risk | Add: *"the AP ownership gives the baseline claimed-slot pattern against which all off-schedule repairs are measured"* |
| §2 Setup | Boundary hyperplanes ($a_j = j$) discarded without explanation | Add: *"boundary cases are handled by limiting argument or direct boundary check and do not affect the contradiction analysis"* |
| §2 Setup | Why the core is called "static" | Add anticipatory phrase: *"slot comparisons are made in cycle-relative coordinates and are phase-independent"* |
| §3.3 | AP-family obstruction example closing | Strengthen: *"the obstruction is not lack of modular structure, but the insufficiency of the AP witness family alone"* |
| §4.2 | "Owned slots" misread risk | Add once: *"'ownership' refers to the AP-limit primary-slot pattern and the perturbative burden of repair, not absolute exclusivity for all perturbed configurations"* |
| §5.2 | Notation $B_{4,0}[0]$, $B_{4,0}[1]$ | Define globally once: *"$[0]$ and $[1]$ denote left and right endpoints respectively"* |
| §5.3 | Chain A — why no alternative repairer | Add one sentence: why no other runner can repair the left edge of $I_8$ in this branch without causing failure elsewhere |
| §5.5 | Runner 2 absent from Universal Blocking table | Add: *"runner 2 is handled at the ownership stage and is absent from this residual table"* |
| §5.5 | "Feasible fillers are exhausted" | Append: *"see Appendix A.10 for the complete range verification"* (make the delegation explicit, not implicit) |
| §6.1 | "Runner 9 must first close $I_4$" moves fast | Add one sentence: why no alternative ordering or filler can avoid that first obligation in the $\sigma_2=-1$ branch |
| §6.2 | Seven $I_9$ regions exhaustive and disjoint | Add: *"these seven regions partition $(a_9^{\min}, a_9^{\max})$ exhaustively; adjacency verified in Appendix A.11"* |

---

## Priority 3 — Structural Observations (no immediate action required)

These are positive observations from the reviewer that should be preserved and not accidentally broken in revision.

- **Strongest narrative paragraph**: closing paragraph of §4 after the Complementary Pairs theorem. Do not shorten or move it.
- **Proof funnel chain**: §3.3 → §4 → §5 → §6 → §7 is the paper's spine. All edits should preserve this visual chain in the section headers.
- **Section 6.2 ($I_9$ decomposition)**: reviewer calls it "one of the best structural results in the draft." Do not compress.
- **Chain B (§5.4)**: reviewer calls it "the cleanest contradiction engine." Keep it at its current length — it is exactly the right size.
- **Universal Blocking summary table**: reviewer explicitly commends it. Keep as is.

---

## Appendix health check (action item)

The reviewer flags that the appendix must be a *ledger* (finite arithmetic verification), not a *second hidden proof*. The two danger zones are:

1. **A.1–A.8** (Sign-range containment): verify that the appendix contains only endpoint arithmetic, not any conceptual exclusion argument that belongs in §5.1.
2. **A.10** (Universal Blocking filler range): same check.
3. **A.11** (Negative-branch ledger for Lemma 6.1): reviewer notes it "must be spotless" because the minimum $538/54395$ will either be trusted or audited.

---

## Change log

| Item | Status |
|---|---|
| P1.1 Sign-range containment meta-paragraph | Pending |
| P1.2 Phase-uniform transport remark | Pending |
| P1.3a Torus membership precision | Pending |
| P1.3b Weaken "positive-measure" to "open witness" | Pending |
| All Priority 2 one-liners | Pending |
| Appendix ledger vs. proof audit | Pending |
