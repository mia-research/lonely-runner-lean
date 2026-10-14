# n=11 LRC Proof — Rigor Gap Assessment
**File:** `lrc_n11_rigor_gap_assessment_v1.md`
**Date:** 2026-03-28
**Source version assessed:** `lrc_n11_ap_paper_v24.md`

---

## Executive Summary

The n=11 LRC proof is **structurally complete**. Every commensurable-ratio (CB) configuration has at least one slot with positive good fraction. The three gaps identified below are **presentational and quantitative errors** in how that conclusion is stated for specific sub-cases — they do not create any actual hole in the LRC proof.

**Verdict:** Safe to proceed to write-up / submission after fixing Gaps 1–3.

---

## Tier 1: Solid Components

These results have no identified gaps.

| Component | Location | Status |
|---|---|---|
| **Theorem B** (explicit witness $t^* = k/((k+1)e_k)$ for $e_k/e_1 \leq k$) | §4 | ✅ Complete. 3-line elementary proof. |
| **Proposition E** (Weyl equidistribution, irrational case) | §5 | ✅ Complete. Standard. |
| **Runner 2 Incompatibility** — lower bound $a_2 \geq 20/9$ | §10, Lemma 11.2.1 | ✅ Proved exactly. Bound comes from $I_4$ coverage requirement. |
| **Runner 2 Incompatibility** — upper bound $a_2 \leq 575/261$ | §10, Lemma 11.2.2 | ✅ Proved exactly. Bound comes from $I_9$ reachability. |
| **Runner 2 Incompatibility** conclusion: gap $5/261 > 0$ | §10 | ✅ The two bounds are incompatible; gap is explicit. |
| **Lemma CR** (right-gap creation by runners 3–8) | §11.2 | ✅ Each runner type either has a direct incompatibility or produces a certifiable right gap. |
| **Chain A** (runner 3, $\sigma_3=+1$): GF$(I_8) \geq 1/50$ | §11.3 (lines 714–737) | ✅ Algebraically correct 4-step cascade over runners (3,8,6,5). Runner-intrinsic: independent of $g_L$. |
| **Chain B** (runner 4, $\sigma_4=+1$): GF$(I_7) \geq 1533/18490$ | §11.3 (lines 739–750) | ✅ Algebraically correct. Runner-intrinsic. |
| **PSM runner 3** ($\sigma_3=-1$): GF$(I_3) \geq 1111/27830$ | §11.3, line 700 | ✅ Correct. |
| **PSM runner 4** ($\sigma_4=-1$): GF$(I_2) \geq 11/20570$ | §11.3, line 706 | ✅ Correct. |
| **Theorem UB structural conclusion** | §11.3 line 769 | ✅ "In all cases GF$(I_k) > 0$ for some $k \in \{1,\ldots,9\}$." Correct and complete. |
| **Phase-Uniform Extension** | §13 | ✅ The $\sigma$-signs are determined by CB speed parameters, not phase. Cascade applies uniformly in every pacemaker sub-cycle of $W_{\mathrm{ref}}$. |
| **Corollary $W_{\mathrm{ref}}$** | §13 | ✅ Follows cleanly from Phase-Uniform Extension. |
| **Computational 112/112** | §14 | ✅ All 112 sign-class boundary configurations verified. Independent confirmation of above. |

---

## Gap 1 — Theorem U Conclusion: Wrong Specific Slots (Presentational)

**Location:** §11.4 line 797 (Theorem U statement) and line 799 (proof summary).

**The error:**

> *Theorem U:* "For any CB configuration with $\sigma_2=+1$: GF$(I_4)$ + GF$(I_9) > 0$."

**Why this is wrong:** Consider Case A2b ($a_9 \in [580/69, 87/10)$, $\sigma_9=-1$) with runner 3 active in Chain A ($\sigma_3=+1$, $a_3 \in [32/(11g_L), 340/109]$). In Chain A, runner 3 covers $I_9$ via $B_{3,2}$, which sets GF$(I_9) = 0$. Simultaneously, if $a_2 = 20/9$ exactly, then $B_{2,0} = [45/110, 54/110] = I_4$ exactly, setting GF$(I_4) = 0$. At this configuration point:
$$\mathrm{GF}(I_4) + \mathrm{GF}(I_9) = 0.$$
The claim of Theorem U is violated.

**What is actually true:** Chain A gives GF$(I_8) \geq 1/50 > 0$ at this point, so the LRC conclusion holds — just via $I_8$, not $I_4$ or $I_9$.

**The correct statement:**

> *Theorem U (corrected):* "For any CB configuration with $\sigma_2=+1$: GF$(I_k) > 0$ for some $k \in \{1,\ldots,9\}$."

This is exactly what Theorem UB already proves (line 769). Theorem U as stated is a *corollary* of Theorem UB; the corollary currently claims more than UB delivers.

**Fix required in v24:** Replace the Theorem U statement and its proof summary at lines 797–799 with the corrected statement above, noting that the specific slot $k$ depends on which of Chain A / Chain B / PSM / direct incompatibility applies.

**Impact on LRC proof:** None. GF $> 0$ somewhere is all that's needed.

---

## Gap 2 — Individual Case Conclusions: Wrong Slot (Presentational)

**Location:** §11.4 cases A2b, A2c, B2, B3, B4 (lines 781–795).

**The error:** Each of these cases ends with a conclusion of the form "GF$(I_9) \geq$ [value]$> 0$." This is correct *when Chain A does not apply* (i.e., runner 3 is absent or has $\sigma_3=-1$). But when runner 3 has $\sigma_3=+1$ and is in its Chain A feasibility range, it covers $I_9$ and GF$(I_9) = 0$. In that sub-case Chain A delivers GF$(I_8) \geq 1/50$ instead.

**Affected cases:**
- **A2b** (line 781): states GF$(I_9) \geq 181/6380$. True only for $\sigma_3=-1$ or runner 3 infeasible.
- **A2c** (line 783): states GF$(I_9) \geq 1/20$. Same caveat.
- **B2** (line 791): states GF$\geq 83/2695$. Same caveat.
- **B3** (line 793): states GF$(I_9) \geq 59/9460$. Same caveat.
- **B4** (line 795): states GF $> 17/430$. Same caveat.

**Fix required:** Each case needs a $\sigma_3$ split:

> *If $\sigma_3 = -1$ or runner 3 infeasible for $I_9$:* [existing GF$(I_9)$ bound].
> *If $\sigma_3 = +1$, Chain A active:* GF$(I_9) = 0$, but Chain A gives GF$(I_8) \geq 1/50$. $\square$

The fix is mechanical — the Chain A analysis already exists in full in §11.3. These case conclusions just need to reference it.

**Impact on LRC proof:** None.

---

## Gap 3 — Minimum Gap Value: Overstated (Quantitative)

**Location:** Line 801 ("Minimum gap: $59/9460$") and line 817 (combined minimum = $538/54395$).

**The error:** The stated minimum gap of $59/9460 \approx 0.00624$ for $\sigma_2=+1$ cases refers to Case B3 with $a_9=86/9$, $a_2=172/81$, giving GF$(I_9) \geq 59/9460$ (when Chain A does not apply). But the Theorem UB summary table (line 760) already records:

> PSM runner 4 ($\sigma_4=-1$): GF$(I_2) \geq 11/20570 \approx 0.000535$.

Since $11/20570 < 59/9460$, the PSM runner 4 sub-case has a *smaller* minimum gap than Case B3. The PSM runner 4 case is compatible with any of the $\beta$-1 through $\beta$-4 regions (runner 4 with $\sigma_4=-1$ is a candidate filler runner for the right gap in those regions). Therefore the true minimum for $\sigma_2=+1$ cases is $\leq 11/20570$, not $59/9460$.

**Revised combined minimum:** Taking $\min(11/20570,\; 538/54395)$: since $11/20570 \approx 0.000535 < 538/54395 \approx 0.00989$, the combined minimum across all 256 sign classes is $\leq 11/20570 \approx 5.35 \times 10^{-4}$ (achieved in the PSM runner 4 sub-case of a $\sigma_2=+1$ configuration).

**Fix required:** Recompute the minimum gap table systematically across all sub-cases, using the per-chain and per-PSM lower bounds in the Theorem UB table (lines 756–768). The minimum is positive — but the numerical value on line 801/817 needs updating.

**Impact on LRC proof:** None. A smaller-but-positive minimum is still positive.

---

## Gap 4 — Theorem U's Proof Summary: Incomplete Coverage Claim

**Location:** Line 799.

> "Cases A1, A2a, A2d, B1 give direct incompatibility. Cases A2b, A2c, B2, B3, B4 produce a right gap in $I_9$ that Theorem UB shows cannot be filled."

The phrase "a right gap in $I_9$ that Theorem UB shows cannot be filled" is imprecise for Chain A sub-cases within A2b, A2c, B2, B3, B4: in those sub-cases, $I_9$ IS filled (by runner 3), but Theorem UB still delivers a gap — just in $I_8$ instead of $I_9$.

**Fix required:** Replace "produce a right gap in $I_9$" with "produce a gap that Theorem UB locates in some slot $I_k$."

---

## What Needs No Fix

The following receive no criticism:

- The **overall argument structure**: Cases B, E, R> are correctly separated; Route 3 (CB case) correctly identifies that GF $> 0$ is the key quantity to prove.
- The **Theorem UB table** itself (lines 756–768): correctly records all sub-case gaps and the slots in which they appear. This is the reliable source of truth.
- The **Chain A and Chain B derivations**: the 4-step algebraic cascades are correct. The runner-intrinsic independence from $g_L$ is correctly noted (lines 737, 750).
- The **PSM lower bounds**: correctly derived and recorded in the table.
- The **Phase-Uniform Extension**: §13 reasoning about $\sigma$-sign stability is sound. The cascade is phase-independent because its inputs (speed parameters $a_i$) are phase-independent.
- The **computational 112/112** check: the boundary configurations were correctly enumerated and verified.
- The **exact C4 certifier** (`lrc_c4_exact_certifier_v1.py`): all 11,440 nine-subsets certified by exact rational arithmetic; all Case D witnesses have $q \leq 5$.

---

## Prioritised Fix List for v25

| Priority | Gap | What to change | Effort |
|---|---|---|---|
| 1 | Gap 1 | Restate Theorem U: "GF$(I_k) > 0$ for some $k$" | 2 lines |
| 2 | Gap 4 | Fix proof summary line 799: "gap in some slot $I_k$" | 1 line |
| 3 | Gap 2 | Add $\sigma_3$ split to cases A2b, A2c, B2, B3, B4 | ~10 lines each |
| 4 | Gap 3 | Recompute minimum gap from Theorem UB table; update lines 801, 815, 817 | Arithmetic |

All four fixes are **mechanical** — they use material already in the paper (Theorem UB table, Chain A result). No new mathematics is required.

---

## Overall Assessment

The n=11 LRC proof for CB configurations is complete and correct at the structural level. The three gaps are:
1. A too-specific corollary claim (the wrong slots are named)
2. Incomplete case splits in individual sub-cases (fixable by adding a $\sigma_3$ branch)
3. A numerical value that is an underestimate of the true minimum gap (the true minimum is smaller but still positive)

None of these gaps allow a counterexample to enter. The proof is ready for a cleanup pass to produce v25.
