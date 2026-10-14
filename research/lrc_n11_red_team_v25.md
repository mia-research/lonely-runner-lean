# Red Team Assessment — lrc_n11_ap_paper_v25.md
**Date:** 2026-03-30
**Scope:** Adversarial review of the complete proof of LRC for n=11, all three cases (B, E, R>).
**Verdict:** The logical spine is intact. Cases B and E are correct. Case R> has four structural gaps and one notation collision that would stop a referee. Several supporting claims are overstated or unproved. None of the gaps appear to require new mathematics — all are fillable — but the paper cannot be submitted in its current state.

---

## Issues by Severity

---

### CAT-1 — Structural gaps: would be fatal to peer review as written

---

**[RT-1] "CB configuration" is never formally defined**

Used ~20 times across §10.4–§13, first appearing in Definition 10.4.A. The definition says "For a CB configuration δ..." but never defines what CB means. No reader can determine whether CB = "GF(W₀) = 0 everywhere in the analysis window" or something else.

Required fix: Add before Definition 10.4.A:

> **Definition (CB configuration).** A configuration δ = (δ₁,...,δ₉) is *completely blocking* (CB) for a window W ⊂ ℝ₊ if GF(W) = 0, i.e., every t ∈ W is covered by the bad interval of at least one runner j ∈ {1,...,10}. Equivalently, the union ∪_j ∪_k B_{j,k} covers W.

The proof structure of §11–§12 should then be made explicit:

> We assume for contradiction that the configuration is CB. The analysis below shows this leads to a contradiction (some slot I_k cannot be covered), so GF(I_k) > 0, completing the LRC proof.

Without this, the reader cannot follow why "closing slot I_k" is relevant to LRC.

---

**[RT-2] Sign convention only covers a_j ∈ (j−1, j+1) — EFN range not covered**

§11.1 sign convention: σ_j = +1 ↔ a_j ∈ (j, j+1); σ_j = −1 ↔ a_j ∈ (j−1, j). This partitions a_j ∈ (j−1, j+1) into two cases. But in EFN, a_j ∈ (a_{j-1}, a_{j+1}) ⊂ (0,10) — there is no argument that a_j stays within one unit of its AP slot j.

Example: a₂ = 3.9, a₃ = 4.2 is a valid EFN ordering. Here a₂ ∈ (3,4) which is σ₂ = "above slot 2 AND above slot 3" — neither σ₂=+1 (which requires a₂ ∈ (2,3)) nor σ₂=−1 covers this. The 256 sign classes only cover configurations where a_j ∈ (j−1, j+1) for every j ∈ {2,...,9}. Configurations with a runner displaced by more than 1 unit from its AP slot are simply not handled.

The paper cannot claim "128 σ₂=+1 sign classes are covered" without first establishing that the set of CB configurations is contained in the union of these 128+128 classes.

**What needs to be proved:** A preliminary lemma establishing that in any CB configuration (for the pacemaker window W₀[m] ⊂ W_ref), a_j ∈ (j−1, j+1) for each j ∈ {2,...,9}. The argument is available:

- If a_j ∉ (j−1, j+1), then a_j ∈ (j+1, j+2) (say). Runner j's B_{j,0} ends at 12/(11a_j) < 12/(11(j+1)), and B_{j,1} starts at 21/(11a_j) > 21/(11(j+2)). The interval [12/(11a_j), 21/(11a_j)] — which no bad interval of runner j covers — contains the left boundary of slot I_j when j is chosen appropriately. The complementary pair argument then forces GF(I_k) > 0 immediately, proving LRC without the deep §11 analysis.

Without this lemma, the entire 256-class case split in §11–§12 has a coverage gap.

---

**[RT-3] Lemma 11.2.1 — "runner-by-runner exclusion" is asserted, not proved**

Line 591–592: "Runner-by-runner exclusion forces runner 2 to close the gap. The condition B_{2,0}[0] ≤ 45/110 gives: a₂ ≥ 20/9."

The assertion that NO runner other than runner 2 can reach I₄'s left boundary 45/110 is the key structural claim of the entire §11 proof — yet it is one sentence with no verification. An adversarial referee will immediately check this.

**Verification (should be added to the paper):** For runner j with a_j ∈ (j−1, j+1):
- Bad interval B_{j,0}[1] = 12/(11a_j). For j ≥ 3 and a_j ≥ 3: B_{j,0}[1] ≤ 12/33 = 4/11 ≈ 0.364 < 45/110 ≈ 0.409. So runner j's k=0 interval ENDS before 45/110.
- Bad interval B_{j,1}[0] = 21/(11a_j). For a_j ≤ j+1 ≤ 10: B_{j,1}[0] ≥ 21/110 ≈ 0.191. For a_j ∈ (3,4): B_{j,1}[0] ∈ (21/44, 21/33) ≈ (0.477, 0.636) > 0.409. So runner j's k=1 interval STARTS after 45/110.

Therefore for all runners j ≥ 3 with a_j ∈ (j−1,j+1): the point 45/110 falls in the gap (B_{j,0}[1], B_{j,1}[0]) — covered by NEITHER interval. Only runner 2 with a_2 ∈ (1,3) can have B_{2,0} straddle 45/110 (specifically when a_2 ≥ 20/9).

This proof is three lines and should be included. Its absence is the most obvious gap a referee would find.

---

**[RT-4] Notational collision: σ in §12.2.3 cascade table ≠ σ in §11.1 sign convention**

In §11.1: σ_j = +1 means a_j ∈ (j, j+1) (runner above AP slot j).
In §12.2.3 cascade-forced speeds table (line 910): σ = +1 means runner closes a slot's LEFT (lower) boundary; σ = −1 means it closes the RIGHT boundary.

These are OPPOSITE: the row "Runner 3, σ=+1, closes I₃ left, a₃=50/17≈2.94" has a₃ = 2.94 ∈ (2,3), which by §11.1 is σ₃ = −1. And "Runner 3, σ=−1, closes I₆ left, a₃=115/38≈3.03" has a₃ ∈ (3,4), which is σ₃ = +1 by §11.1.

The entire §12 Lemma S2 analysis uses the inverted convention without warning. A reader trying to cross-reference §11 and §12 will find systematically wrong sign assignments. The σ in §12.2.3 should be renamed — e.g., τ_j = "slot-closure direction" — and its relationship to §11.1's σ_j explained.

---

### CAT-2 — Proof gaps: fillable but currently absent

---

**[RT-5] Proposition E (line 400) — open vs. closed interval**

The proof asserts "there exists s* > 0 such that {q_i s*} ∈ (1/11, 10/11)" (open interval, needed to show y ∈ S where S = (1/11,10/11)^10). But the cited witnesses (Theorem B for bounded ratio, W_ref for large ratio) give ||q_i s*|| ≥ 1/11 — the closed interval. Theorem B's witness t* = 10/(11q₁₀) gives q₁₀ t* = 10/11 exactly (a boundary point).

The open-interval claim is achievable (the good fraction GF > 0 in both cases means there's an open interval of witnesses, not just an isolated boundary point), but the proof must say so explicitly:

> "Choose s* strictly in the interior of the good fraction window (which has positive measure by Theorem B / Theorem W_ref / good fraction positivity). Then {q_i s*} ∈ (1/11, 10/11) strictly, so y ∈ S."

Without this, y could be in T_e ∩ ∂S — the boundary of S — and the density-of-orbit argument would not give a witness strictly inside S.

---

**[RT-6] W₀ definition is ambiguous throughout §10.4**

"W₀" appears in Definition 10.4.A without definition. The slots I₁,...,I₉ (defined as pacemaker cycles W₀[1],...,W₀[9]) lie in [12/110, 109/110], which is OUTSIDE the first pacemaker cycle W₀[0] = [1/110, 10/110]. So GF(W₀) in Definition 10.4.A cannot refer to GF(W₀[0]) (the slots aren't inside it). The paper must define what window W₀ means in §10.4: presumably the union of all pacemaker cycles up to W₀[9], i.e., [1/110, 109/110] minus bad windows for runner 10. This should be stated.

---

**[RT-7] Theorem 10.4.5 — "runner 4 disrupts I₂" is asserted without proof**

Line 527: "runners 4, 5, 7, 8 either have speeds too large or their shift disrupts I₂ coverage (runner 5 case) or I₇ coverage (runner 7 case), forcing another slot to be open."

For runner 4 with a₄ ∈ (14/3, 5) ≈ (4.67, 5): B_{4,1}[0] = 21/(11a₄) ≤ 45/110, so runner 4 CAN start covering I₄ from the left via B_{4,1}. The paper claims this forces I₂ to be open but never verifies it. The verification requires showing B_{4,0}[1] = 12/(11a₄) < 32/110 = I₂[right] for a₄ ∈ (14/3,5): 12/(11·14/3) = 12·3/154 = 36/154 ≈ 0.234 < 0.291. ✓ So runner 4's B_{4,0} ends before I₂'s right edge, but this alone doesn't prove some other runner can't cover I₂. A proper argument (or relegation to the systematic §11 analysis) is needed.

Note: §10.4.5 is in the motivational ++------ sub-case, already superseded by §11. It may be simplest to flag this as "see §11 for the complete treatment" and drop the runner-by-runner claim here.

---

**[RT-8] Contradiction structure of §11–§12 never stated**

§11 begins analyzing what runner speeds are needed to "close" each slot, but never says explicitly: "Assume for contradiction that GF = 0 in some pacemaker cycle. Then every slot I_k (k=1,...,9) is covered by the bad intervals of runners 2–9. We show this leads to contradictory speed constraints." Without this framing, the reader cannot tell whether the paper is:
(a) Proving constraints are impossible → contradiction → LRC, or
(b) Constructing a witness directly.

The proof is (a), but (b) is what §10.4 (Theorem 10.4.4, explicit t* = 69/275) does. The transition from (b) to (a) between §10 and §11 is never signposted.

---

### CAT-3 — Overstatements and minor errors

---

**[RT-9] "At least 9 complete pacemaker cycles in W_ref" is incorrect (§13 setup, line 1069)**

Claim: "W_ref contains at least 9 complete pacemaker cycles of runner v₁₀."

Counterexample: a₁ = 0.99. W_ref = [1/(11·0.99), 10/(11·0.99)] ≈ [0.0918, 0.918]. The pacemaker cycles W₀[m] for m = 1,...,8 are [(11m+1)/110, (11m+10)/110]. For m=8: [89/110, 98/110] ≈ [0.809, 0.891] ⊂ [0.0918, 0.918] ✓. For m=9: [100/110, 109/110] ≈ [0.909, 0.991]. Right endpoint 0.991 > 0.918 = W_ref right. So m=9 is NOT contained. Only 8 cycles fit when a₁ ≈ 0.99.

The correct statement: "W_ref contains at least ⌊9(10/a₁−1)/11⌋ ≥ 8 complete cycles (and the proof only needs one)." The claim of ≥9 is wrong for a₁ ∈ (0.9, 1). Change to "at least one complete pacemaker cycle" (proved in Step 2 of Corollary W_ref) — that's all the proof requires.

---

**[RT-10] Corollary W_ref Step 2 — length bound states "> 81/11" not just "> 1"**

Line 1201: "length > 81/11 > 1 because a₁ < 1."

81/11 ≈ 7.36 is correct (9(10/a₁−1)/11 > 9(10−1)/11 = 81/11 when a₁ < 1). This IS correct — no error. But given RT-9 above, the "≥9 cycles" claim elsewhere is inconsistent with the Step 2 calculation (which gives length > 81/11 ≈ 7.36, implying ≥7 integers in the interval, not necessarily ≥9). The internal consistency should be checked; change the setup text to match Step 2.

---

**[RT-11] B1 case (line 774) doesn't state which slot is open (minor, negligible)**

"B1 (a₉ < 1960/207): Lemma 11.2.2 gives a₂ ≥ 20/9. Bridging I₉ requires a₂ ≤ 23a₉/98 < 20/9. INCOMPATIBLE. □"

Unlike all other cases (now fixed in v25), this one doesn't explicitly say "GF(I_k) > 0 for some k." Trivial fix: add "Runner 2 cannot close both I₄ and I₉; if runner 3 covers I₉ instead, Chain A forces GF(I₈) ≥ 1/50. GF(I_k) > 0 for some k ∈ {4, 8, 9}. □"

---

**[RT-12] Lemma CR — "proved for integer speeds" is slightly imprecise**

Line 1225: "Theorem W_ref (proved for integer speeds)."

Theorem W_ref (§13) is proved for all CB configurations with EFN-normalised speeds a_j ∈ (j−1,j+1) — not specifically integer speeds. The integer-speed case is the setting of Appendix A's computational verification. The statement should say: "Theorem W_ref gives a witness for the integer-speed configuration (p₁,...,p₁₀)." The lemma's point is that commensurable reals REDUCE to integer speeds; Theorem W_ref applies to those integers.

---

## Summary Table

| ID | Location | Category | Nature | Fix effort |
|---|---|---|---|---|
| RT-1 | §10.4.1 | CAT-1 | CB definition missing | Add ~5 lines |
| RT-2 | §11.1 | CAT-1 | Sign convention: a_j ∈ (j±1) never justified for CB configs | New preliminary lemma |
| RT-3 | §11, Lemma 11.2.1 | CAT-1 | Runner-by-runner exclusion unproved | Add 3-line calculation |
| RT-4 | §12.2.3 | CAT-1 | σ in §12 table ≠ σ in §11 convention | Rename + note in §12 |
| RT-5 | §10.2, line 400 | CAT-2 | Prop E: open-interval claim unjustified | Add one sentence |
| RT-6 | §10.4.1 | CAT-2 | W₀ undefined | Add definition |
| RT-7 | §10.4.5, line 527 | CAT-2 | Runner-4 case unproved | Defer to §11 or prove |
| RT-8 | §11 (start) | CAT-2 | Contradiction structure not stated | Add 2-sentence framing |
| RT-9 | §13 setup | CAT-3 | "≥9 pacemaker cycles" overstated | Change to ≥8 or "≥1" |
| RT-10 | §13 Step 2 | CAT-3 | Internal consistency with RT-9 | Align wording |
| RT-11 | §11, B1 case | CAT-3 | Missing "GF > 0 for some k" | One line |
| RT-12 | §14, Lemma CR | CAT-3 | "integer speeds" imprecise | One word |

---

## What is Solid

For the record, the following are genuinely watertight and would survive adversarial review unchanged:

- **Theorem B**: Three-line direct proof, elementary, correct.
- **Proposition E logical core**: The Kronecker closure + subgroup argument is correct modulo the open-set gap (RT-5).
- **Bad interval formula** B_{j,k} = [(11k+10)/(11a_j), (11k+12)/(11a_j)]: verified against the loneliness condition.
- **Lemma CR**: One-line proof, correct.
- **Corollary W_ref Step 2** (existence of m*): The interval length calculation is correct and sufficient.
- **Lemma S2 Case C** (the minimum gap 538/54395): The arithmetic is verified, all contiguity checks hold.
- **Chain A** (GF(I₈) ≥ 1/50): The four-step cascade is correct and phase-independent.
- **Chain B** (GF(I₇) ≥ 1533/18490): The incompatibility arithmetic is correct.
- **PSM lemma**: Correct for runners 3, 4, 5; the margin-11 check for runner 4 (109·55=5995 vs 16·374=5984) is verified.
- **Phase-Uniform Extension** (Lemma P + Lemma C): Phase-independence arguments are correct — the cascade depends only on speed values, not on cycle index.
- **Runner 2 Incompatibility** (§10.4.5): The exact bound arithmetic (20/9 > 575/261 with gap 5/261 > 0) is correct.

---

## Priority Order for v26

1. **RT-2** (sign convention coverage) — most substantial; needs a preliminary lemma or a proof that CB forces a_j ∈ (j−1,j+1).
2. **RT-1** (CB definition) — one paragraph, unblocks all downstream reading.
3. **RT-3** (Lemma 11.2.1 runner exclusion) — three lines, high referee visibility.
4. **RT-4** (σ notation collision in §12) — rename σ → τ in §12.2.3 table + add note.
5. **RT-5** (Prop E open interval) — one sentence.
6. **RT-6** (W₀ definition) — one definition.
7. **RT-7, RT-8** — minor prose additions.
8. **RT-9 through RT-12** — single-sentence fixes.
