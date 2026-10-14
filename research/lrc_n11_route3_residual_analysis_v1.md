# Route 3 Residual Analysis: WHY Theorem R1 Stops at Ratio 89

**File**: `lrc_n11_route3_residual_analysis_v1.md`
**Date**: 2026-03-26
**Status**: Analysis complete
**Companion files**: `lrc_n11_route3_extension_v1.md` (Theorem R1), `lrc_n11_universalincompat_v3.md` (Theorem U), `lrc_n11_ap_paper_v20.md`

---

## Overview

Theorem R1 closes Case R> for p₁₀/p₁ ∈ (10, 89) using Route 3 + runner-1 isolation. Two residuals remain:

- **Mild residual**: p₁₀/p₁ ∈ [89, 100] — approximately 11 integer ratios per p₁₀
- **Hard residual**: p₁₀/p₁ > 100 — architecturally inaccessible to Route 3

This document explains WHY these residuals exist (the structural mechanism), identifies a logical gap in the Theorem U v3 proof, and characterizes what new argument would close each residual.

---

## §1 The Structural Conflict: Left-Edge Gaps vs. Left-Blocking Runner 1

### §1.1 Route 3 cascade gaps live at left edges of slots

The Route 3 proof works by finding a sub-interval within some slot I_k where runners 2–9 all fail to cover that sub-interval, giving GF_{2-9}(I_k) > 0. The cascade structure determines WHERE that sub-interval lives within I_k.

**Chain A** (runner 3, σ₃=+1, a₃ ∈ (3, 27/8)): cascade 3→8→6→5 forces
- Runner 3 covers I₉, creating I₃ right gap [12/(11a₃), 43/110]
- Runner 8 forced to cover I₃ gap → runner 8 exits I₈ on the left
- Runner 6 forced to cover I₈ left portion → runner 6 exits I₆ on the right
- Runner 5 cannot simultaneously cover the forced positions
- **Gap**: [89/110, B₆,₄[0]] ⊂ I₈, where B₆,₄[0] = 228/275
- **Gap location**: LEFT edge of I₈ = 89/110

**Chain B** (runner 4, σ₄=+1, a₄ ∈ (4, 80/19)): cascade 4→7→5→6 forces
- **Gap location**: LEFT edge of I₇

**Lemma S2** (σ₂=−1): GF_{2-9}(I₉) ≥ 538/54395 > 0 unconditionally
- **Gap location**: within I₉ (right gap [g_L, 109/110])

**Case α-1** (σ₂=+1, σ₉=−1): runner 9 opens I₉ middle gap
- **Gap location**: within I₉

The pattern: **cascade gaps propagate rightward from I₉ to lower-indexed slots (I₈, I₇), leaving gaps at their left edges**. This is because the cascade force is: "runner j must reach left into slot I_{k-1} to cover a gap forced at the left of I_{k-1}."

### §1.2 Runner 1 blocks from the left of W₀

Runner 1 has speed a₁ ∈ (0, 1) (Case R>). Its isolation condition within W₀ = [1/11, 10/11] is:

> Runner 1 is isolated throughout slot I_k iff its fractional parts avoid [0, 1/11) ∪ (10/11, 1] for all t ∈ I_k.

More precisely (Lemma R1.0): runner 1 is isolated in I_k iff a₁ ∈ [10/(11k+1), 100/(11k+10)].

As a₁ decreases from 1, the lower bound 10/(11k+1) for each slot gives the threshold below which runner 1 enters that slot's left boundary and becomes isolated there. But crucially:

**Runner 1's boundary t_block = 1/(11a₁) is the first time in W₀ where runner 1 becomes isolated.** For times t < 1/(11a₁) within W₀, runner 1 is NOT isolated (its fractional part {a₁t} < 1/11). This blocks any GF witness at those times.

As a₁ decreases:
- a₁ = 10/89 ≈ 0.1124: t_block reaches I₈ left = 89/110. Runner 1 enters the Chain A gap.
- a₁ = 25/228 ≈ 0.1096: t_block reaches I₈ right = 228/275. Runner 1 covers the ENTIRE Chain A gap.
- a₁ = 5/39 ≈ 0.1282: t_block reaches I₇ left = 78/110. Runner 1 enters Chain B gap.
- a₁ = 1/10 = 0.100: t_block reaches I₉ left = 10/11. Runner 1 enters W₁.
- a₁ < 1/10: t_block > 10/11 = right boundary of W₀. Runner 1 blocks ALL of W₀.

### §1.3 The collision

Route 3 cascade gaps are at **left edges** of slots. Runner 1 blocks from the **left of W₀** sweeping rightward. These structures are in direct geometric conflict: as the ratio p₁₀/p₁ increases (a₁ decreases), runner 1's blocking boundary advances rightward and consumes the cascade gaps in the order they appear from left to right.

---

## §2 Theorem U v3 Proof Gap

### §2.1 The stated theorem (lrc_n11_universalincompat_v3.md, Line 246)

> **Theorem U**: For any CB configuration with σ₂=+1, GF(I₄) + GF(I₉) > 0.

The proof partitions into Case α (direct incompatibility on a₂) and Case β (right gap in I₉ propagated via runner 3 or 4 cascade). Case β is handled at Line 251:

> "GF(I₄) + GF(I₉) ≥ GF(I₉) > 0 since the gap in I₉ persists, or GF(I_k) > 0 for k ≠ 9."

### §2.2 The logical flaw

**Chain A requires runner 3 to cover I₉.** Specifically:
- Chain A Step 1: runner 3 with σ₃=+1 covers I₉, creating an I₃ gap.
- The cascade then produces GF(I₈) ≥ 1/50.

In Chain A configurations: **GF(I₉) = 0** (runner 3 covers I₉ completely). The I₄+I₉ sum is therefore 0 + 0 = 0 for any configuration where:
- Runner 3 covers I₉ (fixing GF(I₉) = 0), AND
- GF(I₄) = 0 (runners 2, 4–9 collectively cover I₄)

Chain A gives GF(I₈) ≥ 1/50, not GF(I₉) > 0. The theorem statement "GF(I₄) + GF(I₉) > 0" is incorrect for these configurations.

### §2.3 Correct statement

The correct conclusion of Theorem U for σ₂=+1 is:

> **For any CB configuration with σ₂=+1: GF(I_k) > 0 for some k ∈ {1, ..., 9}.**

Specifically:
- Case α: GF(I₄) > 0 OR GF(I₉) > 0 (one or both, depending on a₂'s sub-case)
- Case β, Chain A: GF(I₈) > 0
- Case β, Chain B: GF(I₇) > 0

The sum "GF(I₄) + GF(I₉)" in the v3 theorem statement is an error — it should be "GF(I₄) + GF(I₇) + GF(I₈) + GF(I₉)" or equivalently "GF(I_k) > 0 for some k."

### §2.4 Impact on Theorem R1

Theorem R1 as proved in `lrc_n11_route3_extension_v1.md` is **correct** because it was proved slot-by-slot:
- For Chain A configurations: runner 1 isolated in I₈ (where GF(I₈) > 0) iff a₁ ≥ 10/89.
- For Chain B configurations: runner 1 isolated in I₇ (where GF(I₇) > 0) iff a₁ ≥ 5/39.

The Theorem U v3 error does not affect Theorem R1's validity — it only affects the v3 theorem statement, which should be corrected in any future version.

---

## §3 Corrected Slot-by-Slot Scope of Theorem R1

The following table gives, for each Route 3 configuration class, the slot k where GF_{2-9}(I_k) > 0, the minimum a₁ for runner 1 to be isolated in I_k, and thus the maximum ratio p₁₀/p₁ = 10/a₁ that Theorem R1 closes.

| Configuration | Slot k | GF_{2-9}(I_k) | Min a₁ for isolation | Max ratio closed |
|---|---|---|---|---|
| σ₂=−1 (Lemma S2) | I₉ | ≥ 538/54395 | 1/10 | 100 |
| σ₂=+1, Case α-1 (σ₉=−1, a₉ < 580/69) | I₉ | > 0 (middle gap) | 1/10 | 100 |
| σ₂=+1, Case α-2/α-3 (a₂ ∈ [20/9, 3) sub-case) | I₉ | > 0 | 1/10 | 100 |
| σ₂=+1, Case α-2/α-3 (a₂ ∈ (2, 575/261) sub-case) | I₄ | > 0 | 2/9 | 45 |
| σ₂=+1, Case β, Chain A (runner 3 covers I₉) | I₈ | ≥ 1/50 | **10/89** | **89** |
| σ₂=+1, Case β, Chain B (runner 4 covers I₉) | I₇ | ≥ 1533/18490 | 5/39 | 78 |

**The binding constraint is Chain A in the a₂ sub-case where only I₄ gets a gap (not I₉):** threshold 10/89, giving ratio 89. All other configuration classes have thresholds ≥ 5/39 and thus ratios ≤ 78, which are already within the (10, 89) range.

Wait — let me re-examine. The Chain A threshold is 10/89 and closes ratios < 89. The Case α-2/α-3 I₄ sub-case needs a₁ ≥ 2/9 and closes ratios < 45, which is already within (10, 89). The Lemma S2 and Case α-1 thresholds give ratio ≤ 100, which EXCEEDS 89.

**Revised table with correct interpretation:**

| Configuration | Slot k | Min a₁ | Max ratio closed (10/a₁) | Within (10,89)? |
|---|---|---|---|---|
| σ₂=−1 (all sub-cases) | I₉ | 1/10 | 100 | **YES** — and BEYOND |
| σ₂=+1, Case α-1 | I₉ | 1/10 | 100 | **YES** — and BEYOND |
| σ₂=+1, Case α-2/α-3, I₉ sub-case | I₉ | 1/10 | 100 | **YES** — and BEYOND |
| σ₂=+1, Case α-2/α-3, I₄ sub-case | I₄ | 2/9 | 45 | Yes, easily |
| σ₂=+1, Case β, Chain A | **I₈** | **10/89** | **89** | **Binding — exactly 89** |
| σ₂=+1, Case β, Chain B | I₇ | 5/39 | 78 | Yes |

**Conclusion**: Theorem R1 threshold 10/89 (ratio 89) is set by Chain A. ALL OTHER configuration classes close ratio ≤ 100 (three of them) or ratio ≤ 78 (one of them). The mild residual [89, 100] consists ENTIRELY of Chain A configurations with a₁ ∈ [1/10, 10/89).

---

## §4 The Mild Residual [89, 100]: Structure and Scope

### §4.1 Which configurations form the residual

For p₁₀/p₁ ∈ [89, 100] (equivalently a₁ ∈ [1/10, 10/89)):

- σ₂=−1: **ALREADY CLOSED** — Lemma S2 gives GF(I₉) > 0 and runner 1 is isolated in I₉ for a₁ ≥ 1/10. ✓
- σ₂=+1, Case α-1: **ALREADY CLOSED** — I₉ middle gap, runner 1 isolated in I₉. ✓
- σ₂=+1, Case α-2/α-3 (I₉ sub-case): **ALREADY CLOSED** — I₉ gap, runner 1 isolated. ✓
- σ₂=+1, Case α-2/α-3 (I₄ sub-case): **ALREADY CLOSED** — requires a₁ ≥ 2/9 > 10/89, but this sub-case has ratio ≤ 45 < 89. No overlap with [89, 100]. ✓
- σ₂=+1, Case β, Chain B: **ALREADY CLOSED** — requires ratio ≤ 78 < 89. No overlap. ✓
- **σ₂=+1, Case β, Chain A: OPEN for ratio ∈ [89, 100].**

### §4.2 What fails for Chain A in this range

For a₁ ∈ [1/10, 10/89):
- Chain A gives GF(I₈) ≥ 1/50 (the I₈ gap [89/110, 228/275]).
- Runner 1 isolated in I₈ iff a₁ ≥ 10/89. For a₁ < 10/89: runner 1 NOT isolated in I₈.
  - More precisely: 1/(11a₁) > 89/110 = I₈ left. Runner 1 enters the I₈ gap from the left.

Sub-case: a₁ ∈ [25/228, 10/89) (ratio ∈ (89, 91.2]):
- Runner 1's boundary t_block = 1/(11a₁) ∈ (89/110, 228/275) — enters the gap but does NOT cover it entirely.
- Sub-interval [t_block, 228/275] ⊂ I₈ gap is still uncovered by runners 2–9.
- BUT runner 1 is NOT isolated in this sub-interval (its fractional part {a₁t} < 1/11 for t < 1/(11a₁) and {a₁t} crosses 0 at t = 1/(11a₁)).
- **Upshot**: runners 2–9 leave [89/110, 228/275] open; runner 1 partially blocks it. The portion [t_block, 228/275] has GF_{2-9} > 0 but runner 1 is not isolated there. No full GF_total > 0.

Sub-case: a₁ ∈ [1/10, 25/228) (ratio ∈ (91.2, 100]):
- Runner 1's boundary t_block = 1/(11a₁) ≥ 228/275 = I₈ gap right edge.
- Runner 1 covers the ENTIRE I₈ gap [89/110, 228/275].
- GF_{2-9}(I₈) > 0 but runner 1 additionally blocks all of it. Complete failure.

**In both sub-cases**: Chain A's I₈ gap is blocked. Chain A gives no other gap (GF(I₉) = 0 since runner 3 covers I₉ in Chain A).

### §4.3 Why no alternative slot exists for Chain A in this range

The question is: for Chain A configurations with a₁ ∈ [1/10, 10/89), does ANY slot I_k have:
- GF_{2-9}(I_k) > 0, AND
- Runner 1 isolated in I_k (a₁ ≥ 10/(11k+1))?

For runner 1 to be isolated in I₉: need a₁ ≥ 1/10. This IS satisfied for a₁ ∈ [1/10, 10/89). ✓

BUT: **In Chain A configurations, runner 3 covers I₉** (this is the PREMISE of Chain A — runner 3's σ₃=+1 and a₃ ∈ (3, 27/8) covers I₉ at t ∈ I₉). Therefore GF_{2-9}(I₉) = 0 for all Chain A configurations.

Summary of all slots for Chain A with a₁ ∈ [1/10, 10/89):

| Slot | GF_{2-9}(I_k) > 0? | Runner 1 isolated? | Both? |
|---|---|---|---|
| I₉ | NO (runner 3 covers it) | YES (a₁ ≥ 1/10) | NO |
| I₈ | YES (Chain A gives ≥ 1/50) | NO (a₁ < 10/89) | NO |
| I₇ | Unknown (not Chain B) | YES (a₁ ≥ 5/39 < 1/10 fails — wait) | — |
| I₄ | Not proved > 0 for Chain A | NO (a₁ ≥ 2/9 > 10/89 fails) | NO |

For I₇: runner 1 isolated in I₇ iff a₁ ≥ 5/39 ≈ 0.128. But a₁ < 10/89 ≈ 0.112 < 0.128. So runner 1 is NOT isolated in I₇ either.

**There is no slot I_k where both conditions hold simultaneously for Chain A configurations with a₁ ∈ [1/10, 10/89).** The mild residual is genuine and not an artifact.

---

## §5 The Hard Residual p₁₀/p₁ > 100: Architectural Barrier

### §5.1 Why Route 3 fails completely

For a₁ < 1/10: runner 1's isolation window in W₀ satisfies 1/(11a₁) > 10/11 = right boundary of W₀. Runner 1 is never isolated in W₀. Any GF witness time t must have {a₁t} ∈ [1/11, 10/11], but for t ∈ W₀ = [1/11, 10/11] and a₁ < 1/10:

- {a₁t} = a₁t (since a₁t < (1/10)(10/11) = 1/11)
- So {a₁t} < 1/11 for ALL t ∈ W₀.
- Runner 1 is isolated in W₀ only if {a₁t} ≥ 1/11 — impossible.

Route 3 works within W₀. Runner 1 must be isolated in W₀ for any GF_total > 0 there. The hard residual is architecturally inaccessible to Route 3.

### §5.2 The natural window W₁

Runner 1 is isolated in windows W_m = [m/(11a₁) + 1/(11a₁), (m+1)/(11a₁)] for integer m. The first window where runner 1 could be isolated:

**W₁ = [1/(11a₁), 2/(11a₁)]** (shifted isolation window)

For a₁ < 1/10: W₁ starts at 1/(11a₁) > 10/11 > W₀ right end. W₁ is entirely outside W₀.

Within W₁, runner 10 (speed 10) is cycling rapidly. The structure of I₁,...,I₉ relative to runner 10's pacemaker is different — runner 10 makes ≈ p₁₀/(10p₁) full cycles within W₁. The AP pacemaker structure is reproduced within each sub-window of W₁ of width 1/10.

### §5.3 Why the fix is non-trivial

The Route 3 cascade (Theorem U + Lemma S2) uses the specific slot structure I_k = [(11k+1)/110, (11k+10)/110] based on runner 10 at speed 10 being the AP pacemaker at times t = m/11. In W₁:
- Runner 10 makes approximately p₁₀/(10p₁) half-integer crossings.
- The "slots" relevant to runner 10's pacemaker structure in W₁ are shifted by 1/(11a₁) and compressed by 1/p₁₀ relative to W₀.
- The Complementary Pairs structure (runners 2–9) must be re-derived for these shifted slots.

This is not impossible but requires a separate analysis. The ILE/Containment route (Route 2's companion, proved for integer sub-cases) is likely more natural for this regime.

### §5.4 Integer example: {1, 2, ..., 10, 101}

For the configuration with speeds {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 101} (p₁=1, p₁₀=101, ratio=101):
- a₁ = 10/101 ≈ 0.0990 < 1/10
- W₀ = [1/11, 10/11]. Runner 1 never isolated in W₀.
- W₁ = [101/1110, 202/1110] = [101/1110, 101/555]. Width 1/1110.
- Within W₁: runner 10 (speed 10) makes ≈ 10/11 of a full cycle. Runner 1 (speed 10/101) makes exactly 1/(11) of a cycle.

A numerical verification would check if there exists t ∈ W₁ where all speeds {1, 2, ..., 9, 10} are simultaneously isolated (in their fractional parts at time t using the original speeds {1, ..., 101}).

---

## §6 What Would Close Each Residual

### §6.1 Closing the mild residual [89, 100]

The residual is **exclusively Chain A configurations with σ₂=+1, runner 3 covering I₉, and a₁ ∈ [1/10, 10/89)**.

**Approach 1 (Cascade extension)**: Show that Chain A configurations with runner 3 covering I₉ must also leave a gap in I₃ that runner 1 can exploit. Specifically:
- Chain A Step 1 produces I₃ right gap [12/(11a₃), 43/110].
- For a₁ ∈ [1/10, 10/89): runner 1 isolated in I₃ iff a₁ ≥ 10/(11·3+1) = 10/34 = 5/17 ≈ 0.294 > 10/89. **Fails.**

**Approach 2 (Use I₆ or other cascade slots)**: Chain A cascade goes 3→8→6→5. Check if Chain A also forces GF(I₆) > 0 or GF(I₅) > 0 with runner 1 isolated.
- Runner 1 isolated in I₆ iff a₁ ≥ 10/67 ≈ 0.149 > 10/89. **Fails.**
- Runner 1 isolated in I₅ iff a₁ ≥ 10/56 ≈ 0.179 > 10/89. **Fails.**

**Approach 3 (Different runner isolation)**: Instead of isolating runner 1 in the CASCADE gap slot, show that within the W₀ window where runner 1 IS isolated ([1/(11a₁), W₀ right] for a₁ < 1), the remaining runners 2–9 leave a gap. For a₁ ∈ [1/10, 10/89), runner 1 is isolated in I₉ (since a₁ ≥ 1/10). We need GF_{2-9}(I₉) > 0 for Chain A configurations.

**This is the key question for the mild residual**: does the Chain A condition (runner 3 covers I₉) preclude GF_{2-9}(I₉) > 0?

By definition, YES — Chain A requires runner 3 to cover all of I₉, meaning GF_{2-9}(I₉) = 0 (runner 3's B_{3,+1} covers I₉ for a₃ ∈ (3, 27/8)).

Wait — runner 3 "covering I₉" means runner 3 is NOT isolated in I₉ (it crosses through I₉ without being isolated). For GF_{2-9}(I₉) > 0 we need ALL of runners 2–9 to be isolated throughout some sub-interval of I₉. Runner 3 covering I₉ means {a₃t} passes through [0,1/11) or (10/11,1] for t ∈ I₉ — runner 3 is NOT isolated in all of I₉, so GF_{2-9}(I₉) = 0 in Chain A. Confirmed.

**Approach 4 (Separate window argument)**: Route 3 uses the witness in W₀. For a₁ ∈ [1/10, 10/89), consider the sub-window [1/(11a₁), 10/11] ⊂ W₀ where runner 1 IS isolated. Within this sub-window, apply a cascade argument adapted to the reduced window. This is essentially Route 3 with W₀ replaced by [1/(11a₁), 10/11]. The right boundary 10/11 is fixed; the left boundary moves with a₁.

For a₁ = 10/89 (ratio exactly 89): [1/(11·10/89), 10/11] = [89/110, 10/11]. This is exactly I₈ ∪ I₉! Runner 3 covers I₉ but leaves I₈ gap — runner 1 is isolated at the very left of I₈. Route 3 in this reduced window = Theorem R1 at its boundary. ✓

For a₁ ∈ [1/10, 10/89): [1/(11a₁), 10/11] = [something > 89/110, 10/11]. The window is I₉ only (since 89/110 < 1/(11a₁) < 10/11). In I₉, runner 3 covers → GF_{2-9}(I₉) = 0. Route 3 in this reduced window gives 0.

**Conclusion**: No Route 3 variant closes Chain A for ratio ∈ (89, 100]. A genuinely different mechanism is needed.

**Correct approach (open problem)**: For Chain A configurations with a₁ ∈ [1/10, 10/89), find a witness time t ∈ W₁ = [1/(11a₁), 2/(11a₁)] where runner 1 is isolated. This is the W₁ argument — same as the "hard residual" approach but for a window that OVERLAPS W₀ on the right (W₁ ∩ W₀ ⊃ [1/(11a₁), 10/11] when a₁ ≥ 1/10).

Actually for a₁ ≥ 1/10: W₁ left = 1/(11a₁) ≤ 10/11 = W₀ right. So W₁ starts inside W₀. The question is whether the Route 3 cascade can be applied within W₁ ∩ W₀ = [1/(11a₁), 10/11] specifically at slots other than I₉.

**This suggests a Route 3-W₁ hybrid argument is the natural proof path for the mild residual.**

### §6.2 Closing the hard residual p₁₀/p₁ > 100

**Required**: New argument working in W₁ = [1/(11a₁), 10/(11a₁)] (or sub-windows thereof) where:
- Runner 1 is isolated throughout by construction.
- Runner 10 (speed 10) cycles through ≈ p₁₀/(10p₁) > 10 full cycles within W₁.
- Runners 2–9 must collectively fail to cover some sub-interval.

The ILE/Containment route (Route 2 companion, proved for integer sub-cases) operates in this regime: it uses the "approach window" structure where runner 10 approaches a multiple of 1/10, and shows the other runners cannot all be non-isolated simultaneously during this approach.

Alternatively: the Route 3 cascade structure may re-appear within each sub-window of W₁ of width 1/10 (one cycle of runner 10). If the Complementary Pairs structure holds within each such sub-window — which it does, since CP is a speed-ratio property invariant under time shifts — then Route 3 adapted to W₁ closes the hard residual too.

---

## §7 Summary

| Regime | Mechanism that gives GF > 0 | Runner 1 isolation | Closed? |
|---|---|---|---|
| p₁₀/p₁ ∈ (10, 45) | Theorem U (all cases) | In I₄, I₇, I₈, or I₉ | **YES** (Theorem R1) |
| p₁₀/p₁ ∈ (45, 78) | Theorem U (all except Chain A) | In I₇, I₈, or I₉ | **YES** (Theorem R1) |
| p₁₀/p₁ ∈ (78, 89) | Theorem U (Chain A via I₈; others via I₉) | In I₈ or I₉ | **YES** (Theorem R1) |
| p₁₀/p₁ ∈ [89, 100] | Chain A: gap in I₈ only; all other classes: gap in I₉ | NOT in I₈; IS in I₉ | **Partial**: non-Chain-A closed; Chain A open |
| p₁₀/p₁ > 100 | Route 3 inapplicable; W₁ needed | Not in W₀ | **Open** |

**The binding constraint**: Chain A is the unique configuration class where GF_{2-9} > 0 occurs in I₈ (not I₉). Runner 1 enters I₈ from the left at ratio 89, consuming the Chain A gap. The I₉ window is blocked by runner 3 (the Chain A premise). Result: exactly the range [89, 100] is left open for Chain A.

**The proof gap in Theorem U v3** (Line 251): the stated conclusion "GF(I₄) + GF(I₉) > 0" is incorrect for Chain A configurations. Correct: "GF(I_k) > 0 for some k ∈ {1,...,9}." This does not affect Theorem R1 (which was proved slot-by-slot) but should be corrected in future versions of `lrc_n11_universalincompat_v3.md`.

---

*End of lrc_n11_route3_residual_analysis_v1.md*
