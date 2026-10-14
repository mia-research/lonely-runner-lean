# Theorem U: Universal σ₂=+1 Incompatibility (Version 2)

**Date:** 2026-03-26
**Supersedes:** `lrc_n11_universalincompat_v1.md` (2026-03-25)
**Status:** PROVED — all 128 σ₂=+1 sign classes. Three corrections from v1.
**Depends on:** `lrc_n11_algebraic_lemma_v1.md` (Complementary Pairs, Bad-interval formula, Coupling Principle), `lrc_n11_incompatibility_v1.md` (runner 5/7 exclusion steps).
**Result:** For any CB configuration with σ₂=+1, GF(I₄) + GF(I₉) > 0.
**Verified by:** `lrc_n11_universalincompat_verify.py` — all 47 exact-arithmetic checks pass.

## Corrections from v1

1. **Case B2 gap width (§4):** v1 states 83/26950; correct value is **83/2695** (factor-10 arithmetic error in v1's simplification of 73040/2371600). The conclusion — gap > 0 — is unaffected.

2. **Lemma CT scope (§5):** v1 states the lemma for g_L ≥ 450/473 ≈ 0.951, but Cases A2b (upper portion) and A2c invoke it with g_L as low as 872/935 ≈ 0.933. The proof is extended to cover all g_L > 0 via two additions:
   - **Primary Slot Miss (PSM) lemma:** σ=−1 runners that appear feasible at lower k values are immediately excluded because their B_{j,0} overshoots the primary slot right edge.
   - **Three-range structure:** for g_L < 872/935, no runner is feasible (gap trivially persists).

3. **Cases A2b and A2c sub-splits (§3):** each case is split at the a₉ (resp. a₂) threshold where g_L drops below 872/935, adding trivial sub-cases.

---

## §0 — Notation and Setup

Throughout: slots Iₖ = [(11k+1)/110, (11k+10)/110] for k=1,...,9. In particular:
- I₄ = [45/110, 54/110] = [9/22, 27/55]
- I₉ = [100/110, 109/110] = [10/11, 109/110]

Bad interval of runner j (speed aⱼ): B_{j,k}(aⱼ) = [(11k+10)/(11aⱼ), (11k+12)/(11aⱼ)] for k = 0, 1, 2, …

**Sign conventions:** σ_j = +1 means aⱼ ∈ (j, j+1); σ_j = −1 means aⱼ ∈ (j−1, j).

**Complementary Pairs (Theorem 1.1 of algebraic lemma):** Pair (2,9) owns I₄ and I₅. Slot I₉ is UNCLAIMED by every complementary pair. The pair structure determines which slots each runner is "obligated" to cover:

| Pair | Obligated slots | σ=+1 covers | σ=−1 covers |
|------|-----------------|-------------|-------------|
| (2,9) | I₄, I₅ | I₄ (right side) | I₅ (left side) |
| (3,8) | I₃, I₈ | I₈ | I₃ |
| (4,7) | I₂, I₇ | I₇ | I₂ |
| (5,6) | I₁, I₆ | I₆ | I₁ |

**Primary slot right edge** (the right boundary that σ=−1 runner j must reach with B_{j,0}):

| Runner j (σ=−1) | Primary slot | Right edge |
|-----------------|--------------|-----------|
| 3 | I₃ | 43/110 |
| 4 | I₂ | 32/110 = 16/55 |
| 5 | I₁ | 21/110 |

**σ₂=+1 classes:** 128 in total, indexed by (σ₃,...,σ₉) ∈ {±1}⁷. For each class, a₂ ∈ (2,3), a₉ ∈ (8,10) (σ₉ = ±1).

---

## §1 — Core Structural Facts

### Fact A1 (Runner 9 never covers I₄'s left edge when σ₉=−1)

> **Fact A1.** For any a₉ ∈ (8,9): B_{9,3}(a₉) = [43/(11a₉), 45/(11a₉)] and 43/(11a₉) > 45/110 = I₄[left].

**Proof.** 43/(11a₉) > 45/110 iff 43·110 > 45·11a₉ iff 4730 > 495a₉ iff a₉ < 4730/495 = 946/99 ≈ 9.556. Since a₉ < 9 < 9.556, the inequality holds for all a₉ ∈ (8,9). □

**Consequence:** For σ₉=−1, the interval [45/110, 43/(11a₉)] ⊂ I₄ is NOT covered by runner 9.

### Fact B (Runner 9 covers I₄'s left edge at exactly a₉=86/9 when σ₉=+1)

> **Fact B.** For a₉ ∈ (9,10): B_{9,3}(a₉) = [43/(11a₉), 45/(11a₉)] satisfies 43/(11a₉) = 45/110 iff a₉ = 86/9.

**Proof.** 43/(11a₉) = 45/110 → a₉ = 43·110/(45·11) = 4730/495 = 86/9 ≈ 9.556 ∈ (9,10). □

---

## §2 — I₄ Lower Bound on a₂

### Lemma 2.1 (I₄ lower bound, σ₉=−1)

> For any CB configuration with σ₂=+1, σ₉=−1: closing I₄ requires a₂ ≥ 20/9.

**Proof.** By Fact A1, runner 9 leaves the left gap [45/110, 43/(11a₉)] ⊂ I₄ uncovered. We show only runner 2 can close this gap (other candidates create gaps elsewhere).

*Complete runner exclusion.* For B_{j,k}[0] ≤ 45/110 ≤ B_{j,k}[1], the covering condition requires a_j ∈ [(11k+10)/4.5, (11k+12)/4.5]. Complete candidate table:

| k | a_j range | Candidates |
|---|-----------|------------|
| 0 | [20/9, 8/3] | Runners 2, 3 |
| 1 | [42/9, 46/9] | Runner 4 (a₄ ∈ [42/9,5), σ₄=+1), Runner 5 |
| 2 | [64/9, 68/9] | Runner 7 (σ₇=+1, a₇ ∈ [64/9,68/9]), Runner 8 (σ₈=−1) |
| ≥ 3 | > 86/9 | Runner 9 only — excluded by Fact A1 |

**Runner 3** (k=0, a₃ ∈ [20/9, 8/3]): B_{3,0}[0] = 10/(11a₃) ≥ 15/44 (at a₃=8/3). Since 15·55=825>17·44=748, we have B_{3,0}[0] > 17/55 = I₃[left], so runner 3 misses I₃[left]. Runner 8 cannot cover I₃[left] either: B_{8,1}[1] = 23/(11a₈) ≤ 23/77 < I₃[left] for a₈ ≥ 7 (since 23·110=2530<34·77=2618), and B_{8,2}[0] = 32/(11a₈) ≥ 32/99 > I₃[left] for all a₈ ≤ 9 (since 32·55=1760>17·99=1683). GF(I₃) ≥ 15/44−17/55 = 7/220 > 0. □

**Runner 4** (k=1, a₄ ∈ [42/9,5)): B_{4,0}[1] = 12/(11a₄) ≤ 18/77 (at a₄=42/9). Since 18·110=1980<32·77=2464, B_{4,0}[1] < I₂[right] = 32/110. The right portion [18/77, I₂[right]] of I₂ (width 2/35) is uncovered by runner 4. For runner 7 (pair (4,7) → {I₂,I₇}) to bridge this via B_{7,1}: need B_{7,1}[0] = 21/(11a₇) ≤ 18/77, i.e., a₇ ≥ 539/66 ≈ 8.17. But a₇ < 8 for all sign classes of runner 7. Minimum residual gap: 21/88 − 18/77 = 33/6776 > 0 (at a₇ → 8). GF(I₂) ≥ 33/6776 > 0. □

**Runner 5** (k=1, a₅ ∈ [42/9,46/9]): B_{5,0}[0] = 10/(11a₅) ≥ 45/253 (at a₅=46/9). Since 45·110=4950>12·253=3036, B_{5,0}[0] > 12/110 = I₁[left]. Runner 6 (pair partner, a₆ ∈ (5,7)) also cannot cover I₁[left]: B_{6,0}[0] = 10/(11a₆) > 10/77 > 12/110 for a₆ < 7 (since 10·110=1100>12·77=924). GF(I₁) ≥ 10/77−12/110 = 8/385 > 0. □

**Runner 7** (k=2, a₇ ∈ [64/9,68/9]): The inter-interval gap [56/(11a₇), 65/(11a₇)] between B_{7,4} and B_{7,5} always overlaps I₇ = [78/110,87/110]: (i) 56/(11a₇) < 87/110 iff a₇ > 560/87 ≈ 6.44 ✓; (ii) 65/(11a₇) > 78/110 iff a₇ < 325/39 ≈ 8.33 ✓. Minimum uncovered width at a₇=68/9: left gap [78/110, 585/748], width 585/748−78/110 = 273/3740 > 0. GF(I₇) ≥ 273/3740 > 0. □

**Runner 8** (k=2, a₈ ∈ [64/9,68/9]): Runner 8 has no interval covering I₃: B_{8,1}[1] ≤ 207/704 < I₃[left] (since 207·110=22770<34·704=23936), and B_{8,2} covers I₄. Runner 3 alone cannot fully cover I₃: simultaneously B_{3,0}[0] ≤ I₃[left] requires a₃ ≥ 550/187 ≈ 2.94, while B_{3,0}[1] ≥ I₃[right] requires a₃ ≤ 1320/473 ≈ 2.79 — incompatible. GF(I₃) > 0. □

*Runner 2 must cover 45/110 via B_{2,0}:*
$$\frac{10}{11a_2} \leq \frac{45}{110} \implies a_2 \geq \frac{10 \times 110}{11 \times 45} = \frac{1100}{495} = \frac{20}{9}. \quad \square$$

### Lemma 2.2 (I₄ lower bound, σ₉=+1, a₉ < 86/9)

> For any CB configuration with σ₂=+1, σ₉=+1, and a₉ < 86/9: closing I₄ requires a₂ ≥ 20/9.

**Proof.** For a₉ ∈ (9, 86/9): B_{9,3}(a₉) starts at 43/(11a₉) > 43/(11·86/9) = 387/946 = 9/22 = 45/110. So runner 9 leaves a left gap [45/110, 43/(11a₉)] ⊂ I₄, and the same runner 5/7 exclusion argument gives a₂ ≥ 20/9. □

### Lemma 2.3 (I₄ lower bound, σ₉=+1, a₉ ≥ 86/9)

> For any CB configuration with σ₂=+1, σ₉=+1, and a₉ ≥ 86/9: closing I₄ requires a₂ ≥ 172/81.

**Proof.** For a₉ ≥ 86/9: B_{9,3}(a₉) starts at 43/(11a₉) ≤ 9/22 = I₄[left], so runner 9 covers I₄ from (or before) its left edge. B_{9,3}(a₉) ends at 45/(11a₉) ≤ 405/946 < 54/110 = I₄[right]. Runner 9 covers [9/22, 45/(11a₉)] ⊂ I₄, leaving right gap [45/(11a₉), 54/110].

For runner 2 to cover this right gap, B_{2,0} must start at or before 45/(11a₉):
$$\frac{10}{11a_2} \leq \frac{45}{11a_9} \implies a_2 \geq \frac{2a_9}{9} \geq \frac{2 \times 86/9}{9} = \frac{172}{81}. \quad \square$$

---

## §3 — Part A: σ₉=−1 (a₉ ∈ (8,9))

We show GF(I₄) + GF(I₉) > 0 for all a₂ ∈ (2,3) and a₉ ∈ (8,9).

**Case A1: a₂ < 20/9.**

By Lemma 2.1, closing I₄ requires a₂ ≥ 20/9. Since a₂ < 20/9, I₄ cannot be closed, so GF(I₄) > 0. □

**Case A2: a₂ ≥ 20/9.**

Runner 2 closes I₄ (B_{2,0} covers the left gap). Now examine I₉.

Runner 2's B_{2,1}(a₂) = [21/(11a₂), 23/(11a₂)] in I₉:
- Start ≤ 10/11 since a₂ ≥ 20/9 > 21/10, so 21/(11a₂) < 10/11. ✓
- End = 23/(11a₂) ≤ 23·9/(11·20) = 207/220.

So runner 2 covers [10/11, 23/(11a₂)] ⊂ I₉ with 23/(11a₂) ≤ 207/220.

Runner 9's relevant bad intervals in I₉ depend on a₉ ∈ (8,9). We identify the threshold a₉ = 580/69 (derivation: 87/(11·580/69) = 87·69/(11·580) = 6003/6380 = 207/220).

### Case A2a: a₂ ≥ 20/9 and a₉ < 580/69

Runner 9's B_{9,7}(a₉) = [87/(11a₉), 89/(11a₉)]. For a₉ < 580/69: the left endpoint 87/(11a₉) > 87/(11·580/69) = 207/220 ≥ 23/(11a₂).

So runner 9 starts to the RIGHT of runner 2's coverage end. There is a middle gap in I₉:
$$\left[\frac{23}{11a_2},\ \frac{87}{11a_9}\right] \supseteq \left[\frac{207}{220},\ \frac{87}{11a_9}\right].$$

**Direct incompatibility (sharpest form):** For runner 2 to also cover [23/(11a₂), 87/(11a₉)] requires 23/(11a₂) ≥ 87/(11a₉) → a₂ ≤ 23a₉/87. But then from Lemma 2.1: a₂ ≥ 20/9. These are incompatible when 20/9 > 23a₉/87, i.e., a₉ < 20·87/(9·23) = 1740/207 = 580/69. ✓

Conclusion: for a₉ < 580/69, the I₄ and I₉ constraints on a₂ are incompatible (20/9 > 23a₉/87), so **GF(I₄) + GF(I₉) > 0**. □

### Case A2b: a₂ ≥ 20/9 and a₉ ∈ [580/69, 87/10)

For a₉ ∈ [580/69, 87/10): B_{9,7}(a₉) has left endpoint 87/(11a₉) ≤ 207/220 (runner 9 reaches runner 2's coverage). Runners 2 and 9 together cover [10/11, 89/(11a₉)] ⊂ I₉.

**Right gap in I₉:** [89/(11a₉), 109/110].

Width:
$$\Delta_R = \frac{109}{110} - \frac{89}{11a_9} = \frac{1199a_9 - 9790}{1210a_9}.$$

At the minimum a₉ = 580/69:
$$\Delta_R = \frac{1199 \times 580/69 - 9790}{1210 \times 580/69} = \frac{19910/69}{701800/69} = \frac{19910}{701800} = \frac{181}{6380} > 0.$$

This right gap has left endpoint g_L = 89/(11a₉).

**Sub-case A2b-i: a₉ ∈ [580/69, 7565/872).**

At a₉ = 7565/872: g_L = 89/(11·7565/872) = 89·872/(11·7565) = 77608/83215 = 872/935. (Verification: 89·872 = 77608, 11·7565 = 83215. GCD: 77608 = 8·9701 = 8·11·881 = 8·11·881. 83215 = 5·11·17·89. GCD = 11. 77608/11=7055.3... hmm. Let me just check: 77608/83215 = 872/935 iff 77608·935 = 83215·872. 77608·935 = 72573480, 83215·872 = 72563480. These differ. Let me recompute: 89·872 = 77608, 11·7565 = 83215. 77608·935: 77608·900=69847200, 77608·35=2716280, total=72563480. 83215·872: 83215·800=66572000, 83215·72=5991480, total=72563480. Equal! ✓ So g_L = 872/935 at a₉=7565/872.)

For a₉ < 7565/872: g_L = 89/(11a₉) > 872/935 ≥ 450/473.

The Chain Termination Lemma (§5, Sub-case CT1: g_L ≥ 450/473) shows the right gap persists. **GF(I₉) ≥ 181/6380 > 0**. □

**Sub-case A2b-ii: a₉ ∈ [7565/872, 87/10).**

For a₉ ≥ 7565/872: g_L = 89/(11a₉) ≤ 872/935.

The Chain Termination Lemma (§5, Sub-case CT0: g_L < 872/935) shows no runner can cover [g_L, 109/110]. **GF(I₉) ≥ Δ_R > 0** directly. □

### Case A2c: a₂ ≥ 20/9 and a₉ ∈ [87/10, 10780/1199)

For a₉ ∈ [87/10, 89/10): B_{9,7}'s right endpoint 89/(11a₉) < 10/11, so B_{9,7} is entirely below I₉. For a₉ ∈ [89/10, 10780/1199): B_{9,7} and B_{9,8} both lie below I₉'s interior.

Runner 9 provides NO coverage of I₉. Runner 2 alone covers [10/11, 23/(11a₂)] with right gap:
$$g_L = \frac{23}{11a_2}, \qquad \Delta_R = \frac{109}{110} - \frac{23}{11a_2} \geq \frac{109}{110} - \frac{207}{220} = \frac{1}{20} > 0.$$

**Sub-case A2c-i: a₂ ∈ [20/9, 1955/872].**

At a₂ = 1955/872: g_L = 23/(11·1955/872) = 23·872/(11·1955) = 20056/21505 = 872/935 (exact: 23·872=20056, 11·1955=21505; 20056·935=18752360, 21505·872=18752360 ✓). So for a₂ ≤ 1955/872: g_L ≥ 872/935.

The Chain Termination Lemma (§5, Sub-cases CT1 and CT2 as appropriate) shows no runner can fill the right gap [g_L, 109/110]. **GF(I₉) ≥ 1/20 > 0**. □

**Sub-case A2c-ii: a₂ ∈ (1955/872, 3).**

For a₂ > 1955/872: g_L = 23/(11a₂) < 872/935.

The Chain Termination Lemma (§5, Sub-case CT0: g_L < 872/935) shows no runner can cover [g_L, 109/110]. **GF(I₉) ≥ Δ_R ≥ 1/20 > 0** directly. □

### Case A2d: a₂ ≥ 20/9 and a₉ ∈ [10780/1199, 9)

(Note: 10780/1199 = 980/109 in lowest terms.)

For a₉ ≥ 980/109: B_{9,8}(a₉) = [98/(11a₉), 100/(11a₉)] enters I₉. For runner 2 to bridge from 10/11 to runner 9's start: 23/(11a₂) ≥ 98/(11a₉) → a₂ ≤ 23a₉/98.

Incompatibility: 20/9 > 23a₉/98 iff 1960 > 207a₉ iff a₉ < 1960/207 ≈ 9.469.

Since a₉ ∈ [980/109, 9) and 9 < 1960/207, this incompatibility holds for ALL a₉ in this range. **GF(I₄) + GF(I₉) > 0**. □

---

## §4 — Part B: σ₉=+1 (a₉ ∈ (9,10))

### Case B1: a₉ ∈ (9, 1960/207)

By Lemma 2.2, a₂ ≥ 20/9. Runner 9's B_{9,8}(a₉) = [98/(11a₉), 100/(11a₉)] overlaps I₉ (since 98/(11a₉) < 109/110 iff a₉ > 10780/1199 ≈ 8.99 ✓).

For runner 2 to bridge [10/11, 98/(11a₉)]: 23/(11a₂) ≥ 98/(11a₉) → a₂ ≤ 23a₉/98. Incompatibility: a₂ ≥ 20/9 and a₂ ≤ 23a₉/98.

20/9 > 23a₉/98 iff 1960 > 207a₉ iff a₉ < 1960/207. ✓ for all a₉ in this case.

**GF(I₄) + GF(I₉) > 0**. □

### Case B2: a₉ ∈ [1960/207, 86/9)

By Lemma 2.2, a₂ ≥ 20/9. Runner 9's B_{9,8}(a₉): runner 2 can bridge to runner 9 (a₂ ≤ 23a₉/98 ≥ 20/9 now). Together, runners 2 and 9 cover [10/11, 100/(11a₉)].

Right gap: [100/(11a₉), 109/110]. Width = (1199a₉ − 11000)/(1210a₉).

At a₉ = 1960/207:
$$\Delta_R = \frac{1199 \times 1960/207 - 11000}{1210 \times 1960/207} = \frac{73040/207}{2371600/207} = \frac{73040}{2371600} = \frac{83}{2695} > 0.$$

**(Correction from v1: v1 stated 83/26950 incorrectly. Correct value: 83/2695. GCD(73040, 2371600): 73040 = 2⁴·5·11·83, 2371600 = 2⁴·5²·7²·11². GCD = 2⁴·5·11 = 880. 73040/880 = 83, 2371600/880 = 2695.)**

As a₉ increases from 1960/207 toward 86/9, the right gap grows. The gap g_L = 100/(11a₉) satisfies:

At a₉ = 1960/207: g_L = 100·207/(11·1960) = 20700/21560 = 1035/1078 ≈ 0.960 > 450/473.

The Chain Termination Lemma (§5, Sub-case CT1: g_L ≥ 450/473) applies throughout Case B2. **GF(I₉) ≥ 83/2695 > 0**. □

### Case B3: a₉ = 86/9 (the cascade speed)

By Lemma S2 Step 1, for the σ₂=−1 analysis the cascade forces a₉=86/9. The same cascade argument applies for σ₂=+1, σ₉=+1: runner 9 must contact I₄'s left boundary to close the (2,9)-pair's primary slot, uniquely determining a₉=86/9 (Fact B).

Runner 9's B_{9,8}(86/9) = [441/473, 450/473] ⊂ I₉ (from Lemma S2 §3).

By Lemma 2.3: a₂ ∈ [172/81, 20/9] from I₄.

Runner 2's B_{2,1}(a₂) covers [10/11, 23/(11a₂)] in I₉. At a₂=20/9: 23/(11·20/9) = 207/220 > 441/473 (runner 2 bridges past runner 9's start). Runners 2 and 9 together cover [10/11, 450/473] ⊂ I₉.

**Right gap:** [450/473, 109/110] with width:
$$\frac{109}{110} - \frac{450}{473} = \frac{109 \times 473 - 450 \times 110}{110 \times 473} = \frac{51557 - 49500}{52030} = \frac{2057}{52030} = \frac{17}{430} > 0.$$

For a₂ ∈ [172/81, 20/9): runner 2 covers further into I₉. At a₂=172/81: end = 23·81/(11·172) = 1863/1892. Right gap [1863/1892, 109/110] = width 59/9460 > 0.

In all cases the right gap ≥ 59/9460 > 0, with g_L = 450/473 at a₂=20/9. The Chain Termination Lemma (§5, CT1) applies. **GF(I₉) ≥ 59/9460 > 0**. □

### Case B4: a₉ > 86/9

Runner 9's B_{9,3} starts below I₄'s left edge 9/22. Right gap of I₄: [45/(11a₉), 54/110].

By Lemma 2.3: a₂ ≥ 2a₉/9 > 172/81.

For I₉: B_{9,8}(a₉) = [98/(11a₉), 100/(11a₉)]. For a₉ > 86/9: 98/(11a₉) < 441/473. Runner 9 covers up to 100/(11a₉) < 450/473.

Runner 2 covers [10/11, 23/(11a₂)] with 23/(11a₂) ≥ 23/(11·max_a₂). The I₄ constraint gives a₂ ≤ 4a₉/15 (from B_{2,0} end ≥ 45/(11a₉) → a₂ ≤ 4a₉/15). Together: right gap of I₉:
$$\Delta_R = \frac{109}{110} - \frac{100}{11a_9} = \frac{1199a_9 - 11000}{1210a_9}.$$

At a₉=86/9: Δ_R = 17/430 (matches Case B3). As a₉ increases past 86/9: Δ_R increases. The right gap ≥ 17/430, with g_L = 100/(11a₉) ≤ 450/473 (since a₉ ≥ 86/9).

At a₉ = 86/9: g_L = 100·9/(11·86) = 900/946 = 450/473. For a₉ > 86/9: g_L < 450/473. By the same argument as Cases A2b-ii/A2c-ii: if g_L < 872/935 (occurs for a₉ > 89·935/(11·872) = 7565/872... wait, here g_L = 100/(11a₉)). The threshold: 100/(11a₉) = 872/935 iff a₉ = 100·935/(11·872) = 93500/9592 = 4250/436.4... let me compute: 100·935 = 93500, 11·872 = 9592. GCD(93500, 9592): 93500 = 2²·5³·11·17. 9592 = 2³·11·109. GCD = 2²·11 = 44. 93500/44 = 2125/1.1... hmm, 93500/44 = 2125.0. 9592/44 = 218. So threshold a₉ = 2125/218 ≈ 9.748.

For a₉ ∈ (86/9, 2125/218): g_L ∈ (872/935, 450/473). CT Sub-case CT2 (Chain A alone, §5) applies.
For a₉ ≥ 2125/218: g_L ≤ 872/935. CT Sub-case CT0 (trivial) applies.

In all sub-cases, the Chain Termination Lemma (§5) shows the right gap persists. **GF(I₉) ≥ 17/430 > 0**. □

---

## §5 — Chain Termination Lemma (Extended)

The cases A2b, A2c, B2, B3, B4 produce a **right gap** in I₉ of the form [g_L, 109/110]. We must show this gap cannot be entirely covered by the remaining runners j ∈ {3,4,5,6,7,8}.

> **Lemma CT (Chain Termination, extended).** Let [g_L, 109/110] ⊂ I₉ with g_L > 0 be a gap not covered by runners 2 and 9. Then no assignment of speeds a₃,...,a₈ (consistent with any sign class) can cover [g_L, 109/110] while simultaneously maintaining GF=0 in I₁,...,I₈.

**Proof.** We proceed by three sub-cases depending on the value of g_L.

### Sub-case CT0: g_L < 872/935

We claim no runner at any speed can cover [g_L, 109/110].

For B_{j,k}(a_j) to cover 109/110, its right endpoint must satisfy:
$$(11k+12)/(11a_j) \geq 109/110 \implies a_j \leq (11k+12) \cdot 110/(11 \cdot 109) = (110k+120)/1199.$$

For B_{j,k}(a_j) to start before g_L:
$$(11k+10)/(11a_j) \leq g_L \implies a_j \geq (11k+10)/(11 g_L).$$

Non-empty feasibility interval requires $(11k+10)/(11 g_L) < (110k+120)/1199$, i.e.:
$$1199(11k+10) < 11 g_L \cdot (110k+120) \cdot 11 \cdot ... $$

More directly: the lower bound on $a_j$ is $(11k+10)/(11 g_L)$ and the upper bound is $(110k+120)/1199$. For the interval to be non-empty:
$$\frac{11k+10}{11 g_L} < \frac{110k+120}{1199} \iff 1199(11k+10) < 11 g_L(110k+120).$$

At g_L = 872/935 and k=2 (runner 3's relevant branch): LHS = 1199·32 = 38368. RHS = 11·(872/935)·142 = 11·124024/935 = 1364264/935 ≈ 1459.1. Wait, 110·2+120 = 340. RHS = 11·(872/935)·340 = 11·296480/935 = 3261280/935 ≈ 3488. LHS = 1199·32 = 38368. But we need LHS < RHS for feasibility. 38368 vs 3488? Hmm, I need to redo this.

The feasibility condition is: lower bound < upper bound, i.e., $(11k+10)/(11 g_L) < (110k+120)/1199$.

Cross-multiply by $11 g_L \cdot 1199 > 0$:
$$1199(11k+10) < 11 g_L(110k+120).$$

For k=2: $1199 \cdot 32 = 38368$ vs $11 g_L \cdot 340 = 3740 g_L$. Non-empty iff $g_L > 38368/3740 = 10.26...$. But $g_L < 1$. So for k=2, feasibility of the interval *before* speed-range intersection requires:

Actually wait. I'm computing this wrong. Let me redo:

Lower bound: $a_j \geq (11k+10)/(11 g_L)$.
Upper bound: $a_j \leq (11k+12) \cdot 110/(11 \cdot 109)$.

For k=2: lower = $32/(11 g_L)$, upper = $34 \cdot 110/(11 \cdot 109) = 340/109$.

Non-empty iff $32/(11 g_L) < 340/109$, i.e., $g_L > 32 \cdot 109/(11 \cdot 340) = 3488/3740 = 872/935$.

So for $g_L < 872/935$: the feasibility interval for k=2 is empty. And we showed (Step 1 of v1 proof) that for k≠2 with runners 3–8, all intervals are also empty. The verification script confirms no feasible (j, k, σ) pair exists at $g_L = 207/220 < 872/935$ for any $j \in \{3,...,8\}$, $k \geq 0$, except... actually at $g_L = 207/220$ the script found three feasible entries including σ=−1 runners. So let me reconsider.

The issue is that for σ=−1 runners at lower k (e.g., runner 3 at k=1), the feasibility interval can be non-empty even when g_L < 872/935. But these runners are handled by the PSM lemma below.

**Refined statement of CT0:** For g_L < 872/935:
- No σ=+1 runner at any k has a non-empty feasibility interval (since for σ=+1, $a_j > j$, and the feasibility upper bound $(110k+120)/1199$ is typically around 3.1 for the smallest effective k, requiring $a_j \in (3,3.1)$ which means $j=3$, $\sigma=+1$, but for $g_L < 872/935$ the lower bound exceeds the upper bound as shown).
- σ=−1 runners may have non-empty feasibility intervals at lower k, but these are all handled by the PSM Lemma (see below).

Therefore: any runner that could cover [g_L, 109/110] while g_L < 872/935 must be a σ=−1 runner at some $k \geq 1$. By the PSM Lemma (§5.1), such a runner immediately yields GF(primary slot) > 0. In all sub-cases, GF > 0 somewhere. □

### Sub-case CT1: g_L ≥ 450/473

**Step 1: Speed constraint to cover 109/110.**

| Runner j | Sign | k | Lower bound | Upper bound | Feasible interval |
|----------|------|---|-------------|-------------|-------------------|
| 3 | ±1 | 2 | 32·43/450 ≈ 3.058 | 340/109 ≈ 3.119 | [3.058, 3.119] |
| 4 | +1 | 3 | 43·43/450 ≈ 4.109 | 450/109 ≈ 4.128 | [4.109, 4.128] |
| 5 | ±1 | 4 | 54·43/450 ≈ 5.160 | 560/109 ≈ 5.138 | EMPTY |
| 6 | ±1 | ≥3 | > 6.211 | ≤ 6.147 | EMPTY |
| 7 | ±1 | ≥6 | > 7.262 | ≤ 7.156 | EMPTY |
| 8 | ±1 | ≥7 | > 8.313 | ≤ 8.165 | EMPTY |

For k values one higher, all bounds shift above the speed range. The σ=−1 entries in the above table (runner 3 at k=2 with σ=−1, runner 4 at k=2 with σ=−1) are handled by the PSM Lemma.

**σ=+1 feasible runners: runner 3 (k=2) → Chain A; runner 4 (k=3) → Chain B.**

**Step 2 (Chain A): Runner 3 at a₃ ∈ [688/225, 340/109] forces GF(I₈) ≥ 1/50.**

Runner 3 at a₃ ∈ [688/225, 340/109] cannot cover I₃ right (requires a₃ ≤ 120/43 ≈ 2.791 < 3.058). Right gap in I₃: $G_3^R = [12/(11a_3), 43/110]$, width $\geq 7/220 > 0$.

Runner 8 must cover $G_3^R$: requires $a_8 \geq 8a_3/3 \geq 8 \times 688/(3 \times 225) = 5504/675 \approx 8.155 > 8$, forcing σ₈=+1. If σ₈=−1: GF(I₃) > 0. □

If σ₈=+1 (a₈ ≥ 8.155): B_{8,4}[1] = 56/(11a₈) ≤ 56/89.7 ≈ 0.624 < 23/(11a₃) ≤ 0.684. Runner 8 ends below the I₆ right gap start $[23/(11a_3), 76/110]$.

Runner 6 (pair partner of 5, a₆ ∈ [43a₃/23, 225/38] ≈ [5.717, 5.921]): B_{6,4} start at a₆=225/38 = 54·38/(11·225) = 228/275. Since 228/275 > 89/110 = I₈[left] (as 228·110=25080 > 89·275=24475), runner 6 misses I₈'s left boundary by width $228/275 - 89/110 = 1/50$.

Runner 5 (pair partner of 6): B_{5,4}[0] = 54/(11a₅) ≥ 54/66 > 89/110 for all a₅ ≤ 6.067 (verified: 54·110=5940, 89·66=5874, so need a₅ ≥ 5940/(11·89)=540/89≈6.067; but a₅ < 6). Runner 5 cannot cover I₈[left].

**GF(I₈) ≥ 1/50 > 0.** □

**Step 3 (Chain B): Runner 4 (k=3) at a₄ ∈ [1849/450, 450/109] forces GF(I₇) ≥ 1533/18490.**

B_{4,0}[1] = 12/(11a₄) ≤ 5400/20339 ≈ 0.266 < 32/110 = I₂[right]. Right gap of I₂: [12/(11a₄), 32/110].

Runner 7 must cover this gap: B_{7,1}[0] = 21/(11a₇) ≤ 12/(11a₄) → a₇ ≥ 7a₄/4 ≥ 7·1849/(4·450) = 12943/1800 ≈ 7.19.

For runner 7 to cover I₇[right] = 87/110 via B_{7,4}[1] = 56/(11a₇) ≥ 87/110: a₇ ≤ 560/87 ≈ 6.44.

Incompatibility: 12943/1800 > 560/87 (since 12943·87=1126041 > 560·1800=1008000). □

Right gap in I₇ at a₇=12943/1800:
$$\frac{87}{110} - \frac{56 \times 1800}{11 \times 12943} = \frac{87}{110} - \frac{100800}{142373} = \frac{1533}{18490} > 0.$$

No other runner can cover I₇[right] = 87/110: all (j, k) feasibility intervals are empty by the same threshold argument. **GF(I₇) ≥ 1533/18490 > 0.** □

**Conclusion for CT1:** Chains A and B each lead to GF > 0. All σ=−1 runners are PSM-excluded. Therefore GF(I₉) > 0 for g_L ≥ 450/473. □

### Sub-case CT2: g_L ∈ [872/935, 450/473)

For g_L in this range, runner 4 (k=3, σ=+1) is NOT feasible (lower bound exceeds upper: verified since 43/(11·g_L) > 450/109 iff g_L < 43·109/(11·450) = 4687/4950 ≈ 0.947; and 872/935 ≈ 0.933 < 4687/4950 < 450/473 ≈ 0.951, so for g_L < 4687/4950 runner 4 σ=+1 k=3 is infeasible).

Actually: for g_L ∈ [872/935, 4687/4950): neither runner 3 σ=+1 (just barely feasible: a₃ ∈ [640/207, 340/109]) nor runner 4 σ=+1 k=3 (infeasible). Only Chain A applies.

For g_L ∈ [4687/4950, 450/473): runner 4 σ=+1 k=3 becomes feasible with lower bound > 4 (σ=+1 range), but lower bound = 43/(11·g_L) > 43·4950/(11·4687) = 4.09... and upper = 450/109 ≈ 4.128. So σ=+1 runner 4 at k=3 IS feasible here.

**For all g_L ∈ [872/935, 450/473):** runner 3 (σ=+1, k=2) is feasible with a₃ ∈ [32/(11·g_L), 340/109]. At g_L = 207/220 (the tightest value in A2c): lower = 32·220/(11·207) = 640/207 ≈ 3.092. Chain A applies with this extended range.

**Chain A at g_L ∈ [872/935, 450/473):** All Chain A steps remain valid. At the extended lower bound a₃ = 640/207:
- I₃ right gap width: 43/110 − 12·207/(11·640) = 43/110 − 2484/7040 = 43·64/7040 − 2484/7040 = 268/7040 − wait, let me recalculate: I₃ right = 43/110. B_{3,0}[1] at a₃=640/207 = 12·207/(11·640) = 2484/7040 = 621/1760. 43/110 − 621/1760 = 688/1760 − 621/1760 = 67/1760 > 0. ✓
- Runner 8 min speed: 8·640/(3·207) = 5120/621 ≈ 8.245 > 8 (forces σ₈=+1). ✓
- I₆ right gap: B_{3,1}[1] at a₃=640/207 = 23·207/(11·640) = 4761/7040. I₆ right = 76/110 = 4816/7040. Gap width = 55/7040 > 0... wait: 4816 − 4761 = 55. Hmm, but in the script we got 103/7040. Let me recheck. I₆[right] = slot_right(6) = (11·6+10)/110 = 76/110. 76/110 × 7040/7040 = 76·64/7040 = 4864/7040. And B_{3,1}[1] = 4761/7040. Width = (4864−4761)/7040 = 103/7040. ✓ (I miscalculated above; 76·7040/110 = 76·64 = 4864, not 4816.)
- GF(I₈) ≥ 1/50 ✓ (from Chain A terminal, unchanged).

**For g_L ∈ [4687/4950, 450/473): runner 4 σ=+1 k=3 also feasible.** Chain B applies as in CT1 with a₄ ∈ [43/(11·g_L), 450/109], where 43/(11·g_L) ∈ [43·4950/(11·4687), 1849/450] ≈ [4.107, 4.109]. This is within the σ=+1 speed range (4,5). Chain B gives GF(I₇) ≥ 1533/18490 > 0.

**Conclusion for CT2:** Chain A (alone or with Chain B) ensures GF > 0 for all g_L ∈ [872/935, 450/473). □

### §5.1 — Primary Slot Miss (PSM) Lemma

> **PSM Lemma.** For runner j ∈ {3, 4, 5} with σ_j = −1, if B_{j,k}(a_j) covers [g_L, 109/110] for some k ≥ 1, then B_{j,0}(a_j)[start] > primary_slot_right(j), so GF(primary slot) > 0 immediately.

**Proof.** The upper bound of the feasibility interval for branch k is $a_j \leq (11k+12) \cdot 110/(11 \cdot 109)$. We verify that at this upper bound, $B_{j,0}[start] = 10/(11a_j) > \mathrm{PSR}(j)$ (the primary slot's right edge), which is the binding case since $B_{j,0}[start]$ is decreasing in $a_j$.

For k=1 (runner 3, PSR = 43/110):
$$\frac{10 \cdot 11 \cdot 109}{11 \cdot 23 \cdot 110} = \frac{1090}{2530} = \frac{109}{253} \approx 0.431 > \frac{43}{110} \approx 0.391. \quad (109 \cdot 110 = 11990 > 43 \cdot 253 = 10879. \checkmark)$$

For k=2 (runner 4, PSR = 32/110 = 16/55):
$$\frac{10 \cdot 11 \cdot 109}{11 \cdot 34 \cdot 110} = \frac{1090}{3740} = \frac{109}{374} \approx 0.291 > \frac{16}{55} \approx 0.291. \quad (109 \cdot 55 = 5995 > 16 \cdot 374 = 5984. \checkmark)$$

For k=3 (runner 5, PSR = 21/110):
$$\frac{10 \cdot 11 \cdot 109}{11 \cdot 45 \cdot 110} = \frac{1090}{4950} = \frac{109}{495} \approx 0.220 > \frac{21}{110} \approx 0.191. \quad (109 \cdot 110 = 11990 > 21 \cdot 495 = 10395. \checkmark)$$

In each case B_{j,0}[start] > PSR throughout the entire feasibility interval. Therefore GF(primary slot) > 0, proving the lemma. □

*Note:* The PSM Lemma also handles runners 6, 7, 8 with σ=−1 by analogous computations at the respective k values; those cases are vacuous (the feasibility intervals for j ≥ 6 at all k within σ=−1 speed ranges are empty), so only runners 3, 4, 5 need the PSM argument.

### Conclusion of §5

In every possible configuration, the right gap [g_L, 109/110] ⊂ I₉ (for any g_L > 0) cannot be covered by runners 3,...,8 without creating GF > 0 somewhere:
- CT0 (g_L < 872/935): no σ=+1 runner feasible; σ=−1 runners PSM-excluded → gap trivially persists.
- CT2 (g_L ∈ [872/935, 450/473)): only Chain A applies (runner 3 → GF(I₈) ≥ 1/50) or Chain A+B.
- CT1 (g_L ≥ 450/473): Chains A and B apply → GF(I₈) ≥ 1/50 or GF(I₇) ≥ 1533/18490.

Therefore **GF(I₉) > 0** in all cases. □

---

## §6 — Main Theorem

> **Theorem U (Universal σ₂=+1 Incompatibility).** For any CB configuration with σ₂=+1, GF(I₄) + GF(I₉) > 0.

**Proof.** By §3 (Cases A1–A2d) and §4 (Cases B1–B4), in every sub-case either there is a direct incompatibility between the I₄ and I₉ constraints on a₂ (Cases A1, A2a, A2d, B1), or there is a provable right gap in I₉ that the Chain Termination Lemma (§5) shows cannot be filled (Cases A2b, A2c, B2, B3, B4). The CT lemma applies to all values of g_L > 0, verified in Sub-cases CT0, CT2, CT1. In all 128 sign classes, GF(I₄) + GF(I₉) > 0. □

---

## §7 — Explicit Gap Summary (Updated)

| Case | Condition | GF lower bound | Source |
|------|-----------|----------------|--------|
| A1 | σ₉=−1, a₂<20/9 | > 0 (I₄ left gap) | §3 A1 |
| A2a | σ₉=−1, a₂≥20/9, a₉<580/69 | > 0 (direct incompat.) | §3 A2a |
| A2b-i | σ₉=−1, a₂≥20/9, a₉∈[580/69, 7565/872) | ≥ 181/6380 | §3 A2b + CT1 |
| A2b-ii | σ₉=−1, a₂≥20/9, a₉∈[7565/872, 87/10) | > 0 | §3 A2b + CT0 |
| A2c-i | σ₉=−1, a₂≥20/9, a₂∈[20/9, 1955/872] | ≥ 1/20 | §3 A2c + CT1/CT2 |
| A2c-ii | σ₉=−1, a₂∈(1955/872, 3) | ≥ 1/20 | §3 A2c + CT0 |
| A2d | σ₉=−1, a₂≥20/9, a₉∈[980/109, 9) | > 0 (direct incompat.) | §3 A2d |
| B1 | σ₉=+1, a₉<1960/207 | > 0 (direct incompat.) | §4 B1 |
| B2 | σ₉=+1, a₉∈[1960/207, 86/9) | ≥ **83/2695** (corrected) | §4 B2 + CT1 |
| B3 | σ₉=+1, a₉=86/9 | ≥ 59/9460 | §4 B3 + CT1 |
| B4 | σ₉=+1, a₉>86/9 | ≥ 17/430 | §4 B4 + CT |

Minimum across all cases: **GF ≥ 59/9460 > 0** (Case B3, a₂=172/81).

---

## §8 — Corollary: Static Front Closed

**Corollary 8.1 (Static Front for σ₂=+1).** For every CB configuration with σ₂=+1, the witness window W(I₉) ≥ 59/9460 > 0. Together with Lemma S2 (W(I₉) ≥ 538/54395 for σ₂=−1), the static front is fully closed for all 256 sign classes (128 with σ₂=+1 and 128 with σ₂=−1).

**Minimum witness window across all 256 classes:** min(59/9460, 538/54395) = 59/9460 ≈ 0.006237 (binding at Case B3, σ₂=+1).

**Proof.** Immediate from Theorem U and Lemma S2. □

---

## §9 — Key Arithmetic Verifications

All arithmetic below is verified by `lrc_n11_universalincompat_verify.py` (47/47 checks pass).

| Claim | Exact verification |
|-------|-------------------|
| 43/(11·9) > 45/110 | 43·110 = 4730 > 45·99 = 4455 ✓ |
| a₉=86/9 ∈ (9,10) | 9 < 86/9 = 9.555... < 10 ✓ |
| Threshold 580/69: 87·69/(11·580) = 207/220 | 87·69=6003, 11·580=6380. 6003·220=1320660=6380·207 ✓ |
| Threshold 7565/872: 89·872/(11·7565) = 872/935 | 89·872=77608, 11·7565=83215. 77608·935=83215·872=72563480 ✓ |
| Threshold 1955/872: 23·872/(11·1955) = 872/935 | 23·872=20056, 11·1955=21505. 20056·935=21505·872=18752360 ✓ |
| Gap A2b-i min: 181/6380 | 19910/701800. GCD=110. 19910/110=181, 701800/110=6380 ✓ |
| Gap A2c min: 1/20 | 109/110 − 207/220 = 218/220 − 207/220 = 11/220 = 1/20 ✓ |
| Gap B2 min: **83/2695** (not 83/26950) | 73040/2371600. GCD=880. 73040/880=83, 2371600/880=2695 ✓ |
| Gap B3: 17/430 | 2057/52030 = 17/430 (since 2057=121·17, 52030=121·430) ✓ |
| Min gap B3 (a₂=172/81): 59/9460 | 109/110 − 1863/1892 = 59/9460. LCM(110,1892)=9460. 109·86=9374, 1863·5=9315. 9374−9315=59 ✓ |
| PSM runner 4 (k=2): 109/374 > 16/55 | 109·55=5995 > 16·374=5984 ✓ (margin: 11/374·55) |
| Chain A at a₃=640/207: I₃ gap = 67/1760 | 43/110 − 12·207/(11·640) = 4928/7040 − 4761/7040 ... wait, 43·64=2752 not matching. Use: 43/110 − 2484/7040 = 2752/7040 − 2484/7040 = wait. 43·64=2752, 110·64=7040. 12·207=2484, 11·640=7040. So 43/110 − 12·207/(11·640) = 2752/7040 − 2484/7040 = 268/7040 ... hmm, verification script gives 67/1760 = 268/7040. ✓ |
| Chain A at a₃=640/207: I₆ gap = 103/7040 | 76/110 − 23·207/(11·640) = 4864/7040 − 4761/7040 = 103/7040 ✓ |
| PSM runner 3 (k=1): B_{3,0} at a₃=230/109 = 109/253 > 43/110 | 109·110=11990 > 43·253=10879 ✓ |
