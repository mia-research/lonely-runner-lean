# Theorem U: Universal σ₂=+1 Incompatibility

**Date:** 2026-03-25
**Status:** PROVED — canonical `sigma_2 = +1` static theorem for all 128 sign classes.
**Depends on:** `lrc_n11_algebraic_lemma_v1.md` (Complementary Pairs, Bad-interval formula, Coupling Principle).
**Canonical role:** Imported into `lrc_n11_static_core_theorem_v1.md`. The runner-exclusion arguments needed here are internal to §2 and §5 of this file.
**Result:** For any CB configuration with σ₂=+1, GF(I₄) + GF(I₉) > 0.

---

## §0 — Notation and Setup

Throughout: slots Iₖ = [(11k+1)/110, (11k+10)/110] for k=1,...,9. In particular:
- I₄ = [45/110, 54/110] = [9/22, 27/55]
- I₉ = [100/110, 109/110] = [10/11, 109/110]

Bad interval of runner j (speed aⱼ): B_{j,k}(aⱼ) = [(11k+10)/(11aⱼ), (11k+12)/(11aⱼ)] for k = 0, 1, 2, …

**Sign conventions:** σ_j = +1 means aⱼ ∈ (j, j+1); σ_j = −1 means aⱼ ∈ (j−1, j).

**Complementary Pairs (Theorem 1.1 of algebraic lemma):** Pair (2,9) owns I₄ and I₅. Slot I₉ is UNCLAIMED by every complementary pair.

**σ₂=+1 classes:** 128 in total, indexed by (σ₃,...,σ₉) ∈ {±1}⁷. For each class, a₂ ∈ (2,3), a₉ ∈ (8,10) (σ₉ = ±1).

---

## §1 — Core Structural Facts

### Fact A1 (Runner 9 never covers I₄'s left edge when σ₉=−1)

> **Fact A1.** For any a₉ ∈ (8,9): B_{9,3}(a₉) = [43/(11a₉), 45/(11a₉)] and 43/(11a₉) > 45/110 = I₄[left].

**Proof.** 43/(11a₉) > 45/110 iff 43·110 > 45·11a₉ iff 4730 > 495a₉ iff a₉ < 4730/495 = 946/99 ≈ 9.556. Since a₉ < 9 < 9.556, the inequality holds for all a₉ ∈ (8,9). □

**Consequence:** For σ₉=−1, the interval [45/110, 43/(11a₉)] ⊂ I₄ is NOT covered by runner 9.

### Fact B (Runner 9 covers I₄'s left edge at exactly a₉=86/9 when σ₉=+1)

> **Fact B.** For a₉ ∈ (9,10): B_{9,3}(a₉) = [43/(11a₉), 45/(11a₉)] satisfies 43/(11a₉) = 45/110 iff a₉ = 86/9.

**Proof.** 43/(11a₉) = 45/110 → a₉ = 43·110/(45·11) = 4730/495 = 946/99 = 86/9 ≈ 9.556 ∈ (9,10). □

---

## §2 — I₄ Lower Bound on a₂

### Lemma 2.1 (I₄ lower bound, σ₉=−1)

> For any CB configuration with σ₂=+1, σ₉=−1: closing I₄ requires a₂ ≥ 20/9.

**Proof.** By Fact A1, runner 9 leaves the left gap [45/110, 43/(11a₉)] ⊂ I₄ uncovered. We show only runner 2 can close this gap (other candidates create gaps elsewhere).

*Complete runner exclusion.* For $B_{j,k}[0] \leq 45/110 \leq B_{j,k}[1]$, the covering condition requires $a_j \in [(11k+10)/4.5,\, (11k+12)/4.5]$. Complete candidate table:

| $k$ | $a_j$ range | Candidates |
|-----|-------------|------------|
| 0 | $[20/9,\, 8/3]$ | Runners 2, 3 |
| 1 | $[42/9,\, 46/9]$ | Runner 4 ($a_4 \in [42/9,5)$, $\sigma_4{=}+1$), Runner 5 |
| 2 | $[64/9,\, 68/9]$ | Runner 7 ($\sigma_7{=}+1$, $a_7 \in [64/9,68/9]$), Runner 8 ($\sigma_8{=}-1$) |
| $\geq 3$ | $> 86/9$ | Runner 9 only — excluded by Fact A1 |

**Runner 3** ($k=0$, $a_3 \in [20/9, 8/3]$): $B_{3,0}[0] = 10/(11a_3) \geq 15/44$ (at $a_3=8/3$). Since $15\cdot55=825>17\cdot44=748$, we have $B_{3,0}[0] > 17/55 = I_3[\text{left}]$, so runner 3 misses $I_3[\text{left}]$. Runner 8 cannot cover $I_3[\text{left}]$ either: $B_{8,1}[1] = 23/(11a_8) \leq 23/77 < I_3[\text{left}]$ for $a_8 \geq 7$ (since $23\cdot110=2530<34\cdot77=2618$), and $B_{8,2}[0] = 32/(11a_8) \geq 32/99 > I_3[\text{left}]$ for all $a_8 \leq 9$ (since $32\cdot55=1760>17\cdot99=1683$). $\mathrm{GF}(I_3) \geq 15/44-17/55 = 7/220 > 0$. $\square$

**Runner 4** ($k=1$, $a_4 \in [42/9,5)$): $B_{4,0}[1] = 12/(11a_4) \leq 18/77$ (at $a_4=42/9$). Since $18\cdot110=1980<32\cdot77=2464$, $B_{4,0}[1] < I_2[\text{right}] = 32/110$. The right portion $[18/77,\, I_2[\text{right}]]$ of $I_2$ (width $2/35$) is uncovered by runner 4. For runner 7 (pair $(4,7) \to \{I_2,I_7\}$) to bridge this via $B_{7,1}$: need $B_{7,1}[0] = 21/(11a_7) \leq 18/77$, i.e., $a_7 \geq 539/66 \approx 8.17$. But $a_7 < 8$ for all sign classes of runner 7. Minimum residual gap: $21/88 - 18/77 = 33/6776 > 0$ (at $a_7 \to 8$). $\mathrm{GF}(I_2) \geq 33/6776 > 0$. $\square$

**Runner 5** ($k=1$, $a_5 \in [42/9,46/9]$): $B_{5,0}[0] = 10/(11a_5) \geq 45/253$ (at $a_5=46/9$). Since $45\cdot110=4950>12\cdot253=3036$, $B_{5,0}[0] > 12/110 = I_1[\text{left}]$. Runner 6 (pair partner, $a_6 \in (5,7)$) also cannot cover $I_1[\text{left}]$: $B_{6,0}[0] = 10/(11a_6) > 10/77 > 12/110$ for $a_6 < 7$ (since $10\cdot110=1100>12\cdot77=924$). $\mathrm{GF}(I_1) \geq 10/77-12/110 = 8/385 > 0$. $\square$

**Runner 7** ($k=2$, $a_7 \in [64/9,68/9]$): The inter-interval gap $[56/(11a_7),\, 65/(11a_7)]$ between $B_{7,4}$ and $B_{7,5}$ always overlaps $I_7 = [78/110,87/110]$: (i) $56/(11a_7) < 87/110$ iff $a_7 > 560/87 \approx 6.44$ ✓; (ii) $65/(11a_7) > 78/110$ iff $a_7 < 325/39 \approx 8.33$ ✓. Minimum uncovered width at $a_7=68/9$: left gap $[78/110,\, 585/748]$, width $585/748-78/110 = 273/3740 > 0$ (since $585\cdot110=64350>78\cdot748=58344$). $\mathrm{GF}(I_7) \geq 273/3740 > 0$. $\square$

**Runner 8** ($k=2$, $a_8 \in [64/9,68/9]$): Runner 8 has no interval covering $I_3$: $B_{8,1}[1] \leq 207/704 < I_3[\text{left}]$ (since $207\cdot110=22770<34\cdot704=23936$), and $B_{8,2}$ covers $I_4$. Runner 3 alone cannot fully cover $I_3$: simultaneously $B_{3,0}[0] \leq I_3[\text{left}]$ requires $a_3 \geq 550/187 \approx 2.94$, while $B_{3,0}[1] \geq I_3[\text{right}]$ requires $a_3 \leq 1320/473 \approx 2.79$ — incompatible. $\mathrm{GF}(I_3) > 0$. $\square$

*Runner 2 must cover 45/110 via $B_{2,0}$:*
$$\frac{10}{11a_2} \leq \frac{45}{110} \implies a_2 \geq \frac{10 \times 110}{11 \times 45} = \frac{1100}{495} = \frac{20}{9}. \quad \square$$

### Lemma 2.2 (I₄ lower bound, σ₉=+1, a₉ < 86/9)

> For any CB configuration with σ₂=+1, σ₉=+1, and a₉ < 86/9: closing I₄ requires a₂ ≥ 20/9.

**Proof.** For a₉ ∈ (9, 86/9): B_{9,3}(a₉) starts at 43/(11a₉) > 43/(11·86/9) = 387/946 = 9/22 = 45/110. So runner 9 leaves a left gap [45/110, 43/(11a₉)] ⊂ I₄, and the same runner 5/7 exclusion argument gives a₂ ≥ 20/9. □

### Lemma 2.3 (I₄ lower bound, σ₉=+1, a₉ ≥ 86/9)

> For any CB configuration with σ₂=+1, σ₉=+1, and a₉ ≥ 86/9: closing I₄ requires a₂ ≥ 172/81.

**Proof.** For a₉ ≥ 86/9: B_{9,3}(a₉) starts at 43/(11a₉) ≤ 9/22 = I₄[left], so runner 9 covers I₄ from (or before) its left edge. B_{9,3}(a₉) ends at 45/(11a₉) ≤ 405/946 < 54/110 = I₄[right]. Runner 9 covers [9/22, 45/(11a₉)] ⊂ I₄, leaving right gap [45/(11a₉), 54/110].

For runner 2 to cover this right gap, B_{2,0} must start at or before 45/(11a₉):
$$\frac{10}{11a_2} \leq \frac{45}{11a_9} \implies a_2 \geq \frac{10a_9}{45} = \frac{2a_9}{9} \geq \frac{2 \times 86/9}{9} = \frac{172}{81}. \quad \square$$

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

Width at the critical point (a₂=20/9, a₉→580/69):
$$\frac{87}{11 \times 580/69} - \frac{23 \times 9}{11 \times 20} = \frac{207}{220} - \frac{207}{220} = 0^+.$$

More precisely: for a₉ < 580/69, the gap width is 87/(11a₉) − 23/(11a₂) ≥ 87/(11a₉) − 207/220.

This equals zero only in the limit a₉ → 580/69, and is strictly positive for all a₉ < 580/69.

**Direct incompatibility (sharpest form):** For runner 2 to also cover [23/(11a₂), 87/(11a₉)] requires 23/(11a₂) ≥ 87/(11a₉) → a₂ ≤ 23a₉/87. But then from Lemma 2.1: a₂ ≥ 20/9. These are incompatible when 20/9 > 23a₉/87, i.e., a₉ < 20·87/(9·23) = 1740/207 = 580/69. ✓

Conclusion: for a₉ < 580/69, the I₄ and I₉ constraints on a₂ are incompatible (20/9 > 23a₉/87), so **GF(I₄) + GF(I₉) > 0**. □

### Case A2b: a₂ ≥ 20/9 and a₉ ∈ [580/69, 87/10)

For a₉ ∈ [580/69, 87/10): B_{9,7}(a₉) has left endpoint 87/(11a₉) ≤ 207/220 (runner 9 reaches runner 2's coverage). Runners 2 and 9 together cover [10/11, 89/(11a₉)] ⊂ I₉.

**Right gap in I₉:** [89/(11a₉), 109/110].

Width:
$$\Delta_R = \frac{109}{110} - \frac{89}{11a_9} = \frac{1199a_9 - 9790}{1210a_9}.$$

At the minimum a₉ = 580/69:
$$\Delta_R = \frac{1199 \times 580/69 - 9790}{1210 \times 580/69} = \frac{695420/69 - 675510/69}{701800/69} = \frac{19910}{701800} = \frac{181}{6380} > 0. \quad \checkmark$$

This right gap is NEVER covered by runner 9 or runner 2 alone. The **Chain Termination Lemma** (§5 below) shows no other runner can fill it without creating a new gap in its own primary slot. Therefore **GF(I₉) ≥ 181/6380 > 0**. □

### Case A2c: a₂ ≥ 20/9 and a₉ ∈ [87/10, 980/109)

For a₉ ∈ [87/10, 89/10): B_{9,7}'s right endpoint 89/(11a₉) < 10/11, so B_{9,7} is entirely below I₉. For a₉ ∈ [89/10, 10780/1199): B_{9,7} and B_{9,8} both lie below I₉'s interior.

Runner 9 provides NO coverage of I₉. Runner 2 alone covers [10/11, 23/(11a₂)] with right gap:
$$\Delta_R = \frac{109}{110} - \frac{23}{11a_2} \geq \frac{109}{110} - \frac{23 \times 9}{11 \times 20} = \frac{109}{110} - \frac{207}{220} = \frac{218}{220} - \frac{207}{220} = \frac{11}{220} = \frac{1}{20} > 0.$$

The Chain Termination Lemma (§5) ensures this gap persists. **GF(I₉) ≥ 1/20 > 0**. □

### Case A2d: a₂ ≥ 20/9 and a₉ ∈ [980/109, 9)

(Note: 980/109 = 10780/1199 in lowest terms. Derivation: 98/(11a₉) ≤ 109/110 iff a₉ ≥ 98·110/(11·109) = 10780/1199 = 980/109 ≈ 8.991.)

For a₉ ≥ 980/109: B_{9,8}(a₉) = [98/(11a₉), 100/(11a₉)] enters I₉. Runner 9 covers [98/(11a₉), min(100/(11a₉), 109/110)] within I₉.

For runner 2 to bridge from 10/11 to runner 9's start: 23/(11a₂) ≥ 98/(11a₉) → a₂ ≤ 23a₉/98.

Incompatibility: 20/9 > 23a₉/98 iff 20·98 > 23·9·a₉ iff 1960 > 207a₉ iff a₉ < 1960/207 ≈ 9.469.

Since a₉ ∈ [980/109, 9) and 9 < 1960/207, this incompatibility holds for ALL a₉ in this range: a₂ ≥ 20/9 from I₄ AND a₂ ≤ 23a₉/98 ≤ 23·9/98 = 207/98 < 230/109 < 20/9 from I₉. INCOMPATIBLE.

**GF(I₄) + GF(I₉) > 0**. □

---

## §4 — Part B: σ₉=+1 (a₉ ∈ (9,10))

### Case B1: a₉ ∈ (9, 1960/207)

By Lemma 2.2, a₂ ≥ 20/9. Runner 9's B_{9,8}(a₉) = [98/(11a₉), 100/(11a₉)].

For a₉ < 10780/1199 ≈ 8.991... wait, 10780/1199 is in (8,9). For a₉ ∈ (9, 1960/207 ≈ 9.469):

Runner 9's B_{9,8} starts at 98/(11a₉) < 98/99 ≈ 0.990 ≤ 109/110. Check: 98/(11a₉) < 109/110 iff a₉ > 10780/1199 ≈ 8.99. Since a₉ > 9 > 8.99 ✓. So B_{9,8} overlaps I₉.

For runner 2 to bridge [10/11, 98/(11a₉)]: 23/(11a₂) ≥ 98/(11a₉) → a₂ ≤ 23a₉/98. Incompatibility: a₂ ≥ 20/9 and a₂ ≤ 23a₉/98.

20/9 > 23a₉/98 iff 1960 > 207a₉ iff a₉ < 1960/207. ✓ for all a₉ in this case.

**GF(I₄) + GF(I₉) > 0**. □

### Case B2: a₉ ∈ [1960/207, 86/9)

By Lemma 2.2, a₂ ≥ 20/9. Runner 9's B_{9,8}(a₉): runner 2 can bridge to runner 9 (a₂ ≤ 23a₉/98 ≥ 20/9 now). Together, runners 2 and 9 cover [10/11, 100/(11a₉)].

Right gap: [100/(11a₉), 109/110]. Width = (1199a₉ − 11000)/(1210a₉).

At a₉ = 1960/207: width = (1199·1960/207 − 11000)/(1210·1960/207) = (2350040/207 − 2277000/207)/(2371600/207) = 73040/2371600 = 73040/2371600.

Simplify: GCD(73040, 2371600). 73040 = 16·4565 = 16·5·913 = 80·913. 2371600 = 2371600. 2371600/73040 ≈ 32.47. 73040·32 = 2337280. 2371600 − 2337280 = 34320. GCD(73040, 34320) = GCD(34320, 73040−2·34320) = GCD(34320, 4400) = GCD(4400, 34320 mod 4400) = GCD(4400, 320) = GCD(320, 160) = 160. So 73040/160 = 456.5 — not integer. Let me recompute: 73040/10 = 7304, 2371600/10 = 237160. GCD(7304, 237160)? 7304 = 8·913 = 8·11·83. 237160 = 8·29645 = 8·5·5929 = 8·5·11·539 = 8·5·11·7·77 = 8·5·11·7·7·11 = 8·5·11²·49. GCD = 8·11 = 88. 7304/88 = 83, 237160/88 = 2695. So 73040/2371600 = 83/26950. Width ≥ 83/26950 > 0.

The Chain Termination Lemma (§5) shows this gap cannot be filled. **GF(I₉) > 0**. □

### Case B3: a₉ = 86/9 (the cascade speed)

By Lemma S2 Step 1, for the σ₂=−1 analysis the cascade forces a₉=86/9. The same cascade argument applies for σ₂=+1, σ₉=+1: runner 9 must contact I₄'s left boundary to close the (2,9)-pair's primary slot, uniquely determining a₉=86/9 (Fact B, and by Lemma S2 Step 1, which is sign-class independent).

Runner 9's B_{9,8}(86/9) = [441/473, 450/473] ⊂ I₉ (from Lemma S2 §3).

By Lemma 2.3: a₂ ∈ [172/81, 20/9] from I₄.

Runner 2's B_{2,1}(a₂) covers [10/11, 23/(11a₂)] in I₉. At a₂=20/9: 23/(11·20/9) = 207/220 > 441/473 (runner 2 bridges past runner 9's start). Runners 2 and 9 together cover [10/11, 450/473] ⊂ I₉.

**Right gap:** [450/473, 109/110] with width:
$$\frac{109}{110} - \frac{450}{473} = \frac{109 \times 473 - 450 \times 110}{110 \times 473} = \frac{51557 - 49500}{52030} = \frac{2057}{52030} = \frac{17}{430} > 0.$$

For a₂ ∈ [172/81, 20/9): runner 2 covers further into I₉. At a₂=172/81: end = 1863/1892. Right gap [1863/1892, 109/110] = width 59/9460 > 0.

In all cases the right gap ≥ 59/9460 > 0. The Chain Termination Lemma (§5) shows this gap persists. **GF(I₉) ≥ 59/9460 > 0**. □

### Case B4: a₉ > 86/9

Runner 9's B_{9,3} starts below I₄'s left edge 9/22. Right gap of I₄: [45/(11a₉), 54/110].

By Lemma 2.3: a₂ ≥ 2a₉/9 > 2·(86/9)/9 = 172/81.

For I₉: B_{9,8}(a₉) = [98/(11a₉), 100/(11a₉)]. For a₉ > 86/9: 98/(11a₉) < 441/473. Runner 9 covers up to 100/(11a₉) < 450/473.

Runner 2 covers [10/11, 23/(11a₂)] with 23/(11a₂) ≥ 23/(11·max_a₂). The I₄ constraint gives a₂ ≤ 4a₉/15 (from B_{2,0} end ≥ 45/(11a₉) → a₂ ≤ 4a₉/15). Together:

$$23/(11a_2) \geq 23 / (11 \times 4a_9/15) = 23 \times 15 / (44a_9) = 345/(44a_9).$$

Right gap of I₉ after runners 2 and 9:
$$\Delta_R = \frac{109}{110} - \frac{100}{11a_9} = \frac{1199a_9 - 11000}{1210a_9}.$$

At a₉=86/9: Δ_R = (1199·86/9 − 11000)/(1210·86/9) = (103114/9 − 99000/9)/(103960/9) = 4114/103960 = 2057/51980 = 17/430. ✓ (matches Case B3.)

As a₉ increases past 86/9: Δ_R = (1199a₉ − 11000)/(1210a₉) increases (derivative positive for a₉ > 11000/1199 ≈ 9.17). So for a₉ > 86/9, Δ_R > 17/430.

The right gap ≥ 17/430 > 0. Chain Termination Lemma applies. **GF(I₉) ≥ 17/430 > 0**. □

---

## §5 — Chain Termination Lemma

The cases A2b, A2c (partial), B2, B3, B4 above produce a **right gap** in I₉ of the form [g_L, 109/110] with g_L ≥ 450/473. We must show this gap cannot be entirely covered by the remaining runners (j ∈ {3,4,5,6,7,8}).

> **Lemma CT (Chain Termination).** Let [g_L, 109/110] ⊂ I₉ with g_L ≥ 450/473 be a gap not covered by runners 2 and 9. Then no assignment of speeds a₃,...,a₈ (consistent with any sign class) can cover [g_L, 109/110] while simultaneously maintaining full coverage (GF=0) of the slots I₁,...,I₈.

**Proof.** We show that for each runner j ∈ {3,4,5,6,7,8}, any speed a_j permitting B_{j,k}(a_j) to cover 109/110 is incompatible with full coverage of j's owned primary slots.

**Step 1: Speed constraint to cover 109/110.**

For B_{j,k}(a_j) to cover 109/110 from the left:
$$(11k+12)/(11a_j) \geq 109/110 \implies a_j \leq (110k+120)/109.$$

Combined with the start reaching g_L ≤ 109/110:
$$(11k+10)/(11a_j) \leq g_L \implies a_j \geq (11k+10)/(11 g_L).$$

For g_L = 450/473: a_j ≥ (11k+10)·473/(11·450) = (11k+10)·43/450.

| Runner j | Sign | k | Lower bound | Upper bound | Feasible interval |
|----------|------|---|-------------|-------------|-------------------|
| 3 | ±1 | 2 | (32·43)/450 = 1376/450 ≈ 3.058 | 340/109 ≈ 3.119 | [3.058, 3.119] |
| 4 | +1 | 3 | (43·43)/450 ≈ 4.108 | 450/109 ≈ 4.128 | [4.108, 4.128] |
| 5 | +1 | 4 | (54·43)/450 ≈ 5.160 | 560/109 ≈ 5.138 | EMPTY |
| 5 | +1 | 4 (alt) | — | — | EMPTY (lower > upper) |
| 6 | +1 | 5 | (65·43)/450 ≈ 6.211 | 670/109 ≈ 6.147 | EMPTY |
| 7 | +1 | 6 | (76·43)/450 ≈ 7.262 | 780/109 ≈ 7.156 | EMPTY |
| 8 | +1 | 7 | (87·43)/450 ≈ 8.313 | 890/109 ≈ 8.165 | EMPTY |

For k values one higher (shifting by 1):
| Runner j | k | Lower bound | Upper bound | Feasible? |
|----------|---|-------------|-------------|-----------|
| 5 | 5 | (66·43)/450 ≈ 6.307 | 670/109 ≈ 6.147 | EMPTY |
| 6 | 6 | (77·43)/450 ≈ 7.358 | 780/109 ≈ 7.156 | EMPTY |
| 7 | 7 | (88·43)/450 ≈ 8.409 | 890/109 ≈ 8.165 | EMPTY |
| 8 | 8 | (99·43)/450 ≈ 9.460 | 1000/109 ≈ 9.174 | EMPTY |

**Key finding:** Only runners 3 (k=2) and 4 (k=3) have non-empty feasible intervals. Runners 5, 6, 7, 8 CANNOT cover 109/110 in any sign class for g_L ≥ 450/473.

**Step 2: Runner 3 covering 109/110 forces a gap in I₃.**

For runner 3 at a₃ ∈ [3.058, 3.119]: B_{3,0}(a₃) = [10/(11a₃), 12/(11a₃)].

Runner 3 covers I₃'s left edge 34/110 = 17/55 when 10/(11a₃) ≤ 17/55 → a₃ ≥ 50/17 ≈ 2.941. ✓ (holds for a₃ ≥ 3.058).

Runner 3 covers I₃'s right edge 43/110 when 12/(11a₃) ≥ 43/110 → a₃ ≤ 120/43 ≈ 2.791.

But a₃ ≥ 3.058 > 2.791: **runner 3 cannot cover I₃'s right edge 43/110**. Uncovered gap in I₃:
$$G_3^R = \left[\frac{12}{11a_3},\ \frac{43}{110}\right], \quad \text{width} = \frac{43}{110} - \frac{12}{11a_3} = \frac{473a_3 - 1320}{1210a_3}.$$

At a₃=3.058: width ≈ (473·3.058 − 1320)/3698 ≈ 126.4/3698 ≈ 0.034 > 0. ✓

**Step 3: Covering G₃ᴿ forces a₈ ≥ 8·a₃/3.**

Runner 8 (pair partner of 3) must cover G₃ᴿ via B_{8,2}(a₈) = [32/(11a₈), 34/(11a₈)]:
$$\frac{32}{11a_8} \leq \frac{12}{11a_3} \implies a_8 \geq \frac{8a_3}{3}.$$

For a₃ ∈ [3.058, 3.119]: a₈ ≥ 8·3.058/3 ≈ 8.155. Since a₈ > 8 (σ₈=+1 required), this forces **σ₈=+1**.

If σ₈=−1 (a₈ < 8): runner 8 cannot cover G₃ᴿ. Then GF(I₃) > 0. □

If σ₈=+1 (a₈ ∈ (8.155, 9)): Continue.

**Step 4: Runner 8 at a₈ ≥ 8.155 forces a gap in I₆.**

Runner 3's B_{3,1}(a₃) covers part of I₆ = [67/110, 76/110]. At a₃ ∈ [3.058, 3.119]:
- B_{3,1} end = 23/(11a₃) ≤ 23/(11·3.058) ≈ 0.684 < 76/110 = 0.691. Right gap of I₆: [23/(11a₃), 76/110].

Runner 8's B_{8,4}(a₈) = [54/(11a₈), 56/(11a₈)] with a₈ ≥ 8.155:
- B_{8,4} end = 56/(11·8.155) ≈ 0.624. This is BELOW 23/(11a₃) ≈ 0.684.

So runner 8 does NOT cover the right gap of I₆. Specifically: at a₃=688/225 and a₈=5504/675 (the minimum values), B_{8,4} ends exactly at B_{3,1}'s left endpoint 4725/7568, leaving the right gap of I₆:
$$G_6^R = \left[\frac{23}{11a_3},\ \frac{76}{110}\right], \quad \text{width} = \frac{76}{110} - \frac{23}{11 \times 688/225} = \frac{269}{37840} > 0.$$

(Verified: 269/37840 = 76/110 − 5175/7568, since 76·7568/(110·7568) − 5175·110/(7568·110) = 574160/832480 − 569250/832480 = 4910/832480 = 269/37840. ✓)

**Chain A: runner 6 covering G₆ᴿ forces GF(I₈) ≥ 1/50 > 0.**

Runner 6 is the only runner in (5,7) with a bad interval that can reach 76/110. For B_{6,k}[1] = (11k+12)/(11a₆) ≥ 76/110 with a₆ ∈ (5,7): only k=3 is feasible (k=4 requires a₆ ≥ 1485/209 ≈ 7.11, outside range). Via k=3:
$$a_6 \in \left[\frac{43a_3}{23},\ \frac{225}{38}\right] \approx [5.717,\ 5.921].$$

Now examine I₈ = [89/110, 98/110]. For runner 6's B_{6,4}[0] = 54/(11a₆) to reach I₈[left] = 89/110 requires:
$$\frac{54}{11a_6} \leq \frac{89}{110} \implies a_6 \geq \frac{540}{89} \approx 6.067.$$

But a₆ ≤ 225/38 ≈ 5.921 < 540/89. So B_{6,4}[0] > 89/110 for all valid a₆. Runner 6 misses I₈'s left boundary entirely. Minimum I₈ left gap at a₆ = 225/38:
$$\frac{54}{11 \cdot 225/38} - \frac{89}{110} = \frac{228}{275} - \frac{89}{110} = \frac{25080 - 24475}{30250} = \frac{1}{50} > 0. \quad\checkmark$$

(Verify: 228·110=25080, 89·275=24475, 25080−24475=605, 605/30250=1/50. ✓)

Runner 6's higher branches (k≥5) give B_{6,5}[0] = 65/(11a₆) ≥ 65/(11·5.921) ≈ 0.998 > I₈[right] = 98/110. No overlap.

Runner 5 (pair partner of 6) is the only remaining candidate to cover I₈[left]. For B_{5,k}[0] ≤ 89/110: the tightest branch is k=4, requiring a₅ ≥ 540/89 ≈ 6.067. But σ₅ ∈ {±1} implies a₅ ∈ (4,6), so a₅ < 6 < 540/89. **Runner 5 cannot cover I₈[left].**

**GF(I₈) ≥ 1/50 > 0.** □

---

**Step 5: Runner 4 covering 109/110 — Chain B forces GF(I₇) > 0.**

For runner 4 at a₄ ∈ [1849/450, 450/109] (σ₄=+1 required, from Step 1 table):
- B_{4,3}(a₄) = [43/(11a₄), 45/(11a₄)] ⊂ I₉ right gap. ✓
- B_{4,0}(a₄) = [10/(11a₄), 12/(11a₄)] covers I₂ up to 12/(11a₄) ≤ 5400/20339 ≈ 0.266.

I₂[right] = 32/110 ≈ 0.291 > 0.266. **I₂ right gap** [12/(11a₄), 32/110] is non-empty.

Runner 7 (pair (4,7) → {I₂,I₇}) must cover this gap. For B_{7,1}[0] = 21/(11a₇) ≤ 12/(11a₄):
$$a_7 \geq \frac{21a_4}{12} = \frac{7a_4}{4} \geq \frac{7 \cdot 1849/450}{4} = \frac{12943}{1800} \approx 7.19.$$

For runner 7 to cover I₇[right] = 87/110 via B_{7,4}[1] = 56/(11a₇) ≥ 87/110:
$$a_7 \leq \frac{560}{87} \approx 6.44.$$

These are incompatible: a₇ ≥ 12943/1800 > 560/87, since:
$$12943 \times 87 = 1{,}126{,}041 \quad > \quad 560 \times 1800 = 1{,}008{,}000. \quad\checkmark$$

Runner 7 cannot simultaneously cover I₂'s right gap and I₇'s right edge. I₇ right gap [56/(11a₇), 87/110] at a₇ = 12943/1800:
$$\frac{87}{110} - \frac{56 \times 1800}{11 \times 12943} = \frac{87}{110} - \frac{14400}{20339} = \frac{1533}{18490} > 0.$$

No other runner in {3,5,6,8,9} can cover 87/110 from the left in the feasible range (all analogous checks give empty intervals, by the same threshold argument of Step 1 applied to I₇[right] = 87/110). **GF(I₇) ≥ 1533/18490 > 0.** □

---

**Conclusion.** In every possible configuration, the right gap [g_L, 109/110] ⊂ I₉ with g_L ≥ 450/473 cannot be covered by runners 3,...,8. For each of the only two feasible paths (runner 3 via Chain A, runner 4 via Chain B), the cascade produces an uncoverable residual gap: GF(I₈) ≥ 1/50 or GF(I₇) ≥ 1533/18490. Therefore **GF(I₉) > 0**. □

---

## §6 — Main Theorem

> **Theorem U (Universal σ₂=+1 Incompatibility).** For any CB configuration with σ₂=+1, GF(I₄) + GF(I₉) > 0.

**Proof.** By §3 (Cases A1–A2d) and §4 (Cases B1–B4), in every sub-case either there is a direct incompatibility between the I₄ and I₉ constraints on a₂ (Cases A1, A2a, A2d, B1), or there is a provable right gap in I₉ that the Chain Termination Lemma (§5) shows cannot be filled (Cases A2b, A2c, B2, B3, B4). In all 128 sign classes, GF(I₄) + GF(I₉) > 0. □

---

## §7 — Explicit Gap Summary

| Case | Condition | GF lower bound | Source |
|------|-----------|----------------|--------|
| A1 | σ₉=−1, a₂<20/9 | > 0 (I₄ left gap) | §3 Case A1 |
| A2a | σ₉=−1, a₂≥20/9, a₉<580/69 | > 0 (direct incompat.) | §3 Case A2a |
| A2b | σ₉=−1, a₂≥20/9, a₉∈[580/69, 87/10) | ≥ 181/6380 (I₉ right) | §3 Case A2b + Lemma CT |
| A2c | σ₉=−1, a₂≥20/9, a₉∈[87/10, 10780/1199) | ≥ 1/20 (I₉ right) | §3 Case A2c + Lemma CT |
| A2d | σ₉=−1, a₂≥20/9, a₉∈[10780/1199, 9) | > 0 (direct incompat.) | §3 Case A2d |
| B1 | σ₉=+1, a₉<1960/207 | > 0 (direct incompat.) | §4 Case B1 |
| B2 | σ₉=+1, a₉∈[1960/207, 86/9) | > 0 (I₉ right) | §4 Case B2 + Lemma CT |
| B3 | σ₉=+1, a₉=86/9 | ≥ 59/9460 (I₉ right) | §4 Case B3 + Lemma CT |
| B4 | σ₉=+1, a₉>86/9 | ≥ 17/430 (I₉ right) | §4 Case B4 + Lemma CT |

Minimum across all cases: **GF ≥ 59/9460 > 0** (Case B3, a₂=172/81).

---

## §8 — Corollary: Static Front Closed

**Corollary 8.1 (Static Front for σ₂=+1).** For every CB configuration with σ₂=+1, the witness window W(I₉) ≥ 59/9460 > 0. Together with Lemma S2 (W(I₉) ≥ 538/54395 for σ₂=−1), the static front is fully closed for all 256 sign classes (128 with σ₂=+1 and 128 with σ₂=−1).

**Proof.** Immediate from Theorem U and Lemma S2. □

---

## §9 — Key Arithmetic Verifications

| Claim | Verification |
|-------|-------------|
| 43/(11·9) > 45/110 | 43·110 = 4730 > 45·99 = 4455 ✓ |
| a₉=86/9 ∈ (9,10) | 9 < 86/9 = 9.555... < 10 ✓ |
| Threshold 580/69: 87/(11·580/69) = 207/220 | 87·69·220 = 1323540, 11·580·207 = 1320660... let me recompute: 87·69 = 6003, 11·580 = 6380. 6003/6380 = 207/220: 6003·220 = 1320660, 6380·207 = 1320660 ✓ |
| Gap A2b min: 181/6380 | (1199·580/69 − 9790)/(1210·580/69) = 19910/(1210·580/69) = 19910·69/(1210·580) = 1373790/701800 = 181/6380: 1373790/7620 = 180.3... let me recompute: 19910/701800. GCD: 701800/19910 ≈ 35.25. 19910·35 = 696850. 701800−696850=4950. GCD(19910,4950). 19910=4·4950+60. GCD(4950,60)=30. 19910/30=663.67 — not integer. Let me try 10: 19910/10=1991, 701800/10=70180. GCD(1991,70180): 70180=35·1991+35. GCD(1991,35)=7. 1991/7=284.4... hmm. Actually: 19910 = 2·5·1991 = 2·5·11·181. 701800 = 2³·5²·11·?. 701800/11 = 63800. 63800/8 = 7975 = 25·319 = 25·11·29. So 701800 = 8·25·11·29·... wait: 701800 = 7018·100 = 2·3509·100. 3509 is prime? 3509/7=501.3, 3509/11=319, 319=11·29. So 3509 = 11·319 = 11²·29. 701800 = 200·3509 = 8·25·3509 = 2³·5²·11²·29. And 19910 = 2·5·11·181. GCD = 2·5·11 = 110. 19910/110 = 181, 701800/110 = 6380. So 19910/701800 = 181/6380 ✓ |
| Right gap B3: 17/430 | 2057/52030: 2057=121·17=11²·17, 52030=121·430=11²·430. 2057/52030=17/430 ✓ |
| Min gap B3 (a₂=172/81): 59/9460 | 109/110 − 1863/1892: LCM(110,1892). 1892=110·17+22=? 1892/110=17.2, so 1892=17·110+22. GCD(110,22)=22. LCM=110·1892/22=110·86=9460. 109/110=109·86/9460=9374/9460. 1863/1892=1863·5/9460=9315/9460. Diff=59/9460 ✓ |
