# Lemma S2: Analytic Proof (v2)

**Date:** 2026-03-24
**Status:** PROVED — canonical `sigma_2 = -1` static theorem. Every inequality is a rational arithmetic check.
**Depends on:** `lrc_n11_lemma_s1_runner2_elimination_v1.md`, slot/bad-interval definitions (v14 paper §10.16).
**Canonical role:** Imported into `lrc_n11_static_core_theorem_v1.md`.

---

## Statement

> **Lemma S2.** In every σ₂=−1 sign class, the unclaimed slot I₉ = [100/110, 109/110] retains a positive witness width. The minimum is 538/54395 > 0.

---

## 1. Setup

**Slots:** I_k = [(11k+1)/110, (11k+10)/110]. Key slots:
```
I₄ = [45/110, 54/110],   I₅ = [56/110, 65/110],   I₉ = [100/110, 109/110]
```

**Bad interval:** B_j(a) = [(11j+10)/(11a), (11j+12)/(11a)].

**Pair (2,9) → {I₄, I₅}:** In σ₂=−1, runner 2 has a₂∈[25/14, 24/13] and closes I₅'s left boundary via j=0. Runner 9 must therefore close I₄.

**Cascade constraint:** A speed a_p is *cascade-forced* for runner p iff B_j(a_p) contacts a designated slot boundary AND a_p ∈ (p−1, p+1).

---

## 2. Step 1 — The Only Valid a₉ is 86/9

**Claim:** The only a₉ ∈ (9, 10) closing I₄'s left boundary is a₉ = 86/9.

**Proof.** B_{9,k}[0] = 45/110 (I₄ left) iff a₉ = (110k+100)/45. For a₉ ∈ (9,10): unique solution k=3, giving **a₉ = 430/45 = 86/9**.

I₄ right boundary (54/110): a₉ = (110k+120)/54. For k=3: 25/3 ≈ 8.33 ∉ (9,10). For k=4: 280/27 ≈ 10.37 ∉ (9,10). No solution.

I₅ left boundary (56/110): a₉ = (110k+100)/56. For k=4: 135/14 ≈ 9.64. This would cover I₅ redundantly — runner 2 already closes I₅ left — leaving I₄ uncovered, so W(I₄) > 0 and the class is infeasible at the primary slot level.

For all other a₉ ∈ (9, 10): no branch k contacts any boundary of I₄ or I₅ (no solution to either equation in (9,10) besides those listed), so pair (2,9) fails to cover I₄ → W(I₄) > 0 → infeasible.

**Conclusion:** The only sign class requiring I₉ analysis has a₉ = 86/9. □

---

## 3. Step 2 — Runner 9's Bad Interval in I₉

For a₉ = 86/9:
```
B_{9,8}(86/9) = [(11·8+10)/(11·86/9), (11·8+12)/(11·86/9)]
              = [98·9/(11·86), 100·9/(11·86)]
              = [882/946, 900/946]
              = [441/473, 450/473]
```

Both endpoints lie inside I₉ (441/473 > 100/110 and 450/473 < 109/110, verified below), so runner 9 covers **[441/473, 450/473] ⊂ I₉**.

Checks: 441·110 = 48510 > 100·473 = 47300 ✓ (441/473 > 100/110).
        450·110 = 49500 < 109·473 = 51557 ✓ (450/473 < 109/110).

---

## 4. Step 3 — Cascade-Forced Outer Runner Speeds and Their I₉ Intervals

The outer runners come in complementary pairs. For each pair, σ determines which boundary is closed, and the cascade-forced speed must lie in (p−1, p+1).

**Pairs and cascade-forced speeds:**

| Runner p | σ | Closes | Boundary | a_p formula | j | a_p | In (p−1,p+1)? |
|----------|---|--------|----------|-------------|---|-----|---------------|
| 3 | +1 | I₃ left | 34/110 | (110j+100)/34 | 0 | **50/17** | ✓ 2.94∈(2,4) |
| 3 | −1 | I₆ left | 67/110 | (110j+120)/76 | 1 | **115/38** | ✓ 3.03∈(2,4) |
| 4 | +1 | I₂ left | 23/110 | (110j+100)/23 | 0 | **100/23** | ✓ 4.35∈(3,5) |
| 4 | −1 | I₇ right | 87/110 | (110j+120)/87 | 2 | **340/87** | ✓ 3.91∈(3,5) |
| 5 | −1 | I₈ right | 98/110 | (110j+120)/98 | 3 | **225/49** | ✓ 4.59∈(4,6) |
| 5 | +1 | I₁ left | 12/110 | (110j+100)/12 | — | **None** | ✗ no j gives (4,6) |
| 6 | +1 | I₈ right | 98/110 | (110j+120)/98 | 4 | **40/7** | ✓ 5.71∈(5,7) |
| 6 | −1 | I₁ left | 12/110 | (110j+100)/12 | — | **None** | ✗ |
| 7 | +1 | I₇ right | 87/110 | (110j+120)/87 | 4 | **560/87** | ✓ 6.44∈(6,8) |
| 7 | −1 | I₂ left | 23/110 | (110j+100)/23 | — | **None** | ✗ no j gives (6,8) |
| 8 | +1 | I₆ right | 76/110 | (110j+120)/76 | 4 | **140/19** | ✓ 7.37∈(7,9) |
| 8 | −1 | I₃ left | 34/110 | (110j+100)/34 | — | **None** | ✗ 160/17≈9.41∉(7,9) |
| 10 | — | (free) | — | — | — | **10** | safe throughout I₉ |

**Structural consequence:** In σ₃=−1, runner 8 has no cascade-forced speed (160/17 > 9, outside (7,9)). Runner 8 is present only when σ₃=+1.

**Bad intervals of each cascade-forced runner in I₉:**

For a runner to have a bad interval overlapping I₉=[100/110, 109/110], branch j' must satisfy:
```
(11j'+10)/(11a_p) < 109/110   and   (11j'+12)/(11a_p) > 100/110
```

| Runner | a_p | j' | B[0] | B[1] | eff. ∩ I₉ |
|--------|-----|-----|------|------|-----------|
| p=3, σ=+1 | 50/17 | 2 | **272/275** | 289/275 > 1 | [272/275, 109/110] |
| p=3, σ=−1 | 115/38 | 2 | **1216/1265** | 1292/1265 > 1 | [1216/1265, 109/110] |
| p=4, σ=+1 | 100/23 | 3 | 10/11 | **207/220** | [10/11, 207/220] |
| p=4, σ=−1 | 340/87 | — | >1 | >1 | **∅** |
| p=5, σ=−1 | 225/49 | — | — | — | **∅** |
| p=6, σ=+1 | 40/7 | — | — | — | **∅** |
| p=7, σ=+1 | 560/87 | 5 | 1131/1232 | **5829/6160** | [1131/1232, 5829/6160] |
| p=8, σ=+1 | 140/19 | 6 | **361/385** | **741/770** | [361/385, 741/770] |
| p=10 | 10 | — | — | — | **∅** |

**No-overlap proofs (j' existence contradictions):**

- **p=4, a₄=340/87:** j'=3 gives B_3[0] = 43·87/3740 = 3741/3740 > 1. No overlap with I₉ ⊂ [0,1]. □
- **p=5, a₅=225/49:** j' must satisfy 316/77 < j' < 366/77, i.e. 4.104 < j' < 4.753. No integer. □
- **p=6, a₆=40/7:** same bounds 316/77 < j' < 366/77 (same slot I₈ constraint). No integer. □
- **p=7, σ=−1 (None), p=8, σ=−1 (None), p=5, σ=+1 (None):** excluded by cascade range constraint. □

---

## 5. Step 4 — The Four Sub-Cases

The gap structure depends on σ₃ (determines runner 8's presence) and σ₄ (determines runners 4 and 7's presence). Signs σ₅, σ₁₀ have no effect (runners 5, 6 have no I₉ bad intervals; runner 10 is safe).

---

### Case A: σ₄ = −1 (runners 4 and 7 absent)

When σ₄=−1, runners 4 and 7 have either no I₉ overlap (a₄=340/87) or are None. The only runners with I₉ bad intervals in [10/11, 441/473) are absent. Since runner 9's interval starts at 441/473 > 10/11 = I₉[0], the left portion of I₉ is uncovered:

```
Left gap: (10/11, 441/473)
Width = 441/473 − 10/11 = (441·11 − 10·473)/(11·473)
      = (4851 − 4730)/5203 = 121/5203 = 1/43 > 0
```

Verification: 441·11 = 4851, 10·473 = 4730. ✓

**W(I₉) ≥ 1/43 > 0 for all σ₄=−1 sign classes.** □

---

### Case B: σ₃=+1, σ₄=+1 (runners 4, 7, 8 all present)

**Runners with I₉ bad intervals:** {p4(100/23), p7(560/87), p8(140/19), p9(86/9), p3(50/17)}.

**Left coverage chain** (show [10/11, 741/770] is fully covered):

| Runner | eff. interval in I₉ |
|--------|---------------------|
| p4 | [**10/11**, 207/220] |
| p7 | [1131/1232, 5829/6160] |
| p9 | [441/473, 450/473] |
| p8 | [361/385, 741/770] |

Contiguity checks (each runner's left endpoint ≤ previous runner's right endpoint):
- **p4 starts at I₉[0]:** B_3(100/23)[0] = 989/1100 < 10/11 since 989·11=10879 < 100·1100=110000. So effective start = 10/11. ✓
- **p7 starts before p4 ends:** 1131/1232 < 207/220 since 1131·220=248820 < 1232·207=255024. ✓
- **p9 starts before p7 ends:** 441/473 < 5829/6160 since 441·6160=2716560 < 473·5829=2757117. ✓
- **p8 starts before p9 ends:** 361/385 < 450/473 since 361·473=170753 < 385·450=173250. ✓
- **p8 ends at 741/770.** Combined left coverage: [10/11, 741/770]. ✓

**Right coverage:** runner 3 (a₃=50/17) covers [272/275, 109/110].

**Gap:**
```
G₁ = (741/770, 272/275)
Width = 272/275 − 741/770 = (272·770 − 741·275)/(275·770)
      = (209440 − 203775)/211750 = 5665/211750 = 103/3850 > 0
```

**Verify runner 3 starts above left coverage end:**
272/275 > 741/770 since 272·770=209440 > 741·275=203775. ✓

**Verify no runner covers G₁=(741/770, 272/275)≈(0.962, 0.989):**
All remaining runners (p5, p6, p10) have no I₉ bad intervals (proved in §4). Runner p8 ends at 741/770 = G₁[0] (excluded, open interval). Runner p9 ends at 450/473 < 741/770 (check: 450·770=346500 < 473·741=350493 ✓). □

**W(I₉) = 103/3850 > 0.** □

---

### Case C: σ₃=−1, σ₄=+1 (runners 4, 7 present; runner 8 absent)

**Runners with I₉ bad intervals:** {p4(100/23), p7(560/87), p9(86/9), p3(115/38)}.

**Left coverage chain** (show [10/11, 450/473] is fully covered):

| Runner | eff. interval in I₉ |
|--------|---------------------|
| p4 | [**10/11**, 207/220] |
| p7 | [1131/1232, 5829/6160] |
| p9 | [441/473, 450/473] |

Contiguity checks (same as Case B for p4→p7→p9):
- p4 starts at I₉[0] ✓ (same check)
- p7 starts before p4 ends ✓ (same check)
- p9 starts before p7 ends ✓ (same check)
- p9 ends at 450/473. Combined left coverage: [10/11, 450/473]. ✓

**Right coverage:** runner 3 (a₃=115/38) covers [1216/1265, 109/110].

**Gap:**
```
G₂ = (450/473, 1216/1265)
Width = 1216/1265 − 450/473 = (1216·473 − 450·1265)/(1265·473)
      = (575168 − 569250)/598345 = 5918/598345 = 538/54395 > 0
```

**Verify runner 3 starts above left coverage end:**
1216/1265 > 450/473 since 1216·473=575168 > 1265·450=569250. ✓

**Verify no runner covers G₂=(450/473, 1216/1265)≈(0.951, 0.961):**
- p4 ends at 207/220 < 450/473: 207·473=97911 < 220·450=99000. ✓
- p7 ends at 5829/6160 < 450/473: 5829·473=2757117 < 6160·450=2772000. ✓
- p9 ends at 450/473 = G₂[0] (excluded, open interval). ✓
- p5, p6, p10: no I₉ overlap. ✓
- p8: absent (σ₃=−1). ✓

**W(I₉) = 538/54395 > 0.** □

---

## 6. Summary

| σ₃ | σ₄ | Uncovered region(s) in I₉ | W(I₉) |
|----|-----|---------------------------|--------|
| +1 | +1 | G₁ = (741/770, 272/275) | **103/3850** |
| +1 | −1 | (10/11, 441/473) and G₁ | **8279/165550** |
| −1 | +1 | G₂ = (450/473, 1216/1265) | **538/54395** ← minimum |
| −1 | −1 | (10/11, 441/473) and G₂ | **1803/54395** |

Signs σ₅ and σ₁₀ have no effect on I₉ coverage. Minimum W(I₉) = **538/54395** > 0.

---

## 7. Conclusion

In every σ₂=−1 sign class:

1. If a₉ ≠ 86/9: pair (2,9) fails to cover I₄ → W(I₄)>0 → class infeasible at primary level.
2. If a₉ = 86/9 and σ₄=−1: left gap (10/11, 441/473) has width 1/43 > 0 → W(I₉)>0.
3. If a₉ = 86/9 and σ₃=+1, σ₄=+1: gap G₁ has width 103/3850 > 0 → W(I₉)>0.
4. If a₉ = 86/9 and σ₃=−1, σ₄=+1: gap G₂ has width 538/54395 > 0 → W(I₉)>0.

In all cases no configuration of outer runners simultaneously covers all of I₁,...,I₉. A valid isolation witness exists in every σ₂=−1 sign class. □

---

## 8. Proof Status

Every step is a rational arithmetic check:

| Component | Verification type |
|-----------|------------------|
| Unique a₉=86/9 | Solve (110k+100)/45∈(9,10): unique k=3 |
| Cascade speeds table | Solve boundary equations + check range (p−1,p+1) |
| No-overlap proofs (p4−,p5,p6) | j'-bound contradiction or B[0]>1 |
| Runner 8 absent in σ₃=−1 | 160/17 > 9, outside (7,9) |
| Contiguity chain (Case B and C) | 3 rational inequalities each |
| Gap widths (G₁, G₂) | Direct subtraction of exact fractions |
| No runner covers G₁ or G₂ | Endpoint inequalities, 2 checks each |
| Left gap in Case A | Width = 1/43, direct subtraction |

**Lemma S2: PROVED.** No floating-point arithmetic used.
