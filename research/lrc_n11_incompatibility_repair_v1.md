# ERR-B-01/02 Repair: Missed Candidates in Lemmas 3.1 and 3.2

**Date:** 2026-04-19
**Status:** REPAIR DRAFT — S2/S3 (case analyses required; theorem believed true, proof currently leaks)
**Scope:** `lrc_n11_incompatibility_v1.md` Lemma 3.1 Step 2 (ERR-B-01) and Lemma 3.2 Step 1 (ERR-B-02).

---

## Background

The incompatibility file proves Theorem 4.1: in the ++------ sign class with $a_9=25/3$, $a_6=40/7$, closing both $I_4$ and $I_9$ simultaneously is impossible. The proof reduces to:
- Lemma 3.1: GF$(I_4)=0 \Rightarrow a_2 \geq 20/9$.
- Lemma 3.2: GF$(I_9)=0 \Rightarrow a_2 \leq 575/261$.
- Incompatibility: $20/9 > 575/261$ (gap $5/261$).

The gaps found in the whole-project review (2026-04-18):
- **ERR-B-01** (Lemma 3.1 Step 2): runner 8 at $k=2$ covering $45/110$ was not analysed.
- **ERR-B-02** (Lemma 3.2 Step 1): runners 5, 7, 8 at $k\geq 3$ covering $10/11$ were not fully analysed.

This document provides the case analyses and states where further work is needed.

---

## Bad-interval formula (reminder)

$$B_{j,k} = \left[\frac{11k+10}{11a_j},\; \frac{11k+12}{11a_j}\right], \quad k = 0,1,2,\ldots$$

Key reference points:
- $J_4$ left boundary: $45/110 = 9/22$
- $J_9$ left boundary: $10/11$
- Baton-pass certificate: $t^* = 69/275 \approx 0.2509$ in $I_2$ (runner 9's $I_2$-coverage ends exactly at $t^*$)

---

## ERR-B-01 Repair: Lemma 3.1 Step 2, Runner 8 at $k=2$

### The missed case

For $B_{8,2}$ to cover $45/110$:
$$\frac{32}{11a_8} \leq \frac{9}{22} \leq \frac{34}{11a_8}
\iff a_8 \in \left[\frac{64}{9},\, \frac{748}{99}\right] \approx [7.111,\, 7.556].$$
This is compatible with the ++------ sign constraint $a_8 < 8$. The paper's Step 2 ruled out runner 7 at $k=2$ (since $a_7 < 7 < 64/9$) but did not check runner 8. **Runner 8 at $k=2$ is a genuine missed candidate.**

### Why the simple "GF(slot)$>0$" pattern does not directly apply

For runners 5 and 7 in the existing proof:
- Runner 5 covering $J_4$ via $B_{5,1}$ shifts runner 5 far from its $I_2$-covering position, exposing $t^*=69/275$ (Step 3).
- Runner 7 covering $J_4$ via $B_{7,1}$ leaves $I_7$ uncovered (Step 4).

For runner 8 at $a_8 \in [64/9, 748/99]$:
- $I_8 = [89/110, 98/110]$ is already covered by runner 6 (fixed at $a_6=40/7$, covering $I_8$). So "runner 8 leaves $I_8$ uncovered" does not apply.
- $I_7 = [78/110, 87/110]$: runner 8's $B_{8,4}$ covers $I_7$'s left edge only for $a_8 \leq 280/39 \approx 7.179$. For $a_8 \in (7.179, 7.556)$, runner 8 does not cover $I_7$. But runner 7 at $a_7 \in [990/143, 7) \approx [6.92, 7)$ covers $I_7$ independently.

So runner 8's shift to $a_8 \in [7.111, 7.556]$ does not obviously leave any single slot uncovered by all other runners.

### Correct argument: baton-pass constraint on $t^*$

**Key lemma (Runner 8 at $k=2$ blocks $t^*$ in $I_2$).**

*Claim.* When $a_8 \in [64/9, 748/99]$, runner 8's $B_{8,1}$ does not cover $t^* = 69/275$.

*Proof.* $B_{8,1}$ starts at $21/(11a_8)$. For $a_8 \leq 748/99$:
$$\frac{21}{11 \cdot 748/99} = \frac{21 \times 99}{11 \times 748} = \frac{2079}{8228} \approx 0.2527 > \frac{69}{275} \approx 0.2509.$$
So $B_{8,1}$ starts strictly after $t^*$. Runner 8 cannot cover $t^*$ while in the $k=2$ regime. $\square$

**Key lemma (Runner 2 at $J_9$-covering speed cannot cover $t^*$).**

*Claim.* If $a_2 \leq 575/261$ (the $J_9$-coverage constraint from Lemma 3.2), then runner 2's $B_{2,0}$ does not cover $t^*$.

*Proof.* $B_{2,0}$ starts at $10/(11a_2) \geq 10/(11 \times 575/261) = 10 \times 261/(11 \times 575) = 2610/6325 \approx 0.413 \gg t^* \approx 0.251$. $\square$

**Consequence.** When runner 8 covers $J_4$ ($a_8 \in [64/9, 748/99]$) AND runner 2 covers $J_9$ ($a_2 \leq 575/261$), neither runner covers $t^* = 69/275$ in $I_2$. If no other runner covers $t^*$, the baton-pass certificate gives GF$(I_2)>0$.

### Who can cover $t^*$?

Coverage of $t^* = 69/275$ requires $B_{j,k}$'s start $\leq 69/275 \leq$ end:
$$a_j \in \left[\frac{(11k+10) \times 25}{69},\; \frac{(11k+12) \times 25}{69}\right].$$
For $k=0$: $a_j \in [250/69, 300/69] \approx [3.62, 4.35]$.
For $k \geq 1$: $a_j \geq 775/69 \approx 11.2$, exceeding all runner bounds in the ++------ class.

So **only runners with $a_j \in [3.62, 4.35]$ via $k=0$** can cover $t^*$. In the ++------ class with the given constraints:
- Runner 2 at $a_2 \leq 575/261 \approx 2.2$: excluded ($< 3.62$).
- Runner 3 ($a_3 < 3$): excluded.
- Runner 4 ($a_4 < 4$): **candidate** at $a_4 \in [3.62, 4)$.
- Runner 5 ($a_5 < 5$): **candidate** at $a_5 \in [3.62, 4.35]$.
- Runners 6, 7, 8, 9: outside range (either fixed or speed constraints exclude them).

### Sub-case analysis for $t^*$-covering runners

**Sub-case D1: Runner 4 at $a_4 \in [3.62, 4)$ covers $t^*$.**

At $a_4 \approx 3.8$: $B_{4,0} = [10/(11 \times 3.8), 12/(11 \times 3.8)] \approx [0.239, 0.287]$. This covers $t^* \approx 0.251$. ✓

Now check $I_9$. Runner 4's $B_{4,k}$ can cover $J_9 = [10/11, 261/275]$ only for:
$$\frac{11k+10}{11a_4} \leq \frac{10}{11} \implies a_4 \geq 11k+10 \text{ (for each } k).$$
For $k=0$: $a_4 \geq 10$. Impossible ($a_4 < 4$). For all $k$: $a_4 \geq (11k+10)/10 \geq 1$; end condition: $a_4 \leq (11k+12)/10$. For $k=0$: $[1, 1.2]$; for $k=1$: $[2.1, 2.3]$; for $k=2$: $[3.2, 3.4]$; for $k=3$: $[4.3, 4.5]$ — all outside $[3.62, 4)$.

So runner 4 at $a_4 \in [3.62, 4)$ **cannot cover $J_9$**. Runner 2 must still cover $J_9$ (constraint $a_2 \leq 575/261$ applies). ✓

Runner 4 covering $t^*$ does not interfere with the $I_9$ constraint. However, runner 4 must also not be committed to covering some other critical slot it uniquely covers. In particular: does runner 4 at $a_4 \in [3.62, 4)$ leave any slot without a coverer?

Runner 4's natural slot in the ++------ class requires checking which slot runner 4 at its "natural" speed ($a_4 \to 4^-$) covers. At $a_4 = 4^-$: $B_{4,0} \approx [0.227, 0.273]$ (in $I_2$), $B_{4,1} \approx [0.477, 0.523]$ (between $I_4$ and $I_5$), $B_{4,2} \approx [0.727, 0.773]$ (in or near $I_7$). None of these appear to be the sole coverer of any slot given the other runners present.

**Status of Sub-case D1:** No immediate contradiction found. The configuration $a_8 \in [64/9, 748/99]$, $a_2 \leq 575/261$, $a_4 \in [3.62, 4)$ is not obviously ruled out by the current argument. **A complete Sub-case D1 analysis requires checking whether some slot in $\{I_2, I_3, I_4, I_5, I_6, I_7\}$ is necessarily left uncovered at the corresponding runner speeds. This is not yet resolved and is the primary remaining gap for ERR-B-01.**

**Sub-case D2: Runner 5 at $a_5 \in [3.62, 4.35]$ covers $t^*$.**

At $a_5 \approx 4.3$: $B_{5,0} \approx [0.212, 0.254]$. This covers $t^* \approx 0.251$. ✓

But runner 5 at $a_5 \approx 4.3$ is close to the regime where runner 5 covers $J_4$ via $B_{5,1}$ (which requires $a_5 \geq 42/9 \approx 4.67$). At $a_5 = 4.3 < 4.67$, runner 5 does NOT cover $J_4$ via $B_{5,1}$ — so no conflict with the runner-8 coverage of $J_4$.

Does runner 5 at $a_5 \in [3.62, 4.35]$ leave any slot uncovered? Runner 5's natural role at higher speed ($a_5 \to 5^-$) is covering $I_2$ via $B_{5,0}$ and the baton-pass role at $a_5 \approx 4.4$. At lower speed $a_5 \in [3.62, 4.35]$, runner 5 is covering the left part of $I_2$ via $B_{5,0}$ (which ends at $12/(11a_5) \leq 12/(11 \times 3.62) \approx 0.301$, covering $I_2$'s right end $32/110 \approx 0.291$).

**Status of Sub-case D2:** Similar status to D1. Not resolved without further analysis.

### ERR-B-01 Provisional Repair Conclusion

**Lemma 3.1 as currently stated is incomplete.** The correct version requires Step 2 to include:

> *Runner 8 at $k=2$ ($a_8 \in [64/9, 748/99]$):* Runner 8 can cover $45/110$ via $B_{8,2}$. In this sub-case, the constraint $a_2 \geq 20/9$ does not directly follow. However, neither runner 8 nor runner 2 (at the $J_9$-covering speed $a_2 \leq 575/261$) can cover the baton-pass point $t^* = 69/275$ in $I_2$. If neither runner 4 nor runner 5 is available to cover $t^*$ (due to their own slot-coverage obligations), then GF$(I_2) > 0$ and the theorem holds. The full case analysis verifying that at least one of $\{I_2, I_4, I_9\}$ must have GF $> 0$ in the runner-8 sub-case is **not yet complete**.

**Salvage classification (revised): S2.** The proof needs a genuinely new case analysis, not a simple addendum.

---

## ERR-B-02 Repair: Lemma 3.2 Step 1, Runners 5/7/8 at $k \geq 3$

### The missed cases

For $B_{j,k}$ to cover the left boundary $10/11$ of $J_9$:
$$a_j \in \left[\frac{(11k+10)}{10},\; \frac{(11k+12)}{10}\right].$$

| $k$ | Speed range | Candidate runner (sign constraint) |
|---|---|---|
| 3 | $[4.3, 4.5]$ | Runner 5 ($a_5 < 5$) ✓ |
| 5 | $[6.5, 6.7]$ | Runner 7 ($a_7 < 7$) ✓ |
| 6 | $[7.6, 7.8]$ | Runner 8 ($a_8 < 8$) ✓ |

The paper's Step 1 concludes "no runner for $k \geq 3$" but explicitly notes runner 5 as a candidate for $k=3$ without completing the analysis — self-contradictory.

### Runner 8 at $k=6$ incompatible with ERR-B-01

Runner 8 covering $J_9$ (requires $a_8 \in [7.6, 7.8]$) is **incompatible** with runner 8 covering $J_4$ via $k=2$ (requires $a_8 \in [7.111, 7.556]$). The speed ranges are disjoint ($7.556 < 7.6$). Therefore ERR-B-01 and this ERR-B-02 sub-case are mutually exclusive for runner 8.

**Partial repair:** If runner 8 is at $a_8 \in [7.6, 7.8]$ (covering $J_9$ for Lemma 3.2), then runner 8 is NOT in the ERR-B-01 regime (covering $J_4$ for Lemma 3.1). The two gaps do not compound: in any given configuration, runner 8 covers at most one of $J_4$ or $J_9$ (not both).

### Runner 5 at $k=3$ ($a_5 \in [4.3, 4.5]$)

Runner 5's $B_{5,3}$ covers $J_9$'s left boundary $10/11$:
$$B_{5,3} = \left[\frac{43}{11a_5},\; \frac{45}{11a_5}\right]; \quad a_5 \in [4.3, 4.5].$$
At $a_5 = 4.3$: $B_{5,3} \approx [0.909, 0.951]$. $J_9 = [0.909, 0.949]$. ✓ Runner 5 covers $J_9$ fully.

**Baton-pass argument for runner 5 alternative:**

At $a_5 \in [4.3, 4.5]$, runner 5 is covering $I_9$ via $B_{5,3}$. What is runner 5's $I_2$-covering position?
$$B_{5,0} = \left[\frac{10}{11a_5},\; \frac{12}{11a_5}\right].$$
At $a_5 = 4.3$: $B_{5,0} \approx [0.212, 0.254]$. This DOES cover $t^* = 69/275 \approx 0.251$ (end $\approx 0.254 > t^*$). ✓

So runner 5 at $a_5 \in [4.3, 4.5]$ covers BOTH $J_9$ AND $t^*$ in $I_2$. Unlike the runner 3 alternative (Step 2 in the original proof, where $a_3 \in [3.2, 3.257]$ forces a baton-pass gap in $I_2$), runner 5 in this range does NOT expose $t^*$.

However, runner 5 covering $J_9$ (requiring $a_5 \in [4.3, 4.5]$) may leave $I_2$'s left part uncovered. At $a_5 = 4.3$: $B_{5,0}$ starts at $0.212$ (barely at $I_2$'s left edge $23/110 \approx 0.209$), covering $[0.212, 0.254]$ of $I_2$. The portion $[0.209, 0.212]$ is uncovered by runner 5.

Whether this small left gap in $I_2$ forces GF$(I_2) > 0$ depends on other runners. This requires a detailed case analysis.

**Status:** Similar to ERR-B-01 sub-cases — not immediately resolved. The simple baton-pass argument from the runner-3 case does not directly apply.

### Runner 7 at $k=5$ ($a_7 \in [6.5, 6.7]$)

Runner 7's $B_{7,5}$ covers $J_9$'s left boundary:
$$B_{7,5} = \left[\frac{65}{11a_7},\; \frac{67}{11a_7}\right]; \quad a_7 \in [6.5, 6.7].$$
At $a_7 = 6.6$: $B_{7,5} \approx [0.896, 0.924]$. $J_9 = [0.909, 0.949]$. Overlap: $[0.909, 0.924] \subset J_9$. Runner 7 partially covers $J_9$.

For runner 7 to cover all of $J_9$ up to $261/275 \approx 0.949$: end $\geq 261/275$ requires $a_7 \leq 67 \times 275/(11 \times 261) = 18425/2871 \approx 6.417$. But the range for covering the left boundary requires $a_7 \geq 65/10 = 6.5 > 6.417$. **Contradiction.** Runner 7 cannot cover ALL of $J_9$ via $B_{7,5}$.

So runner 7 via $k=5$ covers only the LEFT part of $J_9$. Runner 2 must still cover the RIGHT part. The constraint on $a_2$ from the right portion of $J_9$ might differ from $575/261$.

Runner 7 covering $J_9$'s left boundary and runner 2 covering its right: requires checking compatibility. Runner 7 at $a_7 \in [6.5, 6.7]$:

**Impact on $I_7$:** Runner 7's coverage of $I_7 = [78/110, 87/110]$ requires $B_{7,4}$ to cover $78/110$, needing $a_7 \geq 990/143 \approx 6.923$. At $a_7 \in [6.5, 6.7]$, runner 7 CANNOT cover $I_7$. → GF$(I_7) > 0$.

**This gives the desired conclusion: runner 7 at $k=5$ covering $J_9$'s left boundary forces GF$(I_7) > 0$, since runner 7 cannot simultaneously cover $I_7$ at the required speed.**

**Step (ERR-B-02 partial fix for runner 7):**

> *Runner 7 at $k=5$ ($a_7 \in [6.5, 6.7]$):* For $B_{7,5}$ to start at or before $10/11$: $a_7 \geq 65/10 = 6.5$. At $a_7 \in [6.5, 6.7]$, runner 7's natural $I_7$-covering interval $B_{7,4}$ ends at $56/(11a_7) \leq 56/(11 \times 6.5) \approx 0.784 < 78/110 \approx 0.709$ — wait, let me recalculate.

$B_{7,4} = [54/(11a_7), 56/(11a_7)]$. For coverage of $I_7$'s left boundary $78/110$: end $\geq 78/110$ requires $a_7 \leq 56 \times 110/(11 \times 78) = 6160/858 = 280/39 \approx 7.179$. And start $\leq 78/110$ requires $a_7 \geq 54 \times 110/(11 \times 78) = 5940/858 = 990/143 \approx 6.923$.

So runner 7 covers $I_7$ only for $a_7 \in [6.923, 7.179]$. At $a_7 \in [6.5, 6.7]$: $6.7 < 6.923$, so runner 7 **cannot cover $I_7$.** → GF$(I_7) > 0$. $\square$

This closes the runner-7 case (ERR-B-02).

### ERR-B-02 Summary

| Alternative | Status |
|---|---|
| Runner 3 at $k=2$ ($a_3 \in [3.2, 3.257]$) | ✓ Closed in original proof (Step 2): GF$(I_2)>0$ via baton-pass |
| Runner 5 at $k=3$ ($a_5 \in [4.3, 4.5]$) | **Open** — runner 5 covers $t^*$ in $I_2$ at this speed; different argument needed |
| Runner 7 at $k=5$ ($a_7 \in [6.5, 6.7]$) | **Closed** (above): forces GF$(I_7)>0$ |
| Runner 8 at $k=6$ ($a_8 \in [7.6, 7.8]$) | **Closed** via mutual exclusion with ERR-B-01 (incompatible with covering $J_4$) |

Remaining open: runner 5 at $k=3$ in ERR-B-02, and the full runner-8 sub-case in ERR-B-01.

---

## Revised Proof Structure (with known repairs applied)

```
Lemma 3.1 (I₄ forces a₂ ≥ 20/9) — AMENDED:
  Step 2: No free runner covers 45/110 EXCEPT:
    - Runner 5 via k=1 (a₅ ∈ [4.67, 5)): → GF(I₂)>0.     ✓ (existing Step 3)
    - Runner 7 via k=1 (a₇ ∈ [4.67, 5.11]): → GF(I₇)>0.  ✓ (existing Step 4)
    - Runner 8 via k=2 (a₈ ∈ [7.11, 7.56]): → ??? OPEN     ✗ (ERR-B-01)
  Step 5: Runner 2 must cover 45/110 → a₂ ≥ 20/9.          ✓ (after Step 2 complete)

Lemma 3.2 (I₉ forces a₂ ≤ 575/261) — AMENDED:
  Step 1: Only runners 2 and 3 cover 10/11 EXCEPT:
    - Runner 5 via k=3 (a₅ ∈ [4.3, 4.5]): → ??? OPEN       ✗ (ERR-B-02)
    - Runner 7 via k=5 (a₇ ∈ [6.5, 6.7]): → GF(I₇)>0.     ✓ (above)
    - Runner 8 via k=6 (a₈ ∈ [7.6, 7.8]): → excluded by    ✓ (mutual exclusion)
      incompatibility with ERR-B-01 runner-8 regime.
  Step 3: Runner 2 must cover J₉ → a₂ ≤ 575/261.           ✓ (after Step 1 complete)
```

**Two sub-cases remain open:**
1. ERR-B-01: Runner 8 covering $J_4$ (Lemma 3.1 Step 2).
2. ERR-B-02: Runner 5 covering $J_9$ at $k=3$ (Lemma 3.2 Step 1).

---

## Recommended next steps

1. **Computational check:** Generate all ++------ configurations with $a_8 \in [64/9, 748/99]$ and verify computationally that GF $> 0$ via some slot. This would confirm the theorem holds despite the proof gap.

2. **Runner-8 sub-case (ERR-B-01):** Use the baton-pass structure: show that for ANY runner $j \in \{4,5\}$ covering $t^*$ at $a_j \in [3.62, 4.35]$, some other slot in $I_3, I_5, I_7$ becomes uncovered (due to the speed constraint shifting runner $j$ away from its natural slot). This requires knowing each runner's natural slot assignments in the ++------ class, which requires reading `lrc_n11_algebraic_lemma_v1.md` §3.

3. **Runner-5 at $k=3$ sub-case (ERR-B-02):** Apply the Complementary Pairs analysis: runners 5 and 6 form a pair covering $\{2,9\}$. Runner 5 at $a_5 \in [4.3, 4.5]$ covering $I_9$ deviates from its natural pair structure; show this leaves a gap in $I_2$ or $I_5$.

4. **General incompatibility strategy:** Instead of proving only "GF$(I_4)$ + GF$(I_9) > 0$", consider proving "GF$(I_k) > 0$ for some $k \in \{2, 4, 7, 9\}$" — a weaker but still sufficient conclusion for Main Claim 5.1 (GF $> 0$ overall).
