# Corrections to `eleven_lonely_runners.tex`

Date: 2026-03-30

---

## Fix 1 — PSM Lemma, Case 1: missing k=2 subcase (proof gap)

**Location:** PSM Lemma proof, Case 1 (formerly the sentence beginning "With $a_3\in(2,3)$, the only feasible index...")

**Issue:** The original text claimed k=1 is the *only* feasible index for which $B_{3,k}$ can cover the right endpoint $109/110$ of the gap when $a_3\in(2,3)$. This is incorrect. Setting k=2 yields $a_3\le 320/109\approx 2.936$, which is a non-empty subinterval of $(2,3)$.

**Why the conclusion is unaffected:** When k=2 and $a_3\in(320/109,3)$, runner 3 uses $B_{3,2}$ to cover the gap but its zeroth bad interval satisfies
$$B_{3,0}[\text{right}] = \frac{12}{11a_3} < \frac{12}{33} = \frac{40}{110} < \frac{43}{110} = I_3[\text{right}],$$
so $B_{3,0}$ falls short of $I_3$'s right edge and $\mathrm{GF}(I_3)>0$ directly.

**Fix applied:** Replaced the single sentence with a paragraph that:
1. Lists both feasible indices (k=1 and k=2).
2. Dismisses k=2 in one sentence via the bound above.
3. Continues with the k=1 analysis unchanged.

**Corrected text:**
> With $a_3\in(2,3)$, the feasible indices are $k=1$ (giving $a_3\le 230/109$) and $k=2$ (requiring $a_3\in(320/109,3)\approx(2.936,3)$ so that $B_{3,2}$ straddles $109/110$). If $k=2$, runner 3 uses $B_{3,2}$ to cover $109/110$ but its zeroth bad interval satisfies $B_{3,0}[\text{right}]=12/(11a_3)<12\cdot109/(11\cdot320)=327/880<344/880=43/110=I_3[\text{right}]$, so $B_{3,0}$ falls short of $I_3$'s right edge and $\mathrm{GF}(I_3)>0$ directly. It therefore suffices to handle $k=1$, giving $a_3\le 230/109$.

---

## Fix 2 — Lemma 6.1: L(a_9) discontinuity note (notational clarification)

**Location:** Lemma 6.1 ($I_4$ lower bound on $a_2$), immediately after the piecewise definition of $L(a_9)$.

**Issue:** $L$ has a deliberate downward jump at $a_9=86/9$: the left-hand limit is $20/9\approx 2.222$, while $L(86/9)=2\cdot(86/9)/9=172/81\approx 2.123$. Without a note, a reader checking the formula at the threshold might suspect a typo or error.

**Why the discontinuity is correct:** At $a_9=86/9$, runner 9 just reaches the left edge of $I_4$, which reduces runner 2's required coverage. The bound on $a_2$ therefore drops at this threshold — the jump is physically meaningful, not a mistake.

**Fix applied:** Added a parenthetical note directly after the closing `\]` of the piecewise display:

> *(Note that $L$ is discontinuous at $a_9=86/9$: the left-hand limit is $20/9\approx 2.222$ while $L(86/9)=172/81\approx 2.123$. This downward jump is intentional: at $a_9=86/9$ runner 9 just reaches the left edge of $I_4$, reducing runner 2's required coverage.)*

---

## Arithmetic spot-checks

| Claim | Verification |
|---|---|
| k=2 feasibility: lower bound 320/109 | $B_{3,2}[\text{left}]=32/(11a_3)\le109/110 \Rightarrow a_3\ge 32\cdot110/(11\cdot109)=3520/1199=320/109\approx2.936$ ✓ |
| k=2 feasibility: upper bound | $B_{3,2}[\text{right}]=34/(11a_3)\ge109/110 \Rightarrow a_3\le 340/109\approx3.119$; combined with $a_3<3$ gives upper bound 3 ✓ |
| k=2 subinterval non-empty | $320/109\approx2.936\in(2,3)$ ✓ |
| $B_{3,0}[\text{right}]<43/110$ for $a_3>320/109$ | $12/(11a_3)<12\cdot109/(11\cdot320)=1308/3520=327/880$; and $43/110=344/880>327/880$ ✓ |
| $L$ left-hand limit at $a_9=86/9$: $20/9\approx2.222$ | $20/9=2.2\overline{2}$ ✓ |
| $L(86/9)=2(86/9)/9=172/81\approx2.123$ | $172/81=2.1234\ldots$ ✓ |
| Jump is downward: $172/81<20/9$ | $20/9=180/81>172/81$ ✓ |
