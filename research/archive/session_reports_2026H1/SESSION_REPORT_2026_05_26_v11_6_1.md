# Session report — v11.6.1 + Theorem 5.2 structural-break finding

**Date:** 2026-05-26 (continuation)
**Start state:** v11.6 drafted; DeepSeek had given ACCEPT-WITH-MINORS on §5.2 with three flags about the explicit Erdős–Turán bound.
**End state:** v11.6.1 shipped with audit fixes + Lemma 5.2-D. **Theorem 5.2 now known to be structurally broken**, not merely bound-vague. v11.7 rewrite (fine-cell strategy mirroring Lean) is the path forward but deferred to a future session.

---

## TL;DR

1. v11.6 had a hidden structural break in Theorem 5.2's proof: the perturbation $\alpha_j = p + 1/(j\sqrt{2})$ forces $\|d\alpha_j\| = 1/(j\sqrt{2})$, which via Koksma–Schoissengeier gives $D_N \geq \Omega(j/N)$, hence $t_j \geq \Omega(j)$ — unbounded. Step 3's compactness limit fails.
2. The naïve Fubini alternative (Strategy c) also fails for the same integer-$p$ Fourier-cross-term reason that broke the manuscript's classical Theorem 5.1 (acknowledged in Remark 5.1).
3. The Lean development (`Theorem52_Weyl.lean`) has been quietly using a **third** approach — **fine-cell combinatorics** — which is the only known viable path. The manuscript needs a v11.7 §5.2 rewritten to mirror this Lean structure.
4. v11.6.1 was shipped with three cleanup patches (audit fixes + new Lemma 5.2-D coprime-$n$ explicit witness covering the 2 LRC-realisable boundary cases). The Lemma 5.2-D content remains valid in v11.7 — it covers exactly the cases the fine-cell approach also needs as an explicit-witness fallback (matching `EMPIRICAL_FINDINGS_2026_05_26.md` Fix 3).
5. Theorem 5.2's **conclusion** is still empirically true on all 20,403 LRC-realisable hard-case inputs. Only the *proof* is broken.

---

## Finding 1: Erdős–Turán is structurally insufficient (DeepSeek-verified)

### The calculation

For $\alpha_j = p + 1/(j\sqrt{2})$ with $p \in \mathbb{Z}^+$, $j \geq 1$, and $d \in \mathbb{Z}^+$ with $\gcd(p, d) = 1$:

$$\bigl\| d \cdot \tfrac{\alpha_j}{d} \bigr\| \;=\; \bigl\| \alpha_j \bigr\| \;=\; \bigl\| p + \tfrac{1}{j\sqrt{2}} \bigr\| \;=\; \bigl\| \tfrac{1}{j\sqrt{2}} \bigr\| \;=\; \tfrac{1}{j\sqrt{2}}$$

(for $j \geq 1$, $1/(j\sqrt{2}) < 1/\sqrt{2} < 1/2$, so the nearest integer is $0$).

The Erdős–Turán $h = d$ term contributes
$$\frac{1}{d \cdot \|d \alpha_j / d\|} = \frac{j\sqrt{2}}{d}.$$

This is linear in $j$.

### The lower bound

By Koksma–Schoissengeier (Kuipers–Niederreiter, *Uniform Distribution of Sequences*, Theorem 2.3.5):

$$D_N(\alpha) \;\geq\; \frac{1}{N} \cdot \max_{1 \leq h \leq N} \frac{1}{h \cdot \|h \alpha\|} - \frac{C}{N}$$

for an absolute constant $C$. Applying with $h = d$ (assuming $d \leq N$):

$$D_N(\alpha_j / d) \;\geq\; \Omega\!\left(\frac{j}{d N}\right).$$

### The structural consequence

For $D_N < \varepsilon$, we need $N \geq \Omega(j / (d \varepsilon))$.

In the v11.6 §5.2 Step 2 the witness $k_j$ satisfies $k_j \leq K(j, \mu(A))$ where $K$ is the smallest $N$ for which the orbit $\varepsilon$-equidistributes. So $K(j, \mu(A)) \geq \Omega(j / (d \mu(A)))$.

The witness is $t_j = s_0 + k_j / d$, hence $t_j \geq \Omega(j / d^2)$ — **unbounded in $j$**.

Step 3 of v11.6 §5.2 takes a subsequence $j_m \to \infty$, computes $\{\alpha_{j_m} t_{j_m}\} = \{p t_{j_m} + t_{j_m} / (j_m \sqrt{2})\}$, and argues the perturbation $t_{j_m} / (j_m \sqrt{2}) \to 0$ because $t_{j_m}$ is bounded. But it's not bounded: $t_{j_m} / (j_m \sqrt{2})$ approaches a nonzero constant $\approx 1/\sqrt{2}$, and the limit $\{\alpha_{j_m} t_{j_m}\}$ is **not** $\{p t_*\}$.

**Conclusion: Theorem 5.2's proof is structurally broken with $\alpha_j = p + 1/(j\sqrt{2})$.**

### DeepSeek verification

A focused single-question DeepSeek-R1:14b prompt (5KB, `--task math --thinking --max-tokens 6144 --timeout 1800`) was run.

Auditor checkpoint:
> [DeepSeek] says: ALL FOUR calculations correct. $\|d\alpha_j\| = 1/(j\sqrt{2})$ confirmed. Koksma–Schoissengeier (Kuipers–Niederreiter Thm 2.3.5) applies giving $D_N \geq \Omega(j/N)$. Proof of Theorem 5.2 is structurally broken (uniform $t_j$ bound fails). Fix: pivot to Fubini-based Strategy (c) mirroring Lean.
>
> Decision: **Accepting** — verdict aligns with independent derivation; Koksma reference is correct; conclusion is forced.

Artifacts: `reports/v11_6_step2_investigation/{deepseek_prompt_v2.txt, deepseek_answer_v2.md, deepseek_thinking_v2.log}`.

### Why no perturbation can fix this

DeepSeek and the user discussed options (a) [modified perturbation $\alpha_j = p + \varepsilon_j$ with $\|d\varepsilon_j\| \nrightarrow 0$] and (b) [bounded-CF irrational like golden ratio $\xi/j$]. Both fail by the same mechanism:

> If $\varepsilon_j \to 0$ then $d \varepsilon_j \to 0$, hence $\|d \cdot (p + \varepsilon_j)\| = \|d \varepsilon_j\| \to 0$. The $h = d$ Erdős–Turán term blows up.

The obstruction is inherent: requiring $\alpha_j \to p$ (for Step 3's limit) is *incompatible* with requiring $\|d\alpha_j\|$ bounded below (for uniform $t_j$).

---

## Finding 2: Naïve Fubini also fails (cross-term obstruction)

The natural alternative — direct measure-factorization $\mu(\{t : t \in G, \{pt\} \in A\}) = \mu(G) \cdot \mu(A)$ — fails for the same reason the manuscript's classical Theorem 5.1 fails for integer $p$.

### The Fourier check

With $G$ being $1/d$-periodic, write $1_G(t) = f(\{dt\})$. Then:

$$\int_0^1 f(\{dt\}) \, 1_A(\{pt\}) \, dt \;=\; \sum_{m,n \in \mathbb{Z}} \hat{f}_m \hat{a}_n \int_0^1 e^{2\pi i (md + np) t} \, dt$$

The time integral is $1$ iff $md + np = 0$, else $0$. Since $\gcd(p, d) = 1$, solutions to $md + np = 0$ are exactly $(m, n) = (kp, -kd)$ for $k \in \mathbb{Z}$. The surviving sum is

$$\sum_{k \in \mathbb{Z}} \hat{f}_{kp} \hat{a}_{-kd}.$$

The $k = 0$ term gives $\hat{f}_0 \hat{a}_0 = \mu(G \cap [0,1)) \cdot \mu(A)$ — the desired product. But the $k \neq 0$ cross-terms generally **do not vanish** for integer $p$, breaking the product formula.

This is exactly the obstruction acknowledged in v11.6 §5.1 Remark 5.1 (lines 352–361), which is precisely *why* the manuscript had to introduce the perturbation $\alpha_j$ in the first place.

So neither Strategy (a) [Erdős–Turán perturbation] nor Strategy (c) [direct Fubini] is viable. Strategy (b) [Lemma 4.1 explicit interval + Lipschitz] is a partial fallback (works for large $p$) but not a complete proof.

---

## Finding 3: The Lean is using a third strategy — fine cells

`LonelyRunner/LonelyRunner/LRC/Theorem52_Weyl.lean` (1646 lines) has been quietly using a different approach. Key structural observations from a survey of its lemma names:

| Line | Lemma / Theorem | Role |
|---|---|---|
| 17–18 | Header comment | "Theorem 5.2 is NOT Weyl's classical equidistribution theorem" |
| 250–256 | Deleted historical note | Confirms arbitrary-A formulation is FALSE; replacement restricts to finite union of intervals |
| 64–80 | `goodSet_periodic_multiple`, `jointGoodSet_periodic` | Periodicity structure |
| 97–184 | `crt_bijection_structure`, `crt_map_injective`, `crt_index_bijection` | CRT bijection at the index/cell level (not the continuous interval level) |
| 278–469 | `goodSet_period_characterization`, `goodSet_contains_cell`, `goodSet_disjoint_cell`, `cell_inclusion` | Cell-by-cell analysis of $G$ |
| 530–611 | `jointGoodSet_contains_cell`, `jointGoodSet_disjoint_cell`, `goodCellIdx` | Explicit good cells in joint set |
| 638–807 | `cellAt_pairwise_disjoint`, `cellAt_volume`, `goodCellsUnion_measure`, `jointGoodSet_measure_lower_bound`, `jointGoodSet_measure_eq` | Measure of explicit cell union |
| 838–903 | `fract_pt_on_fine_cell`, `fine_cell_subset_G_cell` | Fine cells in $[0, 1/(Lp))$ |

### What the Lean proof actually does (inferred)

1. Partition $[0, 1)$ into cells of length $1/(Lp)$ (or $1/(np)$ — exact size depends on the structure).
2. For each cell $C_m$, determine whether $C_m \subset G$ and whether $\{pt : t \in C_m\} \subset A$ (or some refinement).
3. Show that **at least one** cell satisfies both — by an explicit construction or a counting argument with the cells.
4. Non-emptiness follows directly.

This avoids Weyl, Erdős–Turán, and Fubini entirely. It's a **combinatorial proof** at the level of equally-spaced cells.

The drawback is verbosity: 1646 lines in Lean translates to substantial manuscript prose. The advantage is rigour: no asymptotic limits, no irrationality manipulations, no convergence subtleties.

---

## What we shipped: v11.6.1

Three patches were applied to v11.6 before the structural break was discovered. These are all still valid and survive into v11.7.

### Patch 1: Stale "$1/L$" parenthetical at §1 intro outline

The v11.5→v11.6 sweep missed one occurrence at line 93. Fixed: "period $1/d$ where $d = \gcd$(slow speeds); $\gcd(p, L) = 1$ where $L = \operatorname{lcm}$(slow speeds)".

### Patch 2: §5.2 Step 1 bookkeeping

v11.6 text checked "$\alpha_j / L$ is irrational", but Theorem 5.1's hypothesis (when applied to $G$ which is $1/d$-periodic) requires $\alpha_j / d$ irrational. Both happen to be true, so the conclusion is unaffected, but the logic is now consistent with Step 2.

### Patch 3: Lemma 5.2-D + Corollary 5.2-E + Remark 5.2-F

New content inserted after Remark 5.2-C (~lines 511–586).

**Lemma 5.2-D** (Coprime-$n$ Explicit Witness): If $v_j \bmod (nv_1) \in [v_1, (n-1)v_1]$ for every speed $v_j$, then $t^* = 1/(nv_1)$ is an LRC certificate.

Special case $v_1 = 1$: condition reduces to $n \nmid v_j$ for all $j$, witness is $t^* = 1/n$.

**Verification table** confirms both LRC-realisable boundary-only cases from `EMPIRICAL_FINDINGS_2026_05_26.md` satisfy the lemma:
- DI: $n=5$, speeds $\{1,3,4,7\}$, residues mod 5: $1, 3, 4, 2 \in [1,4]$ ✓
- ModDI: $n=6$, speeds $\{1,3,4,5,9\}$, residues mod 6: $1, 3, 4, 5, 3 \in [1,5]$ ✓

**Corollary 5.2-E**: Lemma 5.2-D may be invoked in place of Theorem 5.2 when its hypothesis is satisfied.

**Remark 5.2-F**: Scope clarification — Lemma 5.2-D is not a universal replacement for Theorem 5.2 (its hypothesis fails on most LRC inputs, e.g., any with $V \equiv 0 \pmod{nv_1}$). Its role is robustness, Lean parity (Fix 3 from EMPIRICAL_FINDINGS), and transparency.

These patches survive into v11.7 because:
- Patches 1 & 2 are independent of the proof technique used in §5.2.
- Lemma 5.2-D handles the same 2 LRC-realisable boundary cases that the fine-cell approach will need to handle as an explicit-witness fallback (Fix 3).

---

## v11.7 drafting plan (for a future session)

### Scope

Rewrite §5.2 from scratch using the fine-cell approach mirrored from `Theorem52_Weyl.lean`. Preserve all other §§1–4 and §§6–13 content. Keep Lemma 5.2-D / Corollary 5.2-E / Remark 5.2-F from v11.6.1.

### Recommended preparation

1. **Read** `Theorem52_Weyl.lean` lines 64–903 carefully (the cell-level and fine-cell lemmas). Aim for an English-prose summary of the proof outline.
2. **Re-read** `THEOREM52_RESEARCH.md` (Lean roadmap) and `THEOREM52_PROGRESS.md` to understand the current state of formal verification.
3. **Read** `EMPIRICAL_FINDINGS_2026_05_26.md` Fix 3 once more — it independently identifies the fine-cell / explicit-witness path.

### Drafting outline for new §5.2

1. **Setup**: $G$ as before ($1/d$-periodic), $A$ as before (finite union of intervals derived from integer-speed family).
2. **Definition: Fine cells**. Subintervals of $[0, 1)$ of length $1/(d \cdot p \cdot \max u_j)$ (or some similar denominator) with explicit endpoints.
3. **Lemma**: each fine cell $C$ is either entirely in $G$ or entirely in $G^c$ (similarly for $\{pt\} \in A$).
4. **Counting argument**: of the $d \cdot p \cdot \max u_j$ cells in $[0, 1)$, how many satisfy both conditions? Show count is $\geq 1$ (perhaps by a Chinese-Remainder-style counting).
5. **Conclusion**: pick any qualifying cell, take its midpoint as the witness $t_*$.

### Risk register

| Risk | Mitigation |
|---|---|
| Lean proof has unresolved `sorry`s in the fine-cell lemmas | Check Lean build status before relying on those lemmas; `Theorem52_Weyl.lean` currently has 3 sorries (per session-state.md) |
| Counting argument needs gcd / CRT structure not obvious from Lean | Read `crt_bijection_structure`, `crt_index_bijection`, `crt_map_injective` carefully; these provide the count |
| Translation may bloat manuscript significantly | Aim for ~150–200 lines of prose for §5.2; cite Lean for full detail |
| Two boundary-only LRC cases may not satisfy fine-cell hypothesis | Lemma 5.2-D from v11.6.1 already handles them; cite Corollary 5.2-E as the formal fallback |

---

## Artifacts produced this session

| File | Role |
|---|---|
| `lrc_proof_allN_v11_6_1.md` | v11.6.1 manuscript (986 lines) |
| `V11_6_1_PATCH_SUMMARY.md` | Patch-level diff/rationale from v11.6 to v11.6.1 |
| `reports/v11_6_step2_investigation/deepseek_prompt.txt` | First (broad) DeepSeek prompt |
| `reports/v11_6_step2_investigation/deepseek_answer.md` | First DeepSeek answer (53 lines; inconclusive Option B) |
| `reports/v11_6_step2_investigation/deepseek_thinking.log` | First DeepSeek thinking trace (172 lines; truncated at token limit) |
| `reports/v11_6_step2_investigation/deepseek_prompt_v2.txt` | Focused single-question DeepSeek prompt |
| `reports/v11_6_step2_investigation/deepseek_answer_v2.md` | Second DeepSeek answer (59 lines; definitive structural-break verdict) |
| `reports/v11_6_step2_investigation/deepseek_thinking_v2.log` | Second DeepSeek thinking trace (91 lines) |
| `SESSION_REPORT_2026_05_26_v11_6_1.md` | this file |

---

## Memory file delta

Append to `memory/MEMORY.md`:

> **2026-05-26 (cont. cont.):** Theorem 5.2's $\alpha_j = p + 1/(j\sqrt{2})$ Erdős–Turán proof is structurally broken. $\|d\alpha_j\| = 1/(j\sqrt{2})$ forces $D_N \geq \Omega(j/N)$ (Koksma–Schoissengeier, KN Thm 2.3.5), hence $t_j$ unbounded, hence Step 3 compactness fails. DeepSeek-verified (`reports/v11_6_step2_investigation/deepseek_answer_v2.md`). Naive Fubini also fails (cross-terms from $md + np = 0$ with $m = kp$, $n = -kd$ survive). Lean is using **fine-cell combinatorics** instead (`Theorem52_Weyl.lean` lines 530–903). v11.7 will rewrite §5.2 to mirror Lean fine-cell approach. v11.6.1 shipped with audit fixes + Lemma 5.2-D (coprime-$n$ explicit witness covering both boundary-only LRC cases). See `SESSION_REPORT_2026_05_26_v11_6_1.md` for full report.
