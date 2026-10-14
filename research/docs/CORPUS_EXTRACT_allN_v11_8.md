# Corpus Extract — `lrc_proof_allN_v11_8.md`

**Source file:** `/Users/trentpalelei/Desktop/Math Ex/lrc_proof_allN_v11_8.md`
**Source title (L1):** `# A Proof of the Lonely Runner Conjecture (Conditional)`
**Source version (L3):** `**Version:** 11.8`  **Date (L4):** `**Date:** 2026-05-27`
**Source length:** 1754 lines.
**Extract date:** 2026-09-07.

This is a **reference index**, not a review. Every recorded claim is a verbatim
quote from the source with its line number. Line numbers are 1-indexed and refer
to the file as it stood at extraction time. No quality assessment is offered and
none should be inferred from inclusion or omission.

Quoting convention: `L<n>` is the line on which the quoted text begins. Multi-line
quotes are reproduced as they appear in the source, including LaTeX markup.

---

## 1. The dependency chain

The manuscript is a strong induction on `n` (§2.5). The induction hypothesis is
stated at **L388**:

> - **Hypothesis $\mathbf{H}(m)$:**  LRC holds for all $m' \leq m$ runners
>   (i.e.\ all tuples of $m'-1$ distinct positive integer speeds, any gcd).

and **L391–392**:

> In every sub-case below, the inductive instances invoked satisfy $m < n$.
> No instance invokes the $n$-runner problem being proved.

Numbered results, in file order.

### 1.1 §2 — Setup and Notation (heading L298)

**Conjecture (LRC, all n) — L314**
> **Conjecture (LRC, all $n$).**  *For every choice of $n-1$ distinct positive
> speeds $v_1,\ldots,v_{n-1}$, there exists $t \geq 0$ such that
> $\|v_j t\| \geq 1/n$ for all $j = 1,\ldots,n-1$.*

Depends on: nothing (it is the target statement).

**Lemma 2.1 (Fundamental Identity) — L359**
> **Lemma 2.1** (Fundamental Identity).  *For any integers $a \geq 1$, $b \geq 1$ and any real $t$,*
> $$
> \{a \cdot \{bt\}\} = \{abt\}.
> $$

Depends on: nothing beyond the definition of the fractional part (proof L364–369).
Used by: Corollary 2.2; Theorem 5.2-S (L600); Theorem 10.1 Step 2 (L1360);
Theorem 11.1 Step 5 (L1598, L1605); the LRC-equivalence observation (L1100).
Its downstream role is flagged at L379–382:
> **Remark.**  Lemma 2.1 is used crucially in Theorems 10.1 and 11.1: when
> $V = pq$, it gives $\{Vt\} = \{p \cdot \{qt\}\} = \{q \cdot \{pt\}\}$,
> allowing the condition $\|Vt\| \geq 1/n$ to be re-expressed in terms of the
> fractional part $\{pt\}$ alone.

**Corollary 2.2 — L371**
> **Corollary 2.2.**  For integers $a,b \geq 1$ and real $t$,
> $$
> \|a \cdot \{bt\}\| = \|abt\|.
> $$

Depends on: Lemma 2.1 (stated in its proof, L376–377).

### 1.2 §3 — Base Cases (heading L397)

**Base of the induction: H(2) — L410**
> **Base of the induction: $\mathbf{H}(2)$.**  LRC holds for $1$ runner $v_1$:
> take $t = 1/(2v_1)$, giving $\|v_1 \cdot 1/(2v_1)\| = 1/2 \geq 1/3$. $\checkmark$

**n = 3 conclusion — L424**
> **Conclusion.**  Every $n=3$ instance falls into BSR or LR.  $\mathbf{H}(3)$ holds. $\square$

Depends on: Theorem 6.1 (BSR branch, L413), Theorem 7.1 (LR branch, L417), H(2).
The exhaustiveness at n=3 is asserted at L406–408:
> Therefore the BSR condition ($V \leq 2v_1$) and the LR condition ($V > 2v_1$)
> are **jointly exhaustive** — the hard case range $(2v_1, 2v_1]$ is empty.  The
> $n=3$ proof requires no DI or DI-MOD.

### 1.3 §4 — The Positive-Measure Lemma (heading L435)

**Lemma 4.1 (Positive-Measure Lemma) — L441**
> **Lemma 4.1** (Positive-Measure Lemma).  *Assume $\mathbf{H}(n-1)$ (LRC holds for $n-1$ runners).
> Then the simultaneous good set $G_s = \bigcap_{j=1}^{n-2} G_j$ has positive
> Lebesgue measure: $\mu(G_s) > 0$.*

with the addendum at L445:
> *Moreover, $G_s$ contains a non-degenerate closed interval.*

Depends on: `H(n-1)` (Step 1, L449). Explicit bound at L480:
> \delta \;\geq\; \frac{1}{n(n-1)\,v_{n-2}}. \tag{$\star$}

Generalisation clause used downstream, L491–498:
> **Remark (general application).**  Although Lemma 4.1 is stated for the
> $n-2$ slow runners using $\mathbf{H}(n-1)$, the argument is identical for any
> set of $k \geq 1$ distinct positive integer speeds: given $\mathbf{H}(k+1)$
> (which provides a time with $\|v_j t^{**}\| \geq 1/(k+1) > 1/n$ for all $j$
> in the set, whenever $k+1 \leq n-1$), the Lipschitz argument produces a
> neighbourhood of positive length in the good set.  We apply this freely in
> Theorems 10.1 and 11.1 to sub-systems $S_{\rm ind}$ and speed tuples
> $(w_1,\ldots,w_r,q)$.

Used by: Theorem 7.1 Step 2 (L1203); Theorem 10.1 Step 1 (L1353); Theorem 11.1
Step 1 (L1497) and Step 2 (L1512); Theorem 5.2-U's proof (L741).

### 1.4 §5 — Weyl Equidistribution (heading L502); §5.1 (L511)

**Theorem 5.1 (Weyl, 1916) — L513**
> **Theorem 5.1** (Weyl, 1916).  *Let $L$ be a positive integer and $\alpha > 0$
> with $\alpha/L \notin \mathbb{Q}$.  Let $G \subseteq \mathbb{R}$ be measurable,
> $\tfrac{1}{L}$-periodic, with positive density $\delta = \operatorname{dens}(G) > 0$.
> Let $A \subseteq [0,1)$ be measurable with $\mu(A) = \sigma > 0$.  Then*

Depends on: Fourier expansion (proof L524–538). Requires irrational `α/L`.

**Remark 5.1 (Why integer speed fails) — L540**
> **Remark 5.1** (Why integer speed fails).  If $\alpha = p \in \mathbb{Z}^+$ and
> $L \in \mathbb{Z}^+$, the equation $mL + kp = 0$ has non-trivial integer solutions:

The consequence is stated at L549:
> prove only non-emptiness for integer $p$.

### 1.5 §5.2 — The version we need (heading L551)

Itemised separately in §3 of this extract. Ordered list of numbered items with
line numbers:

| Item | Line | Kind |
|---|---|---|
| Theorem 5.2 (Integer-Speed Non-emptiness — Easy Case) | L570 | proved (proof L811–965) |
| Conjecture 5.2-H (Integer-Speed Non-emptiness — Hard Case) | L586 | conjecture, no proof |
| Theorem 5.2-S (Cardinality Sublemma) | L591 | proved (proof L600–621) |
| Corollary 5.2-S' (Refined open scope of Conjecture 5.2-H) | L623 | scope statement |
| Theorem 5.2-P (Pigeonhole Sub-condition) | L632 | proved (proof L648–657) |
| Remark 5.2-P (Empirical status of Theorem 5.2-P) | L659 | empirical |
| Remark 5.2-V (Cardinality Discriminator, Phase 6) | L686 | empirical |
| Theorem 5.2-U (Effective Pigeonhole under disjoint bands — Phase 7b) | L723 | proved (proof L733–751) |
| Corollary 5.2-U' (Large-p regime) | L753 | corollary of 5.2-U |
| Remark 5.2-W (Combined verification range — Phase 7) | L777 | empirical |
| Remark 5.2-A (Structural restriction on A) | L799 | scope statement |
| Remark 5.2 (Role in §§10–11) | L967 | scope statement |
| Remark 5.2-B (Counterexample to the original "arbitrary closed A" form) | L975 | counterexample |
| Remark 5.2-C (Empirical scope of validity / evidence for Conjecture 5.2-H) | L991 | empirical |
| Lemma 5.2-D (Coprime-n Explicit Witness) | L1006 | proved (proof L1015–1026) |
| Corollary 5.2-E (Alternative path when fine-cell counting is unavailable) | L1045 | proved (proof L1055–1056) |
| Remark 5.2-F (Status and scope of Lemma 5.2-D) | L1058 | scope statement |
| Remark 5.2-G (Status of Conjecture 5.2-H and the analytic gap, refined) | L1080 | open-item statement |

Dependencies inside §5.2:
- Theorem 5.2 — proof is self-contained fine-cell counting; hypotheses `gcd(p,L_G)=1`, `p ≥ n L_G`, `μ(G∩[0,1))>0`, `μ(A)>0`.
- Theorem 5.2-S — depends on Lemma 2.1 (L600) and `H(n-1)` (L617).
- Theorem 5.2-P — depends on Steps 1 and 3 of Theorem 5.2's proof (L641, L655) plus pigeonhole.
- Theorem 5.2-U — depends on Theorem 5.2-P (L751) and Lemma 4.1 (L741).
- Corollary 5.2-U' — depends on Theorem 5.2-U.
- Corollary 5.2-S' — depends on Theorem 5.2, Theorem 5.2-S, Theorem 5.2-P, Remark 5.2-V (L624–625).
- Lemma 5.2-D — self-contained residue computation.
- Corollary 5.2-E — depends on Lemma 5.2-D (L1055).

### 1.6 §6 — Bounded Speed Ratio (heading L1157)

**Theorem 6.1 (Bounded Speed Ratio) — L1159**
> **Theorem 6.1** (Bounded Speed Ratio).  *If $V \leq (n-1)v_1$, then $t^* = 1/(nv_1)$ satisfies
> $\|v_j t^*\| \geq 1/n$ for all $j = 1, \ldots, n-1$.*

Depends on: nothing inductive. Confirmed at L1651:
> directly. Uses no inductive hypothesis. *Unconditional.* $\checkmark$

### 1.7 §7 — Large Speed Ratio (heading L1190)

**Theorem 7.1 (Large Speed Ratio) — L1192**
> **Theorem 7.1** (Large Speed Ratio).  *If $V > (n-1)\,v_{n-2}$, then there exists $t$ with
> $\|v_j t\| \geq 1/n$ for all $j = 1,\ldots,n-1$.*

Depends on: `H(n-1)` (Step 1, L1197) and Lemma 4.1 (Step 2, L1203).
Boundary handoff recorded at L1243–1244:
> and the argument breaks.  The boundary case $V = (n-1)v_{n-2}$ falls into the
> hard case (§9.1) and is handled by Theorem 10.1 or Theorem 11.1.

### 1.8 §8 — Remark on the Hard Case (heading L1248)

No numbered result. Content indexed in §4 of this extract.

### 1.9 §9 — Case Exhaustion: The Hard Case (heading L1267)

**Definition (hard case) — L1271** — quoted in §4 below.

**Lemma 9.1 (Case Exhaustion) — L1276**
> **Lemma 9.1** (Case Exhaustion).  *The cases of Theorem 6.1, Theorem 7.1, and
> the hard case are mutually exclusive and collectively exhaustive.*

Depends on: Theorem 6.1, Theorem 7.1, the §9.1 Definition.

**Lemma 9.2 (Hard-Case Partition) — L1308**
> **Lemma 9.2** (Hard-Case Partition).  *In the hard case, let $p$ be the
> largest prime factor of $V$.  Exactly one of the following holds:*

Depends on: nothing beyond divisibility (proof L1314–1315).

**Lemma 9.3 (r ≤ n−3) — L1317**
> **Lemma 9.3** ($r \leq n-3$).  *In case (b) of Lemma 9.2, let
> $r = \#\{j : p \mid v_j\}$.  Then $r \leq n-3$.*

Depends on: the §2.2 GCD normalisation (cited at L1323).

### 1.10 §10 — Divisor Induction (heading L1328)

**Theorem 10.1 (Divisor Induction) — L1330**
> **Theorem 10.1** (Divisor Induction).  *In the hard case, suppose the largest
> prime $p$ of $V$ satisfies $\gcd(p,\, \operatorname{lcm}(v_1,\ldots,v_{n-2}))
> = 1$. Write $V = p q$ (so $q = V/p$). Then $G_s \cap G_V \neq \emptyset$,
> unconditionally if any of the following hold:
> (i) $p \ge n \cdot \operatorname{lcm}(v_1, \ldots, v_{n-2})$ (easy case,
> Theorem~5.2 applies);
> (ii) the speed tuple $(v_1, \ldots, v_{n-2}, V)$ satisfies the residue
> hypothesis of Lemma~5.2-D (boundary case);
> (iii) the band $\beta$-coverage $\mathcal{B}$ and target index set
> $\mathcal{I}_A$ satisfy $|\mathcal{B}| + |\mathcal{I}_A| > n L_A$
> (pigeonhole case, Theorem~5.2-P applies);
> (iv) the bands $\{B_{\alpha_0} : \alpha_0 \in \mathcal{I}_G\}$ are pairwise
> disjoint in $m''$-space and $p / v_{\max} + 1 / u_{\max} > n(n-1)/2$
> (asymptotic-$p$ case, Theorem~5.2-U applies, with $u_{\max} = q$ here).
> The conclusion holds conditionally on Conjecture~5.2-H in the residual
> where none of (i)–(iv) apply.*

Depends on: Lemma 4.1 via `H(n-1)` (Step 1, L1353); Lemma 2.1 (Step 2, L1361);
Theorem 5.2 / Lemma 5.2-D / Theorem 5.2-P / Theorem 5.2-U / Conjecture 5.2-H
(Step 4, L1390–1437). The four branches of Step 4 begin at L1392 (Easy case),
L1397 (Boundary case), L1403 (Pigeonhole case, with the Asymptotic-p sub-case
at L1417), L1426 (Hard case, residual).

### 1.11 §11 — Modified Divisor Induction (heading L1454)

Preceded by L1456:
> This is the key new theorem.

**Theorem 11.1 (Modified Divisor Induction) — L1458**
> **Theorem 11.1** (Modified Divisor Induction).  *In the hard case, suppose
> the largest prime $p$ of $V$ satisfies $p \mid v_{j_k}$ for $k = 1, \ldots, r$
> (with $r \ge 1$), where $\{j_1, \ldots, j_r\}$ are the indices of slow runners
> divisible by $p$. Write $w_k = v_{j_k}/p$ (so $v_{j_k} = p w_k$) and
> $q = V/p$. Then $G_s \cap G_V \neq \emptyset$, unconditionally if any of the
> following hold:
> (i) $p \ge n \cdot \operatorname{lcm}(S_{\mathrm{ind}})$ (easy case,
> Theorem~5.2 applies);
> (ii) the speed tuple $(v_1, \ldots, v_{n-2}, V)$ satisfies the residue
> hypothesis of Lemma~5.2-D (boundary case);
> (iii) the band $\beta$-coverage $\mathcal{B}$ and target index set
> $\mathcal{I}_A$ for the §11.1 configuration
> $(G_{\mathrm{ind}}, \mathrm{jointGoodSet}(w_1,\ldots,w_r,q), p)$ satisfy
> $|\mathcal{B}| + |\mathcal{I}_A| > n L_A$ (pigeonhole case,
> Theorem~5.2-P applies);
> (iv) the bands are pairwise disjoint and $p / v_{\max} + 1 / u_{\max} >
> n(n-1)/2$ (asymptotic-$p$ case, Theorem~5.2-U applies, with
> $v_{\max} = \max_{v_j \in S_{\mathrm{ind}}} v_j$ and
> $u_{\max} = \max(w_1, \ldots, w_r, q)$).
> The conclusion holds conditionally on Conjecture~5.2-H in the residual
> where none of (i)–(iv) apply.*

Depends on: Lemma 9.3 (L1480); `H(n-1-r)` (L1495); `H(r+2)` (L1508); Lemma 4.1
(L1497, L1512); Lemma 2.1 (L1599, L1606); Theorem 5.2 / Lemma 5.2-D /
Theorem 5.2-P / Theorem 5.2-U / Conjecture 5.2-H (Step 4, L1536–1582; branches
begin L1538, L1543, L1549, with the Asymptotic-p sub-case at L1563, and the
residual at L1571).

### 1.12 §12 — Main Theorem (heading L1621)

**Theorem 12.1** — quoted in full in §2 of this extract.

Depends on: §2.2 reduction (L1642); §3.1 base case (L1645); Lemma 9.1 (L1648);
Theorem 6.1, Theorem 7.1, Lemma 9.2, Theorem 10.1, Theorem 11.1 (L1650–1673);
and Conjecture 5.2-H in the residual.

Well-foundedness asserted at L1678–1679:
> The induction is well-founded: every hypothesis invoked is $\mathbf{H}(m)$
> for some $m \le n - 1 < n$. $\square$

**Remark 12.1-A (Verified unconditional range and analytical coverage) — L1681.**

### 1.13 §13 — References (heading L1729)

Nine entries, L1732–1753: BGSST98, BHK01, BS08, Chen92, Cusick74, KN74, Tao18,
Weyl16, Wills67.

---

## 2. What "conditional" means here

### 2.1 The conditioning statements

**Title — L1**
> # A Proof of the Lonely Runner Conjecture (Conditional)

**Status block — L5–L12**
> **Status:** Unconditional for $n \le 7$ and slow speeds $\le 10$. For general
> $n$, unconditional whenever Theorem~5.2-P (pigeonhole sub-condition) or
> Theorem~5.2-U (asymptotic-$p$ regime) applies — empirically $99.04\%$ of
> LRC-shape configurations in the searched range. Conditional on
> Conjecture~5.2-H only in the pigeonhole-failure residual (the $0.96\%$ of
> LRC-shape inputs where $|\mathcal{B}| + |\mathcal{I}_A| \le n L_A$ and
> Lemma~5.2-D's residue hypothesis fails). All $88$ enumerated residual cases
> at $n \le 10$ are positive by direct verification (Remark~5.2-W).

**Abstract — L228–L231**
> The Main Theorem is therefore unconditional in this verified range and
> conditional on Conjecture~5.2-H for general $n$. The boundary cases of the
> hard regime are additionally covered unconditionally by Lemma~5.2-D
> (Coprime-$n$ Explicit Witness).

**Introduction — L252–L256**
> This paper proves the conjecture **conditionally** for all $n \ge 3$ and
> **unconditionally** for $n \le 7$ with slow speeds bounded by $10$ (the
> empirically verified range — but note that LRC for $n \le 7$ is already
> classical; the value of v11.7 is the unified framework and its near-complete
> unconditional status). The proof proceeds by strong induction on $n$.

### 2.2 The single unproved hypothesis: Conjecture 5.2-H

**Conjecture 5.2-H — L586–L589 (full statement)**
> **Conjecture 5.2-H** (Integer-Speed Non-emptiness — Hard Case).
> *Under the same hypotheses as Theorem~5.2 but with $p < n L_G$ in place of
> $p \ge n L_G$, **and with the additional cardinality constraint
> $k_G + k_A = n - 1$**, the conclusion still holds.*

The "same hypotheses as Theorem 5.2" referenced are at L570–L584 (quoted in §3.1
below): distinct positive integer families `v_1..v_k` and `u_1..u_ℓ`,
`L_G = lcm(v_i)`, `L_A = lcm(u_j)`, `G` and `A` the corresponding good sets at
threshold `1/n`, `gcd(p, L_G) = 1`, `μ(G ∩ [0,1)) > 0`, `μ(A) > 0`; the
conclusion is `G ∩ {t ≥ 0 : {pt} ∈ A} ≠ ∅`.

**Its exact open scope — Corollary 5.2-S', L623–L630**
> **Corollary 5.2-S'** (Refined open scope of Conjecture~5.2-H).
> *Combined with Theorem~5.2 (Easy Case), Theorem~5.2-S, Theorem~5.2-P, and
> Remark~5.2-V, the open scope of Conjecture~5.2-H is exactly: $p < n L_G$ AND
> $k_G + k_A = n - 1$ AND Lemma~5.2-D's residue hypothesis fails AND the input
> falls outside both the pigeonhole-satisfying region (Theorem~5.2-P) and the
> direct-verification range $n \le 7$, $|G_{\mathrm{speeds}}| \le 3$,
> $|A_{\mathrm{speeds}}| \le 2$, $p \le 19$ (Remark~5.2-V). Within the
> verification range, all $5{,}517$ LRC-shape inputs have $N_{\text{joint}} \ge 1$.*

**Restated at Remark 5.2-G, L1080–L1083**
> **Remark 5.2-G** (Status of Conjecture~5.2-H and the analytic gap, refined).
> After the cardinality sublemma (Theorem~5.2-S), Conjecture~5.2-H's open scope
> is exactly: hard regime $p < n L_G$, cardinality $k_G + k_A = n - 1$, and
> Lemma~5.2-D's residue hypothesis fails (Corollary~5.2-S').

**The self-reference observation — L1100–L1110**
> **The LRC-equivalence observation.**  At $k_G + k_A = n - 1$, the joint
> condition $t \in G \cap \{t : \{pt\} \in A\}$ is, via Lemma~2.1, equivalent
> to the LRC condition for the $(n-1)$-element speed set
> $W = \{v_1, \ldots, v_{k_G}\} \cup \{p u_1, \ldots, p u_{k_A}\}$ at threshold
> $1/n$. Since this is exactly the LRC statement at $n$ for $W$, **Conjecture~5.2-H
> at the LRC-shape edge case is logically equivalent to the LRC inductive step
> at $n$** for the speed structure arising from §§10–11. Theorem~5.2 therefore
> does not add logical content beyond the §§10.1/11.1 conclusions themselves
> in this restricted scope; its role is to *separate* the analytic content
> (fine-cell counting in the easy regime) from the structural content (the
> gcd/§§10–11 reductions).

The same point appears in the v11.8 changelog at L59–L62:
> The underlying analytic gap (Conjecture~5.2-H's logical equivalence to the
> LRC inductive step at $k_G + k_A = n - 1$, per Phase~4) is unchanged. The
> patches narrow the *stated* conditional footprint of Theorems~10.1, 11.1,
> 12.1; they do not close any new mathematical content.

No conjecture named "5.2-SR-H" appears anywhere in the file. Grep for `SR` and
`Slot-Residue` returns no hits in this manuscript. Conjecture 5.2-H is the only
item labelled `Conjecture` other than the LRC statement itself at L314.

### 2.3 Theorem 12.1 — Main Theorem, quoted in full (L1623–L1638)

> **Theorem 12.1** (Lonely Runner Conjecture — Conditional).  *For all $n \ge 3$
> and all tuples of $n-1$ distinct positive real speeds, there exists
> $t \ge 0$ such that $\|v_j t\| \ge 1/n$ for all $j = 1, \ldots, n-1$,
> **conditionally on Conjecture~5.2-H**. The statement holds **unconditionally**
> when, for the input speed tuple normalised per §2.2, every invocation of
> Theorem~5.2 in the inductive proof falls into one of the unconditional
> sub-cases of Theorems~10.1 / 11.1: the easy regime $p \ge n L$, the
> boundary case covered by Lemma~5.2-D, the pigeonhole case covered by
> Theorem~5.2-P ($|\mathcal{B}| + |\mathcal{I}_A| > n L_A$), or the
> asymptotic-$p$ case covered by Theorem~5.2-U (pairwise-disjoint bands and
> $p / v_{\max} + 1 / u_{\max} > n(n-1)/2$). In particular, the statement
> holds unconditionally for all $n \le 7$ with slow speeds $\le 10$, where
> Conjecture~5.2-H has been exhaustively verified on the entire space of
> LRC-realisable hard-case inputs (see Remark~5.2-C); and the empirical
> coverage of Theorem~5.2-P alone reaches $99.04\%$ of LRC-shape
> configurations in the searched range (see Remark~5.2-P).*

### 2.4 The residual, as scoped in Remark 12.1-A (L1707–L1717)

> The conditional content of Theorem~12.1 is therefore restricted to inputs
> where (i) the hard regime $p < n L$ holds, (ii) Lemma~5.2-D's residue
> hypothesis fails, (iii) the pigeonhole inequality
> $|\mathcal{B}| + |\mathcal{I}_A| > n L_A$ fails, and (iv) the asymptotic
> Theorem~5.2-U does not apply (bands overlap or $p$ is below the
> $v_{\max} n(n-1)/2$ threshold). Empirically this residual is $0.96\%$ of
> LRC-shape inputs in the searched range ($53$ inputs at
> $n \le 7$ plus an additional $35$ enumerated at $n \in \{8, 9, 10\}$, see
> Remark~5.2-W); all $88$ are positive by direct verification, and the
> residual is mostly concentrated at $p \in \{2, 3\}$ with small
> $|\mathcal{I}_G|$ and overlapping bands.

---

## 3. §5.2 in detail (lines 551–1157)

### 3.1 Theorem 5.2 — exact statement (L570–L584)

> **Theorem 5.2** (Integer-Speed Non-emptiness — Easy Case).
> *Let $v_1, \ldots, v_k$ and $u_1, \ldots, u_\ell$ be families of distinct
> positive integers (entries distinct within each family). Set
> $L_G := \operatorname{lcm}(v_1, \ldots, v_k)$ and
> $L_A := \operatorname{lcm}(u_1, \ldots, u_\ell)$, and let*
> $$
> G \;=\; \bigl\{t \ge 0 : \|v_i t\| \ge \tfrac{1}{n} \;\text{for all}\; i\bigr\},
> \qquad
> A \;=\; \bigl\{\phi \in [0,1) : \|u_j \phi\| \ge \tfrac{1}{n} \;\text{for all}\; j\bigr\}.
> $$
> *Let $p$ be a positive integer with $\gcd(p, L_G) = 1$ and $p \ge n L_G$.
> Assume $\mu(G \cap [0,1)) > 0$ and $\mu(A) > 0$. Then*
> $$
> G \;\cap\; \bigl\{t \ge 0 : \{pt\} \in A\bigr\} \;\ne\; \emptyset.
> $$

Its proof occupies L811–L965, in four steps: Step 1 (Cell dichotomy for G, L816),
Step 2 (Cell dichotomy for A, L859), Step 3 (Joint fine cells, L865), Step 4
(Existence of a jointly good fine cell via the easy-case hypothesis, L913).
The point at which the easy-case hypothesis is consumed, L926–L934:
> The map $m'' \mapsto m'' \bmod (n L_G L_A)$ is periodic with period
> $n L_G L_A$. The band has length $L_A p$. The **easy-case hypothesis**
> $p \ge n L_G$ gives
> $$
> L_A p \;\ge\; n L_G L_A,
> $$
> so the band has length at least $n L_G L_A$, hence $m'' \bmod (n L_G L_A)$
> attains every value in $[0,\, n L_G L_A)$ as $m''$ varies in the band.

### 3.2 Sub-lemmas inside §5.2, with statements

**Conjecture 5.2-H — L586.** Quoted in full at §2.2 above.

**Theorem 5.2-S (Cardinality Sublemma) — L591–L598**
> **Theorem 5.2-S** (Cardinality Sublemma).
> *Let the hypotheses of Theorem~5.2 hold (LRC-shape, $\gcd(p, L_G) = 1$,
> $\mu(G \cap [0,1)) > 0$, $\mu(A) > 0$, no restriction on $p$ vs.\ $n L_G$),
> and additionally suppose*
> $$
> k_G + k_A \;\le\; n - 2.
> $$
> *Then $G \cap \{t : \{pt\} \in A\} \ne \emptyset$.*

**Corollary 5.2-S' — L623.** Quoted in full at §2.2 above.

**Theorem 5.2-P (Pigeonhole Sub-condition) — L632–L646**
> **Theorem 5.2-P** (Pigeonhole Sub-condition).
> *Under the hypotheses of Theorem~5.2 (LRC-shape, $\gcd(p, L_G) = 1$, positive
> measures), define the band $\beta$-coverage set*
> $$
> \mathcal{B} \;:=\; \bigcup_{\alpha_0 \in \mathcal{I}_G}
>    \Bigl\{ \bigl\lfloor (m'' \bmod n L_G L_A)/L_G \bigr\rfloor :
>           m'' \in [\alpha_0 \cdot L_A p,\; (\alpha_0 + 1) \cdot L_A p) \Bigr\}
> \;\subseteq\; \{0, 1, \ldots, n L_A - 1\},
> $$
> *where $\mathcal{I}_G$ is the $G$-good cell index set defined in Step~1 of the
> proof of Theorem~5.2. If*
> $$
> |\mathcal{B}| \;+\; |\mathcal{I}_A| \;>\; n L_A,
> $$
> *then $G \cap \{t : \{p t\} \in A\} \ne \emptyset$.*

**Theorem 5.2-U (Effective Pigeonhole under disjoint bands — Phase 7b) — L723–L731**
> **Theorem 5.2-U** (Effective Pigeonhole under disjoint bands — Phase 7b).
> *Under the hypotheses of Theorem~5.2-P, suppose the $|\mathcal{I}_G|$ bands
> $\{B_{\alpha_0} : \alpha_0 \in \mathcal{I}_G\}$ — each of width $L_A p$ in the
> $m''$-space $[0, n L_G L_A)$ — are pairwise disjoint. If*
> $$
> \frac{p}{v_{\max}} + \frac{1}{u_{\max}} > \frac{n(n-1)}{2},
> $$
> *where $v_{\max} = \max_i v_i$ and $u_{\max} = \max_j u_j$, then pigeonhole
> holds and the conclusion of Theorem~5.2 follows.*

**Corollary 5.2-U' (Large-p regime) — L753–L755**
> **Corollary 5.2-U'** (Large-$p$ regime). *In particular, if $p > v_{\max} \cdot
> n(n-1)/2$ and the bands are pairwise disjoint, then pigeonhole holds
> unconditionally.*

**Lemma 5.2-D (Coprime-n Explicit Witness) — L1006–L1013**
> **Lemma 5.2-D** (Coprime-$n$ Explicit Witness).
> *Let $n \ge 3$ and let $v_1 < v_2 < \cdots < v_{n-1}$ be distinct positive
> integers (here $v_{n-1}$ may denote the fast runner $V$).  Suppose that for
> every $j = 1, \ldots, n-1$ the residue $v_j \bmod (n v_1)$ lies in
> $[v_1,\, (n-1) v_1]$.  Then $t^* := 1/(n v_1)$ is an LRC certificate:*
> $$
> \|v_j\, t^*\| \;\ge\; \tfrac{1}{n} \qquad \text{for every } j = 1, \ldots, n-1.
> $$

**Corollary 5.2-E (Alternative path when fine-cell counting is unavailable) — L1045–L1053**
> **Corollary 5.2-E** (Alternative path when fine-cell counting is unavailable).
> *Suppose the hard case (§§10–11) places the Theorem~5.2 application in the
> hard regime $p < n L_G$, where the fine-cell counting argument of
> Theorem~5.2 (Easy Case) does not apply and the joint non-emptiness conclusion
> is, in general, only conditional on Conjecture~5.2-H. If the integer speeds
> $(v_1, \ldots, v_{n-2}, V)$ satisfy the hypothesis of Lemma~5.2-D, then
> $t^* = 1/(n v_1)$ is itself a joint witness, and the proof of the Main
> Theorem may invoke Lemma~5.2-D directly in place of Theorem~5.2 (and
> unconditionally).*

### 3.3 Recorded counterexamples

**The v11.5 "arbitrary closed A" form is false — L557–L561**
> The original v11.5 statement
> allowed $A$ to be an arbitrary closed set of positive measure; this is
> **false** (counterexample in Remark~5.2-B). The restricted form, which suffices
> for §§10–11, requires $A$ itself to be the good set for a family of distinct
> positive integer speeds.

**Remark 5.2-B, the explicit counterexample — L975–L984**
> **Remark 5.2-B** (Counterexample to the original "arbitrary closed $A$" form).
> The general statement of v11.5 with $A$ arbitrary closed of positive measure
> is **false**. Take $n = 5$, slow speeds $(v_1, v_2) = (1, 2)$
> (so $L = 2$, $d = 1$), $p = 3$ (coprime to $L = 2$), and let
> $A = [0.45, 0.55]$ (closed interval of measure $0.10 > 0$).
> Then $G = \{t : \|t\| \geq 1/5 \;\text{and}\; \|2t\| \geq 1/5\}$ has positive
> measure, but a direct computation (verified analytically and by sampling
> $10^7$ points in $[0,1)$) shows
> $G \cap \{t : \{3t\} \in [0.45, 0.55]\}$ has measure zero, and in fact is
> empty after intersecting with the open interior of $G$.

**681 counterexamples to the unrestricted fine-cell statement — L83–L87 (changelog)**
> 3. **The Lean development's fine-cell approach is sound only in the easy case
>    ($p \ge n L_G$).** Its hard case ($p < n L_G$) carries an open `sorry`. An
>    exhaustive harness found 681 abstract counterexamples to the unrestricted
>    fine-cell lemma; **0 are LRC-realisable**, but no analytic argument
>    currently bridges the LRC-realisable hard case to the conclusion.

**Counterexamples localised to the over-specified stratum — L697–L706**
> Every counterexample has $\delta \in \{1, 2, 3\}$; no counterexample has
> $\delta = 0$. Combined with Theorem~5.2-P, this means **every LRC-shape input
> in the searched range (5{,}517 of them) satisfies Conjecture~5.2-H**:
> $5{,}464$ via Theorem~5.2-P and the remaining $53$ via direct verification.
>
> The structural reading: the abstract joint-fine-cell statement is only false
> in the *over-specified* regime $\delta \ge 1$ (which Theorem~5.2-S leaves out
> of scope, since it requires $\delta \le -1$). In the LRC-relevant regime
> $\delta = 0$, no counterexample is found, and the conjecture is consistent
> with all evidence to date.

**The counterexample stratum forces the k_G + k_A = n − 1 restriction — L1095–L1098**
> The $\le n - 2$ stratum is now covered by Theorem~5.2-S. The $= n - 1$
> stratum is empirically counterexample-free but the analytic question is
> open. The $\ge n$ stratum has counterexamples — confirming that
> Conjecture~5.2-H must restrict to $k_G + k_A = n - 1$.

### 3.4 Restrictions added to make a statement true

**Remark 5.2-A (Structural restriction on A) — L799–L809**
> **Remark 5.2-A** (Structural restriction on $A$).  The original v11.5
> statement allowed $A$ to be *any* closed set of positive measure. That
> statement is **false**; a counterexample (verified analytically and numerically)
> is recorded in Remark~5.2-B. The restriction "$A$ is the good set for an
> integer-speed family" matches exactly the usage in Theorems~10.1 and 11.1 and
> is what is provable. The restriction is preserved through the inductive proof
> of LRC because every $A$ arising in §§10–11 has this form (see §10.1 Step 2
> for DI, §11.1 Step 2 for ModDI). The further partition into the easy and
> hard regimes corresponds exactly to the partition used in the formal Lean
> development (`joint_fine_cell_exists_easy` proven; the complementary
> `joint_fine_cell_exists` hard case carries an open `sorry`).

**The two-regime split — L562–L568**
> - the **easy regime** $p \ge n L_G$, where $L_G$ is the lcm of the slow-runner
>   speeds, in which the conclusion is proved unconditionally by a fine-cell
>   counting construction (Theorem~5.2 below);
> - the **hard regime** $p < n L_G$, in which the conclusion is left as
>   Conjecture~5.2-H, verified exhaustively at $n \le 7$ with slow speeds $\le 10$.

**Lemma 5.2-D's own scope limit — L1076–L1078**
> The lemma is *not* a universal alternative to Theorem~5.2: its hypothesis
> restricts the residue pattern of the speeds modulo $n v_1$, which fails on
> most LRC inputs (e.g.\ any input with $V \equiv 0 \pmod{n v_1}$).

**Period correction recorded in the v11.5→v11.6 changelog — L189–L195**
> **§5.2** — Theorem 5.2 is restated with the structural restriction needed for
> its actual usage in §§10–11 (the target set $A$ is itself a good set for an
> integer-speed family). The "$1/L$" period claim in Step 2 of the proof is
> replaced with the correct "$1/d$" period; the bound $K$ in the bounded-witness
> step is adjusted accordingly (it remains finite, so the compactness step
> survives). The original statement (arbitrary closed $A$) is empirically false;
> a counterexample is recorded at the end of §5.2.

### 3.5 Gap statements inside §5.2

**Two approaches ruled out — L1125–L1135**
> Two previously natural approaches to a full analytic proof of the hard case
> have been ruled out by the v11.6.1 audit cycle:
>
> - **Erdős–Turán perturbation.** The perturbation $\alpha_j = p + 1/(j\sqrt 2)$
>   forces $\|d\alpha_j\| = 1/(j\sqrt 2)$, which by Koksma–Schoissengeier
>   (Kuipers–Niederreiter, *Uniform Distribution of Sequences*, Theorem 2.3.5)
>   forces $D_N(\alpha_j/d) \ge \Omega(j/(dN))$, hence $t_j \ge \Omega(j/d^2)$,
>   unbounded in $j$; the compactness step then fails.
> - **Direct Fubini factorisation.** The integral $\int 1_G(t)\, 1_A(\{pt\})\, dt$
>   fails to factor for integer $p$: Fourier cross-terms $(m, n) = (kp, -kd)$
>   satisfy $md + np = 0$ and contribute, breaking the product formula.

**Candidate routes and the closing statement — L1137–L1153**
> A successful proof of Conjecture~5.2-H at the LRC-shape edge case must work
> by a method that genuinely accomplishes the LRC inductive step $n - 1 \to n$
> under the $V = pq$ structure of §§10–11. The natural candidates are:
>
> - A non-trivial strengthening of the fine-cell counting argument that
>   exploits the LRC-shape constraint $k_G + k_A = n - 1$ beyond what the
>   easy-case hypothesis $p \ge n L_G$ already provides.
> - A direct combinatorial-pigeonhole argument on the cell-index lattice
>   $\mathbb{Z}/(n L_G L_A)$, leveraging the fact that the band shift set
>   $\{r_{\alpha_0} L_A : \alpha_0 \in \mathcal{I}_G\}$ inherits structure
>   from the slow-runner cell dichotomies.
> - An entirely different combinatorial route that bypasses Theorem~5.2's
>   intermediate altogether, e.g., a direct LRC-internal compositional
>   argument leveraging the $V = pq$ structure (Option E of
>   `LonelyRunner/THEOREM52_JOINT_FINE_CELL_FALSE.md`).
>
> The author has not found such an argument and leaves the matter open.

**Residual persistence — L786–L790**
> $n=8$ (4), $n=9$ (9), $n=10$ (4). The residual is **persistent across $n$**
> (not asymptotically vanishing under our search), which sharpens the conclusion:
> - the residual cannot be dismissed as a small-$n$ artifact;
> - it must be either characterised as a structural family or covered by a
>   strengthened analytic bound (overlap-aware Lemma 7b.1).

**Empirical status table of Theorem 5.2-P — L664–L667**
> | Stratum | Pigeonhole holds | Pigeonhole fails |
> |---|---|---|
> | Counterexamples to Conjecture~5.2-H ($N_{\text{joint}} = 0$) | 0 | 681 |
> | Conjecture~5.2-H holds ($N_{\text{joint}} \ge 1$) | 34{,}825 | 3{,}158 |

**Phase 4 mining table — L1089–L1093**
> | Stratum | Inputs | Counterexamples |
> |---|---|---|
> | $k_G + k_A \le n - 2$ | 16{,}924 | 0 |
> | $k_G + k_A = n - 1$ | 8{,}388 | 0 |
> | $k_G + k_A \ge n$ | 13{,}352 | 681 |

---

## 4. The hard case (§8 at L1248, §9 at L1267)

### 4.1 Definition of the hard case — L1271–L1274

> **Definition.**  The **hard case** is:
> $$
> (n-1)\,v_1 \;<\; V \;\leq\; (n-1)\,v_{n-2}.
> $$

That is, the configuration is hard exactly when the maximum speed `V` lies
strictly above `(n−1)v_1` and at or below `(n−1)v_{n−2}` — the band left over
between the Theorem 6.1 (BSR) and Theorem 7.1 (LR) ranges. Lemma 9.1's proof
states this at L1289–L1292:
> These three cases are exhaustive and mutually exclusive: Theorem 6.1 covers
> $V \leq (n-1)v_1$, Theorem 7.1 covers $V > (n-1)v_{n-2}$, and the hard case
> fills the gap $(n-1)v_1 < V \leq (n-1)v_{n-2}$ between them.  (For $n = 3$
> the gap is empty and only Theorems 6.1 and 7.1 arise; see §3.1.) $\square$

Structural consequences of being in the hard case — L1300–L1302:
> In the hard case, $(n-1)v_1 < V \leq (n-1)v_{n-2}$, so:
> - $V > (n-1)v_1$ (the hard case lower bound, directly from the definition).
> - $v_{n-2} \geq V/(n-1)$ (the second-fastest slow runner is at least $V/(n-1)$).

### 4.2 §8 — why no bridge construction (L1250–L1263)

> **Why no "bridge" construction is needed.**
>
> One might attempt, for the hard case $(n-1)v_1 < V \leq (n-1)v_{n-2}$, a
> *bridge construction*: if some runner $v_j$ satisfies $V/(n-1) \leq v_j \leq (n-1)v_1$,
> take $t^* = 1/(nv_j)$.  Then all runners with speed $\geq v_j$ satisfy
> $\|v_i t^*\| = v_i/(nv_j) \in [1/n, (n-1)/n]$.  However, the slow runners
> (speeds $< v_j$) give $v_i t^* = v_i/(nv_j) < 1/n$, so $t^*$ fails for them.
> No simple modification of this construction handles the slow group in general.
>
> The correct approach does not depend on magnitude thresholds at all.  Theorems
> 10.1 and 11.1 partition the hard case by the *prime structure* of $V$: the
> largest prime $p$ of $V$ either divides some slow runner (Theorem 11.1) or
> does not (Theorem 10.1).  This partition covers all of the hard case regardless
> of whether any $v_j$ lies in $[V/(n-1),(n-1)v_1]$.

### 4.3 §9.3 — what "DI vs. DI-MOD exhaustion" splits into (heading L1306)

**Lemma 9.2 (Hard-Case Partition) — L1308–L1312**
> **Lemma 9.2** (Hard-Case Partition).  *In the hard case, let $p$ be the
> largest prime factor of $V$.  Exactly one of the following holds:*
>
> *(a) $\gcd(p, \operatorname{lcm}(v_1,\ldots,v_{n-2})) = 1$* — **Theorem 10.1** (Divisor Induction) applies.
> *(b) $p \mid v_j$ for some $j \in \{1,\ldots,n-2\}$* — **Theorem 11.1** (Modified Divisor Induction) applies.

Proof (L1314–L1315):
> *Proof.*  For any prime $p$, either $p$ divides $\operatorname{lcm}(v_1,\ldots,v_{n-2})$
> or it does not.  These cases are exhaustive and mutually exclusive. $\square$

So the split is on whether the **largest prime factor `p` of `V`** is coprime to
the lcm of the slow speeds (branch (a) → DI, Theorem 10.1) or divides at least
one slow speed (branch (b) → DI-MOD, Theorem 11.1).

**Lemma 9.3 (r ≤ n−3) — L1317–L1318**, which bounds the branch-(b) count:
> **Lemma 9.3** ($r \leq n-3$).  *In case (b) of Lemma 9.2, let
> $r = \#\{j : p \mid v_j\}$.  Then $r \leq n-3$.*

**No separate Bridge theorem — L1294–L1296**
> **Remark.**  Whether or not some $v_j$ lies in $[V/(n-1),(n-1)v_1]$, the hard
> case is always handled by Theorem 10.1 or Theorem 11.1.  No separate Bridge
> theorem is needed (see §8).

**§12's restatement of the same split — L1656–L1673**
> - **Hard case** ($(n-1) v_1 < V \le (n-1) v_{n-2}$): By Lemma~9.2, exactly
>   one of:
>   - **Divisor Induction (DI)** (largest prime $p$ of $V$ coprime to all slow
>     runners): Theorem~10.1 applies. Uses $\mathbf{H}(n-1)$ via Lemma~4.1.
> ...
>   - **Modified Divisor Induction (DI-MOD)** (largest prime $p$ of $V$
>     divides some slow runner): Theorem~11.1 applies. Uses
>     $\mathbf{H}(n-1-r)$ (for $G_{\rm ind}$, primary, $n-1-r \le n-2$) and
>     $\mathbf{H}(r+2)$ (for $A$, primary, $r+2 \le n-1$).

Within each of DI and DI-MOD, Step 4 splits further into four sub-branches
(§10.1: L1392 Easy / L1397 Boundary / L1403 Pigeonhole with the Asymptotic-p
sub-case at L1417 / L1426 Hard-case residual; §11.1: L1538 / L1543 / L1549 with
Asymptotic-p at L1563 / L1571 residual).

---

## 5. Every open item

Recorded individually, each with file line and verbatim sentence. Items are
listed in file order. Incidental prose uses of the keywords (for example "the
gap $(n-1)v_1 < V \leq (n-1)v_{n-2}$" at L1291, which names an interval rather
than a deficiency, and "It remains to choose $m''$..." at L921, which is
narrative) are excluded and noted at the end.

**Open item 1 — L59–L60**
> The underlying analytic gap (Conjecture~5.2-H's logical equivalence to the
> LRC inductive step at $k_G + k_A = n - 1$, per Phase~4) is unchanged.

**Open item 2 — L61–L62**
> The
> patches narrow the *stated* conditional footprint of Theorems~10.1, 11.1,
> 12.1; they do not close any new mathematical content.

**Open item 3 — L84–L87**
> Its hard case ($p < n L_G$) carries an open `sorry`. An
> exhaustive harness found 681 abstract counterexamples to the unrestricted
> fine-cell lemma; **0 are LRC-realisable**, but no analytic argument
> currently bridges the LRC-realisable hard case to the conclusion.

**Open item 4 — L138–L141 (changelog statement of Conjecture 5.2-H's scope)**
> - **Conjecture~5.2-H (Hard Case, $p < n L_G$)** — narrowed to the exact open
>   scope: $p < n L_G$ AND $k_G + k_A = n - 1$ AND Lemma~5.2-D fails. At this
>   scope the conjecture is logically equivalent (via Lemma~2.1) to the LRC
>   inductive step at $n$ for the combined speed set.

**Open item 5 — L145–L146**
> No counterexample
> known.

**Open item 6 — L131–L134**
> The
> residual is PERSISTENT across $n$ — not asymptotically vanishing — but every
> residual is positive with min $N_{\text{joint}} = 2$.

**Open item 7 — L150–L153**
> - **Theorems~10.1, 11.1, 12.1** are now stated with an explicit *conditional
>   on Conjecture~5.2-H* clause whenever the Theorem~5.2 application falls in
>   the hard case. The unconditional range is $n \le 7$ and slow speeds $\le
>   10$, where Conjecture~5.2-H is exhaustively verified.

**Open item 8 — L194–L195**
> The original statement (arbitrary closed $A$) is empirically false;
> a counterexample is recorded at the end of §5.2.

**Open item 9 — L228–L229 (Abstract)**
> The Main Theorem is therefore unconditional in this verified range and
> conditional on Conjecture~5.2-H for general $n$.

**Open item 10 — L286–L288 (Introduction)**
> Conjecture~5.2-H is verified
> exhaustively for $n \le 7$, slow speeds $\le 10$, but its general analytic
> proof is left open.

**Open item 11 — L270–L271 (Theorem 10.1 status line in the Introduction)**
> *Unconditional when $p \ge n \cdot L$ or when
>   Lemma~5.2-D applies; conditional on Conjecture~5.2-H otherwise.*

**Open item 12 — L276–L278 (Theorem 11.1 status line in the Introduction)**
> *Unconditional
>   when $p \ge n \cdot L_{\mathrm{ind}}$ or when Lemma~5.2-D applies;
>   conditional on Conjecture~5.2-H otherwise.*

**Open item 13 — L557–L559**
> The original v11.5 statement
> allowed $A$ to be an arbitrary closed set of positive measure; this is
> **false** (counterexample in Remark~5.2-B).

**Open item 14 — L567–L568**
> - the **hard regime** $p < n L_G$, in which the conclusion is left as
>   Conjecture~5.2-H, verified exhaustively at $n \le 7$ with slow speeds $\le 10$.

**Open item 15 — L586–L589 (the conjecture itself)**
> **Conjecture 5.2-H** (Integer-Speed Non-emptiness — Hard Case).
> *Under the same hypotheses as Theorem~5.2 but with $p < n L_G$ in place of
> $p \ge n L_G$, **and with the additional cardinality constraint
> $k_G + k_A = n - 1$**, the conclusion still holds.*

**Open item 16 — L623–L630 (Corollary 5.2-S', the exact open scope)**
> *Combined with Theorem~5.2 (Easy Case), Theorem~5.2-S, Theorem~5.2-P, and
> Remark~5.2-V, the open scope of Conjecture~5.2-H is exactly: $p < n L_G$ AND
> $k_G + k_A = n - 1$ AND Lemma~5.2-D's residue hypothesis fails AND the input
> falls outside both the pigeonhole-satisfying region (Theorem~5.2-P) and the
> direct-verification range $n \le 7$, $|G_{\mathrm{speeds}}| \le 3$,
> $|A_{\mathrm{speeds}}| \le 2$, $p \le 19$ (Remark~5.2-V).*

**Open item 17 — L757–L762**
> The disjoint-bands assumption is generic: bands $\alpha_0, \alpha_0'$ overlap
> iff $|(\alpha_0 - \alpha_0') p \bmod n L_G| < p$, which happens for "exceptional"
> shift configurations. Phase 7's empirical mining (75 LRC-shape pigeonhole
> failures recorded) confirms that the residual is exactly the regime where
> bands DO overlap; for these inputs Theorem~5.2-U does not apply, and the
> direct verification of Remark~5.2-V is used instead.

**Open item 18 — L786–L790**
> The residual is **persistent across $n$**
> (not asymptotically vanishing under our search), which sharpens the conclusion:
> - the residual cannot be dismissed as a small-$n$ artifact;
> - it must be either characterised as a structural family or covered by a
>   strengthened analytic bound (overlap-aware Lemma 7b.1).

**Open item 19 — L806–L809 (Remark 5.2-A, Lean parity)**
> The further partition into the easy and
> hard regimes corresponds exactly to the partition used in the formal Lean
> development (`joint_fine_cell_exists_easy` proven; the complementary
> `joint_fine_cell_exists` hard case carries an open `sorry`).

**Open item 20 — L971–L972 (Remark 5.2)**
> unconditionally **whenever $p \ge n L_G$**, and conditionally on
> Conjecture~5.2-H otherwise.

**Open item 21 — L975–L977 (Remark 5.2-B)**
> **Remark 5.2-B** (Counterexample to the original "arbitrary closed $A$" form).
> The general statement of v11.5 with $A$ arbitrary closed of positive measure
> is **false**.

**Open item 22 — L1048–L1049 (Corollary 5.2-E)**
> Theorem~5.2 (Easy Case) does not apply and the joint non-emptiness conclusion
> is, in general, only conditional on Conjecture~5.2-H.

**Open item 23 — L1076–L1078 (Remark 5.2-F)**
> The lemma is *not* a universal alternative to Theorem~5.2: its hypothesis
> restricts the residue pattern of the speeds modulo $n v_1$, which fails on
> most LRC inputs (e.g.\ any input with $V \equiv 0 \pmod{n v_1}$).

**Open item 24 — L1080–L1083 (Remark 5.2-G)**
> **Remark 5.2-G** (Status of Conjecture~5.2-H and the analytic gap, refined).
> After the cardinality sublemma (Theorem~5.2-S), Conjecture~5.2-H's open scope
> is exactly: hard regime $p < n L_G$, cardinality $k_G + k_A = n - 1$, and
> Lemma~5.2-D's residue hypothesis fails (Corollary~5.2-S').

**Open item 25 — L1095–L1098**
> The $\le n - 2$ stratum is now covered by Theorem~5.2-S. The $= n - 1$
> stratum is empirically counterexample-free but the analytic question is
> open. The $\ge n$ stratum has counterexamples — confirming that
> Conjecture~5.2-H must restrict to $k_G + k_A = n - 1$.

**Open item 26 — L1104–L1108 (the self-reference)**
> **Conjecture~5.2-H
> at the LRC-shape edge case is logically equivalent to the LRC inductive step
> at $n$** for the speed structure arising from §§10–11. Theorem~5.2 therefore
> does not add logical content beyond the §§10.1/11.1 conclusions themselves
> in this restricted scope

**Open item 27 — L1117–L1120 (Lean parallel, evidence item 2 for the conjecture)**
> 2. **Lean parallel.** The formal Lean development
>    `LonelyRunner/LRC/Theorem52_Weyl.lean` proves the easy case
>    (`joint_fine_cell_exists_easy`) by exactly the construction above, but
>    carries an open `sorry` for the hard case.

**Open item 28 — L1125–L1126**
> Two previously natural approaches to a full analytic proof of the hard case
> have been ruled out by the v11.6.1 audit cycle:

**Open item 29 — L1153**
> The author has not found such an argument and leaves the matter open.

**Open item 30 — L1344–L1345 (Theorem 10.1 statement)**
> The conclusion holds conditionally on Conjecture~5.2-H in the residual
> where none of (i)–(iv) apply.*

**Open item 31 — L1433–L1437 (Theorem 10.1 Step 4, residual branch)**
> is then the statement of Conjecture~5.2-H specialised to $(G_s, A, p)$,
> and is currently available only conditionally on that conjecture.
> Empirically, this residual amounts to $0.96\%$ of LRC-shape inputs in the
> searched range — all of which are directly verified positive in
> Remark~5.2-V.

**Open item 32 — L1477–L1478 (Theorem 11.1 statement)**
> The conclusion holds conditionally on Conjecture~5.2-H in the residual
> where none of (i)–(iv) apply.*

**Open item 33 — L1578–L1582 (Theorem 11.1 Step 4, residual branch)**
> is then the statement of Conjecture~5.2-H specialised to
> $(G_{\mathrm{ind}}, A, p)$, and is currently available only conditionally
> on that conjecture. Empirically this residual is $0.96\%$ of LRC-shape
> inputs in the searched range, and all enumerated cases are positive by
> direct verification (Remark~5.2-V).

**Open item 34 — L1626 (Theorem 12.1)**
> **conditionally on Conjecture~5.2-H**.

**Open item 35 — L1675–L1676 (Theorem 12.1 proof conclusion)**
> In every case $G_s \cap G_V \neq \emptyset$ (under the stated conditional or
> unconditional clauses), providing the required $t$.

**Open item 36 — L1707–L1712 (Remark 12.1-A, the residual's four conditions)**
> The conditional content of Theorem~12.1 is therefore restricted to inputs
> where (i) the hard regime $p < n L$ holds, (ii) Lemma~5.2-D's residue
> hypothesis fails, (iii) the pigeonhole inequality
> $|\mathcal{B}| + |\mathcal{I}_A| > n L_A$ fails, and (iv) the asymptotic
> Theorem~5.2-U does not apply (bands overlap or $p$ is below the
> $v_{\max} n(n-1)/2$ threshold).

**Open item 37 — L1719–L1725 (what would remove the condition)**
> The unconditional extension to general $n$ requires either (i) a proof of
> Conjecture~5.2-H restricted to the pigeonhole-failure residual, (ii) a
> proof that the residual remains finite as $n \to \infty$ (via $L_G$
> growth), or (iii) a structurally different bypass of the hard-regime
> application of Theorem~5.2 (e.g., a direct LRC-internal compositional
> argument leveraging the $V = p q$ structure without reducing to the joint
> integer-speed non-emptiness problem).

**Keyword hits excluded as incidental prose** (recorded so the grep is auditable):
L921 (`It remains to choose $m''$ in this band...` — narrative step), L193
(`it remains finite, so the compactness step survives` — a property, not an
incompleteness), L1291–L1292 (`fills the gap $(n-1)v_1 < V \leq (n-1)v_{n-2}$
between them` and `the gap is empty` — the word names an interval), L1216
(`We claim $I \cap G_V \neq \emptyset$` — a proof-internal claim that is then
proved at L1218–L1235). Every occurrence of `sorry` in the file (L84, L809,
L1120) refers to the Lean development and all three are recorded above.

There are **no** occurrences of `TODO`, `unproved`, `unresolved`, or `pending`
anywhere in the file.

---

## 6. Mentions of n=8, n=11, prime-power n, composite n

### 6.1 n = 8

Three occurrences, all recorded.

**L245–L249 (verification history of LRC in the literature)**
> it has been verified for $n \leq 8$: the cases $n = 3,4$ are
> elementary; $n = 5$ was settled by Chen \cite{Chen92} (see also the attribution
> in \cite{BGSST98}); $n = 6$ by Bienia, Goddyn, Gvozdjak, Sebő, and Tarsi
> \cite{BGSST98}; $n = 7$ by Bohman, Holzman, and Kleitman \cite{BHK01}; and
> $n = 8$ by Barajas and Serra \cite{BS08}.

**L785–L786 (the residual census)**
> The 88 residuals enumerate as: $n=4$ (2), $n=5$ (26), $n=6$ (25), $n=7$ (18),
> $n=8$ (4), $n=9$ (9), $n=10$ (4).

**L1713–L1715 (the residual split between verified ranges)**
> LRC-shape inputs in the searched range ($53$ inputs at
> $n \le 7$ plus an additional $35$ enumerated at $n \in \{8, 9, 10\}$, see
> Remark~5.2-W); all $88$ are positive by direct verification

**L1736–L1737 (reference entry)**
> - \[BS08\] J. Barajas, O. Serra.
>   *The lonely runner with seven runners.* Electron. J. Combin. 15 (2008), R48.

The search range that includes n=8 is stated at L778–L779:
> The combined Phase 5/6/7 mining covers $n \in \{3..10\}$ with speeds $\le 10$
> and primes $\le 19$ (boundaries vary by phase).

and at L124:
> $n \in \{7..10\}$ and derives an analytical sufficient condition

### 6.2 n = 11

No occurrence. Grep for `n=11`, `n = 11`, and `11` as a runner count returns no
hit in this manuscript. (`11.1`, `11.8`, `§11` are section and version numbers.)

### 6.3 Prime-power n, composite n

No occurrence. Grep for `prime power`, `prime-power`, and `composite` returns no
hits anywhere in the file.

### 6.4 Whether the argument's steps require n prime, n a prime power, or work for all n

Every occurrence of the word `prime` in the file is at L130, L135, L171, L231,
L267, L556, L661, L779, L978, L1006, L1087, L1260, L1261, L1309, L1314, L1322,
L1331, L1459, L1522, L1658, L1665, L1693. In each case the primality is a
property of the auxiliary integer `p` (the largest prime factor of the maximum
speed `V`), or of the search-range bound "primes $\le 19$", or of the word
"coprime" — never a hypothesis on `n` itself.

The standing hypothesis on `n` is stated at L302 and L341:

**L302**
> Let $n \geq 3$.  Place $n$ runners on a circle of unit circumference.

**L341**
> Throughout the proof we fix $n \geq 3$ and a speed tuple $(v_1,\ldots,v_{n-1})$

The primality that the case split does use is `p`'s, quoted at L1308–L1309:
> **Lemma 9.2** (Hard-Case Partition).  *In the hard case, let $p$ be the
> largest prime factor of $V$.

and used in Theorem 11.1 Step 3, L1521–L1522:
> For every $v_j \in S_{\rm ind}$: $p \nmid v_j$ by definition of $S_{\rm ind}$.
> Since $p$ is prime, $\gcd(p, v_j) = 1$.

`n` appears in arithmetic hypotheses in two places, neither of which is a
primality or prime-power condition on `n`:

**Lemma 5.2-D's residue hypothesis, L1008–L1010** (a condition on the speeds
modulo `n v_1`, not on `n`):
> Suppose that for
> every $j = 1, \ldots, n-1$ the residue $v_j \bmod (n v_1)$ lies in
> $[v_1,\, (n-1) v_1]$.

**Its special case, L1028–L1029** (a divisibility condition on the speeds by `n`):
> **Special case** ($v_1 = 1$).  The hypothesis reduces to $n \nmid v_j$ for every
> $j$, and the certificate becomes $t^* = 1/n$.

Theorem 12.1 is stated for all `n ≥ 3` (L1623–L1625, quoted at §2.3 above), and
the only stated restriction on its unconditional range is the Conjecture 5.2-H
residual and the verified search range — not any arithmetic property of `n`.
The one place where `n` growth enters is asymptotic, at L764–L769:
> The asymptotic interpretation: for fixed $v_{\max}$ and $n \to \infty$, the
> $L_G$ for LRC-shape DI grows super-linearly (in fact $L_G \ge \text{lcm}(2, \ldots, n-1)
> \sim e^n$ by Chebyshev / PNT), so the Hard Case range $p < n L_G$ contains the
> analytic regime $p > v_{\max} n(n-1)/2$ for all $n$ exceeding an explicit
> threshold. Inside this analytic regime, Theorem~5.2-U closes the conjecture
> unconditionally; outside, it joins the finite residual list.

---

## 7. Coverage statement

Lines of `/Users/trentpalelei/Desktop/Math Ex/lrc_proof_allN_v11_8.md` actually
opened and read for this extraction, in the order read:

- L1–L240
- L240–L440
- L440–L660
- L660–L900
- L900–L1160
- L1160–L1460
- L1460–L1754

Union: **L1–L1754, the complete file (1754 lines), with no unread range.**

Additional keyword greps run over the whole file, whose hits are reported in §5
and §6: `sorry`, `TODO`, `open`, `gap`, `conjecture`, `unproved`, `assumed`,
`conditional`, `pending`, `remains`, `unresolved`, `not proved`, `we do not`,
`false`, `counterexample`, `prime`, `prime power`, `prime-power`, `composite`,
`n = 8`, `n=8`, `n = 11`, `n=11`, `Barajas`, `BS08`.
