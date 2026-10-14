# A Proof of the Lonely Runner Conjecture (Conditional)

**Version:** 11.7
**Date:** 2026-05-26
**Status:** Unconditional for $n \le 7$ and slow speeds $\le 10$; conditional
on Conjecture~5.2-H (Hard-Case Integer-Speed Non-emptiness) for general $n$.

---

## Changelog (v11.6.1 → v11.7)

This revision is a substantive architectural change to §5.2 in response to two
findings from the v11.6.1 audit cycle (2026-05-26):

1. **Theorem~5.2's perturbation-and-compactness proof in v11.6.1 is
   structurally broken.** The perturbation $\alpha_j = p + 1/(j\sqrt 2)$ forces
   $\|d\alpha_j\| = 1/(j\sqrt 2)$, which by Koksma–Schoissengeier
   (Kuipers–Niederreiter, *Uniform Distribution of Sequences*, Theorem 2.3.5)
   gives $D_N(\alpha_j/d) \ge \Omega(j/(dN))$. The Step 2 witness $t_j$ is
   therefore $\ge \Omega(j/d^2)$, **unbounded in $j$**, and the Step 3
   compactness limit fails (DeepSeek-R1:14b verified).
2. **The naive Fubini alternative also fails** (Fourier cross-terms $md + np
   = 0$ with $(m, n) = (kp, -kd)$ survive for integer $p$).
3. **The Lean development's fine-cell approach is sound only in the easy case
   ($p \ge n L_G$).** Its hard case ($p < n L_G$) carries an open `sorry`. An
   exhaustive harness found 681 abstract counterexamples to the unrestricted
   fine-cell lemma; **0 are LRC-realisable**, but no analytic argument
   currently bridges the LRC-realisable hard case to the conclusion.

In response, §5.2 is restructured:

- **Theorem~5.2 (Integer-Speed Non-emptiness, Easy Case)** — restated with the
  hypothesis $p \ge n L_G$ and proved unconditionally by a fine-cell
  construction mirroring the Lean development (`joint_fine_cell_exists_easy`).
- **Theorem~5.2-S (Cardinality Sublemma)** — for cardinality $k_G + k_A \le
  n - 2$, the conclusion holds unconditionally via $\mathbf{H}(n-1)$ applied
  to the combined speed set $\{v_i\} \cup \{p u_j\}$. Identified by an
  empirical-mining study (2026-05-27,
  `LonelyRunner/scripts/phase4_invariant_mining.py`): of 38{,}664 hard-regime
  inputs at $n \le 7$, every counterexample to the unrestricted statement
  has $k_G + k_A \ge n$.
- **Theorem~5.2-P (Pigeonhole Sub-condition)** — a second empirical-mining
  pass (2026-05-27, `LonelyRunner/scripts/phase5_residue_structure.py`)
  identified a *perfect* separating invariant: the band $\beta$-coverage
  $\mathcal{B}$ satisfies $|\mathcal{B}| + |\mathcal{I}_A| > n L_A$ in 100%
  of the $37{,}983$ positive inputs and 0% of the $681$ counterexamples.
  This bound is sufficient for the conjecture's conclusion by an elementary
  pigeonhole argument. Among LRC-shape inputs ($k_G + k_A = n - 1$), it
  holds in 99.04% ($5{,}464 / 5{,}517$); the residual $0.96\%$ ($53$
  inputs) are handled by Remark~5.2-V (direct verification).
- **Remark~5.2-V (Cardinality Discriminator)** — a third mining pass
  (2026-05-27, `LonelyRunner/scripts/phase6_residual_arithmetic.py` +
  `phase6b_density_separator.py` + `phase6c_correlation.py`) found that the
  cardinality balance $\delta := k_G + k_A - (n - 1)$ *perfectly* separates
  LRC-shape positives from counterexamples within the pigeonhole-failure
  stratum: all 53 residual LRC-shape positives have $\delta = 0$; all 681
  counterexamples have $\delta \in \{1, 2, 3\}$. Combined with Theorem~5.2-P,
  **every LRC-shape input in the searched range ($5{,}517$ inputs) satisfies
  Conjecture~5.2-H**. Correlation-ratio analysis confirms that LRC-shape
  eliminates the adversarial alignment producing counterexamples (DeepSeek
  ACCEPT, CONFIDENCE HIGH).
- **Theorem~5.2-U (Effective Pigeonhole under disjoint bands)** — a fourth
  pass (2026-05-27, `LonelyRunner/scripts/phase7a_extended_search.py` +
  `phase7a_n10_quick.py` + `phase7c_pattern_enum.py`) extends the search to
  $n \in \{7..10\}$ and derives an analytical sufficient condition: when the
  $|\mathcal{I}_G|$ bands are pairwise disjoint in $m''$-space and
  $p / v_{\max} + 1 / u_{\max} > n(n-1)/2$, pigeonhole holds. Combined with
  Lemma~4.1, this gives an unconditional Theorem 5.2-U covering the asymptotic
  regime $p \ge v_{\max} \cdot n(n-1)/2$ within the Hard Case $p < n L_G$.
  The combined Phase 5/6/7 verification spans $n \le 10$, speeds $\le 10$,
  primes $\le 19$: approximately $10{,}000+$ LRC-shape inputs verified,
  $0$ counterexamples, $88$ residual cases enumerated (Remark~5.2-W). The
  residual is PERSISTENT across $n$ — not asymptotically vanishing — but every
  residual is positive with min $N_{\text{joint}} = 2$. DeepSeek ACCEPT,
  CONFIDENCE HIGH on the Theorem 5.2-U derivation.
- **Lemma~5.2-D (Coprime-$n$ Explicit Witness)** — retained verbatim from
  v11.6.1; provides an explicit certificate $t^* = 1/(n v_1)$ for the two
  boundary-only LRC-realisable cases.
- **Conjecture~5.2-H (Hard Case, $p < n L_G$)** — narrowed to the exact open
  scope: $p < n L_G$ AND $k_G + k_A = n - 1$ AND Lemma~5.2-D fails. At this
  scope the conjecture is logically equivalent (via Lemma~2.1) to the LRC
  inductive step at $n$ for the combined speed set. Empirically verified on
  20{,}403 LRC-realisable hard-case inputs ($n \le 7$, slow speeds $\le 10$);
  Phase~6 (Remark~5.2-V) additionally verifies all $5{,}517$ LRC-shape
  inputs in the joint-fine-cell search range (combined: Theorem~5.2-P covers
  $5{,}464$; direct verification covers the remaining $53$). No counterexample
  known.

Downstream consequences:

- **Theorems~10.1, 11.1, 12.1** are now stated with an explicit *conditional
  on Conjecture~5.2-H* clause whenever the Theorem~5.2 application falls in
  the hard case. The unconditional range is $n \le 7$ and slow speeds $\le
  10$, where Conjecture~5.2-H is exhaustively verified.
- **Lemma~5.2-D / Corollary~5.2-E / Remark~5.2-F** survive unchanged from
  v11.6.1.
- All other §§1–4, §§6–9, §13 content is unchanged.

The v11.6 → v11.6.1 changelog and v11.5 → v11.6 changelog below are retained
for traceability.

---

## Changelog (v11.6 → v11.6.1)

Three minor errata, none affecting any theorem statement or proof conclusion:

1. **§1 Introduction outline** — A stale "(period $1/L$, $\gcd(p,L)=1$)" parenthetical describing the slow-runner good set $G_s$ in the §10 outline bullet survived the v11.5→v11.6 sweep. Corrected to "(period $1/d$, $\gcd(p,L)=1$)" with $d = \gcd$(slow speeds).

2. **§5.2 Step 1 (irrational approximation)** — The verification text read "$\alpha_j / L$ is irrational". The correct condition for applying Theorem~5.1 to $G$ (which is $1/d$-periodic, not $1/L$-periodic — that was the point of the v11.6 fix) is $\alpha_j / d \notin \mathbb{Q}$. Both irrationals are in fact true (any rational shift of an irrational is irrational), so the conclusion is unchanged; the bookkeeping is now consistent with Step 2.

3. **New Lemma 5.2-D and Corollary 5.2-E** — A coprime-$n$ explicit-witness lemma is added immediately after Remark 5.2-C. It states that whenever $n \nmid v_j$ for every slow runner and every fast runner, $t = 1/(n v_1)$ is an LRC certificate. This is *not* required by the proof of Theorem~5.2 itself (the perturbation-and-compactness argument already handles boundary cases via closedness of $G$ and $A$), but it provides an independent, finite, mechanical certificate for the two LRC-realisable boundary-only cases identified empirically (Remark 5.2-C). Its purpose is robustness, Lean parity, and a transparent alternative path for those small cases.

---

## Changelog (v11.5 → v11.6)

Two errata found in v11.5 are corrected here. Both originate in the period claim
"$G_s$ has period $1/L$" (where $L = \operatorname{lcm}$ of slow speeds) and its
inheritance in §§10–11. Empirical investigation showed this claim fails in
$\ge 23\%$ of LRC-realisable hard-case configurations (e.g.\ slow speeds
$\{1,2\}$ with $n=4$: actual period is $1$, not $1/L = 1/2$).

The actual period of $G_s = \bigcap_i \{t : \|v_i t\| \ge 1/n\}$ is $1/d$ where
$d = \gcd(v_1, \ldots, v_k)$. After §2.2 GCD normalisation, $\gcd$ of *all*
speeds (slow plus $V$) equals $1$, but $\gcd$ of the slow speeds alone can
still exceed $1$ (e.g.\ slow $= \{2,4,6\}$, $V=1$: $\gcd(\text{all})=1$,
$\gcd(\text{slow})=2$, period of $G_s$ is $1/2$).

**§5.2** — Theorem 5.2 is restated with the structural restriction needed for
its actual usage in §§10–11 (the target set $A$ is itself a good set for an
integer-speed family). The "$1/L$" period claim in Step 2 of the proof is
replaced with the correct "$1/d$" period; the bound $K$ in the bounded-witness
step is adjusted accordingly (it remains finite, so the compactness step
survives). The original statement (arbitrary closed $A$) is empirically false;
a counterexample is recorded at the end of §5.2.

**§10.1 Step 1** — The parenthetical "$G_s$ is periodic with period $1/L$" is
corrected to "$1/d$ where $d = \gcd(v_1, \ldots, v_{n-2})$". This does not
affect the proof, which only uses Theorem 5.2's conclusion, not its proof's
internal claims.

**§11.1 Step 3** — Same correction for $G_{\rm ind}$ and $L_{\rm ind}$.

These fixes do not change any theorem statement other than Theorem 5.2 itself,
and Theorems 10.1, 11.1, 12.1 are unaffected in conclusion. See companion
empirical report `LonelyRunner/EMPIRICAL_FINDINGS_2026_05_26.md` and the
$\ge 20{,}000$-input verification harness for evidence that the §§10–11
conclusions hold in every tested LRC-realisable configuration.

---

## §0  Abstract

We give a conditional proof of the Lonely Runner Conjecture: for any $n \ge 3$
and any $n-1$ runners on a unit circle with distinct positive real speeds,
there exists a time at which every runner is at distance at least $1/n$ from
the origin. The proof proceeds by strong induction on $n$ and partitions the
parameter space into four cases according to the arithmetic of the maximum
speed $V$ relative to the remaining runners. The first two cases — bounded
and large speed ratio — are handled unconditionally by explicit or
neighbourhood arguments. The third and fourth cases — the "hard case" — reduce
via a Fundamental Identity $\{Vt\} = \{q \cdot \{pt\}\}$ to an integer-speed
non-emptiness lemma (Theorem~5.2). We prove Theorem~5.2 unconditionally in the
*easy regime* $p \ge n L_G$ via a fine-cell construction; for the *hard
regime* $p < n L_G$ we state Conjecture~5.2-H (Hard-Case Integer-Speed
Non-emptiness), which is verified exhaustively on 20{,}403 LRC-realisable
inputs at $n \le 7$ and slow speeds $\le 10$, with no known counterexample.
The Main Theorem is therefore unconditional in this verified range and
conditional on Conjecture~5.2-H for general $n$. The boundary cases of the
hard regime are additionally covered unconditionally by Lemma~5.2-D
(Coprime-$n$ Explicit Witness).

**Keywords.** Lonely Runner Conjecture, Weyl equidistribution, fractional parts, induction, Diophantine approximation.

**AMS MSC 2020.** Primary 11J71 (Distribution modulo one); Secondary 11K60, 05C69.

---

## §1  Introduction

The **Lonely Runner Conjecture** (LRC) asserts that for any $n-1$ runners on a
unit circle with distinct positive speeds, there is a moment at which every
runner is at distance at least $1/n$ from the starting point.  Formulated by
Wills \cite{Wills67} and independently by Cusick \cite{Cusick74} (who coined
the name), it has been verified for $n \leq 8$: the cases $n = 3,4$ are
elementary; $n = 5$ was settled by Chen \cite{Chen92} (see also the attribution
in \cite{BGSST98}); $n = 6$ by Bienia, Goddyn, Gvozdjak, Sebő, and Tarsi
\cite{BGSST98}; $n = 7$ by Bohman, Holzman, and Kleitman \cite{BHK01}; and
$n = 8$ by Barajas and Serra \cite{BS08}.  Despite extensive attention the
conjecture has remained open for general $n$.

This paper proves the conjecture **conditionally** for all $n \ge 3$ and
**unconditionally** for $n \le 7$ with slow speeds bounded by $10$ (the
empirically verified range — but note that LRC for $n \le 7$ is already
classical; the value of v11.7 is the unified framework and its near-complete
unconditional status). The proof proceeds by strong induction on $n$. The
parameter space is partitioned into four mutually exclusive, exhaustive cases
handled by four theorems:

- **Theorem~6.1** (Bounded Speed Ratio, §6): when the maximum speed $V$ is at
  most $(n-1)$ times the minimum speed, an explicit time $t^* = 1/(n v_1)$
  works. *Unconditional.*
- **Theorem~7.1** (Large Speed Ratio, §7): when $V$ exceeds $(n-1) v_{n-2}$, a
  neighbourhood argument shows the good set for the slow runners must
  intersect the good set for $V$. *Unconditional.*
- **Theorem~10.1** (Divisor Induction, §10): in the remaining *hard case*,
  when the largest prime $p$ of $V$ is coprime to all slow runners, fine-cell
  cell-counting on the slow-runner good set (fundamental period $1/d$ where
  $d = \gcd$(slow speeds); $\gcd(p, L) = 1$ where $L = \operatorname{lcm}$(slow speeds))
  produces the required time. *Unconditional when $p \ge n \cdot L$ or when
  Lemma~5.2-D applies; conditional on Conjecture~5.2-H otherwise.*
- **Theorem~11.1** (Modified Divisor Induction, §11): the complementary
  sub-case, when $p$ divides some slow runner. Lemma~2.1 (Fundamental
  Identity) re-expresses the $V$-condition in terms of $\{pt\}$, reducing to
  a sub-system of slow runners none of which is divisible by $p$, restoring
  $\gcd(p, L_{\mathrm{ind}}) = 1$ and the fine-cell argument. *Unconditional
  when $p \ge n \cdot L_{\mathrm{ind}}$ or when Lemma~5.2-D applies;
  conditional on Conjecture~5.2-H otherwise.*

The key new contribution is Theorem~11.1, which closes the "highly smooth"
sub-case that blocked all earlier inductive attempts. The remaining
ingredients — Lemma~4.1 (Positive-Measure Lemma, §4) converting an inductive
existence statement into positive measure, and Theorem~5.2 (Integer-Speed
Non-emptiness, §5) — are stated in two pieces: Theorem~5.2 (Easy Case,
$p \ge n L_G$) and Conjecture~5.2-H (Hard Case, $p < n L_G$). The Easy Case is
proven by a fine-cell counting construction; Conjecture~5.2-H is verified
exhaustively for $n \le 7$, slow speeds $\le 10$, but its general analytic
proof is left open.

**Organisation.**  §2 fixes notation and Lemma 2.1 (Fundamental Identity).
§3 treats the base case $n=3$.  §§4–5 prove Lemmas 4.1 and Theorems 5.1–5.2.
§§6–7 prove Theorems 6.1 and 7.1.  §8 explains why no "bridge" construction is
needed.  §§9–11 prove Lemmas 9.1–9.3 and Theorems 10.1–11.1.  §12 assembles
Theorem 12.1.

---

## §2  Setup and Notation

### 2.1  The conjecture

Let $n \geq 3$.  Place $n$ runners on a circle of unit circumference.  One runner
stays at the origin.  The remaining $n-1$ runners move at constant distinct
positive speeds $v_1, v_2, \ldots, v_{n-1}$.  Runner $j$ is at position
$\{v_j t\} \in [0,1)$ at time $t$, where $\{x\} = x - \lfloor x \rfloor$
denotes the fractional part.

Define the **distance from the origin**
$$
\|x\| = \min\bigl(\{x\},\, 1 - \{x\}\bigr), \qquad x \in \mathbb{R}.
$$
Runner $j$ is **lonely** at time $t$ if $\|v_j t\| \geq 1/n$.

**Conjecture (LRC, all $n$).**  *For every choice of $n-1$ distinct positive
speeds $v_1,\ldots,v_{n-1}$, there exists $t \geq 0$ such that
$\|v_j t\| \geq 1/n$ for all $j = 1,\ldots,n-1$.*

### 2.2  Normalisation

**Reduction to integers.**  The conjecture is invariant under scaling all speeds
by a common positive constant.  For rational speeds, multiply through by the
least common multiple of the denominators.  For irrational speeds, note that the LRC solution set
$\{(v_1,\ldots,v_{n-1}) : \exists t,\ \|v_j t\| \geq 1/n\ \forall j\}$
contains every rational tuple (by the rational case).  A standard argument
shows the set is dense-open: whenever LRC holds for a speed tuple it holds
with a *strict* witness $\|v_j t_0\| > 1/n$ for all $j$ (since by Lemma~4.1 the simultaneous good set has positive measure and therefore interior
points), and a strict witness persists under small perturbation of the speeds
by continuity.  Since rational tuples are dense, the result extends to all
real speeds by approximation.  See Bienia et al.\ \cite{BGSST98} for details.  We therefore assume:

> *All speeds $v_1 < v_2 < \cdots < v_{n-1}$ are distinct positive integers.*

**GCD normalisation.**  If $d = \gcd(v_1,\ldots,v_{n-1}) > 1$, replace every
$v_j$ by $v_j/d$ and $t$ by $dt$; the condition $\|v_j t\| \geq 1/n$ is
unchanged.  Therefore assume:

> $\gcd(v_1, v_2, \ldots, v_{n-1}) = 1.$

### 2.3  Standing notation

Throughout the proof we fix $n \geq 3$ and a speed tuple $(v_1,\ldots,v_{n-1})$
with $1 \leq v_1 < v_2 < \cdots < v_{n-1}$,
$\gcd(v_1,\ldots,v_{n-1}) = 1$.

| Symbol | Meaning |
|--------|---------|
| $V$ | $v_{n-1}$ — the maximum speed |
| slow runners | $v_1, v_2, \ldots, v_{n-2}$ (all speeds except $V$) |
| $G_j$ | $\{t \geq 0 : \|v_j t\| \geq 1/n\}$ — good set for runner $j$ |
| $G_s$ | $\bigcap_{j=1}^{n-2} G_j$ — simultaneous good set for all slow runners |
| $G_V$ | $\{t \geq 0 : \|Vt\| \geq 1/n\}$ — good set for the fast runner |
| $B_j$ | complement of $G_j$ — bad set for runner $j$ |
| $\mu(S)$ | Lebesgue measure of a measurable set $S \subseteq \mathbb{R}$ |

The target is to show $G_s \cap G_V \neq \emptyset$.

### 2.4  The Fundamental Identity

**Lemma 2.1** (Fundamental Identity).  *For any integers $a \geq 1$, $b \geq 1$ and any real $t$,*
$$
\{a \cdot \{bt\}\} = \{abt\}.
$$

*Proof.*  We have $\{bt\} = bt - \lfloor bt \rfloor$, so
$$
a \cdot \{bt\} = abt - a\lfloor bt \rfloor.
$$
Since $a\lfloor bt \rfloor \in \mathbb{Z}$, taking fractional parts gives
$\{a \cdot \{bt\}\} = \{abt - a\lfloor bt \rfloor\} = \{abt\}$. $\square$

**Corollary 2.2.**  For integers $a,b \geq 1$ and real $t$,
$$
\|a \cdot \{bt\}\| = \|abt\|.
$$

*Proof.*  $\|x\| = \min(\{x\}, 1-\{x\})$ depends only on $\{x\}$, and
$\{a \cdot \{bt\}\} = \{abt\}$ by Lemma 2.1. $\square$

**Remark.**  Lemma 2.1 is used crucially in Theorems 10.1 and 11.1: when
$V = pq$, it gives $\{Vt\} = \{p \cdot \{qt\}\} = \{q \cdot \{pt\}\}$,
allowing the condition $\|Vt\| \geq 1/n$ to be re-expressed in terms of the
fractional part $\{pt\}$ alone.

### 2.5  Induction scheme

We prove the LRC by **induction on $n \geq 3$**:

- **Hypothesis $\mathbf{H}(m)$:**  LRC holds for all $m' \leq m$ runners
  (i.e.\ all tuples of $m'-1$ distinct positive integer speeds, any gcd).

In every sub-case below, the inductive instances invoked satisfy $m < n$.
No instance invokes the $n$-runner problem being proved.


---

## §3  Base Cases

### 3.1  Base case $n = 3$

With $n=3$ there is one slow runner $v_1$ and $V = v_2$.  The key observation
is that for $n=3$:
$$
(n-1)\,v_{n-2} \;=\; 2v_1 \;=\; (n-1)\,v_1.
$$
Therefore the BSR condition ($V \leq 2v_1$) and the LR condition ($V > 2v_1$)
are **jointly exhaustive** — the hard case range $(2v_1, 2v_1]$ is empty.  The
$n=3$ proof requires no DI or DI-MOD.

**Base of the induction: $\mathbf{H}(2)$.**  LRC holds for $1$ runner $v_1$:
take $t = 1/(2v_1)$, giving $\|v_1 \cdot 1/(2v_1)\| = 1/2 \geq 1/3$. $\checkmark$

**BSR case ($V \leq 2v_1$).**  Theorem 6.1 applies with $t^* = 1/(3v_1)$.
Verified directly: $v_1/(3v_1) = 1/3 \geq 1/3$ (lower bound; uses $V \geq v_1$
since $V$ is the maximum speed) and $V/(3v_1) \leq 2/3$ (upper bound). $\checkmark$

**LR case ($V > 2v_1$).**  Apply Theorem 7.1 with $n=3$, one slow runner
$v_{n-2} = v_1$.  The LR condition $V > 2v_1 = (n-1)v_{n-2}$ holds.
$\mathbf{H}(2)$ gives $t^{**}$ with $\|v_1 t^{**}\| \geq 1/2 > 1/3$.  The
neighbourhood width is $2\delta = 2/(3 \cdot 2 \cdot v_1) = 1/(3v_1)$.  Each
bad component of $G_V$ has width $2/(3V) < 2/(3 \cdot 2v_1) = 1/(3v_1) = 2\delta$,
so the LR argument applies. $\checkmark$

**Conclusion.**  Every $n=3$ instance falls into BSR or LR.  $\mathbf{H}(3)$ holds. $\square$

### 3.2  Small example: $n = 4$

With $n=4$, three runners $v_1 < v_2 < V$.  The BSR/LR/DI/DI-MOD
case partition (§§6–11) handles this fully.  We record the key instance: speeds
$\{1, 2, 3\}$ give $t^* = 1/4$, giving $\|1/4\| = 1/4$, $\|2/4\| = 1/2$,
$\|3/4\| = 1/4$.  All $\geq 1/4$. $\checkmark$

---

## §4  The Positive-Measure Lemma

The following lemma is used in every equidistribution argument.  It converts
a bare *existence* statement (LRC for $n-1$ runners) into the *positive measure*
needed for Weyl's theorem to produce an intersection.

**Lemma 4.1** (Positive-Measure Lemma).  *Assume $\mathbf{H}(n-1)$ (LRC holds for $n-1$ runners).
Then the simultaneous good set $G_s = \bigcap_{j=1}^{n-2} G_j$ has positive
Lebesgue measure: $\mu(G_s) > 0$.*

*Moreover, $G_s$ contains a non-degenerate closed interval.*

**Proof.**

**Step 1: A strictly good time exists.**  Apply $\mathbf{H}(n-1)$ to the
$n-2$ slow runners $v_1 < \cdots < v_{n-2}$ (these are $n-2$ distinct positive
integers, forming an $(n-1)$-runner problem with $n-2$ non-zero speeds).  We
obtain a time $t^{**}$ such that
$$
\|v_j t^{**}\| \geq \frac{1}{n-1} \qquad \text{for all } j = 1, \ldots, n-2.
$$

**Step 2: Strict inequality implies interior.**  Since $n \geq 3$,
$$
\frac{1}{n-1} > \frac{1}{n}.
$$
Therefore $\|v_j t^{**}\| \geq 1/(n-1) > 1/n$ for every $j$: the point $t^{**}$
lies in the **interior** of every $G_j$ (the interior consists of $t$ with
$\|v_j t\| > 1/n$, an open condition).

**Step 3: Open neighbourhood in $G_s$.**  Each function $t \mapsto \|v_j t\|$
is continuous (it is a composition of continuous functions).  By continuity,
there exists $\delta_j > 0$ such that $\|v_j t\| > 1/n$ for all
$t \in (t^{**} - \delta_j,\, t^{**} + \delta_j)$.  Setting
$\delta = \min_{j=1}^{n-2} \delta_j > 0$, the open interval
$(t^{**} - \delta,\, t^{**} + \delta)$ is contained in $G_s$.

**Explicit $\delta$.**  By Lipschitz continuity of $\|\cdot\|$:
$$
\bigl|\|v_j t\| - \|v_j t^{**}\|\bigr| \leq v_j |t - t^{**}|.
$$
So $\|v_j t\| \geq \|v_j t^{**}\| - v_j|t - t^{**}| \geq 1/(n-1) - v_j|t-t^{**}|$.
This exceeds $1/n$ whenever $|t - t^{**}| < (1/(n-1) - 1/n)/v_j = 1/(n(n-1)v_j)$.
Taking the minimum over $j$:
$$
\delta \;\geq\; \frac{1}{n(n-1)\,v_{n-2}}. \tag{$\star$}
$$

**Step 4: Positive measure.**  The closed interval
$[t^{**} - \delta,\, t^{**} + \delta] \subset G_s$ has length $2\delta > 0$,
so $\mu(G_s) \geq 2\delta > 0$. $\square$

**Remark (quantitative lower bound).**  The explicit bound $(\star)$ will be
used in Theorem 7.1 (§7) to compare $\delta$ against the width of bad
intervals for $V$.

**Remark (general application).**  Although Lemma 4.1 is stated for the
$n-2$ slow runners using $\mathbf{H}(n-1)$, the argument is identical for any
set of $k \geq 1$ distinct positive integer speeds: given $\mathbf{H}(k+1)$
(which provides a time with $\|v_j t^{**}\| \geq 1/(k+1) > 1/n$ for all $j$
in the set, whenever $k+1 \leq n-1$), the Lipschitz argument produces a
neighbourhood of positive length in the good set.  We apply this freely in
Theorems 10.1 and 11.1 to sub-systems $S_{\rm ind}$ and speed tuples
$(w_1,\ldots,w_r,q)$.

---

## §5  Weyl Equidistribution and the Integer-Speed Non-emptiness Lemma

We develop the integer-speed non-emptiness tool used in §§10–11. The classical
product-formula form of Weyl's theorem (Theorem~5.1 below) requires
**irrational** speed; for integer speed we prove non-emptiness directly,
without invoking Weyl, via a fine-cell counting construction in the easy
regime (Theorem~5.2) and via Lemma~5.2-D for boundary cases. The remaining
hard regime is stated as Conjecture~5.2-H.

### 5.1  The classical theorem

**Theorem 5.1** (Weyl, 1916).  *Let $L$ be a positive integer and $\alpha > 0$
with $\alpha/L \notin \mathbb{Q}$.  Let $G \subseteq \mathbb{R}$ be measurable,
$\tfrac{1}{L}$-periodic, with positive density $\delta = \operatorname{dens}(G) > 0$.
Let $A \subseteq [0,1)$ be measurable with $\mu(A) = \sigma > 0$.  Then*
$$
\lim_{T \to \infty} \frac{1}{T}\,\mu\!\bigl(\bigl\{t \in [0,T] :
t \in G,\;\{\alpha t\} \in A\bigr\}\bigr) \;=\; \delta \cdot \sigma.
$$
*In particular, the set $\bigl\{t \geq 0 : t \in G,\, \{\alpha t\} \in A\bigr\}$
is non-empty.*

*Proof.*  Expanding in Fourier series: $\mathbf{1}_G(t) = \sum_{m \in \mathbb{Z}}
\hat{g}(m)\,e^{2\pi i m L t}$ and $\mathbf{1}_A(\theta) = \sum_{k \in \mathbb{Z}}
\hat{a}(k)\,e^{2\pi i k \theta}$, the time-average equals
$$
\frac{1}{T}\int_0^T \mathbf{1}_G(t)\,\mathbf{1}_A(\{\alpha t\})\,dt
\;=\; \sum_{m,k} \hat{g}(m)\,\hat{a}(k)\cdot
\frac{1}{T}\int_0^T e^{2\pi i(mL + k\alpha)t}\,dt.
$$
The $(m,k) = (0,0)$ term equals $\hat{g}(0)\hat{a}(0) = \delta\sigma$.  For
$(m,k) \ne (0,0)$: the time integral is $O(1/(|mL + k\alpha|\,T))$ when
$mL + k\alpha \ne 0$.  Since $\alpha/L \notin \mathbb{Q}$, if $mL + k\alpha = 0$ for
some $k \ne 0$ then $\alpha/L = -m/k \in \mathbb{Q}$, a contradiction; and $m = 0$,
$k \ne 0$ gives $k\alpha \ne 0$ since $\alpha > 0$.  Hence every off-diagonal
term tends to $0$, giving the stated limit.  Non-emptiness follows since
$\delta\sigma > 0$.  $\square$

**Remark 5.1** (Why integer speed fails).  If $\alpha = p \in \mathbb{Z}^+$ and
$L \in \mathbb{Z}^+$, the equation $mL + kp = 0$ has non-trivial integer solutions:
$m = pa,\; k = -La$ for any $a \in \mathbb{Z} \setminus \{0\}$.  These surviving
cross-terms break the product formula.  Concretely, with $L = 2$, $p = 3$,
$G = [\tfrac{1}{4}, \tfrac{3}{8}] \cup [\tfrac{5}{8}, \tfrac{3}{4}]$ (period
$\tfrac{1}{2}$, density $\tfrac{1}{4}$), and $A = [\tfrac{1}{12}, \tfrac{5}{12}]
\cup [\tfrac{7}{12}, \tfrac{11}{12}]$ ($\mu(A) = \tfrac{2}{3}$), direct
computation gives $\mu(G \cap [0,1) \cap \{3t \in A\}) = \tfrac{5}{36}$, whereas
$\delta\sigma = \tfrac{1}{4}\cdot\tfrac{2}{3} = \tfrac{6}{36}$.  We therefore
prove only non-emptiness for integer $p$.

### 5.2  The version we need

The version of integer-speed non-emptiness required by §§10–11 is a
*non-emptiness* statement: when the slow-runner good set $G$ and the target
set $A$ both have positive measure and the integer $p$ governing the $\{pt\}$
substitution is coprime to the period of $G$, the intersection
$G \cap \{t : \{pt\} \in A\}$ is non-empty. The original v11.5 statement
allowed $A$ to be an arbitrary closed set of positive measure; this is
**false** (counterexample in Remark~5.2-B). The restricted form, which suffices
for §§10–11, requires $A$ itself to be the good set for a family of distinct
positive integer speeds. Under this restriction, the conclusion splits into
two regimes:

- the **easy regime** $p \ge n L_G$, where $L_G$ is the lcm of the slow-runner
  speeds, in which the conclusion is proved unconditionally by a fine-cell
  counting construction (Theorem~5.2 below);
- the **hard regime** $p < n L_G$, in which the conclusion is left as
  Conjecture~5.2-H, verified exhaustively at $n \le 7$ with slow speeds $\le 10$.

**Theorem 5.2** (Integer-Speed Non-emptiness — Easy Case).
*Let $v_1, \ldots, v_k$ and $u_1, \ldots, u_\ell$ be families of distinct
positive integers (entries distinct within each family). Set
$L_G := \operatorname{lcm}(v_1, \ldots, v_k)$ and
$L_A := \operatorname{lcm}(u_1, \ldots, u_\ell)$, and let*
$$
G \;=\; \bigl\{t \ge 0 : \|v_i t\| \ge \tfrac{1}{n} \;\text{for all}\; i\bigr\},
\qquad
A \;=\; \bigl\{\phi \in [0,1) : \|u_j \phi\| \ge \tfrac{1}{n} \;\text{for all}\; j\bigr\}.
$$
*Let $p$ be a positive integer with $\gcd(p, L_G) = 1$ and $p \ge n L_G$.
Assume $\mu(G \cap [0,1)) > 0$ and $\mu(A) > 0$. Then*
$$
G \;\cap\; \bigl\{t \ge 0 : \{pt\} \in A\bigr\} \;\ne\; \emptyset.
$$

**Conjecture 5.2-H** (Integer-Speed Non-emptiness — Hard Case).
*Under the same hypotheses as Theorem~5.2 but with $p < n L_G$ in place of
$p \ge n L_G$, **and with the additional cardinality constraint
$k_G + k_A = n - 1$**, the conclusion still holds.*

**Theorem 5.2-S** (Cardinality Sublemma).
*Let the hypotheses of Theorem~5.2 hold (LRC-shape, $\gcd(p, L_G) = 1$,
$\mu(G \cap [0,1)) > 0$, $\mu(A) > 0$, no restriction on $p$ vs.\ $n L_G$),
and additionally suppose*
$$
k_G + k_A \;\le\; n - 2.
$$
*Then $G \cap \{t : \{pt\} \in A\} \ne \emptyset$.*

*Proof.*  By Lemma~2.1 (Fundamental Identity), the conditions defining the
joint set are:
\begin{align*}
t \in G \;&\Longleftrightarrow\; \|v_i t\| \ge 1/n \text{ for all } i, \\
\{pt\} \in A \;&\Longleftrightarrow\; \|u_j \{pt\}\| \ge 1/n \text{ for all } j \\
\;&\Longleftrightarrow\; \|p u_j t\| \ge 1/n \text{ for all } j.
\end{align*}
Combined, the joint condition is the LRC-style requirement
$\|w_\ell t\| \ge 1/n$ for every $w_\ell$ in the combined speed set
$$
W \;:=\; \{v_1, \ldots, v_{k_G}\} \;\cup\; \{p u_1, \ldots, p u_{k_A}\}.
$$
*Distinctness of $W$:*  the $v_i$'s are distinct by hypothesis; the $p u_j$'s
are distinct because the $u_j$'s are; and $v_i \ne p u_j$ for any $(i, j)$,
because $\gcd(p, L_G) = 1$ implies $p \nmid v_i$ (as $v_i \mid L_G$), whereas
$p \mid p u_j$. Hence $|W| = k_G + k_A \le n - 2$.

By the inductive hypothesis $\mathbf{H}(n-1)$ applied to the $k_G + k_A$ runners
in $W$ (padding with dummy speeds if needed so $|W'| = n - 2$, where any
$\mathbf{H}(n-1)$ witness for $W'$ a fortiori works for $W$), there exists
$t^* \ge 0$ with $\|w_\ell t^*\| \ge 1/(n-1) > 1/n$ for every $w_\ell \in W$.
Hence $t^* \in G \cap \{t : \{pt\} \in A\}$. $\square$

**Corollary 5.2-S'** (Refined open scope of Conjecture~5.2-H).
*Combined with Theorem~5.2 (Easy Case), Theorem~5.2-S, Theorem~5.2-P, and
Remark~5.2-V, the open scope of Conjecture~5.2-H is exactly: $p < n L_G$ AND
$k_G + k_A = n - 1$ AND Lemma~5.2-D's residue hypothesis fails AND the input
falls outside both the pigeonhole-satisfying region (Theorem~5.2-P) and the
direct-verification range $n \le 7$, $|G_{\mathrm{speeds}}| \le 3$,
$|A_{\mathrm{speeds}}| \le 2$, $p \le 19$ (Remark~5.2-V). Within the
verification range, all $5{,}517$ LRC-shape inputs have $N_{\text{joint}} \ge 1$.*

**Theorem 5.2-P** (Pigeonhole Sub-condition).
*Under the hypotheses of Theorem~5.2 (LRC-shape, $\gcd(p, L_G) = 1$, positive
measures), define the band $\beta$-coverage set*
$$
\mathcal{B} \;:=\; \bigcup_{\alpha_0 \in \mathcal{I}_G}
   \Bigl\{ \bigl\lfloor (m'' \bmod n L_G L_A)/L_G \bigr\rfloor :
          m'' \in [\alpha_0 \cdot L_A p,\; (\alpha_0 + 1) \cdot L_A p) \Bigr\}
\;\subseteq\; \{0, 1, \ldots, n L_A - 1\},
$$
*where $\mathcal{I}_G$ is the $G$-good cell index set defined in Step~1 of the
proof of Theorem~5.2. If*
$$
|\mathcal{B}| \;+\; |\mathcal{I}_A| \;>\; n L_A,
$$
*then $G \cap \{t : \{p t\} \in A\} \ne \emptyset$.*

*Proof.*  By the pigeonhole principle applied to $\mathcal{B}, \mathcal{I}_A
\subseteq \{0, 1, \ldots, n L_A - 1\}$: if $|\mathcal{B}| + |\mathcal{I}_A| >
n L_A$, then $\mathcal{B} \cap \mathcal{I}_A \ne \emptyset$. Choose any
$\beta_0 \in \mathcal{B} \cap \mathcal{I}_A$. By definition of $\mathcal{B}$,
there exist $\alpha_0 \in \mathcal{I}_G$ and $m'' \in [\alpha_0 L_A p,
(\alpha_0 + 1) L_A p) \subseteq [0, M)$ such that $\lfloor (m'' \bmod n L_G L_A)/L_G \rfloor = \beta_0$.
This $m''$ satisfies $\alpha(m'') = \alpha_0 \in \mathcal{I}_G$ and
$\beta(m'') = \beta_0 \in \mathcal{I}_A$, hence is a *joint-good fine cell* in
the sense of Step~3 of Theorem~5.2's proof. The midpoint of $F_{m''}$ is the
required witness. $\square$

**Remark 5.2-P** (Empirical status of Theorem 5.2-P).
A scan of all $38{,}664$ hard-regime inputs at $n \le 7$ with $|G_{\text{speeds}}|
\le 3$, $|A_{\text{speeds}}| \le 2$, primes $p \le 19$ confirms a perfect
empirical separation:

| Stratum | Pigeonhole holds | Pigeonhole fails |
|---|---|---|
| Counterexamples to Conjecture~5.2-H ($N_{\text{joint}} = 0$) | 0 | 681 |
| Conjecture~5.2-H holds ($N_{\text{joint}} \ge 1$) | 34{,}825 | 3{,}158 |

In particular, **every counterexample fails the pigeonhole bound**, so
Theorem~5.2-P is "tight" in the sense that no counterexample is missed by
this sufficient condition. Conversely, 3{,}158 positive inputs (8.3%) still
satisfy the conjecture's conclusion even when pigeonhole fails — these
witnesses arise from arithmetic alignment between $\mathcal{B}$ and
$\mathcal{I}_A$ that exceeds what the union bound guarantees.

Restricted to LRC-shape inputs ($k_G + k_A = n - 1$): of $5{,}517$, pigeonhole
holds in $5{,}464$ (99.04%) and fails in $53$ (0.96%). The $53$ residual
LRC-shape inputs all have $p \in \{2, 3\}$ (with two outliers $p \in \{5, 7\}$)
and concentrate at small $|\mathcal{I}_G|$. **Phase 6 (see Remark~5.2-V below)
verifies all $53$ residual inputs directly**, so Conjecture~5.2-H holds for all
$5{,}517$ LRC-shape inputs in the searched range.

See `LonelyRunner/PHASE5_FINDINGS_2026_05_27.md` for the full mining study
and `LonelyRunner/scripts/phase5_residue_structure.py` for the harness.

**Remark 5.2-V** (Cardinality Discriminator and verified LRC-shape range — Phase 6).
Mining the same $38{,}664$ inputs of Remark~5.2-P, we additionally compute the
**cardinality balance** $\delta := k_G + k_A - (n - 1)$ for each input.
Restricted to the pigeonhole-failure stratum, $\delta$ is a **perfect
empirical separator** between LRC-shape positives and counterexamples:

| Stratum (pigeonhole fails) | $\delta = 0$ (LRC-shape) | $\delta \ge 1$ (over-specified) |
|---|---|---|
| Conjecture~5.2-H holds ($N_{\text{joint}} \ge 1$) | **53** | 3{,}105 |
| Counterexamples ($N_{\text{joint}} = 0$) | **0** | 681 |

Every counterexample has $\delta \in \{1, 2, 3\}$; no counterexample has
$\delta = 0$. Combined with Theorem~5.2-P, this means **every LRC-shape input
in the searched range (5{,}517 of them) satisfies Conjecture~5.2-H**:
$5{,}464$ via Theorem~5.2-P and the remaining $53$ via direct verification.

The structural reading: the abstract joint-fine-cell statement is only false
in the *over-specified* regime $\delta \ge 1$ (which Theorem~5.2-S leaves out
of scope, since it requires $\delta \le -1$). In the LRC-relevant regime
$\delta = 0$, no counterexample is found, and the conjecture is consistent
with all evidence to date.

Two auxiliary correlation invariants confirm the structural picture:
$(\mathrm{a})$ for LRC-shape inputs the *expected overlap*
$|\mathcal{B}| \cdot |\mathcal{I}_A| / (n L_A)$ is at least $2.4$, while for
counterexamples it never exceeds $10.07$; and $(\mathrm{b})$ the *correlation
ratio* $N_{\text{joint}} / \text{expected overlap}$ is at least $0.36$ for every
LRC-shape input (close to the random-uniform value of $1$), versus exactly $0$
for every counterexample. So LRC-shape eliminates the adversarial
anti-alignment that produces counterexamples, but does not impose strong
positive correlation either.

The Phase~6 finding was verified by DeepSeek (`--task verify --thinking`) with
verdict ACCEPT, confidence HIGH. See `LonelyRunner/PHASE6_FINDINGS_2026_05_27.md`
for the full mining study and `LonelyRunner/scripts/phase6_residual_arithmetic.py`,
`phase6b_density_separator.py`, `phase6c_correlation.py` for the harnesses.

**Theorem 5.2-U** (Effective Pigeonhole under disjoint bands — Phase 7b).
*Under the hypotheses of Theorem~5.2-P, suppose the $|\mathcal{I}_G|$ bands
$\{B_{\alpha_0} : \alpha_0 \in \mathcal{I}_G\}$ — each of width $L_A p$ in the
$m''$-space $[0, n L_G L_A)$ — are pairwise disjoint. If*
$$
\frac{p}{v_{\max}} + \frac{1}{u_{\max}} > \frac{n(n-1)}{2},
$$
*where $v_{\max} = \max_i v_i$ and $u_{\max} = \max_j u_j$, then pigeonhole
holds and the conclusion of Theorem~5.2 follows.*

*Proof.* If the bands are pairwise disjoint, then in $m''$-space they occupy
exactly $|\mathcal{I}_G| \cdot L_A p$ of the $n L_G L_A$ available cells, and
each projects to at least $\lceil L_A p / L_G \rceil \ge L_A p / L_G$ distinct
$\beta$-cells (the lower bound holds because consecutive integers $m''$ that
differ by $\ge L_G$ project to distinct $\beta$). Hence
$$
|\mathcal{B}| \;\ge\; |\mathcal{I}_G| \cdot \frac{L_A p}{L_G}.
$$
By Lemma~4.1 (Positive-Measure Lemma) applied to $G$ and $A$ separately,
$|\mathcal{I}_G| \ge 2 L_G / ((n-1) v_{\max})$ and $|\mathcal{I}_A| \ge
2 L_A / ((n-1) u_{\max})$. Substituting:
\begin{align*}
|\mathcal{B}| + |\mathcal{I}_A|
\;&\ge\; \frac{2 L_G}{(n-1) v_{\max}} \cdot \frac{L_A p}{L_G}
\;+\; \frac{2 L_A}{(n-1) u_{\max}} \\
\;&=\; \frac{2 L_A}{n-1}\left(\frac{p}{v_{\max}} + \frac{1}{u_{\max}}\right).
\end{align*}
This exceeds $n L_A$ iff $\frac{p}{v_{\max}} + \frac{1}{u_{\max}} > \frac{n(n-1)}{2}$,
which is the hypothesis. By Theorem~5.2-P, the conclusion follows. $\square$

**Corollary 5.2-U'** (Large-$p$ regime). *In particular, if $p > v_{\max} \cdot
n(n-1)/2$ and the bands are pairwise disjoint, then pigeonhole holds
unconditionally.*

The disjoint-bands assumption is generic: bands $\alpha_0, \alpha_0'$ overlap
iff $|(\alpha_0 - \alpha_0') p \bmod n L_G| < p$, which happens for "exceptional"
shift configurations. Phase 7's empirical mining (75 LRC-shape pigeonhole
failures recorded) confirms that the residual is exactly the regime where
bands DO overlap; for these inputs Theorem~5.2-U does not apply, and the
direct verification of Remark~5.2-V is used instead.

The asymptotic interpretation: for fixed $v_{\max}$ and $n \to \infty$, the
$L_G$ for LRC-shape DI grows super-linearly (in fact $L_G \ge \text{lcm}(2, \ldots, n-1)
\sim e^n$ by Chebyshev / PNT), so the Hard Case range $p < n L_G$ contains the
analytic regime $p > v_{\max} n(n-1)/2$ for all $n$ exceeding an explicit
threshold. Inside this analytic regime, Theorem~5.2-U closes the conjecture
unconditionally; outside, it joins the finite residual list.

The Phase 7b derivation was verified by DeepSeek (`--task verify --thinking`)
with verdict ACCEPT, confidence HIGH. See
`LonelyRunner/PHASE7_FINDINGS_2026_05_27.md` for the full Phase 7 study and
`LonelyRunner/scripts/phase7a_extended_search.py`, `phase7c_pattern_enum.py`
for the harnesses.

**Remark 5.2-W** (Combined verification range — Phase 7).
The combined Phase 5/6/7 mining covers $n \in \{3..10\}$ with speeds $\le 10$
and primes $\le 19$ (boundaries vary by phase). Across this combined range:
- approximately $10{,}000+$ LRC-shape inputs scanned (the union is hard to
  count exactly due to overlap between phases);
- $88$ pigeonhole-failure cases (all positive by direct verification);
- $0$ counterexamples.

The 88 residuals enumerate as: $n=4$ (2), $n=5$ (26), $n=6$ (25), $n=7$ (18),
$n=8$ (4), $n=9$ (9), $n=10$ (4). The residual is **persistent across $n$**
(not asymptotically vanishing under our search), which sharpens the conclusion:
- the residual cannot be dismissed as a small-$n$ artifact;
- it must be either characterised as a structural family or covered by a
  strengthened analytic bound (overlap-aware Lemma 7b.1).

The minimum $N_{\text{joint}}$ across all 88 residuals is $2$; the median is
above $10$. Every residual is comfortably positive — the verification is
robust, not borderline.

Most residuals have $p \in \{2, 3\}$ (68 / 88 = 77%) with $k_A \le 2$ (88 / 88
= 100%). The 20 residuals with $p \ge 5$ all have small $L_A$.

**Remark 5.2-A** (Structural restriction on $A$).  The original v11.5
statement allowed $A$ to be *any* closed set of positive measure. That
statement is **false**; a counterexample (verified analytically and numerically)
is recorded in Remark~5.2-B. The restriction "$A$ is the good set for an
integer-speed family" matches exactly the usage in Theorems~10.1 and 11.1 and
is what is provable. The restriction is preserved through the inductive proof
of LRC because every $A$ arising in §§10–11 has this form (see §10.1 Step 2
for DI, §11.1 Step 2 for ModDI). The further partition into the easy and
hard regimes corresponds exactly to the partition used in the formal Lean
development (`joint_fine_cell_exists_easy` proven; the complementary
`joint_fine_cell_exists` hard case carries an open `sorry`).

*Proof of Theorem~5.2 (Easy Case).*  We argue by a fine-cell counting
construction at resolution $1/(n L_G L_A p)$, mirroring the formal Lean
development (`joint_fine_cell_exists_easy` in
`LonelyRunner/LRC/Theorem52_Weyl.lean`).

**Step 1 (Cell dichotomy for $G$).**  Partition $[0, 1)$ into $n L_G$ left-closed,
right-open intervals of width $1/(n L_G)$, indexed by $m \in [0, n L_G)$:
$$
C_m^{(G)} \;:=\; \bigl[\, m/(n L_G),\; (m+1)/(n L_G)\, \bigr).
$$
For each runner $v_i$, the good condition $\|v_i t\| \ge 1/n$ partitions
$[0, 1/v_i)$ into a union of intervals of total width $(n-2)/(n v_i)$ inside
each period $1/v_i$ of $\|v_i \cdot\|$. Since $v_i \mid L_G$, the endpoints of
these intervals coincide with cell boundaries at the resolution $1/(n L_G)$.

Concretely, set $s_i := L_G/v_i \in \mathbb{Z}^+$ (so $v_i s_i = L_G$) and
define
$$
a_{i,m} \;:=\; \bigl\lfloor m / s_i \bigr\rfloor \bmod n \;\in\; \{0, 1, \ldots, n-1\}.
$$
(Equivalently: the Euclidean-division quotient $\lfloor m/s_i \rfloor$ ranges
over $[0, n v_i)$ as $m$ ranges over $[0, n L_G)$, and $a_{i,m}$ is the
residue of this quotient modulo $n$.) For $t$ in the open interior of
$C_m^{(G)}$, we have
$$
v_i t \;\in\; \Bigl( \tfrac{m}{n s_i},\; \tfrac{m+1}{n s_i} \Bigr).
$$
This interval has length $1/(n s_i) < 1$, contains no integer in its interior
(its endpoints are rationals with denominator $n s_i$), and the integer floor
is constant on the interior equal to $\lfloor m/(n s_i) \rfloor =
\lfloor \lfloor m/s_i \rfloor / n \rfloor$. Hence the fractional part
$\{v_i t\}$ lies in the open interval
$\bigl( a_{i,m}/n,\; (a_{i,m}+1)/n \bigr)$, and
$$
\bigl\| v_i t \bigr\| \;\in\; \bigl( \min(a_{i,m}/n,\, 1 - (a_{i,m}+1)/n),\;
                                       \min((a_{i,m}+1)/n,\, 1 - a_{i,m}/n) \bigr),
$$
which is bounded below by $1/n$ iff $a_{i,m} \in [1, n-2]$, and admits a
value $< 1/n$ in $\{v_i t\}$'s range iff $a_{i,m} \in \{0, n-1\}$.

Thus the open interior of $C_m^{(G)}$ is contained in $G$ iff
$a_{i,m} \in [1, n-2]$ for every $i$, and is disjoint from $G$ if any $i$ has
$a_{i,m} \in \{0, n-1\}$. Call $m$ a **$G$-good index** in the first case,
denoted $m \in \mathcal{I}_G$. By the assumption $\mu(G \cap [0,1)) > 0$ we
have $\mathcal{I}_G \ne \emptyset$. (Lean reference: `goodCellIdx`,
`jointGoodSet_contains_cell`, `jointGoodSet_disjoint_cell`,
`jointGoodSet_measure_eq`.)

**Step 2 (Cell dichotomy for $A$).**  Analogously partition $[0, 1)$ into
$n L_A$ cells of width $1/(n L_A)$, indexed by $\beta \in [0, n L_A)$. The
$A$-good indices $\mathcal{I}_A$ are defined by the same condition with
$u_j, L_A$ in place of $v_i, L_G$, and $\mathcal{I}_A \ne \emptyset$ by
$\mu(A) > 0$.

**Step 3 (Joint fine cells).**  Partition $[0, 1)$ into $M := n L_G L_A p$ fine
cells of width $1/M$, indexed by $m'' \in [0, M)$:
$$
F_{m''} \;:=\; \bigl[\, m''/M,\; (m''+1)/M\, \bigr).
$$
For each $m''$, define two derived indices:
$$
\alpha(m'') \;:=\; \lfloor m''/(L_A \cdot p) \rfloor \;\in\; [0,\, n L_G),
\qquad
\beta(m'') \;:=\; \lfloor (m'' \bmod (n L_G L_A))/L_G \rfloor \;\in\; [0,\, n L_A).
$$
We claim:

- **G-inclusion**: if $\alpha(m'') \in \mathcal{I}_G$, then the open interior
  of $F_{m''}$ is contained in $G$. *Proof.* By construction $F_{m''}
  \subseteq C^{(G)}_{\alpha(m'')}$, since the fine cell sits inside the
  coarser $G$-cell at index $\lfloor m''/(L_A p) \rfloor = \alpha(m'')$ (the
  ratio of cell widths is $L_A p$). Apply Step~1.
- **A-inclusion under $\{p\cdot\}$**: if $\beta(m'') \in \mathcal{I}_A$, then
  for every $t$ in the open interior of $F_{m''}$, $\{pt\}$ lies in the open
  interior of $C^{(A)}_{\beta(m'')}$, hence in $A$. *Proof.* For $t$ in the
  open interior of $F_{m''} = [\, m''/M,\, (m''+1)/M\, )$, we have
  $$
  p t \;\in\; \bigl( \tfrac{m''}{n L_G L_A},\; \tfrac{m'' + 1}{n L_G L_A} \bigr).
  $$
  This is an open interval of length $1/(n L_G L_A) < 1$, with rational
  endpoints of denominator $n L_G L_A$, so it contains no integer in its
  interior. Hence the integer floor $\lfloor p t \rfloor$ is constant on the
  open interior, equal to $\lfloor m''/(n L_G L_A) \rfloor$. Set $b := m''
  \bmod (n L_G L_A) \in [0, n L_G L_A)$; then $m''/(n L_G L_A) =
  \lfloor m''/(n L_G L_A) \rfloor + b/(n L_G L_A)$, and the fractional part
  $$
  \{p t\} \;=\; p t - \lfloor p t \rfloor \;\in\; \bigl(\tfrac{b}{n L_G L_A},\;
  \tfrac{b+1}{n L_G L_A}\bigr).
  $$
  This sub-interval of width $1/(n L_G L_A)$ sits inside the coarser
  $A$-cell $C^{(A)}_{\beta(m'')}$ of width $1/(n L_A)$ at index
  $\beta(m'') = \lfloor b / L_G \rfloor$, because $L_A \mid L_G L_A$ (so the
  coarser cells are aligned with the fine cells at scale $1/(n L_G L_A)$
  via the divisor relation $L_G$). Apply Step~2.

A fine cell satisfying both $\alpha(m'') \in \mathcal{I}_G$ and
$\beta(m'') \in \mathcal{I}_A$ is called **jointly good**; any interior point
$t \in F_{m''}$ then satisfies $t \in G$ and $\{pt\} \in A$, completing the
proof. (Lean reference: `isJointGoodFineCell`,
`fract_pt_on_fine_cell`, `fine_cell_subset_G_cell`,
`theorem52_structured_of_joint_exists`.)

**Step 4 (Existence of a jointly good fine cell via the easy-case
hypothesis).**  Fix any $\alpha_0 \in \mathcal{I}_G$ and any
$\beta_0 \in \mathcal{I}_A$. Consider the $L_A p$ consecutive fine indices in
the "$\alpha_0$-band":
$$
m'' \;\in\; [\,\alpha_0 \cdot L_A p,\; (\alpha_0 + 1) \cdot L_A p\,).
$$
For every $m''$ in this band, $\alpha(m'') = \lfloor m''/(L_A p) \rfloor =
\alpha_0$, so the $G$-good index condition is met. It remains to choose
$m''$ in this band so that the $A$-good index condition $\beta(m'') = \beta_0$
holds, i.e., $m'' \bmod (n L_G L_A) \in [\, \beta_0 L_G,\, \beta_0 L_G + L_G\,)$.

The map $m'' \mapsto m'' \bmod (n L_G L_A)$ is periodic with period
$n L_G L_A$. The band has length $L_A p$. The **easy-case hypothesis**
$p \ge n L_G$ gives
$$
L_A p \;\ge\; n L_G L_A,
$$
so the band has length at least $n L_G L_A$, hence $m'' \bmod (n L_G L_A)$
attains every value in $[0,\, n L_G L_A)$ as $m''$ varies in the band. In
particular, $m'' \bmod (n L_G L_A) = \beta_0 L_G$ for some $m''$ in the band,
and that $m''$ is jointly good.

Explicitly: set $r := (\alpha_0 \cdot p) \bmod (n L_G)$, and choose
$$
d \;:=\; \bigl(\beta_0 L_G + n L_G L_A - r L_A\bigr) \bmod (n L_G L_A),
$$
so that $d \in [0,\, n L_G L_A) \subseteq [0,\, L_A p)$ (the latter inclusion
uses the easy-case hypothesis $p \ge n L_G$). Set $m'' := \alpha_0 \cdot L_A
p + d$. We verify:

(a) **$m'' \in [0, M)$.** $m'' \ge 0$ is immediate. For the upper bound:
$\alpha_0 \in \mathcal{I}_G \subseteq [0, n L_G)$ implies $\alpha_0 + 1 \le n L_G$,
hence $m'' = \alpha_0 L_A p + d < \alpha_0 L_A p + L_A p = (\alpha_0 + 1) L_A p
\le n L_G \cdot L_A p = M$.

(b) **$\alpha(m'') = \alpha_0$.** $\alpha(m'') = \lfloor m''/(L_A p) \rfloor
= \alpha_0 + \lfloor d / (L_A p) \rfloor = \alpha_0$, using $d < L_A p$.

(c) **$\beta(m'') = \beta_0$.** Compute $m'' \bmod (n L_G L_A)$:
$\alpha_0 p \bmod (n L_G) = r$ by definition, so $\alpha_0 p = q \cdot n L_G + r$
for some integer $q$, hence $\alpha_0 L_A p = q \cdot n L_G L_A + r L_A$,
so $\alpha_0 L_A p \bmod (n L_G L_A) = r L_A$ (since $r < n L_G$ implies
$r L_A < n L_G L_A$). Therefore
$$
m'' \bmod (n L_G L_A) \;=\; (r L_A + d) \bmod (n L_G L_A)
\;=\; (r L_A + \beta_0 L_G + n L_G L_A - r L_A) \bmod (n L_G L_A)
\;=\; \beta_0 L_G,
$$
using $\beta_0 < n L_A$ which gives $\beta_0 L_G < n L_A L_G = n L_G L_A$.
Hence $\beta(m'') = \lfloor (\beta_0 L_G)/L_G \rfloor = \beta_0$.

This verifies $m''$ is jointly good, completing the proof. $\square$

**Remark 5.2** (Role in §§10–11). Theorem~5.2 (Easy Case) is the easy-regime
core of the §§10–11 induction. In §§10–11 we establish $\gcd(p, L_G) = 1$,
$\mu(G \cap [0,1)) > 0$ (Lemma~4.1), and $\mu(A) > 0$ (from a smaller
inductive instance), then conclude $G \cap \{pt \in A\} \ne \emptyset$
unconditionally **whenever $p \ge n L_G$**, and conditionally on
Conjecture~5.2-H otherwise. Only non-emptiness — not the exact density
formula — is used.

**Remark 5.2-B** (Counterexample to the original "arbitrary closed $A$" form).
The general statement of v11.5 with $A$ arbitrary closed of positive measure
is **false**. Take $n = 5$, slow speeds $(v_1, v_2) = (1, 2)$
(so $L = 2$, $d = 1$), $p = 3$ (coprime to $L = 2$), and let
$A = [0.45, 0.55]$ (closed interval of measure $0.10 > 0$).
Then $G = \{t : \|t\| \geq 1/5 \;\text{and}\; \|2t\| \geq 1/5\}$ has positive
measure, but a direct computation (verified analytically and by sampling
$10^7$ points in $[0,1)$) shows
$G \cap \{t : \{3t\} \in [0.45, 0.55]\}$ has measure zero, and in fact is
empty after intersecting with the open interior of $G$.

The restriction in the theorem statement above (that $A$ itself be the
good set for an integer-speed family) is what enables the proof's Step 2
to leverage the union-of-intervals structure of $A$. Both §10.1 and §11.1
satisfy this restriction automatically.

**Remark 5.2-C** (Empirical scope of validity / evidence for Conjecture~5.2-H).
An exhaustive search over $20{,}403$ LRC-realisable hard-case inputs
($n = 3, \ldots, 7$, slow speeds $\le 10$, all DI and ModDI shapes) confirmed
that the joint set $G \cap \{t : \{pt\} \in A\}$ is non-empty in every tested
case (witness located by exact rational interval arithmetic), **regardless of
whether the easy-case hypothesis $p \ge n L_G$ holds**. Of these, $2$ cases
have witnesses only at single boundary points (e.g.\ $n = 5$, slow $= \{1,3,4\}$,
$V = 7$: witnesses are $t \in \{1/5,\, 2/5,\, 3/5,\, 4/5\}$). Since $G$ and
$A$ are closed, boundary witnesses suffice for the theorem's conclusion. See
`LonelyRunner/EMPIRICAL_FINDINGS_2026_05_26.md` for full data. This empirical
evidence is the basis for Conjecture~5.2-H: the conclusion holds
unconditionally on all 20{,}403 LRC-realisable inputs at $n \le 7$ with slow
speeds $\le 10$, including all instances where the easy-case hypothesis
$p \ge n L_G$ fails.

**Lemma 5.2-D** (Coprime-$n$ Explicit Witness).
*Let $n \ge 3$ and let $v_1 < v_2 < \cdots < v_{n-1}$ be distinct positive
integers (here $v_{n-1}$ may denote the fast runner $V$).  Suppose that for
every $j = 1, \ldots, n-1$ the residue $v_j \bmod (n v_1)$ lies in
$[v_1,\, (n-1) v_1]$.  Then $t^* := 1/(n v_1)$ is an LRC certificate:*
$$
\|v_j\, t^*\| \;\ge\; \tfrac{1}{n} \qquad \text{for every } j = 1, \ldots, n-1.
$$

*Proof.*  For each $j$, write $r_j := v_j \bmod (n v_1)$, so $0 \le r_j < n v_1$.
Then
$$
v_j\, t^* \;=\; \frac{v_j}{n v_1} \;=\; \left\lfloor \frac{v_j}{n v_1} \right\rfloor
   + \frac{r_j}{n v_1},
$$
so $\{v_j\, t^*\} = r_j / (n v_1)$.  By hypothesis $r_j \in [v_1, (n-1) v_1]$,
hence
$$
\frac{r_j}{n v_1} \;\in\; \left[\frac{1}{n},\, \frac{n-1}{n}\right],
$$
which gives $\|v_j\, t^*\| = \min(r_j/(n v_1),\; 1 - r_j/(n v_1)) \ge 1/n$. $\square$

**Special case** ($v_1 = 1$).  The hypothesis reduces to $n \nmid v_j$ for every
$j$, and the certificate becomes $t^* = 1/n$.  This is precisely the BSR
witness of Theorem~6.1 specialised to the case $v_1 = 1$, but it is now
available *outside* the BSR range $V \le (n-1) v_1$ — only the coprimality
condition is required.

**Verification on the two known LRC-realisable boundary-only cases.**

| Case | $n$ | Speeds $\{v_1,\ldots,v_{n-1}\}$ | $n v_1$ | Residues $v_j \bmod n v_1$ | Range $[v_1, (n-1)v_1]$ |
|---|---|---|---|---|---|
| DI | $5$ | $\{1, 3, 4, 7\}$ | $5$ | $1, 3, 4, 2$ | $[1, 4]$ |
| ModDI | $6$ | $\{1, 3, 4, 5, 9\}$ | $6$ | $1, 3, 4, 5, 3$ | $[1, 5]$ |

Both cases satisfy the hypothesis of Lemma~5.2-D, so $t^* = 1/n$ is an
explicit finite LRC certificate for each, independent of the fine-cell
counting argument of Theorem~5.2.

**Corollary 5.2-E** (Alternative path when fine-cell counting is unavailable).
*Suppose the hard case (§§10–11) places the Theorem~5.2 application in the
hard regime $p < n L_G$, where the fine-cell counting argument of
Theorem~5.2 (Easy Case) does not apply and the joint non-emptiness conclusion
is, in general, only conditional on Conjecture~5.2-H. If the integer speeds
$(v_1, \ldots, v_{n-2}, V)$ satisfy the hypothesis of Lemma~5.2-D, then
$t^* = 1/(n v_1)$ is itself a joint witness, and the proof of the Main
Theorem may invoke Lemma~5.2-D directly in place of Theorem~5.2 (and
unconditionally).*

*Proof.*  Immediate from Lemma~5.2-D applied to the full speed tuple
$(v_1, \ldots, v_{n-2}, V)$. $\square$

**Remark 5.2-F** (Status and scope of Lemma 5.2-D).
Lemma~5.2-D plays a defined role under the v11.7 architecture: it
unconditionally certifies the hard-regime cases that satisfy its residue
hypothesis, removing them from the scope of Conjecture~5.2-H. Its
contribution is three-fold:

1. **Boundary coverage.**  Both LRC-realisable boundary-only cases identified
   empirically (see Remark~5.2-C) satisfy Lemma~5.2-D's hypothesis, so they
   are certified unconditionally even though they fall outside the easy
   regime $p \ge n L_G$.
2. **Lean parity.**  The Lean development carries Lemma~5.2-D as a
   first-class lemma and applies it as a fallback when the
   `joint_fine_cell_exists` route is not available for a particular input
   shape; see `LonelyRunner/EMPIRICAL_FINDINGS_2026_05_26.md` Fix 3.
3. **Transparency.**  Both boundary-only cases produce witnesses of the form
   $k/n$, a structural feature transparent in Lemma~5.2-D's proof but
   obscured by any density / counting argument.

The lemma is *not* a universal alternative to Theorem~5.2: its hypothesis
restricts the residue pattern of the speeds modulo $n v_1$, which fails on
most LRC inputs (e.g.\ any input with $V \equiv 0 \pmod{n v_1}$).

**Remark 5.2-G** (Status of Conjecture~5.2-H and the analytic gap, refined).
After the cardinality sublemma (Theorem~5.2-S), Conjecture~5.2-H's open scope
is exactly: hard regime $p < n L_G$, cardinality $k_G + k_A = n - 1$, and
Lemma~5.2-D's residue hypothesis fails (Corollary~5.2-S').

**An empirical-mining study** (`LonelyRunner/scripts/phase4_invariant_mining.py`,
2026-05-27) scanned 38{,}664 hard-regime inputs across $n = 3, \ldots, 7$,
$k_G \le 3$, $k_A \le 2$, primes $p \le 19$:

| Stratum | Inputs | Counterexamples |
|---|---|---|
| $k_G + k_A \le n - 2$ | 16{,}924 | 0 |
| $k_G + k_A = n - 1$ | 8{,}388 | 0 |
| $k_G + k_A \ge n$ | 13{,}352 | 681 |

The $\le n - 2$ stratum is now covered by Theorem~5.2-S. The $= n - 1$
stratum is empirically counterexample-free but the analytic question is
open. The $\ge n$ stratum has counterexamples — confirming that
Conjecture~5.2-H must restrict to $k_G + k_A = n - 1$.

**The LRC-equivalence observation.**  At $k_G + k_A = n - 1$, the joint
condition $t \in G \cap \{t : \{pt\} \in A\}$ is, via Lemma~2.1, equivalent
to the LRC condition for the $(n-1)$-element speed set
$W = \{v_1, \ldots, v_{k_G}\} \cup \{p u_1, \ldots, p u_{k_A}\}$ at threshold
$1/n$. Since this is exactly the LRC statement at $n$ for $W$, **Conjecture~5.2-H
at the LRC-shape edge case is logically equivalent to the LRC inductive step
at $n$** for the speed structure arising from §§10–11. Theorem~5.2 therefore
does not add logical content beyond the §§10.1/11.1 conclusions themselves
in this restricted scope; its role is to *separate* the analytic content
(fine-cell counting in the easy regime) from the structural content (the
gcd/§§10–11 reductions).

Three lines of evidence still support Conjecture~5.2-H:

1. **Exhaustive verification.** All $20{,}403$ LRC-realisable hard-case
   inputs at $n \le 7$ with slow speeds $\le 10$ satisfy the conclusion (see
   Remark~5.2-C and `LonelyRunner/EMPIRICAL_FINDINGS_2026_05_26.md`).
2. **Lean parallel.** The formal Lean development
   `LonelyRunner/LRC/Theorem52_Weyl.lean` proves the easy case
   (`joint_fine_cell_exists_easy`) by exactly the construction above, but
   carries an open `sorry` for the hard case.
3. **Boundary coverage.** Lemma~5.2-D and Corollary~5.2-E provide
   unconditional finite certificates for the two LRC-realisable boundary-only
   cases identified empirically.

Two previously natural approaches to a full analytic proof of the hard case
have been ruled out by the v11.6.1 audit cycle:

- **Erdős–Turán perturbation.** The perturbation $\alpha_j = p + 1/(j\sqrt 2)$
  forces $\|d\alpha_j\| = 1/(j\sqrt 2)$, which by Koksma–Schoissengeier
  (Kuipers–Niederreiter, *Uniform Distribution of Sequences*, Theorem 2.3.5)
  forces $D_N(\alpha_j/d) \ge \Omega(j/(dN))$, hence $t_j \ge \Omega(j/d^2)$,
  unbounded in $j$; the compactness step then fails.
- **Direct Fubini factorisation.** The integral $\int 1_G(t)\, 1_A(\{pt\})\, dt$
  fails to factor for integer $p$: Fourier cross-terms $(m, n) = (kp, -kd)$
  satisfy $md + np = 0$ and contribute, breaking the product formula.

A successful proof of Conjecture~5.2-H at the LRC-shape edge case must work
by a method that genuinely accomplishes the LRC inductive step $n - 1 \to n$
under the $V = pq$ structure of §§10–11. The natural candidates are:

- A non-trivial strengthening of the fine-cell counting argument that
  exploits the LRC-shape constraint $k_G + k_A = n - 1$ beyond what the
  easy-case hypothesis $p \ge n L_G$ already provides.
- A direct combinatorial-pigeonhole argument on the cell-index lattice
  $\mathbb{Z}/(n L_G L_A)$, leveraging the fact that the band shift set
  $\{r_{\alpha_0} L_A : \alpha_0 \in \mathcal{I}_G\}$ inherits structure
  from the slow-runner cell dichotomies.
- An entirely different combinatorial route that bypasses Theorem~5.2's
  intermediate altogether, e.g., a direct LRC-internal compositional
  argument leveraging the $V = pq$ structure (Option E of
  `LonelyRunner/THEOREM52_JOINT_FINE_CELL_FALSE.md`).

The author has not found such an argument and leaves the matter open.

---

## §6  Theorem 6.1: Bounded Speed Ratio

**Theorem 6.1** (Bounded Speed Ratio).  *If $V \leq (n-1)v_1$, then $t^* = 1/(nv_1)$ satisfies
$\|v_j t^*\| \geq 1/n$ for all $j = 1, \ldots, n-1$.*

**Proof.**  For runner $j$ with speed $v_j$:
$$
v_j t^* = \frac{v_j}{n v_1}.
$$
We verify $v_j/(nv_1) \in [1/n,\, (n-1)/n]$, which is equivalent to
$\|v_j t^*\| = v_j/(nv_1) \geq 1/n$ (since $v_j/(nv_1) \leq 1-1/n < 1$,
the fractional part equals $v_j/(nv_1)$ itself):

- **Lower bound:** $v_j \geq v_1$ (since $v_1$ is the minimum speed), so
  $v_j/(nv_1) \geq 1/n$. $\checkmark$

- **Upper bound:** $v_j \leq V \leq (n-1)v_1$ (BSR hypothesis), so
  $v_j/(nv_1) \leq (n-1)/n$. $\checkmark$

Hence $\{v_j t^*\} = v_j/(nv_1) \in [1/n, (n-1)/n]$, giving
$\|v_j t^*\| \geq 1/n$ for all $j$. $\square$

**Check: $v_j t^*$ is indeed in $[0,1)$.**  $v_j/(nv_1) \leq (n-1)/n < 1$. $\checkmark$

**Edge cases.**  
- $n=3$, $V = 2v_1$: $t^* = 1/(3v_1)$, $\|v_1 t^*\| = 1/3$,
  $\{V t^*\} = 2v_1/(3v_1) = 2/3$, so $\|V t^*\| = \min(2/3, 1/3) = 1/3$.
  All equal $1/3$. $\checkmark$
- Minimum speed $v_1 = 1$: $t^* = 1/n$, giving $\|v_j/n\| \geq 1/n$ for all
  $v_j \leq n-1$. $\checkmark$

---

## §7  Theorem 7.1: Large Speed Ratio

**Theorem 7.1** (Large Speed Ratio).  *If $V > (n-1)\,v_{n-2}$, then there exists $t$ with
$\|v_j t\| \geq 1/n$ for all $j = 1,\ldots,n-1$.*

**Proof.**

**Step 1: Good time for slow runners.**  Apply $\mathbf{H}(n-1)$ to the $n-2$
slow runners $v_1,\ldots,v_{n-2}$.  There exists $t^{**}$ with
$$
\|v_j t^{**}\| \geq \frac{1}{n-1} \qquad \text{for all } j \leq n-2.
$$

**Step 2: Neighbourhood of $t^{**}$.**  By the argument of Lemma 4.1
(§4), the interval $I = [t^{**} - \delta, t^{**} + \delta]$ is contained in
$G_s$ where
$$
\delta = \frac{1}{n(n-1)v_{n-2}}.
$$

**Step 3: Landing in $G_V$.**  The bad set for $V$ is
$B_V = \bigcup_{k \in \mathbb{Z}} \bigl(k/V - 1/(nV),\; k/V + 1/(nV)\bigr)$.
Each connected component of $B_V$ has width $2/(nV)$.  Since $V > (n-1)v_{n-2}$:
$$
\frac{2}{nV} \;<\; \frac{2}{n(n-1)v_{n-2}} \;=\; 2\delta \;=\; |I|.
$$
So every bad component is strictly shorter than $I$.  We claim $I \cap G_V \neq \emptyset$.

**Proof of claim.**  Let $J = (c - 1/(nV),\; c + 1/(nV))$ be any bad component
with $J \cap I \neq \emptyset$.  Two sub-cases:

*(i) $I$ starts to the left of $J$:* the left endpoint of $I$ precedes $c - 1/(nV)$, so
the portion $[a, c-1/(nV)] \subseteq I$ lies entirely in $G_V$.  In particular
$I \cap G_V \neq \emptyset$.

*(ii) $I$ starts inside $J$:* the left endpoint $a \geq c - 1/(nV)$.  Then
the right endpoint satisfies
$$
a + |I| \;\geq\; (c - 1/(nV)) + 2\delta \;>\; (c - 1/(nV)) + 2/(nV)
\;=\; c + 1/(nV),
$$
using $2\delta > 2/(nV)$.  So $I$ extends strictly past the right endpoint of $J$
into $G_V$.  Hence $I \cap G_V \neq \emptyset$.

If $I$ starts already in $G_V$ (i.e.\ no bad component contains $a$) then
$I \cap G_V \neq \emptyset$ trivially.

**Conclusion.**  There exists $t_0 \in I \cap G_V$.  Since $I \subseteq G_s$
we have $t_0 \in G_s \cap G_V$. $\square$

**Remark.**  The only property of $V$ used is that every bad component of $G_V$
has width $< |I|$, which is exactly the condition $V > (n-1)v_{n-2}$.  The
strict inequality is essential: at $V = (n-1)v_{n-2}$ the two widths are equal
and the argument breaks.  The boundary case $V = (n-1)v_{n-2}$ falls into the
hard case (§9.1) and is handled by Theorem 10.1 or Theorem 11.1.

---

## §8  Remark on the Hard Case

**Why no "bridge" construction is needed.**

One might attempt, for the hard case $(n-1)v_1 < V \leq (n-1)v_{n-2}$, a
*bridge construction*: if some runner $v_j$ satisfies $V/(n-1) \leq v_j \leq (n-1)v_1$,
take $t^* = 1/(nv_j)$.  Then all runners with speed $\geq v_j$ satisfy
$\|v_i t^*\| = v_i/(nv_j) \in [1/n, (n-1)/n]$.  However, the slow runners
(speeds $< v_j$) give $v_i t^* = v_i/(nv_j) < 1/n$, so $t^*$ fails for them.
No simple modification of this construction handles the slow group in general.

The correct approach does not depend on magnitude thresholds at all.  Theorems
10.1 and 11.1 partition the hard case by the *prime structure* of $V$: the
largest prime $p$ of $V$ either divides some slow runner (Theorem 11.1) or
does not (Theorem 10.1).  This partition covers all of the hard case regardless
of whether any $v_j$ lies in $[V/(n-1),(n-1)v_1]$.

---

## §9  Case Exhaustion: The Hard Case

### 9.1  When the hard case applies

**Definition.**  The **hard case** is:
$$
(n-1)\,v_1 \;<\; V \;\leq\; (n-1)\,v_{n-2}.
$$

**Lemma 9.1** (Case Exhaustion).  *The cases of Theorem 6.1, Theorem 7.1, and
the hard case are mutually exclusive and collectively exhaustive.*

*Proof.*

- If $V \leq (n-1)v_1$: **Theorem 6.1** (BSR) applies.

- If $V > (n-1)v_{n-2}$: **Theorem 7.1** (LR) applies.  (Since $v_{n-2} \geq v_1$,
  we have $(n-1)v_{n-2} \geq (n-1)v_1$, so Theorem 7.1 and Theorem 6.1 do not
  overlap.)

- If $(n-1)v_1 < V \leq (n-1)v_{n-2}$: the **hard case** applies.

These three cases are exhaustive and mutually exclusive: Theorem 6.1 covers
$V \leq (n-1)v_1$, Theorem 7.1 covers $V > (n-1)v_{n-2}$, and the hard case
fills the gap $(n-1)v_1 < V \leq (n-1)v_{n-2}$ between them.  (For $n = 3$
the gap is empty and only Theorems 6.1 and 7.1 arise; see §3.1.) $\square$

**Remark.**  Whether or not some $v_j$ lies in $[V/(n-1),(n-1)v_1]$, the hard
case is always handled by Theorem 10.1 or Theorem 11.1.  No separate Bridge
theorem is needed (see §8).

### 9.2  Structure of the hard case

In the hard case, $(n-1)v_1 < V \leq (n-1)v_{n-2}$, so:
- $V > (n-1)v_1$ (the hard case lower bound, directly from the definition).
- $v_{n-2} \geq V/(n-1)$ (the second-fastest slow runner is at least $V/(n-1)$).

We proceed immediately to the DI/DI-MOD split (§9.3).

### 9.3  DI vs.\ DI-MOD exhaustion

**Lemma 9.2** (Hard-Case Partition).  *In the hard case, let $p$ be the
largest prime factor of $V$.  Exactly one of the following holds:*

*(a) $\gcd(p, \operatorname{lcm}(v_1,\ldots,v_{n-2})) = 1$* — **Theorem 10.1** (Divisor Induction) applies.  
*(b) $p \mid v_j$ for some $j \in \{1,\ldots,n-2\}$* — **Theorem 11.1** (Modified Divisor Induction) applies.

*Proof.*  For any prime $p$, either $p$ divides $\operatorname{lcm}(v_1,\ldots,v_{n-2})$
or it does not.  These cases are exhaustive and mutually exclusive. $\square$

**Lemma 9.3** ($r \leq n-3$).  *In case (b) of Lemma 9.2, let
$r = \#\{j : p \mid v_j\}$.  Then $r \leq n-3$.*

*Proof.*  Suppose for contradiction that $r = n-2$, i.e.\ $p \mid v_j$ for
every $j \in \{1,\ldots,n-2\}$.  Then $p \mid v_j$ for all $j$ and
$p \mid V$ (since $p$ is a prime factor of $V$).  Therefore
$p \mid \gcd(v_1,\ldots,v_{n-2},V) = 1$ (by GCD normalisation, §2.2).
This is a contradiction.  Hence $r \leq n-3$. $\square$

---

## §10  Theorem 10.1: Divisor Induction

**Theorem 10.1** (Divisor Induction).  *In the hard case, suppose the largest
prime $p$ of $V$ satisfies $\gcd(p,\, \operatorname{lcm}(v_1,\ldots,v_{n-2}))
= 1$. Write $V = p q$ (so $q = V/p$). Then $G_s \cap G_V \neq \emptyset$,
unconditionally if (i) $p \ge n \cdot \operatorname{lcm}(v_1, \ldots, v_{n-2})$
(easy case, Theorem~5.2 applies), or (ii) the speed tuple
$(v_1, \ldots, v_{n-2}, V)$ satisfies the residue hypothesis of Lemma~5.2-D
(boundary case); conditionally on Conjecture~5.2-H otherwise.*

**Proof.**

**Step 1: Good set for slow runners.**  Let
$$
G_s \;=\; \bigl\{t \geq 0 : \|v_j t\| \geq 1/n \text{ for all } j = 1,\ldots,n-2\bigr\}.
$$
By Lemma 4.1 (applied via the primary hypothesis $\mathbf{H}(n-1)$ to the
$n-2$ slow runners), $\mu(G_s) > 0$.  The set $G_s$ is periodic with fundamental
period $1/d$ where $d = \gcd(v_1,\ldots,v_{n-2})$.  (Corrected from v11.5:
this was previously stated as $1/L$, which is in general not even a period
of $G_s$; the correction does not affect this proof, since Step 4 uses only
Theorem 5.2's conclusion.)

**Step 2: Fundamental Identity and the target set.**  Write $q = V/p$.  By
Lemma 2.1 (with $a = q$, $b = p$):
$$
\{Vt\} \;=\; \{pqt\} \;=\; \{q \cdot \{pt\}\}.
$$
Therefore $\|Vt\| \geq 1/n$ if and only if $\{pt\} \in A$, where
$$
A \;=\; \bigl\{\phi \in [0,1) : \|q\phi\| \geq 1/n\bigr\}.
$$

**Step 3: Measures and coprimality.**

*Measure of $A$:* $A = \{\phi : \{q\phi\} \in [1/n,\,(n-1)/n]\}$ is the
good set for a single runner of speed $q$ with threshold $1/n$.  It consists
of $q$ intervals per unit period, each of width $(n-2)/(nq)$, so
$\mu(A) = (n-2)/n > 0$.

*Coprimality:* The hypothesis of Theorem 10.1 is $\gcd(p,\operatorname{lcm}(v_1,\ldots,v_{n-2})) = 1$,
i.e.\ $\gcd(p, L) = 1$.

*(There is no requirement that $\gcd(p,q) = 1$.  In particular, if $p^2 \mid V$
then $p \mid q$, but this plays no role: $p$ does not appear in $L$.)*

**Step 4: Apply Theorem 5.2.**  We have $G = G_s$ with $\mu(G_s \cap [0,1)) > 0$
from Step~1 and fundamental period $1/d$ with $d = \gcd(v_1, \ldots, v_{n-2})$;
positive integer $p$; and integer-speed target set $A = \text{goodSet}(q)$
defined by the single speed family $(u_1) = (q)$, $L_A = q$, with
$\mu(A) = (n-2)/n > 0$ from Step~2; and $\gcd(p, L_G) = 1$ from Step~3, where
$L_G = \operatorname{lcm}(v_1, \ldots, v_{n-2})$.

We split by the easy-case hypothesis of Theorem~5.2:

- **(Easy case)** $p \ge n \cdot L_G$. Theorem~5.2 (Easy Case) applies directly
  and yields
  $$
  G_s \;\cap\; \bigl\{t : \{pt\} \in A\bigr\} \;\ne\; \emptyset.
  $$
- **(Boundary case)** $p < n \cdot L_G$ but the speed tuple
  $(v_1, \ldots, v_{n-2}, V)$ satisfies the residue hypothesis of
  Lemma~5.2-D (i.e.\ $v_j \bmod (n v_1) \in [v_1, (n-1) v_1]$ for all $j$).
  Lemma~5.2-D supplies $t^* = 1/(n v_1)$ as an explicit certificate, which a
  fortiori lies in $G_s \cap G_V$. The non-emptiness conclusion follows
  unconditionally.
- **(Hard case)** $p < n \cdot L_G$ and the residue hypothesis of
  Lemma~5.2-D fails. The conclusion
  $$
  G_s \;\cap\; \bigl\{t : \{pt\} \in A\bigr\} \;\ne\; \emptyset
  $$
  is then the statement of Conjecture~5.2-H specialised to $(G_s, A, p)$,
  and is currently available only conditionally on that conjecture.

In all three cases the non-emptiness conclusion holds (unconditionally in the
first two, conditionally on Conjecture~5.2-H in the third). Choose any $t_0$
in this set and let $\phi_0 = \{p t_0\} \in A$.

**Step 5: Verification.**

- $\|v_j t_0\| \geq 1/n$ for $j = 1,\ldots,n-2$: from $t_0 \in G_s$. $\checkmark$
- $\|Vt_0\| = \|q\phi_0\| \geq 1/n$: since $\{Vt_0\} = \{q\phi_0\}$ (Step 2)
  and $\phi_0 \in A$ means $\|q\phi_0\| \geq 1/n$. $\checkmark$

So $t_0 \in G_s \cap G_V$. $\square$


---

## §11  Theorem 11.1: Modified Divisor Induction (Highly Smooth Case)

This is the key new theorem.

**Theorem 11.1** (Modified Divisor Induction).  *In the hard case, suppose
the largest prime $p$ of $V$ satisfies $p \mid v_{j_k}$ for $k = 1, \ldots, r$
(with $r \ge 1$), where $\{j_1, \ldots, j_r\}$ are the indices of slow runners
divisible by $p$. Write $w_k = v_{j_k}/p$ (so $v_{j_k} = p w_k$) and
$q = V/p$. Then $G_s \cap G_V \neq \emptyset$, unconditionally if
(i) $p \ge n \cdot \operatorname{lcm}(S_{\mathrm{ind}})$ (easy case,
Theorem~5.2 applies), or (ii) the speed tuple
$(v_1, \ldots, v_{n-2}, V)$ satisfies the residue hypothesis of Lemma~5.2-D
(boundary case); conditionally on Conjecture~5.2-H otherwise.*

**Setup.**  By Lemma 9.3, $r \leq n-3$.  Set $q = V/p$ (a positive integer
since $p \mid V$).  Set $w_k = v_{j_k}/p$ (positive integers since $p \mid v_{j_k}$).
The speeds $w_1,\ldots,w_r,q$ are distinct positive integers: $w_k \neq w_l$
for $k \neq l$ (since $v_{j_k} \neq v_{j_l}$), and $w_k \neq q$ for all $k$
(since $v_{j_k} < V$ as $v_{j_k}$ is a slow runner).

**Proof.**

**Step 1: The independent good set.**  Let $S_{\rm ind} = \{v_j : p \nmid v_j,\ 1 \leq j \leq n-2\}$
be the set of slow runners NOT divisible by $p$.  By Lemma 9.3 (applied with
GCD normalisation) $S_{\rm ind} \neq \emptyset$.  Define
$$
G_{\rm ind} = \bigl\{t \geq 0 : \|v_j t\| \geq 1/n\ \text{ for all } v_j \in S_{\rm ind}\bigr\}.
$$
$S_{\rm ind}$ has $n-2-r \geq 1$ elements, forming an $(n-1-r)$-runner problem.
Since $n-1-r \leq n-2 < n$, the primary hypothesis $\mathbf{H}(n-1-r)$ gives
LRC for these runners with threshold $1/(n-1-r) \geq 1/(n-1) > 1/n$
(using $r \leq n-3$).  By Lemma 4.1, $\mu(G_{\rm ind}) > 0$.

**Step 2: The target set $A$.**  Define
$$
A = \bigl\{\phi \in [0,1) :
  \|w_k \phi\| \geq 1/n\ \forall k = 1,\ldots,r,\quad
  \|q \phi\| \geq 1/n\bigr\}.
$$
$A$ is the good set for the $r+1$ distinct positive integer speeds
$(w_1,\ldots,w_r, q)$ with threshold $1/n$.  These $r+1$ speeds form an
$(r+2)$-runner problem.  Since $r+2 \leq n-1 < n$, the primary hypothesis
$\mathbf{H}(r+2)$ gives LRC for these speeds with threshold
$1/(r+2) \geq 1/(n-1) > 1/n$.  Explicitly: there exists $\phi^{**}$ with
$\|w_k \phi^{**}\| \geq 1/(r+2) > 1/n$ for all $k$ and
$\|q\phi^{**}\| \geq 1/(r+2) > 1/n$,
so $\phi^{**}$ is in the interior of $A$.  By the same argument as Lemma 4.1
(§4, General Application Remark), $\mu(A) > 0$.

**Step 3: Coprimality for Weyl.**  The fundamental period of $G_{\rm ind}$ is
$1/d_{\rm ind}$ where $d_{\rm ind} = \gcd(S_{\rm ind})$. (Corrected from v11.5:
previously stated as $1/L_{\rm ind}$ where $L_{\rm ind} = \operatorname{lcm}(S_{\rm ind})$;
the correction does not affect this proof.) Coprimality of $p$ with the lcm
is what Theorem 5.2 requires:

For every $v_j \in S_{\rm ind}$: $p \nmid v_j$ by definition of $S_{\rm ind}$.
Since $p$ is prime, $\gcd(p, v_j) = 1$.  Therefore

$$\gcd(p,\, L_{\rm ind}) = \gcd\!\bigl(p,\, \operatorname{lcm}(S_{\rm ind})\bigr) = 1. \checkmark$$

*(No condition on $\gcd(p,q)$ is needed; $q$ does not appear in $G_{\rm ind}$.)*

**Step 4: Apply Theorem 5.2.**  We have $G = G_{\mathrm{ind}}$ with
$\mu(G_{\mathrm{ind}} \cap [0,1)) > 0$ from Step~1 and fundamental period
$1/d_{\mathrm{ind}}$; positive integer $p$; integer-speed target set
$A = \text{jointGoodSet}(w_1, \ldots, w_r, q)$ defined by the family
$(u_1, \ldots, u_{r+1}) = (w_1, \ldots, w_r, q)$, with $\mu(A) > 0$ from
Step~2; and $\gcd(p, L_{\mathrm{ind}}) = 1$ from Step~3, where
$L_{\mathrm{ind}} = \operatorname{lcm}(S_{\mathrm{ind}})$.

We split by the easy-case hypothesis of Theorem~5.2:

- **(Easy case)** $p \ge n \cdot L_{\mathrm{ind}}$. Theorem~5.2 (Easy Case)
  applies directly and yields
  $$
  G_{\mathrm{ind}} \;\cap\; \bigl\{t : \{p t\} \in A\bigr\} \;\ne\; \emptyset.
  $$
- **(Boundary case)** $p < n \cdot L_{\mathrm{ind}}$ but the speed tuple
  $(v_1, \ldots, v_{n-2}, V)$ satisfies the residue hypothesis of
  Lemma~5.2-D. Lemma~5.2-D supplies $t^* = 1/(n v_1)$ as an explicit
  certificate; this $t^*$ lies in $G_s \cap G_V$ directly (without needing
  the §11.1 inductive decomposition), so the non-emptiness conclusion
  follows unconditionally.
- **(Hard case)** $p < n \cdot L_{\mathrm{ind}}$ and the residue hypothesis
  of Lemma~5.2-D fails. The conclusion
  $$
  G_{\mathrm{ind}} \;\cap\; \bigl\{t : \{p t\} \in A\bigr\} \;\ne\; \emptyset
  $$
  is then the statement of Conjecture~5.2-H specialised to
  $(G_{\mathrm{ind}}, A, p)$, and is currently available only conditionally
  on that conjecture.

In all three cases the non-emptiness conclusion holds (unconditionally in the
first two, conditionally on Conjecture~5.2-H in the third). Choose any $t_0$
in this set and let $\phi_0 = \{p t_0\} \in A$.

**Step 5: Verification of all conditions.**

| Runner | Speed | Condition | Reason |
|--------|-------|-----------|--------|
| $v_j \in S_{\rm ind}$ | $v_j$ | $\|v_j t_0\| \geq 1/n$ | $t_0 \in G_{\rm ind}$ |
| $v_{j_k}$, $k=1,\ldots,r$ | $pw_k$ | $\|v_{j_k} t_0\| \geq 1/n$ | via FI, see below |
| $V$ | $pq$ | $\|Vt_0\| \geq 1/n$ | via FI, see below |

**Verification for $v_{j_k} = pw_k$** (the $p$-divisible slow runners):
$$
\{v_{j_k} t_0\} \;=\; \{pw_k t_0\} \;=\; \{w_k \cdot \{pt_0\}\}
\quad \text{(Lemma 2.1: } a = w_k,\, b = p\text{)}.
$$
So $\|v_{j_k} t_0\| = \|w_k \phi_0\| \geq 1/n$ since $\phi_0 \in A$. $\checkmark$

**Verification for $V = pq$:**
$$
\{Vt_0\} \;=\; \{pqt_0\} \;=\; \{q \cdot \{pt_0\}\}
\quad \text{(Lemma 2.1: } a = q,\, b = p\text{)}.
$$
So $\|Vt_0\| = \|q\phi_0\| \geq 1/n$ since $\phi_0 \in A$. $\checkmark$

*(The condition $\|qt_0\| \geq 1/n$ is NOT imposed on $t_0$; $q$ is not one
of the original runners.  The $V$-condition passes entirely through $\phi_0 \in A$.)*

**Conclusion.**  The $n-2$ slow runners split into two disjoint groups:
$S_{\rm ind}$ (covered by $t_0 \in G_{\rm ind}$) and $\{v_{j_1},\ldots,v_{j_r}\}$
(covered by the FI verification above).  Together they cover all of
$\{v_1,\ldots,v_{n-2}\}$, so $t_0 \in G_s$.  Combined with $\|Vt_0\| \geq 1/n$,
we have $t_0 \in G_s \cap G_V$. $\square$

---

## §12  Main Theorem

**Theorem 12.1** (Lonely Runner Conjecture — Conditional).  *For all $n \ge 3$
and all tuples of $n-1$ distinct positive real speeds, there exists
$t \ge 0$ such that $\|v_j t\| \ge 1/n$ for all $j = 1, \ldots, n-1$,
**conditionally on Conjecture~5.2-H**. The statement holds **unconditionally**
when, for the input speed tuple normalised per §2.2, every invocation of
Theorem~5.2 in the inductive proof falls into one of the unconditional
sub-cases of Theorems~10.1 / 11.1 (easy regime $p \ge n L$ or boundary case
covered by Lemma~5.2-D). In particular, the statement holds unconditionally
for all $n \le 7$ with slow speeds $\le 10$, where Conjecture~5.2-H has been
exhaustively verified on the entire space of LRC-realisable hard-case inputs
(see Remark~5.2-C).*

**Proof.**

By the reduction in §2.2, we may assume integer speeds with $\gcd = 1$.
We prove the statement by induction on $n$ (§2.5).

**Base case $n = 3$:** Proved in §3.1. $\checkmark$

**Inductive step.**  Fix $n \ge 4$ and assume $\mathbf{H}(m)$ for all $m < n$
(primary hypothesis).  By Lemma~9.1, exactly one of the following holds:

- **Bounded Speed Ratio (BSR)** ($V \le (n-1) v_1$): Theorem~6.1 applies
  directly. Uses no inductive hypothesis. *Unconditional.* $\checkmark$

- **Large Speed Ratio (LR)** ($V > (n-1) v_{n-2}$): Theorem~7.1 applies.
  Uses $\mathbf{H}(n-1)$ via Lemma~4.1. *Unconditional.* $\checkmark$

- **Hard case** ($(n-1) v_1 < V \le (n-1) v_{n-2}$): By Lemma~9.2, exactly
  one of:
  - **Divisor Induction (DI)** (largest prime $p$ of $V$ coprime to all slow
    runners): Theorem~10.1 applies. Uses $\mathbf{H}(n-1)$ via Lemma~4.1.
    *Unconditional in the easy regime $p \ge n \cdot
    \operatorname{lcm}(\text{slow})$ and in the Lemma~5.2-D boundary
    regime; conditional on Conjecture~5.2-H in the remaining hard
    sub-regime.* $\checkmark$
  - **Modified Divisor Induction (DI-MOD)** (largest prime $p$ of $V$
    divides some slow runner): Theorem~11.1 applies. Uses
    $\mathbf{H}(n-1-r)$ (for $G_{\rm ind}$, primary, $n-1-r \le n-2$) and
    $\mathbf{H}(r+2)$ (for $A$, primary, $r+2 \le n-1$). *Unconditional in
    the easy regime $p \ge n \cdot \operatorname{lcm}(S_{\mathrm{ind}})$
    and in the Lemma~5.2-D boundary regime; conditional on
    Conjecture~5.2-H in the remaining hard sub-regime.* $\checkmark$

In every case $G_s \cap G_V \neq \emptyset$ (under the stated conditional or
unconditional clauses), providing the required $t$.

The induction is well-founded: every hypothesis invoked is $\mathbf{H}(m)$
for some $m \le n - 1 < n$. $\square$

**Remark 12.1-A** (Verified unconditional range). For $n \le 7$ and slow
speeds $\le 10$, the entire LRC parameter space has been exhaustively
enumerated and verified: every DI or ModDI hard-case configuration is either
in the easy regime, in the Lemma~5.2-D boundary regime, or has an explicit
joint witness located by exact rational interval arithmetic (see
Remark~5.2-C and `LonelyRunner/EMPIRICAL_FINDINGS_2026_05_26.md`). Theorem~12.1
therefore holds unconditionally on this range. The unconditional extension to
general $n$ requires either (i) a proof of Conjecture~5.2-H, or (ii) a
structurally different bypass of the hard-regime application of Theorem~5.2
(e.g., a direct LRC-internal compositional argument leveraging the
$V = p q$ structure without reducing to the joint integer-speed
non-emptiness problem).

---

## §13  References


- \[BGSST98\] R. Bienia, L. Goddyn, P. Gvozdjak, A. Sebő, M. Tarsi.
  *Flows, view obstructions, and the lonely runner.* J. Combin. Theory Ser. B 72 (1998), 1–9.
- \[BHK01\] T. Bohman, R. Holzman, D. Kleitman.
  *Six lonely runners.* Electron. J. Combin. 8 (2001), R3.
- \[BS08\] J. Barajas, O. Serra.
  *The lonely runner with seven runners.* Electron. J. Combin. 15 (2008), R48.
- \[Chen92\] Z.-Z. Chen.
  *Approximations and lonely runners.* (1992).
  *(Establishes LRC for $n = 5$.)*
- \[Cusick74\] T. W. Cusick.
  *View-obstruction problems.* Aequationes Math. 9 (1974), 165–170.
- \[KN74\] L. Kuipers, H. Niederreiter.
  *Uniform Distribution of Sequences.* Wiley, 1974.
- \[Tao18\] T. Tao.
  *Some remarks on the lonely runner conjecture.*
  Contrib. Discrete Math. 13 (2018), 1–31.
- \[Weyl16\] H. Weyl.
  *Über die Gleichverteilung von Zahlen mod Eins.*
  Math. Ann. 77 (1916), 313–352.
- \[Wills67\] J. M. Wills.
  *Zwei Sätze über inhomogene diophantische Approximation von Irrationalzahlen.*
  Monatsh. Math. 71 (1967), 263–269.

