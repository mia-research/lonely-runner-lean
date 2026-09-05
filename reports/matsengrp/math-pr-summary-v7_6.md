# Math PR Summary: LRC Proof v7.6

**Tool:** math-pr-summarizer
**Source file:** `lrc_proof_v7_6_preprint.md`
**Author:** Trent Palelei, MI Research Foundation
**Version:** v7.6, March 2026
**Summary prepared:** 2026-03-14

---

## 1. Main Theorem

**Theorem A (Lonely Runner Conjecture).** *For all $n \geq 3$ and all tuples $E = (e_1, \ldots, e_{n-1})$ of distinct positive integers with $\gcd(E) = 1$:*
$$x_0(E) \geq 1,$$
*i.e., there exists $t \in \mathbb{R}$ such that $\|e_i t\|_{\mathbb{R}/\mathbb{Z}} \geq 1/n$ for all $i = 1,\ldots,n-1$.*

**Arithmetic formulation.** Set $L = \mathrm{lcm}(E)$, $N = nL$. The safe-point count is
$$x_0(E) = \#\bigl\{k \in \{1,\ldots,N-1\} : (e_i k \bmod N) \in [L,\,(n-1)L]\ \forall i\bigr\}.$$
The condition $x_0(E) > 0$ is equivalent to the LRC for the tuple $E$.

**Quantitative bound.** The stronger bound $x_0(E) \geq \varphi(n)$ is established on the following branches:

| Branch | Bound | Method |
|---|---|---|
| Case 1 (no divisible runner) | $x_0 \geq \varphi(n)$ | Theorem 4.1, analytic |
| Prime $n$ | $x_0 \geq \varphi(n)$ | Proposition 10.5, analytic + certified |
| Composite $n$, dropped unit | $x_0 \geq \varphi(n)$ | Proposition 11.3, analytic + certified |
| Composite $n$, dropped two non-units, multi-prime | $B_{\rm safe} \geq \varphi(n)(n-2)/2$ | Theorem 9.3b, analytic |
| Composite $n$, dropped two non-units, $n=p^k$ | $B_{\rm safe} \geq \varphi(n)(n-2)/2$ | Theorem 9.3f, analytic |

---

## 2. Proof Architecture

### 2.1 Top-Level Case Partition

The proof partitions all speed tuples $E$ at the highest level by whether any speed is divisible by $n$. Define $E_{\rm div} = \{e \in E : n \mid e\}$ and $E_{\rm non} = E \setminus E_{\rm div}$.

- **Case 1** ($E_{\rm div} = \emptyset$): Handled by direct arithmetic witnesses (§4). The $\varphi(n)$ witness times $W = \{jL : 1 \leq j \leq n-1,\, \gcd(j,n)=1\}$ are all safe.

- **Case 2** ($E_{\rm div} \neq \emptyset$): The main combinatorial content. Subdivided as below.

- **Irrational speeds** (§3): If speeds are not all rationally commensurate, Weyl equidistribution on $\mathbb{T}^r$ settles the conjecture without the case analysis.

### 2.2 Case 2 Sub-structure

The Case 2 analysis operates over the **divisible-fibre interval**
$$B_{\rm div} = \{b \in \mathbb{Z} : L/n \leq b \leq (n-1)L/n\},\quad |B_{\rm div}| = (n-2)L/n+1.$$
A fibre $b$ is **safe** if $\bigcup_i \mathrm{bad}(e_i, t_i(b), n) \neq \mathbb{Z}/n\mathbb{Z}$.

The sub-partitioning is:

```
Case 2
├── Small base cases (L ∈ {n, 2n}): Proposition 5.1
├── Prime n
│   ├── |E_div| = 1: Lemma 7.1 + Proposition 10.5
│   └── |E_div| ≥ 2: Theorems 8.2, 8.3
└── Composite n (n ≥ 4)
    ├── |E_div| = 1
    │   ├── Some dropped runner is a unit: Lemma 5.2 + Proposition 11.3
    │   └── Both dropped runners non-units (Unit-Complete)
    │       ├── n even (Sub-case B1): floor-0 unit coverage gap
    │       ├── n odd, ≥ 2 prime factors (Sub-case B2): Theorems 9.2c + 9.3b
    │       └── n = p^k, k ≥ 2 (Sub-case B3): Theorems 9.2c + 9.3f
    └── |E_div| ≥ 2: Unit-Complete by Lemma 9.4 → Theorem 12.1
```

### 2.3 The Coverage Insufficiency Principle

The unifying conceptual argument (§2) is the **Coverage Insufficiency Principle**: the aggregate coverage function
$$\mathrm{ACapacity}(r, b) = \#\{e \in E_{\rm non} : r \in \mathrm{bad}(e, \lfloor eb/L \rfloor, n)\}$$
cannot satisfy $\mathrm{ACapacity}(r, b) \geq 1$ for all $r \in \mathbb{Z}/n\mathbb{Z}$ simultaneously at every $b \in B_{\rm div}$. This manifests via four failure modes:

1. **Unit dropout (static):** A missing unit $d$ exposes its sole-covered residue $r_d = -d^{-1} \bmod n$ on the interval $I_d = [L/n, L/(n-1))$.
2. **Floor-reset handoff failure:** At a floor-reset event, both Coverage Gates CG1 and CG2 fail to provide a covering unit, leaving the departing residue uncovered.
3. **Transparency:** Non-unit runners with $\gcd(e,n) \geq 3$ have empty bad sets on a positive fraction $(g-2)/g$ of floor states.
4. **Misalignment (prime-power):** Level-$(k-1)$ residues in $\mathbb{Z}_{p^k}$ can only be covered at dangerous floors, which are sparsely distributed.

---

## 3. Novel Methods (Top 5)

**1. The Sole Cover Bijection (§5.3)**

The inversion map $e \mapsto -e^{-1} \bmod n$ is a bijection on the $\varphi(n)$ units of $\mathbb{Z}_n$. For each unit $e$, the residue $r_e = -e^{-1} \bmod n$ is covered *exclusively* by runner $e$ throughout the floor-0 interval $I_0 = [L/n, L/(n-1))$. This is because at floor state $t=0$, the bad set of any unit $e'$ is $\{0, -e'^{-1}\}$, so $r_e$ can only be covered by $e' = e$. Removing a unit runner $d$ from the speed set thereby permanently exposes its uniquely owned residue $r_d$ on the entire interval $I_d$, yielding an explicit safe-fibre certificate.

**2. Dropped-Runner Targeting (Theorem 9.2c, §9.2c)**

For composite $n$ with a missing non-unit $d = au$ (where $a$ is composed entirely of primes dividing $n$ and $\gcd(u,n)=1$), the proof constructs a specific unit $e_u = n - u$ and a specific floor-reset index
$$m = \bigl(-nd^{-1} \bmod e_u\bigr) + 1 \in \{2,\ldots,e_u-1\}$$
such that: (i) there are no CG1 coverers at the $m$-th floor-reset event of $e_u$ (because $m-1$ is invertible mod $e_u$, making the CG1 congruence $e(m-1) \equiv 0 \pmod{e_u}$ impossible for $0 < e < e_u$), and (ii) the unique CG2 solution is exactly $d$. Since $d$ is absent, the departing residue $r_{\rm dep} = -(m-1)e_u^{-1} \bmod n$ is uncovered. This targeting construction — locating a specific floor-reset event with algebraically provable coverage failure — is a key innovation that handles all composite Unit-Complete branches uniformly.

**3. Coverage Gates CG1/CG2 (Lemma 9.2a, §9.2a)**

At a floor-reset event $b_m = mL/e_u$ for unit $e_u$, the floor of any other unit runner $e'$ is $t_{e'} = (e'm - s)/e_u$ where $s = e'm \bmod e_u$. The precise condition for $e'$ to cover the departing residue $r_{\rm dep} = -(m-1)e_u^{-1} \bmod n$ reduces to exactly two arithmetic gates:
- **CG1:** $e'm \bmod e_u = e'$ (requires $e' < e_u$),
- **CG2:** $e'+e_u \geq n$ and $e'm \bmod e_u = e'+e_u-n$.

This two-gate characterization of coverage transfer at floor transitions is new. It converts a coverage question into a purely arithmetic one and enables the targeted construction of uncovered moments.

**4. Period Decomposition and Counting Bridge (§10)**

For prime $n$ with $|E_{\rm div}|=1$, the proof writes $L = L_0 M$ (where $M$ is the free runner speed, $\gcd(M, nL_0) = 1$) and partitions $B_{\rm div}$ by the floor of the divisible runner into periods $\mathrm{Period}_k = \{b : \lfloor nb/L \rfloor = k\}$, $k = 1,\ldots,n-2$. The floor-0 miss set $\mathrm{miss}(0)$ has size $\geq 2$ (since the inversion map $e \mapsto -e^{-1}$ is injective and only $n-3$ units are retained). The free runner $M$ adds at most $|\mathrm{bad}(M,t,n)| = 2$ new residues to the bad set; this limits the fraction of fibres in $\mathrm{Period}_1$ that can be unsafe. The threshold $M_0 = \lceil n^2(n-1)/(L_0(n-2))\rceil$ separates the analytic regime ($M \geq M_0$, handled by the count) from a certified regime ($1 \leq M < M_0 < n^2$, enumerated exhaustively for $n \leq 30$).

**5. Universal Witness Pair for Chamber Persistence (Theorems 9.2d-I through 9.2d-III, §9.2d)**

For odd composite $n$ with smallest prime factor $p = p_{\min}$ and $m_0 = n/p$, the pair $c_1 = 2m_0 - 1$, $c_2 = 2m_0 - 2$ are both in the resonance interval $(2n/(p+1), 2n/p)$. A parity argument shows at most one of $\{c_1, c_2\}$ is a non-unit of $n$ (if both were non-units then $p \mid (2m_0-1) - 2(m_0-1) = 1$, impossible). The unit of the pair provides an isolated floor-reset event at $m=2$ whose CG2 solution is $pe_u - n$, a non-unit (since $p \mid n$ implies $p \mid pe_u - n$), so no unit covers the departing residue. This pair of closed-form witnesses covers all odd composite $n$ with $\geq 2$ prime factors uniformly, verified exhaustively for all $1{,}800$ values of odd $n \leq 5000$ with $\geq 2$ distinct prime factors.

---

## 4. Key Lemmas

| Name | Statement (brief) | Section |
|---|---|---|
| **Lemma 5.2 (Sole Cover)** | If unit $d \notin E_{\rm non}$, then $r_d = -d^{-1} \bmod n$ is uncovered for all $b \in I_d = [L/n, L/(n-1))$; hence $x_0 \geq 1$. | §5.3 |
| **Lemma G-PRES** | For $1 < g < n$ with $g \mid n$: the subgroup $H_g = (n/g)\mathbb{Z}_n$ contains no unit of $\mathbb{Z}_n$. (Every $r \in H_g$ satisfies $\gcd(r,n) \geq n/g \geq 2$.) | §6 |
| **Lemma 9.1 (Floor-Reset Count)** | For unit $e_u \geq 2$ with $\gcd(e_u,n)=1$: the number of floor-reset events for $e_u$ within $B_{\rm div}$ is exactly $e_u - 1$. | §9.1 |
| **Lemma 9.2a (Coverage Criteria / CG1–CG2)** | At the $m$-th floor-reset event of unit $e_u$, unit $e'$ covers the departing residue $r_{\rm dep} = -(m-1)e_u^{-1} \bmod n$ if and only if CG1 or CG2 holds (explicit arithmetic conditions given). | §9.2a |
| **Theorem 9.2c (Dropped-Runner Targeting)** | For composite $n \geq 4$ and non-unit $d \notin E_{\rm non}$: there exists unit $e_u = n-u$ and index $m \in \{2,\ldots,e_u-1\}$ such that the $m$-th floor-reset event of $e_u$ has no CG1 coverers and unique CG2 runner equal to $d$; since $d \notin E_{\rm non}$, the departing residue is uncovered, giving $B_{\rm safe} \geq 1$. | §9.2c |
| **Theorem 9.3b (Multi-Prime Quantitative Bound)** | For odd composite $n$ with $\geq 2$ distinct prime factors and both dropped runners non-units: $B_{\rm safe} \geq \varphi(n)(n-2)/2$. | §9.3 |
| **Lemma 9.3c (Level Bottleneck)** | For $n = p^k$ and any runner $e \in E_{\rm non}$: $r \in L_{k-1} := \{p^{k-1},\ldots,(p-1)p^{k-1}\}$ lies in $\mathrm{bad}(e,t,n)$ only if $p^{k-1} \mid t$ or $p^{k-1} \mid (t+1)$; hence $e$ can cover any element of $L_{k-1}$ on at most a $2/p^{k-1}$ fraction of floor values. | §9.3 |
| **Theorem 9.3f (Prime-Power Quantitative Bound)** | For $n = p^k$ with $p \geq 3$ odd and both dropped runners non-units: $B_{\rm safe} \geq \varphi(n)(n-2)/2$. | §9.3 |
| **Lemma 9.3f-LCM** | For $n = p^k$ and $T = \{u : 1 \leq u \leq n-1,\, p \nmid u\}$: $\mathrm{lcm}(T) = \mathrm{lcm}(1,\ldots,n-1)/p^{k-1} \geq 2^{n-2}/p^{k-1}$. | §9.3 |
| **Proposition 10.5 (Prime $n$ Quantitative Bound)** | For prime $n \geq 5$, all Case-2 families with $|E_{\rm non}|=n-3$, all $M \geq 1$: $x_0 \geq n-1 = \varphi(n)$. (Analytic for $M \geq M_0$; certified enumeration for $1 \leq M < M_0$, covering 36,847 cases with zero failures.) | §10.5 |

---

## 5. Section Dependencies

The table records which sections logically depend on results from earlier sections. An entry "X → Y" means section Y uses results from section X.

| Section | Title | Depends On |
|---|---|---|
| §1 | Introduction, normalisation, case partition | — |
| §2 | Coverage Insufficiency Principle (blueprint) | §1 |
| §3 | Irrational speeds (Weyl equidistribution) | §1; references §4, §§5–12 for Step 4a boundary case |
| §4 | Case 1: all speeds coprime to $n$ | §1 |
| §5 | Case 2 setup; bad sets; Sole Cover bijection | §1, §2 |
| §6 | Structural lemmas (G-PRES, FLOOR0, R1-SWEEP) | §5 |
| §7 | Prime $n$, one divisible runner | §5, §6 |
| §8 | Prime $n$, multiple divisible runners | §5, §6, §7 |
| §9.0 | Baseline Safety lemma | §5, §6 |
| §9.1 | Floor-reset events and count | §5 |
| §9.2a | Coverage Criteria (CG1/CG2) | §9.1 |
| §9.2b | $m=1$ event always covered | §9.2a |
| §9.2c | Dropped-Runner Targeting theorem | §9.2a |
| §9.2d | Chamber Persistence witnesses (supplementary) | §9.2c |
| §9.3 | Master Safe-Fibre Bound; Quantitative bounds (9.3b, 9.3c–9.3f) | §9.2c; §6 (G-PRES for prime-power sub-case) |
| §9.4 | Unit-Complete condition | §5 |
| §9.5 | Run Cap lemma | §9.3 |
| §9.6 | Quantitative composite summary | §9.3, §9.5 |
| §10 | Prime $n$ counting bridge | §5, §6, §7; Appendix A.4 for certified branch |
| §11 | Composite $n$ templates and Sub-cases B1–B3 | §5, §6, §9.2c, §9.3, §9.4; Appendix A.5 |
| §12 | Composite $n$, multiple divisible runners | §9.2c, §9.4 |
| §13 | Proof of Main Theorem | §3, §4, §5, §7, §8, §9, §10, §11, §12 |
| Appendix A.1 | $L=2n$ base cases | §5.2 |
| Appendix A.2 | Multi-prime chamberwise verification | §9.3, §9.2d |
| Appendix A.3 | Prime-power quantitative verification | §9.3f |
| Appendix A.4 | Certified branch for prime $n \leq 30$ | §10.3–§10.5 |
| Appendix A.5 | Certified branch for composite $n \leq 12$ | §11, Proposition 11.3 |
| Appendix A.6 | Cross-check of CG1/CG2 | §9.2a |
| Appendix A.7 | Chamber persistence: $m \equiv 1 \pmod{p}$ events | §9.2d, Theorem 9.2d-III |

---

## 6. Open Items / Gaps

The following items are identified in the text as open, supplementary only (not used in Theorem A), or relying on certified enumeration rather than a closed analytic argument.

### 6.1 Items Explicitly Marked Supplementary (Not Used in Theorem A)

**Supplementary Program 9.2d — Full Chamber Persistence.**
The proof of Theorem A requires only $B_{\rm safe} \geq 1$ (Tier 1). The stronger chamberwise claim — that *every* chamber in $B_{\rm div}$ contains an uncovered residue throughout the Unit-Complete multi-prime branch — is recorded as "Supplementary Program 9.2d" and is *not* proved in full generality. The analytic general relay step covers events with $\gcd(m-1, p) = 1$. The sparse sub-sequence with $m \equiv 1 \pmod{p_{\min}}$ is handled only by finite certified computation (Appendix A.7: 532 events for odd $n \leq 100$). A closed analytic argument for this residual sub-sequence is absent.

**Sub-case G(ii) of the Multi-Prime Unit-Complete Branch.**
The stronger chamberwise phenomenon (full $B_{\rm safe} = |B_{\rm div}|$) fails in Sub-case G(ii) of the Unit-Complete multi-prime branch, and this is stated as "expected" (§A.2 remark). However, no explicit characterisation of the Sub-case G(ii) failure is given; the cases are distinguished only informally.

### 6.2 Certified-Computation Dependencies (Finite, but Not Purely Analytic)

**Prime $n \leq 30$, Certified Branch (Appendix A.4).**
Proposition 10.5 relies on exhaustive enumeration of 36,847 cases for prime $n \leq 30$ and $1 \leq M < M_0(n)$. The analytic threshold $M_0 < n^2$ bounds the search space finitely. For $n \geq 31$, Lemma 10.4 makes $M_0 = 1$ (no enumeration needed). The enumeration carries SHA-256 certificates for reproducibility, but the verified cases remain computation-dependent.

**Composite $n \leq 12$, Certified Branch (Appendix A.5).**
Proposition 11.3 relies on exhaustive enumeration of all admissible tuples with composite $n \leq 12$ and $L < n(n-1)(\varphi(n)+1)$. Again, the enumeration is SHA-256 certified but computation-dependent.

**$L \in \{n, 2n\}$ Base Cases (Proposition 5.1 / Appendix A.1).**
The claim $x_0 \geq n-1$ for $L = 2n$ is verified only computationally for $n \leq 20$. The analytic argument in §5.2 establishes $x_0 \geq 1$; the stronger bound $x_0 \geq n-1$ for this base case is stated as "supporting evidence" rather than proved.

### 6.3 Quantitative Gap: $n$ Even, Unit-Complete (Sub-case B1)

Sub-case B1 ($n$ even, both dropped runners non-units) establishes $x_0 \geq 1$ via Theorem 9.2c. The quantitative bound $x_0 \geq \varphi(n)$ for this branch is **not** claimed or proved in the body; the table in §13 omits the even Unit-Complete branch from the Tier-2 ($x_0 \geq \varphi(n)$) summary. This is an acknowledged scope limitation.

### 6.4 Remark on a Retracted Argument

Section 9.3 contains an explicit remark retracting an earlier independence route for the prime-power sub-case:

> "An earlier independence route (attempting to bound the joint fraction of dangerous fibres via coprimality of periods across mod-$p$ runner groups) is false."

The retraction is stated but the error in the earlier route is not analysed in detail. The correct argument proceeds from a single safe chamber (Theorem 9.2c) rather than from a group-independence ansatz. No residue of the retracted argument appears to remain in the proof, but reviewers should verify that the current Theorem 9.3f argument does not silently invoke any form of the discarded independence.

### 6.5 Forward Reference: Theorem 8.3 Proof Detail

Theorem 8.3 (extreme divisible runners, $k \equiv 0$ or $k \equiv -1 \pmod n$) cites Proposition 10.5 (§10) in its proof. The invocation "Proposition~10.5 then yields $x_0 \geq \varphi(n)$" is given as a forward reference within §8. The applicability of Proposition 10.5 to the "extreme" tuples considered in Theorem 8.3 (where not all dropped runners are necessarily units) should be verified; the statement of Proposition 10.5 covers all Case-2 families with $|E_{\rm non}| = n-3$, which includes the case arising in Theorem 8.3.

---

*End of structured summary for v7.6.*
