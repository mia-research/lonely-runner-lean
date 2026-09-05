# LRC: Z0S Discrepancy Analysis — Mathematical Findings
**Date:** 2026-03-07
**Script:** `z0s_discrepancy_analysis_v1.py` (6,123 checks, n ∈ {6,8,9,10,12,15,16,18,20,25})

---

## 1. The Correct Coverage Criterion (replaces broken old criterion)

### Old criterion (WRONG)
> Runner $e'$ covers $r_{\rm dep}(e_u, m)$ iff $\bigl(\tfrac{e_u}{\gcd(e_u, e')}\bigr) \mid (m-1)$.

This had **623 failures** across 6,123 checks (old script showed 40 failures for n ∈ {6,8,9,10,12} only).

### Derivation of the correct criterion

At the $m$-th z=0 event of unit runner $e_u$ (fibre $b_m = mL/e_u$):
- Departing residue: $r_{\rm dep} = -(m-1) e_u^{-1} \bmod n$
- Floor state of unit $e'$: $t_{e'} = \lfloor e' m / e_u \rfloor$
- $e'$ covers $r_{\rm dep}$ iff $e' r_{\rm dep} \equiv -t_{e'}$ or $-(t_{e'}+1) \pmod{n}$

Substituting $r_{\rm dep}$ and writing $s := e' m \bmod e_u$, then
$$(m-1) e' e_u^{-1} \equiv t_{e'} + (s - e') e_u^{-1} \pmod{n}$$

So the coverage condition $(m-1) e' e_u^{-1} \equiv t_{e'}$ or $t_{e'}+1 \pmod{n}$ reduces to:
$$(s - e') e_u^{-1} \equiv 0 \text{ or } 1 \pmod{n} \quad\Longleftrightarrow\quad s \equiv e' \text{ or } e' + e_u \pmod{n}$$

Since $s \in \{0, \ldots, e_u - 1\}$:

> **Correct Coverage Criterion:** Let $s = e' m \bmod e_u$. Runner $e'$ covers $r_{\rm dep}(e_u, m)$ iff:
> - **Cond 1:** $s = e'$  (requires $e' < e_u$, i.e., smaller runner), OR
> - **Cond 2:** $e' + e_u \geq n$ AND $s = e' + e_u - n$  (wrap-around for large runners)

**Verified:** 0 discrepancies across 6,123 checks. ✓

---

## 2. What the Discrepancy Types Mean

### Old criterion: 623 failures categorised as:
| Type | Count | Mechanism | Explanation |
|------|-------|-----------|-------------|
| False positives (old says covered, isn't) | ~350 | $m=1$ with $e' > e_u$ | Old criterion triggers since $0 \mid (m-1)=0$, but $e'$ is at floor $\geq 1$, where $0 \notin \text{bad}(e', t \geq 1, n)$ |
| False negatives (old misses real coverage) | ~270 | Cond 2 (wrap-around) | Coverage when $e'+e_u \geq n$ is not captured by the divisibility rule |

The old criterion conflated two independent effects into a single divisibility condition that captures neither correctly.

---

## 3. The m=1 Event Is Always Covered — a Structural Theorem

**Theorem (m=1 Absorption):** For any unit $e_u \geq 2$ with $e' = e_u - 1$ or any unit $e' < e_u$ in $E_{\rm non}$, the $m=1$ z=0 event of $e_u$ is covered.

**Proof:** At $m=1$: $r_{\rm dep} = 0$, and for any $e' < e_u$: $s = e' \cdot 1 \bmod e_u = e'$ (since $e' < e_u$). So Cond 1 fires. In particular, $e' = 1$ is always a unit, always satisfies $1 < e_u$ (for $e_u \geq 2$), and always covers the $m=1$ event. $\square$

**Corollary:** The z=0 counting argument of Theorem 8.3 overcounts by $\varphi(n)$ (one $m=1$ event per unit runner $e_u \geq 2$ is always covered). The claimed bound $B_{\rm safe} \geq \varphi(n)(n-2)/2$ from Z0S.3 cannot be proved by counting z=0 events — the actual contribution from z=0 events to $B_{\rm safe}$ is at most:
$$\sum_{e_u \in \text{units}, e_u \geq 2} \bigl[(e_u - 1) - (\text{covered events for } e_u)\bigr]$$
and each runner $e_u$ loses at least 1 event (the $m=1$ event), plus additional events via Cond 2.

---

## 4. Coverage Structure: Two Clean Rules

The correct criterion has a beautiful Beatty/three-distance interpretation:
- **Cond 1** ($s = e'$): at the $m$-th z=0 event of $e_u$, runner $e'$ "steps in sync" with $e_u$ in the sense that $e' m \equiv e' \pmod{e_u}$, i.e., $e'(m-1) \equiv 0 \pmod{e_u}$. For $\gcd(e', e_u) = 1$, this forces $m = 1$. For $\gcd(e', e_u) = g > 1$, it also fires at $m = 1 + e_u/g, 1 + 2e_u/g, \ldots$
- **Cond 2** ($s = e'+e_u-n$): fires when the combined speed $e' + e_u \geq n$, so their combined Beatty-sequence position "wraps around" past $n$.

**Observation:** Cond 1 fires for $e' < e_u$ only (stepping down), Cond 2 fires for $e' + e_u \geq n$ (complementary large runners). Together they form a complete dichotomy on the speed circle modulo $n$.

---

## 5. Non-unit Runner Transparency

**Theorem (Transparency):** For speed $e$ with $g = \gcd(e, n) \geq 2$, the bad set $\text{bad}(e, t, n) = \emptyset$ iff $t \bmod g \in \{1, 2, \ldots, g-2\}$ (the "transparent zone"). The transparency fraction is $(g-2)/g$.

Specifically:
- $g = 2$: transparency fraction $= 0$. A runner with $\gcd(e,n)=2$ is **NEVER transparent**.
- $g = 3$ (e.g., n=9 with $e=3,6$): transparency fraction $= 1/3$.
- $g = 5$ (e.g., n=25 with $e=5,10,15,20$): transparency fraction $= 3/5$.
- $g = p$ (e.g., n=p^2 with $e=jp$): transparency fraction $= (p-2)/p$.

---

## 6. Simultaneous Transparency — Where the Approach Fails

**Attempt:** For G4.OT B3 (n=p^k, both dropped runners non-units), if all non-unit runners in $E_{\rm fix}$ are simultaneously transparent, then only unit runners contribute to coverage, their union = $\{0\} \cup \text{units}$, and non-unit residues are uncovered → safe fibre.

**Numerical result (n = 9, 25, 27, 49):** NO simultaneous-transparency windows exist.

**Why for n=9:** Non-units are $e=3$ and $e=6$, both with $g=3$.
- $e=3$ transparent: $\lfloor 3\alpha \rfloor \equiv 1 \pmod 3$, i.e., $\alpha \in [1/3, 2/3)$ in $[1/9, 8/9]$
- $e=6$ transparent: $\lfloor 6\alpha \rfloor \equiv 1 \pmod 3$, i.e., $\alpha \in [1/6, 1/3) \cup [2/3, 5/6)$

These windows are **disjoint** — when $e=3$ is transparent, $e=6$ is not, and vice versa. The transparency windows alternate with no overlap.

**General pattern for n=p^k:** Non-unit speeds are multiples of $p$: $e = jp$. Runner $e=jp$ is transparent when $\lfloor jp\alpha \rfloor \bmod p = 1$. As $j$ grows, the transparency windows subdivide and stagger, making simultaneous transparency impossible.

**Conclusion:** The simultaneous-transparency route is **closed off** for n=p^k. A different analytical approach is required.

---

## 7. Where Safe Fibres Actually Come From (for G4.OT B3)

Despite the negative results above, LRC holds numerically (0 violations in all tested cases). Safe fibres must exist. The question is **why**.

### Case n=9 (=3²): floor-0 argument works directly

Both non-units {3,6} are dropped. $E_{\rm fix}$ = all 6 units.
At floor-0: unit runners cover $\{0\} \cup \text{units} = \{0,1,2,4,5,7,8\}$.
Miss $= \{3,6\}$ (non-unit residues) $\neq \emptyset$. Safe fibres on the interval $(L/9, L/8)$. ✓

This works because **all non-units are dropped**, leaving no non-unit runner to cover the non-unit residues.

### Case n=p² with p ≥ 5 (e.g., n=25): floor-0 argument fails

There are $p-1 \geq 4$ non-units. Only 2 are dropped; the remaining $p-3$ are in $E_{\rm fix}$ and cover $H_p$ (non-unit residues) at floor 0. Union = $\mathbb{Z}_n$, no safe residue.

Safe fibres must be found at **higher floor states** where the non-unit runners in $E_{\rm fix}$ have empty bad sets — but simultaneous transparency doesn't exist. So the safe fibres come from a more complex floor-state combination.

### Key open question for B3 (p ≥ 5)
**Does there always exist a fibre $b \in B_{\rm div}$ where the union of bad sets $\bigcup_{e \in E_{\rm fix}} \text{bad}(e, \lfloor eb/L \rfloor, n) \neq \mathbb{Z}_n$?**

Numerically: YES. Analytically: OPEN. This is the crux of Gap A for composite n with multiple non-unit runners in $E_{\rm fix}$.

---

## 8. Revised Gap A Taxonomy

| Sub-case | Status | Reason |
|----------|--------|--------|
| Dropped unit in $E_{\rm div}$ (any n) | ✓ PROVED | Sole Cover interval gives miss of width $\geq 1/(n(n-1))$ |
| n=9 (=3²), both non-units dropped | ✓ PROVED | Floor-0 gives miss $= \{3,6\}$ |
| n prime, all cases | ✓ PROVED | Sections 6–9 (counting bridge, Cases i–iiib) |
| n=p², p=3 | ✓ PROVED | Floor-0 argument above |
| n=p^k, p≥5, few non-units remaining | ⚠ OPEN | Floor-0 fails; transparency windows disjoint |
| n=p^k, general | ⚠ OPEN | No analytical mechanism identified |
| Composite n, multiple prime factors | ⚠ OPEN | Different structure; cases 10, 12, 15, 18, 20 pass numerically |

---

## 9. What the Discrepancy Analysis Reveals About Proof Strategy

The two-condition coverage structure (Cond1/Cond2) strongly suggests:

**The right framework is not Z0S counting but a Farey/Beatty adjacency argument.**

The covered events follow the pattern: coverage fires when $e'm/e_u$ is within $1/n$ of an integer (modulo 1). This is exactly the **LRC condition applied locally** — i.e., the question of when runner $e'$ is "not lonely" relative to a virtual runner at speed $e_u$ at time $t = m/e_u$.

This self-referential structure suggests:
1. **Inductive approach:** Use LRC for smaller $n$ to prove it for $n$.
2. **Fourier/measure approach:** Average number of uncovered residues over all fibres must be positive.
3. **Three-distance approach:** The Beatty sequence structure of coverage guarantees "gaps" in the coverage pattern.

**Recommended next analytical step:** Prove that for n=p^k with $p \geq 5$, the average number of uncovered residues over $b \in B_{\rm div}$ is at least $p^{k-1}(p-2)/p > 0$, using the transparency fraction of non-unit runners.

---

## 10. Implications for the Proof Document

| Section | Change needed |
|---------|---------------|
| §8.1 (Z0S.1) | Add: "The m=1 event is always covered; effective safe-event count is $\sum_{e_u} (e_u - 2)$, not $\sum (e_u-1)$" |
| §8.2 (Unit Residue Isolation) | Replace false proof with new criterion statement (Cond1/Cond2 theorem) |
| §8.3 (Z0S.3) | Keep as [⚠ GAP A] — new criterion shows counting bound is too optimistic |
| §10.2 (G4.OT B3) | Split: n=9 sub-case proved by floor-0; general p≥5 sub-case is open |
| §14 (Gap Registry) | Add new entries: "B3-FLOOR-0" (proved n=9), "B3-GENERAL" (open for p≥5) |

The correct coverage criterion (Cond1/Cond2) should be added as a proved lemma:

> **Lemma (Coverage at z=0 Events):** At the $m$-th z=0 event of unit runner $e_u$, unit runner $e'$ covers $r_{\rm dep}(e_u, m)$ iff $s = e'$ (Cond 1, requires $e' < e_u$) or $s = e' + e_u - n$ with $e' + e_u \geq n$ (Cond 2), where $s = e' m \bmod e_u$.

This is a clean, proved result that replaces the broken Z0S Unit Residue Isolation lemma.
