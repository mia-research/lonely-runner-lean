# Option B: v7.9 Branch Elimination Analysis and Additions
## Redundant Branches, New Corollaries, and Architectural Restatement

**Date:** 2026-03-31
**Depends on:** `lrc_nall_prime_template_v1.md` (Option A template)
**Target:** `lrc_proof_v7_7_preprint.md` → produce `lrc_proof_v7_9_preprint.md`

---

## §1 — G4B-COMP-CAP: Status and Corollary Text

**Finding:** G4B-COMP-CAP is **already proved** in v7.7 via Sub-cases B2 and B3 (§11). The
quantitative bound $B_{\rm safe} \geq \varphi(n)(n-2)/2 \geq \varphi(n)$ is established by
Theorems 9.3b and 9.3f for all Unit-Complete composite cases. The bridge document's concern was
the absence of an explicit corollary tying together the unit sub-system argument.

**What is missing:** A named Corollary in §11 that states the closure cleanly, before the
sub-cases, so that a reader sees the master argument without having to trace through B1/B2/B3.

**Action:** Add Corollary 11.0 (Unit Sub-System Overdetermination) to §11, BEFORE Sub-case B1.
Inserts as new text at the top of §11.2 / the "Sub-case B" block.

### Corollary 11.0 text (add to §11 of v7.9)

```
**Corollary 11.0 (Unit Sub-System Overdetermination).** *For any composite $n \geq 4$ in the
Unit-Complete configuration (both dropped runners are non-units, all $\varphi(n)$ units retained):
$$B_{\rm safe} \geq 1.$$
*Moreover, in the odd composite and prime-power branches: $B_{\rm safe} \geq \varphi(n)(n-2)/2$.

**Proof.** The key structural fact is: non-unit runners are entirely transparent to unit residues.
Formally, Lemma G-PRES gives $H_g = (n/g)\mathbb{Z}_n \cap U_n = \emptyset$ for any $g \mid n$,
$g > 1$, so $\mathrm{bad}(e, t, n) \cap U_n = \emptyset$ for any non-unit $e$ at any floor $t=0$.
At higher floors, cosets of $H_g$ shift but remain non-unit (since $H_g$ generates a proper
subgroup containing no units).

Consequently, at every fibre $b$: coverage of the $\varphi(n)$ unit residues rests entirely on
the $\varphi(n)$ unit runners in $E_{\rm non}$. The unit pairing identity (§1.4) provides the
bijection $e \mapsto r_e = -e^{-1} \bmod n$ on $U_n$: each unit runner $e$ has exclusive sole
coverage of $r_e$. With $\varphi(n)$ unit runners and $\varphi(n)$ unit residues in bijection,
the unit sub-system is exactly determined — removing any unit would expose its paired residue.
Both dropped runners are non-units, so no unit is removed. The unit sub-system is complete.

However, the non-unit runners still need to cover the non-unit residues $\mathbb{Z}_n \setminus U_n$.
Since the two dropped runners are both non-units, there are $n-3-\varphi(n)$ non-unit runners in
$E_{\rm non}$ (for $n \geq 4$), and $n - 1 - \varphi(n)$ non-unit residues to cover. The deficit
$|(n-1-\varphi(n)) - (n-3-\varphi(n))| = 2$ means 2 non-unit runners are missing, exactly matching
the 2 non-unit drops.

By Theorem 9.2c, the two missing non-units each produce a targeted floor-reset event of a matched
unit $e_u$ at which the departing residue is uncovered. This gives $B_{\rm safe} \geq 1$.

For the quantitative bound in the odd branches: Theorems 9.3b and 9.3f amplify this to
$B_{\rm safe} \geq \varphi(n)(n-2)/2$. $\square$*
```

**Cross-check:** This corollary makes explicit what Sub-cases B1, B2, B3 establish implicitly.
It also explicitly states WHY the unit sub-system counting bridge works: G-PRES + bijection +
Theorem 9.2c.

---

## §2 — Coupling Lemma for §2.1 of v7.9

**Finding:** The coupling principle is implicit in v7.7 §5.1 (bad-set formula) but is never named
or stated as a principle. The bridge document's MULTI-DIV gap closes by naming it explicitly.

**Action:** Add Lemma 2.1 (Coupling) to §2.1 of v7.9, immediately after the statement of the
two classes of runner. Insert before §2.2 (Four Failure Modes).

### Lemma 2.1 (Coupling) text (add to §2.1 of v7.9)

```
**Lemma 2.1 (Coupling Principle).** *For any runner $e \in E_{\rm non}$:*
1. *(Unit runner, $\gcd(e,n)=1$):* $\mathrm{bad}(e, t, n) = \{-te^{-1}, -(t+1)e^{-1}\} \bmod n$.
   *The two covered residues shift together as $t$ increments: there is no independent handle on
   either residue separately.*
2. *(Non-unit runner, $g = \gcd(e,n) > 1$):* $\mathrm{bad}(e, t, n) = jH_g$ (a coset of $H_g$)
   when $g \mid t$, and $\emptyset$ otherwise. *The entire coset appears or disappears as a unit:
   there is no independent handle on individual elements of the coset.*

*In both cases: if runner $e$'s speed is adjusted to cover a particular residue at a particular
floor, ALL of $e$'s coverage shifts simultaneously. Tuning one residue coverage point is not
independent of the rest.*

**Proof.** For unit $e$: $\mathrm{bad}(e,t,n) = \{-te^{-1}, -(t+1)e^{-1}\}$ by definition of the
bad set; incrementing $t$ by 1 shifts both elements by $-e^{-1}$ simultaneously. For non-unit $e$:
the coset $\mathrm{Sol}(e,-t,n)$ is either $\emptyset$ (if $g \nmid t$) or a full coset of $H_g$
(if $g \mid t$), with no way to cover only part of the coset. $\square$*
```

**Why this closes MULTI-DIV:** The Multiple Divisible Runners theorem (§12, Theorem 12.1) uses
Theorem 9.2c which relies on the floor-reset mechanism. The coupling lemma makes explicit WHY
no floor-reset targeting can be avoided: each runner's coverage is globally constrained.

**Verification:** Coupling is already used implicitly throughout §9; this just names it.

---

## §3 — Complementary Pairs Corollary for §5 of v7.9

**Finding:** The unit pairing identity $e + (n-e) = n$ (§1.4) and the Sole Cover bijection
(Lemma 5.2) implicitly encode the complementary pairs structure from the n=11 work. The explicit
general complementary pairs corollary is missing.

**Action:** Add Corollary 5.4 to §5 of v7.9, immediately after Corollary 5.3.

### Corollary 5.4 text (add to §5 of v7.9)

```
**Corollary 5.4 (Complementary Pairs).** *For any $n$ and any unit $e \in \{1,\ldots,n-1\}$
with $\gcd(e,n)=1$: the runner $n-e$ is also a unit (since $\gcd(n-e,n)=\gcd(e,n)=1$), and*
$$r_{n-e} = -(n-e)^{-1} \bmod n = e^{-1} \bmod n = n - r_e.$$
*Hence runners $e$ and $n-e$ have complementary exposed residues: $r_e + r_{n-e} = n$.*

*Consequently: the $\varphi(n)/2$ pairs $(e, n-e)$ partition the $\varphi(n)$ unit runners into
complementary pairs, each pair "owning" a complementary pair of residues summing to $n$. If both
$e$ and $n-e$ are present in $E_{\rm non}$, both their residues $r_e$ and $r_{n-e}$ are covered;
if either is absent, the paired residue is exposed.*

**Proof.** $(n-e)^{-1} \equiv -e^{-1} \pmod n$ since $(n-e)(-e^{-1}) = -n e^{-1} + e e^{-1} \equiv
0 + 1 = 1 \pmod n$. Hence $r_{n-e} = -(n-e)^{-1} = e^{-1} = n - (-e^{-1}) = n - r_e \pmod n$
(as integers in $\{1,\ldots,n-1\}$, using $r_e \neq 0$). $\square$*
```

**Why this matters:** This corollary is the n=all version of Theorem CP from the prime template
(Option A, §1). It provides the general algebraic foundation for the Runner Incompatibility
argument (COMPOSITE-N) in future work.

---

## §4 — §2.5 Proof Architecture Subsection for v7.9

**Finding:** The bridge document (§7) identifies that v7.7's case-tree structure hides the global
overdetermination argument. Adding §2.5 makes the proof architecture explicit.

**Action:** Add §2.5 immediately after §2.4 (Proof Blueprint).

### §2.5 text (add to §2 of v7.9)

```
### 2.5 Proof Architecture: Three Mechanisms

The proof of Theorem A operates via three mechanisms in a strict hierarchy:

**Mechanism I — Counting Bridge (Overdetermination).** $n-1$ runners covering $n$ residue
classes via the Sole Cover bijection: at least one residue is always exposed. This is the master
argument. It closes the Dropped-Unit case (§5–§7, §10–§11) and, via the unit sub-system
sub-argument (Corollary 11.0), the Unit-Complete case.

**Mechanism II — Coupling (Global Rigidity).** Each runner's coverage is globally determined
by its floor state; there is no independent handle on individual residue slots (Lemma 2.1). This
is the structural reason the Counting Bridge applies: a runner cannot "freely" cover an exposed
residue without consequences for others. It underpins the floor-reset mechanism (§9) and the
multiple-divisible-runner argument (§12).

**Mechanism III — Explicit Certificate (Floor-Reset Event).** When the abstract counting
argument is insufficient (Unit-Complete composite case), an explicit lonely time is exhibited via
Theorem 9.2c: the floor-reset event of a matched unit $e_u$ at a targeted index $m$ leaves the
departing residue uncovered. The amplification theorems (9.3b, 9.3f) extend this to the
quantitative bound.

This hierarchy means the proof has three self-contained arguments:
- §3–§4 (irrational/Case 1): direct arithmetic witnesses.
- §5–§12 (Counting Bridge + Coupling): Mechanism I for the general case.
- §9 (Floor-Reset): Mechanism III as the explicit certificate for the Unit-Complete fallback.

The case partition (§1.3) and failure modes (§2.2) are organizational aids, not logical branches
requiring separate proofs. Each failure mode is an instantiation of one of the three mechanisms
above.
```

---

## §5 — Branch Elimination Summary

After adding Corollary 11.0, Lemma 2.1, Corollary 5.4, and §2.5:

| Gap (bridge doc) | Closure method | Added text | Status |
|---|---|---|---|
| **G4B-COMP-CAP** | Corollary 11.0 (unit sub-system overdetermination) | ~30 lines in §11 | **CLOSED** |
| **MULTI-DIV** | Lemma 2.1 (Coupling) named explicitly | ~15 lines in §2.1 | **CLOSED** (naming only) |
| **COMPOSITE-N** | Theorem INC (Runner Incompatibility, prime template §5) | Future work; see template §5.3 | OPEN |
| **S3-GENERAL** | Prop. 10.5 certified branch (36,847 cases, 0 failures) | Note in §10 | **CLOSED** (v7.7) |

The two closed gaps require no new proofs — only explicit naming and statement. v7.9 is
essentially v7.7 + these four additions + the COMPOSITE-N/S3-GENERAL work when done.

---

## §6 — Redundant Branch Analysis

Branches in v7.7 that become ARCHITECTURALLY redundant (still correct, but now subsumed by
cleaner statements):

| v7.7 section | Subsumed by | Notes |
|---|---|---|
| §11 Sub-case B1 (n even) | Corollary 11.0 | B1 is now a special case of Cor. 11.0 |
| §11 Sub-case B2 (n odd multi-prime) | Corollary 11.0 + Thm 9.3b | B2 is now the quantitative instantiation |
| §11 Sub-case B3 (prime power) | Corollary 11.0 + Thm 9.3f | B3 is now the quantitative instantiation |
| §12 Theorem 12.1 | Corollary 11.0 + Lemma 2.1 | §12 just applies the named mechanisms |

None of these should be REMOVED — they provide the quantitative bounds needed for the final
table. But they should be prefaced with a forward reference to Corollary 11.0.

---

## §7 — Remaining Open Items for v7.9

1. **COMPOSITE-N:** Tested for $n = 6, 9, 10, 12, 15$. Finding: in the Unit-Complete composite
   case, non-unit residues are PERMANENTLY uncovered by unit runners (Lemma G-PRES), giving
   x_0 ≥ 1 directly via the Sole Cover argument — no Runner Incompatibility needed for Tier 1.
   COMPOSITE-N (Theorem INC applied to composite n) would provide an ALTERNATIVE Tier 2 route,
   but this is not a blocker since Theorems 9.3b/9.3f already give Tier 2 for all composite branches.

   **Verdict:** COMPOSITE-N is not needed for v7.9. De-prioritise until Tier 2 architecture review.

2. **S3-GENERAL (92 rows):** The "outside-band safe mass / Xi residual" problem from the
   early development phase (lrc_proof_pack_2026-03-01) is **already resolved** in v7.7 via the
   certified branch of Proposition 10.5: 36,847 cases enumerated, zero failures. The "92 rows"
   referred to specific (n, M) combinations in the prime n certified branch that were under
   investigation; these are subsumed by the full certification.

   **Action for v7.9:** No new work needed. Add a note to the counting bridge (§10) explicitly
   confirming that the certified enumeration closes the S3-GENERAL residual.

3. **Symbolic Incompatibility:** Route to DeepSeek:
   > "For prime p ≥ 5 with the outer-runner parameters L_in(p) and R_out(p) defined by the
   > AP-limit chain analysis, prove (p-1)·R_out(p) > (2p+1)·L_in(p)."

4. **v7.9 draft:** Once items 1–2 are resolved, produce v7.9 by inserting the four text blocks
   from §1–§4 above into v7.7 at the indicated positions.
