# Bridge Document: From n=11 to n=all
## How the Branching Was Defeated and What It Means for the General Proof

**Date:** 2026-03-31
**Context:** n=11 AP paper complete (v21, 2026-03-27). n=all proof at v7.8. This document maps the five anti-branching mechanisms discovered in n=11 onto the n=all proof, identifies which are already present, and states the specific theorems needed to close the remaining gaps.

---

## §0 — The Root Cause of Branching

In both n=11 and n=all, branching arose from the same mistake: **treating each configuration as an independent case** rather than seeing the global constraint structure. Every time a slot was closed by fixing a runner's speed, new sub-cases opened based on how the fixed runner's *other* bad intervals affected neighboring slots. The cascade appeared to require unlimited nesting.

The resolution in both settings is the same insight: **the system is globally overdetermined**. The runners do not have enough degrees of freedom to simultaneously close all slots. This is a single structural fact, and it closes all cases at once — without ever needing to enumerate them.

The five mechanisms below are the precise forms this insight takes in n=11. Each has a direct n=all analogue.

---

## §1 — Mechanism 1: The Coupling Principle

### n=11 statement
Runner j has bad intervals $B_{j,k} = [(11k+10)/(11a_j),\, (11k+12)/(11a_j)]$. **All bad intervals scale as $1/a_j$.** Tuning $a_j$ to close slot $I_m$ moves ALL of runner j's other bad intervals simultaneously. There is no independent handle on any single slot.

*This is why cases exist:* locking runner 9 to close $I_1$ places $B_{9,1}$ inside $I_2$, propagating the constraint.
*This is also why cases are bounded:* each runner can only lock to ONE resonance speed; after all 8 runners are locked, the system is overdetermined.

### n=all analogue (v7.8 §2.1, Lemma 2.2 implicit)
For a unit runner $e$ at floor state $t$: $\mathrm{bad}(e, t, n) = \{-te^{-1},\, -(t+1)e^{-1}\} \bmod n$. The two covered residues advance together as $t$ increments — there is no way to shift one without shifting both. For a non-unit $e$ with $g = \gcd(e,n)$: the bad coset is $jH_g$ (a rigid translate of the same subgroup), and the opaque/transparent toggle is entirely determined by $t \bmod g$.

**Status in v7.8:** The coupling is present implicitly in the bad-set formula, but is **not stated as a named principle**. The proof would be cleaner if Coupling were stated explicitly as a lemma at the top of §2, before the case partition.

**Action:** Add a "Coupling Lemma" to §2.1 of v7.9: *When runner e's speed changes, all floor-state transitions shift uniformly. There is no independent handle on any single residue class.*

---

## §2 — Mechanism 2: Overdetermination

### n=11 statement
8 free runner speeds $a_2, \ldots, a_9$. Closing ALL 9 slots requires ≥9 independent resonance conditions (one per slot: lock at least one runner's $B_{j,k}$ to each slot edge). 9 conditions, 8 unknowns → **generically no joint solution**. At least one slot always has GF > 0.

This is the master argument. It is why the cascade must terminate, regardless of which branch is taken. The explicit incompatibility (Runner 2: $a_2 \geq 20/9$ vs $a_2 \leq 575/261$) is the computational verification of this for the ++------ class.

### n=all analogue (v7.8 §10–11, counting bridge)
$n-1$ runners covering $n$ residue classes. Unit runners each exclusively own one residue class via the bijection $e \mapsto -e^{-1} \bmod n$. With $n-1$ runners and $n$ classes, at least one class is uncovered.

**For prime n:** The bijection covers $n-1$ classes; one is exposed. The counting bridge in §10–11 formalises this. **PROVED.**

**For composite n, dropped-unit:** Same argument — the absent unit $d$ exposes $r_d = -d^{-1} \bmod n$ on $I_d$. **PROVED** (Lemma 5.2).

**For composite n, Unit-Complete (G4B-COMP-CAP):** All unit runners are present, so the dropped runners are non-units. The unit sub-system still satisfies the bijection — there are $\varphi(n)$ unit runners covering $\varphi(n)$ residue classes each with exclusive ownership. However, the counting argument "$n-1$ runners, $n$ classes" now applies to the FULL system, not just units. The non-unit runners cover cosets of subgroups $H_g$, which contain NO units (by Lemma G-PRES in v7.8). Hence the unit residue classes must be covered entirely by unit runners, and the same overdetermination applies to the unit sub-system.

**Key claim for G4B-COMP-CAP:** In a Unit-Complete configuration, the unit runners form a sub-system of size $\varphi(n)$ covering $\varphi(n)$ residue classes. Non-unit runners are transparent to unit residues (by G-PRES). The counting bridge for the unit sub-system gives the same overdetermination as the prime case. GF > 0 follows.

**Status:** The individual pieces (G-PRES, Theorem 9.2c) are proved in v7.8. What is missing is the explicit statement that the unit sub-system counting bridge closes G4B-COMP-CAP **without** new machinery. This should follow from combining G-PRES + Theorem 9.2c + the $\varphi(n)$ unit pairing identity (§1.4 of v7.8).

**Action:** Add a Corollary in §11 of v7.9: *In a Unit-Complete configuration for any $n$, the unit sub-system satisfies overdetermination independently of the non-unit runners. G4B-COMP-CAP closes.* Verify with DeepSeek `--thinking`.

---

## §3 — Mechanism 3: Complementary Pairs / Mod-n Bijection

### n=11 statement
For runner $j \in \{2,\ldots,9\}$, in the AP limit: runner $j$ sits at boundary position $1/11$ at witness $t_{j^{-1} \bmod 11}$ and at $10/11$ at witness $t_{10j^{-1} \bmod 11}$. These two witnesses are **complementary** (sum to 11), and their slots are the two "owned" slots of runner $j$.

Since $j \leftrightarrow 11-j$ maps $j^{-1} \leftrightarrow -(j^{-1})$, runners $j$ and $11-j$ own the SAME pair of slots. This gives 4 complementary pairs covering 8 slots, with $I_9$ unclaimed. The sign pattern then determines which direction each runner approaches, creating forced conflicts between paired runners.

**This replaced all sign-class case analysis:** instead of 256 cases, one structural theorem covers all sign patterns.

### n=all analogue (v7.8 §5.3, Lemma 5.2)
The Sole Cover bijection $e \mapsto -e^{-1} \bmod n$ is exactly the n=all version of the mod-n ownership structure. The "complementary pairs" in general n are: $e$ and $n-e$ are both units (since $\gcd(e,n) = \gcd(n-e,n)$), and their inverses satisfy $e^{-1} + (n-e)^{-1} \equiv e^{-1}(1 - (n-e)^{-1}e^{-1}\cdot en) \equiv \ldots$ more directly: $(n-e)^{-1} \equiv -e^{-1} \pmod n$. So $r_{n-e} = -(n-e)^{-1} = e^{-1} \bmod n = n - r_e \pmod n$.

**The general complementary pairs theorem:** For any $n$, runners $e$ and $n-e$ (both units) have $r_e + r_{n-e} = n$, i.e., their exposed residues are complementary in $\mathbb{Z}/n\mathbb{Z}$. This is the exact n=all analogue of the n=11 pairing.

**Status in v7.8:** The bijection is stated (Lemma 5.2, Corollary 5.3) but the pairing structure ($e \leftrightarrow n-e$, $r_e \leftrightarrow n - r_e$) is **not stated explicitly**. It is implicitly used in the unit pairing identity (§1.4) but not developed as a structural tool.

**Action:** Add a "Complementary Pairs Corollary" to §5 of v7.9 stating the pairing $e \leftrightarrow n-e$ and its consequence for the bad-set structure. This will be needed for Mechanism 5.

---

## §4 — Mechanism 4: Explicit Certificate / Phase-Uniform Propagation

### n=11 statement
Instead of proving GF > 0 abstractly, the proof exhibits the rational witness $t^* = 69/275$ (the exact moment runner 9 exits its $k=1$ bad interval). This witness is valid for ALL sign configurations in the ++------ class within $W_{\rm ref}$. The Phase-Uniform Theorem (Lemma P + Lemma C in v21) then propagates this to every pacemaker sub-cycle without repeating the argument.

**This replaced the infinite cascade:** instead of proving each sub-cycle separately, one witness + one propagation lemma covers all.

### n=all analogue (v7.8 §9, Theorem 9.2c, Dropped-Runner Targeting)
The floor-reset mechanism is the n=all analogue: at a floor-reset event of matched unit $e_u$ at fibre $b^* = mL/e_u$, the Coverage Gate (CG1/CG2) fails for all unit runners, leaving $r_{\rm dep}$ uncovered. This is an **explicit lonely time** analogous to $t^*$.

The Phase-Uniform analogue is Theorem 9.3b/9.3f (amplification): a single isolated floor-reset event amplifies to $B_{\rm safe} \geq \varphi(n)(n-2)/2$ safe fibres.

**Status in v7.8:** This mechanism is well-developed for prime n and composite Unit-Complete. The gap is for the **S3-GENERAL** frontier: outside-band safe mass for 92 residual rows in the prime n large-L case. The question is whether a universal floor-reset certificate covers all 92 rows, or whether per-row analysis is needed.

**Action:** Before attempting per-row analysis of the 92 S3 residuals, check whether Theorem 9.3b already covers them under a uniform parameter range. Route to DeepSeek for targeted review of the 92 rows against the existing amplification theorem.

---

## §5 — Mechanism 5: Runner Incompatibility (Hard Constraint Collision)

### n=11 statement (the key lesson)
For runner 2 in the ++------ class:
- Closing slot $I_4$ requires $a_2 \geq 20/9$
- Closing slot $I_9$ requires $a_2 \leq 575/261$
- Since $20/9 = 5220/2349 > 5175/2349 = 575/261$: **incompatible**. GF$(I_4)$ + GF$(I_9) > 0$ unconditionally.

No cascade. No sub-cases. One runner, two slots, one algebraic contradiction.

**This is the strongest mechanism and the least exploited in n=all.** It requires no global overdetermination argument — just identifying a single runner whose slot-closing constraints conflict.

### n=all analogue — NOT YET IN v7.8
The n=all analogue would be: for a given CB configuration on general $n$, identify a "critical runner" $e_c$ and two residues $r_k, r_{k'}$ such that:
- Covering $r_k$ at floor $t_k$ requires $e_c b/L$ to enter a specific interval $[A_k, B_k)$
- Covering $r_{k'}$ at floor $t_{k'}$ requires $e_c b/L \in [A_{k'}, B_{k'})$
- These two intervals are disjoint

If such a pair $(r_k, r_{k'})$ exists for every CB configuration, then at least one is always uncovered — no case analysis needed.

**Where to look for this structure:**

1. **The unit pairing identity** ($e + (n-e) = n$) gives a direct algebraic relationship between complementary runners. If both runners $e$ and $n-e$ are present, their joint coverage requirements on complementary residue pairs ($r_e$ and $r_{n-e}$) may be incompatible.

2. **Non-unit runner coset rigidity:** A non-unit runner $e$ with $g = \gcd(e,n)$ covers only cosets of $H_g$ at opaque floors. If a unit residue $r$ lies in $H_g^c$ (the complement), then $e$ can NEVER cover $r$ at any floor — an automatic incompatibility.

3. **The critical composite case (COMPOSITE-N):** For composite $n$ with a Unit-Complete CB configuration, the unit runners must cover all $\varphi(n)$ unit residues. By the complementary pairs structure, each unit runner $e$ is "responsible" for $r_e$ and $n - r_e$. If two complementary unit runners $e, n-e$ are both present and both have σ-sign conflicts (analogous to ++------ in n=11), their joint coverage of $(r_e, r_{n-e})$ may create the incompatibility.

**Action:** Attempt to prove the following for COMPOSITE-N:

> **Proposed Incompatibility Lemma (for v7.9).** For any $n$ and any CB configuration with all unit runners present (Unit-Complete), there exists a unit runner $e_c \in E_{\rm non}$ and two residues $r, r' \in \mathbb{Z}/n\mathbb{Z}$ such that the floor-state conditions for $e_c$ to cover $r$ and to cover $r'$ are mutually exclusive.

If proved, this closes COMPOSITE-N via the same one-runner, two-slot argument as Runner 2 Incompatibility in n=11.

---

## §6 — Gap Map: n=all Open Frontier vs. n=11 Mechanisms

| Gap | Mechanism that closes it | Status | Theorem needed |
|-----|--------------------------|--------|----------------|
| **G4B-COMP-CAP** | Mechanism 2 (overdetermination) + G-PRES | Unit sub-system counting bridge; G-PRES + 9.2c already proved | Add Corollary in §11: unit sub-system closes gap independently |
| **COMPOSITE-N** | Mechanism 5 (incompatibility) | Not attempted | Proposed Incompatibility Lemma (§5 above) |
| **S3-GENERAL** (92 rows) | Mechanism 4 (explicit certificate) | Check if Theorem 9.3b already covers uniformly | DeepSeek adversarial review of 92 rows vs. 9.3b |
| **MULTI-DIV** | Mechanism 1 (coupling) | Mostly proved in §12 | Verify universality of coupling statement; should close |

---

## §7 — Architectural Restatement for v7.9

The v7.8 proof is structured as: **Case partition → 4 Failure Modes → section-by-section closure**. This hides the global structure. The cleaner architecture, revealed by the n=11 work, is:

**Master argument (Mechanism 2):**
> $n-1$ runners, $n$ residue classes, bijective sole-cover ownership. By overdetermination, complete coverage is impossible.

**Supporting structure (Mechanisms 1, 3):**
> Coupling: the system is constrained globally, not slot-by-slot. Complementary pairs: the ownership structure is rigid and sign-pattern-independent.

**Fallback closures (Mechanisms 4, 5):**
> When the counting bridge is insufficient (Unit-Complete case), exhibit an explicit lonely time (floor-reset certificate) or prove an algebraic incompatibility between two coverage requirements on the same runner.

**For v7.9:** Add a §2.5 "Proof Architecture" subsection that explicitly states this hierarchy, with forward pointers to where each mechanism appears. This makes the proof readable as a single argument rather than a case tree.

---

## §8 — Recommended Session Order

1. **Immediate:** Attempt G4B-COMP-CAP via unit sub-system argument (§2 above). This likely closes with existing lemmas — no new machinery. Update gap status file if confirmed.

2. **Next:** Test the Proposed Incompatibility Lemma (§5 above) for small composite $n$ (n=6, 9, 10) empirically. If the pattern holds, formalise for COMPOSITE-N.

3. **Then:** Route 92 S3-GENERAL rows through DeepSeek against Theorem 9.3b. If all 92 are covered: S3-GENERAL closes. If not: the exceptions define the true residual.

4. **Final:** Incorporate all closures into v7.9, with the restatement of §7 above as the new §2.5.

**Remaining open after these steps (anticipated):** Zero, or a very narrow residual in COMPOSITE-N for specific $n$ values. The frontier should collapse from 4 branches to ≤1.
