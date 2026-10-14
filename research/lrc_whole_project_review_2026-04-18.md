# LRC Project — Whole-Project Review

**Date opened:** 2026-04-18
**Author:** Claude adjudication pass (supersedes `lrc_proof_status.md` Tier-1-COMPLETE claim)
**Scope:** Lineage A (n=all Tier 1, v11.x line) · Lineage B (n=11 AP paper) · Lineage C (Tier 2, v10.12 line)
**Methodology:** Adversarial re-derivation of each major theorem; counterexamples at n ∈ {5,6,7,8,11} hand-computed and independently re-checked.

---

## Executive Verdict

| Lineage | Previous ledger claim | Current verdict | Grounds |
|---|---|---|---|
| A — n=all Tier 1 (v11.2) | Tier 1 COMPLETE (2026-04-18) | **INCORRECT** | Lemma 2.5 iff false (two counterexamples at n=5); Lemma 10.2 floor formula wrong for q_e≥1; Thm 8.2 L-bound false; Thm 11.1 Case A L-bound false. |
| B — n=11 AP paper (v22/v31) | PROVED (Route 3) | **INCOMPLETE** | Baton-pass and phase-uniformity check out; **Runner-2 Incompatibility** enumeration gaps confirmed (ERR-B-01, B-02, B-03). Main Claim 5.1 likely true but proof presently leaks. |
| C — Tier 2 (v10.12) | ⚠ PARTIAL (GG2, PL-KINDEP open) | **PENDING RE-AUDIT** | Uses v10-era distributed safe-fibre reasoning, NOT the unified Lemma 2.5; may survive the Lineage-A collapse. |

**Bottom line.** The Tier 1 "COMPLETE" ledger entry for v11.2 is not supported. The n=all proof is, at this writing, **not proven**. The n=11 and Tier 2 lineages require independent re-derivation before their status can be reaffirmed.

The single most important immediate action: **do not treat v11.2 as a preprint-ready manuscript.** A replacement for Lemma 2.5 must be derived before §§6, 8, 10, 11 can be salvaged.

---

## Lineage A — Error Catalog

### ERR-A-01 — Lemma 2.5(a), Fibre–safe-point identity (FATAL)

- **Location:** `lrc_proof_v11_2.md`:§2.4, lines 140–148.
- **Statement (as written):** For $e \in E_{\mathrm{non}}$ and $b \in B_{\mathrm{div}}$: $(eb \bmod N) \in [L,(n-1)L]$ iff $[b]_n \notin \mathrm{bad}(e, \lfloor eb/L\rfloor, n)$.
- **Defect:** Both directions false. The proof claims (line 148) "the condition fails iff $\rho_e \cdot [b]_n \equiv -t$ or $-(t+1) \pmod n$". This identity is unjustified and false: the correct safety condition is $t \bmod n \in \{1,\ldots,n-2\}$ (modulo the $r=0$ boundary at $t\equiv n-1$), which is a function of $t$ alone, **not** a function of $[b]_n$ interacting with $t$. The bad-set framework conflates $\rho_e \cdot b \bmod n$ (which equals $eb \bmod n$) with $t = \lfloor eb/L\rfloor$; these are different quantities.
- **Counterexample 1 (safe but predicted unsafe):** $n=5$, $E=(3,5)$, $L=15$, $N=75$, $b=6$.
  - $eb = 3 \cdot 6 = 18$; $18 \bmod 75 = 18 \in [15, 60]$, so **safe**.
  - $t = \lfloor 18/15 \rfloor = 1$; $[b]_5 = 1$; $\rho_e = 3$, $\rho_e^{-1} \equiv 2 \pmod 5$.
  - $\mathrm{bad}(3,1,5) = \{-1\cdot 2, -2\cdot 2\} \bmod 5 = \{3, 1\}$.
  - $[b]_5 = 1 \in \{1,3\}$, so lemma predicts **unsafe**. ✗
- **Counterexample 2 (unsafe but predicted safe):** same $n,E,L,N$; $b=4$.
  - $eb = 12$; $12 \bmod 75 = 12 \notin [15,60]$, so **unsafe**.
  - $t = \lfloor 12/15 \rfloor = 0$; $[b]_5 = 4$; $\mathrm{bad}(3,0,5) = \{0, -2\} = \{0, 3\}$.
  - $[b]_5 = 4 \notin \{0,3\}$, so lemma predicts **safe**. ✗
- **Verified by:** hand computation, independently re-checked by Explore agent in prior turn.
- **Upstream dependencies:** Lemma 2.4 (sound); decomposition $eb \bmod nL = (t \bmod n)L + r$ (sound — this is Euclidean division).
- **Downstream dependents:** §2.4 bad-set framework; §5.2 Lemma 5.1a (base-fibre coverage); §5.2 Lemma 5.1b (thinness); §6 sliding-window chain (Prop 6.1); Lemma 6.0 (coverage-transfer); §9 Lemma 9.2, Theorem 9.2c; §10 Lemma 10.2, Proposition 10.1; §11 Theorem 11.1; §12 Theorem A.
- **Salvage status:** **S2 / possibly S4.** The correct safety criterion ("$t \bmod n \in \{1,\ldots,n-2\}$") does NOT decompose into a per-$[b]_n$ condition as the paper claims. However, a *different* invariant — the value $e b \bmod nL \in [L,(n-1)L]$ — can be re-indexed differently, perhaps by chamber (the intervals $b \in [tL/e, (t+1)L/e)$ on which $t = \lfloor eb/L\rfloor$ is constant). Whether the §6 sliding-window/coverage-transfer machinery survives depends on whether the reset identity (Lemma 6.0) retains meaning once the "bad-set at a fibre" is replaced by a chamber-indexed notion. This is a non-trivial rebuild; it is NOT a local patch.

### ERR-A-02 — Lemma 10.2 floor formula

- **Location:** `lrc_proof_v11_2.md`:§10, line 414.
- **Statement (as written):** "for $e = nq_e + \rho_e$ with $\rho_e \in \{1,\ldots,n-1\}$: $\lfloor eb/L\rfloor \equiv \rho_e - 1 \pmod n$ on $J$".
- **Defect:** The formula is $\lfloor eb/L\rfloor \equiv \rho_e - 1 - q_e \pmod n$ in general, not $\rho_e - 1$. The paper's computation handles the case $q_e = 0$ (runners $e < n$) only.
- **Counterexample:** $n=6$, $e=7$, $L=42$, $b=34$ (in $J = [(n-2)L/(n-1),\,(n-1)L/n] = [33.6, 35]$). Here $q_e = 1$, $\rho_e = 1$. $eb = 238$; $238/42 = 5.666\ldots$; $\lfloor eb/L\rfloor = 5$. Paper predicts $\rho_e - 1 = 0 \pmod 6$; actual $5 \pmod 6 \ne 0$. ✗
- **Downstream impact:** All subsequent work in §10 builds $\mathrm{bad}(e, \rho_e - 1, n)$ and concludes $\{\rho_e^{-1}-1, n-1\}$ is the bad set. For $q_e \geq 1$ runners, the actual bad set is $\{-(\rho_e - 1 - q_e)\rho_e^{-1}, \ldots\}$ — different, and the "$s_d = d^{-1} - 1$ uncovered" conclusion does not go through without reworking.
- **Salvage status:** **S3 (weaken-and-keep, possibly).** The late-window strategy still works when restricted to $q_e = 0$ runners. For $n$ not too large and $E \subset \{1, \ldots, n-1\} \cup \{n, 2n, \ldots\}$ (no non-divisible speed exceeds $n$), the lemma is correct as stated. Generic $E$ with $e_i \geq n+1$ non-divisible requires the $-q_e$ correction throughout §10.

### ERR-A-03 — Theorem 8.2 L-bound

- **Location:** `lrc_proof_v11_2.md`:§8, line 331.
- **Statement (as written):** "The residual $L < n(n-1)$, equivalently $L \in \{n, 2n\}$, is covered by Proposition 5.1."
- **Defect:** $L < n(n-1)$ and $L \in \{n, 2n\}$ are not equivalent. For $n \geq 5$: $n(n-1) = 20, 30, 42, \ldots$; multiples of $n$ below this include $\{n, 2n, 3n\}$ for $n=5$ ($L \in \{5,10,15\}$, but also $L = 20$ fails $< 20$), and more for larger $n$.
- **Actual range missed:** $L \in \{3n, 4n, \ldots, \lfloor n(n-1)/n\rfloor \cdot n\} = \{3n, \ldots, (n-2)n\}$ (those multiples of $n$ below $n(n-1)$ not handled by Prop 5.1).
- **Downstream impact:** Theorem 8.2's chamber argument assumes $|I \cap B_{\mathrm{div}}| \geq 1$ which requires $L \geq n(n-1)$; for the missed $L$ range no alternative coverage is given.
- **Salvage status:** **S3.** Extend Prop 5.1 or add a dedicated small-$L$ subcase (likely a finite enumeration for $n \leq N_0$, analytic for $n$ large).

### ERR-A-04 — Theorem 11.1 Case A L-bound (same defect)

- **Location:** `lrc_proof_v11_2.md`:§11, line 453.
- **Statement (as written):** "$|E_{\mathrm{div}}| \geq 2$ forces $L \geq \operatorname{lcm}(n, 2n) = 2n$ and, more sharply, $L \geq 2n \cdot (n-1) = 2n(n-1)$ whenever two distinct divisible speeds are present."
- **Defect:** $\operatorname{lcm}(n, 2n) = 2n$, not $2n(n-1)$. The "more sharply" claim is unjustified. Two divisibles $\{n, 2n\}$ force $L \geq 2n$ only.
- **Downstream impact:** Same as ERR-A-03; invalidates the chamber-width estimate.
- **Salvage status:** **S3** (same remedy as ERR-A-03).

### ERR-A-05 — §12.2 "no computational certificate"

- **Location:** `lrc_proof_v11_2.md`:§12.2, line 501.
- **Statement (as written):** "No computational certificate is invoked."
- **Defect:** §8 (Theorem 8.2 proof, line 335) and §11 (Theorem 11.1 Case A, line 465) BOTH explicitly invoke the harness `reports/v11_1_verification/harness_v11_1.py` as the means of handling small-$L$ residuals.
- **Salvage status:** **S3** (documentation fix) if residuals can be made analytic; **S4** (keep but disclose) if the harness is genuinely required.

---

## Lineage A — Salvage Map

| Error ID | Classification | Fix scope |
|---|---|---|
| ERR-A-01 | **S2/S4** | Rebuild §2.4 framework: replace $[b]_n$-indexed bad-set with chamber-indexed or floor-indexed notion; re-derive §5.1b thinness, §6 coverage-transfer, §9 Theorem 9.2c, §10 Lemma 10.2 in new framework. |
| ERR-A-02 | S3 | Add $-q_e$ correction throughout §10 proofs; re-check Lemma 10.2 conclusion survives. |
| ERR-A-03 | S3 | Extend Prop 5.1 small-$L$ coverage; or add finite-enumeration certificate with explicit range. |
| ERR-A-04 | S3 | Same as A-03. |
| ERR-A-05 | S3 | Rewrite §12.2 honestly; either make residuals analytic or disclose the harness. |

**Recommended rebuild order:**
1. Fix ERR-A-01 first — all downstream lemmas depend on it. Without a correct fibre-safe identity, §§5–11 are castles on sand.
2. Once a correct framework is in place, re-derive Lemma 6.0 (coverage-transfer) in the new language.
3. Then re-derive Lemma 10.2 and Theorem 9.2c.
4. Finally fix the small-$L$ bookkeeping (A-03, A-04, A-05).

**Likely outcome:** Some portion of v10.12's distributed safe-fibre machinery will have to be reinstated. The v11.1/v11.2 "unified Lemma 2.5" refactor introduced a structural defect the earlier architecture did not have.

**§2.4 Rebuild document:** `lrc_sec2_4_rebuild_v1.md` (2026-04-19). Provides:
- Correct safety criterion: $T_e(b) \bmod n \in \{1,\ldots,n-2\}$ — function of floor state alone, not of $[b]_n$.
- Replacement **Lemma 2.5'** (Chamber-Safe Characterization): proved from first principles; correctly handles both counterexamples.
- Explanation of how bad-sets remain useful as *residue-level bookkeeping* tools (not fibre-safety tests).
- Minimal repair checklist: 7 items, sequential critical path.
- Sliding-window (§6) survival analysis: structure survives; usage of bad-set as fibre-safety iff must be replaced.
- ERR-A-02 (Lemma 10.2) corrected formula: $T_e \equiv \rho_e - 1 - q_e \pmod n$; paper was correct only for $q_e=0$.

---

## Lineage B — n=11 AP Paper (re-audit 2026-04-18)

### ✓ Verified sound

**Baton-pass witness $t^* = 69/275$** (`lrc_n11_baton_pass_v1.md`, Case C). Independently re-derived:
- $a_9 \cdot t^* = (25/3)(69/275) = 1725/825 = 23/11$; fractional part $= 1/11$ ✓
- $a_5 \cdot t^* = (100/23)(69/275) = 6900/6325 = 12/11$; fractional part $= 1/11$ ✓

Both runners 5 and 9 reach position $1/11$ simultaneously at $t^*$. Exact rational. ✓

**Lemma P (phase-independence of bad-interval widths)** (`lrc_n11_periodicity_lemma_v1.md`). Width $|B_{j,k}| = 2/(11a_j)$ follows by direct subtraction; trivially $k$- and $m$-independent. ✓

**Lemma C (cascade conclusions speed-range only)** — **CONDITIONAL.** Each algebraic step in Lemma C is a ratio/width computation (e.g., step A2 gives $a_8 \geq 8a_3/3$ from $k'=2$; step A4 computes $B_{6,4}[0] = 228/275$ exactly at $a_6 = 225/38$). These are phase-independent. However, soundness of Lemma C as a whole depends on the underlying Chain A / Chain B / PSM cascade being *complete* (enumerating every runner that can cover the target gap). Cascade completeness audit deferred — requires reading `lrc_n11_universalincompat_v3.md`.

**Theorem PU** closes the flagged "GF(I₄)+GF(I₉)>0 wrong for Chain A" defect in `lrc_n11_route3_residual_analysis_v1.md:251` by correctly framing the conclusion as "GF(I_k^{(m)}) > 0 for SOME k ∈ {1,...,8}", not specifically {4,9}. ✓ (conditional on Lemma C completeness)

### ✗ Gaps found

### ERR-B-01 — Lemma 3.1 Step 2 misses runner 8 at k=2

- **Location:** `lrc_n11_incompatibility_v1.md`:§3 Lemma 3.1 Step 2, lines 73–81.
- **Statement (as written):** "For runner $j \in \{4,5,7,8\}$ ($a_j < j$) to have $B_{j,k}$ start at or before $45/110$" — paper enumerates $k=0,1,2$ but rules out $k=2$ via "Runner 7 has $a_7 < 7 < 7.11$".
- **Defect:** Paper considers only runner 7 for $k=2$, ignoring runner 8. Runner 8 at $k=2$ requires $a_8 \in [64/9,\,748/99] \approx [7.111,\,7.556]$ — fully compatible with $\sigma_8 = -1$ in the ++------ class ($a_8 < 8$).
- **Explicit witness:** At $a_8 = 64/9$: $B_{8,2} = [32\cdot 9/(11\cdot 64),\,34\cdot 9/(11\cdot 64)] = [288/704,\,306/704] = [9/22,\,153/352] = [45/110,\,153/352]$. The interval starts **exactly** at $45/110$ — the left boundary of $J_4$ — so runner 8 covers the boundary point without invoking runner 2.
- **Downstream impact:** Lemma 3.1's conclusion "covering $45/110$ requires $a_2 \geq 20/9$" is only valid if runner 8 is excluded. With runner 8 as a candidate, the bound $a_2 \geq 20/9$ does not follow. Theorem 4.1 (the incompatibility) becomes conditional on ruling out runner 8 in Step 2.
- **Salvage status:** **S3 (weaken-and-keep, likely).** The paper's pattern for ruling out alternatives (runner 5 → GF(I₂)>0; runner 7 → GF(I₇)>0) suggests runner 8 at $a_8 \in [7.111,\,7.556]$ likely creates GF > 0 in some slot (candidates: I₆ or I₈ via runner 8's shifted bad intervals). This needs to be written out; the theorem should survive but the proof is incomplete as stated.

### ERR-B-02 — Lemma 3.2 Step 1 misses runners 5/7/8 at $k \geq 3$

- **Location:** `lrc_n11_incompatibility_v1.md`:§3 Lemma 3.2 Step 1, lines 125–132.
- **Statement (as written):** Paper enumerates $k=0,1,2$ and jumps to $k=7$, concluding "no runner for $k \geq 3$ in the feasible speed range."
- **Defect:** The paper's $k \geq 3$ sweep is not exhaustive. At least three missed candidates:
  - **$k=3$, runner 5:** $a_5 \in [43/10,\,45/10] = [4.3,\,4.5]$, compatible with $\sigma_5 = -1$ ($a_5 < 5$). Paper FLAGS this ("runner 5 could be in this range") but does not analyze. Self-contradictory with the later conclusion.
  - **$k=5$, runner 7:** requires $a_7 \in [65/10,\,67/10] = [6.5,\,6.7]$, compatible with $\sigma_7 = -1$ ($a_7 < 7$). Not mentioned.
  - **$k=6$, runner 8:** requires $a_8 \in [76/10,\,78/10] = [7.6,\,7.8]$, compatible with $\sigma_8 = -1$ ($a_8 < 8$). Not mentioned.
- **Downstream impact:** Lemma 3.2's "only runner 2 can cover $10/11$" claim is false as stated. The bound $a_2 \leq 575/261$ is not forced; alternative coverers exist at three separate $(j,k)$ combinations.
- **Salvage status:** **S3 (weaken-and-keep).** As in ERR-B-01, each alternative likely creates GF > 0 elsewhere (e.g., shifting runner 7 away from its natural $I_7$ coverage). The lemma's overall strategy should survive but requires at least three additional case analyses.

### ERR-B-03 — Theorem 4.1 incompatibility inherits both gaps

- **Location:** `lrc_n11_incompatibility_v1.md`:§4 Theorem 4.1, lines 167–184.
- **Statement (as written):** "By Lemma 3.1, closing $I_4$ requires $a_2 \geq 20/9$. By Lemma 3.2, closing $I_9$ requires $a_2 \leq 575/261$. These are incompatible."
- **Defect:** Neither sub-bound is forced without first ruling out the candidates missed in ERR-B-01 and ERR-B-02. The 5/261 gap argument is correct arithmetic ($5220 > 5175$), but its premise (only runner 2 can cover the boundaries) is unestablished.
- **Salvage status:** **S3 / S2.** Contingent on ERR-B-01 and ERR-B-02 being patched. Main Claim 5.1 is likely still true (the paper's pattern of alternatives-create-GF-elsewhere is plausible) but the proof is presently incomplete.

### Pending Lineage-B audit items (next session)

- **Cascade completeness** in `lrc_n11_universalincompat_v3.md`: do Chain A / Chain B / PSM fully enumerate candidates for covering each target gap? The Runner-2 Incompatibility gaps suggest the cascade-enumeration habit in Lineage B may be systemic. If so, Lemma C is weaker than claimed.
- **Corollary W_ref** (`lrc_n11_periodicity_lemma_v1.md`): the statement "runner $v_{10}$ makes at least 81 pacemaker sub-cycles within $W_{\mathrm{ref}}$" uses $a_1 < 1$ for ratio > 10; re-verify the $\geq 81$ count.
- **Residual [89, 100]** closure: the "Route 3 + W₁ hybrid" approach suggested in `lrc_n11_route3_residual_analysis_v1.md:283` is sketched but not written out.

**Lineage-B provisional verdict:** n=11 proof is **not presently airtight**. Three enumeration gaps found; likely patchable but requires work. Zenodo v31 should not be cited as settled until ERR-B-01/02/03 are resolved.

---

## Lineage C — Tier 2 / v10.12 (pending re-audit)

- `lrc_proof_v10_12.md` uses Lemma 2.1 (Coupled blocking) + per-case safe-fibre reasoning, **not** a unified iff identity. On face it may escape ERR-A-01.
- Open Tier 2 flags from `lrc_proof_status.md`: GG2 upgrade, PL-KINDEP.
- Next-session audit: step through v10.12 §2.1 and §§7–10, checking each safe-fibre derivation on its own terms. If v10.12 is sound, it becomes the fallback canonical.

---

## Recommended Canonical Working Version (provisional)

Until re-audit completes:

- **n=11**: `lrc_n11_ap_paper_v22.md` provisionally, pending Theorem U re-derivation. Zenodo v31 is frozen and should not be cited as settled.
- **n=all Tier 1**: no canonical version — v11.2 is broken, v10.12 not yet re-audited. **Do not cite any current file as "Tier 1 proved."**
- **n=all Tier 2**: pending v10.12 re-audit.

---

---

## Lineage C — Error Catalog (v10.12 Tier 1 + Tier 2 line)

**Architecture:** v10.12 does **not** use the unified Lemma 2.5 iff that broke in Lineage A. Instead it uses distributed reasoning: §2.1 Lemma 2.1 "Coupled blocking", §5 actual-speed floor-reset chain (CT.1-FINAL, inherited from v10.11), §9.2c Dropped-Runner Targeting, §11.3a Late-window safe-fibre lemma. **However, two of these pillars carry their own actual-vs-representative defects.**

### ERR-C-01 — Lemma 11.3a (Late-window safe-fibre lemma), v10.12 only

- **Location:** `lrc_proof_v10_12.md`:§11.3, lines 817–838.
- **Statement (as promoted in v10.12):** "Proved for composite $n \geq 4$. ... the residue $s_d := d^{-1}-1$ is uncovered by every retained runner at every fibre $b \in J \cap \mathbb{Z}$ where $J = [(n-2)L/(n-1), (n-1)L/n]$."
- **Defect:** The proof explicitly restricts to "retained runner $e \in \{1, \ldots, n-1\}$" and uses the floor-state bound $\lfloor eb/L\rfloor = e-1$, which holds only when the **actual speed** $e < n$. For actual speeds $e = nq + \rho$ with $q \geq 1$ (residue $\rho$ but larger integer value), the actual floor at $b^* = (n-1)L/n$ is $(n-1)q + \rho - 1$, not $\rho - 1$. Additionally, the proof does **not** address divisible runners $e = kn$, which at $b^*$ have floor $k(n-1)$ and bad set $\mathbb{Z}/n\mathbb{Z}$ (since $n \mid k(n-1)+1$ for $k=1$).
- **Counterexample (hand-verified and python-checked):** $n=6$, $E = \{7, 2, 3, 10, 6\}$, $d=5$ dropped unit. $L = \operatorname{lcm}(7,2,3,10,6) = 210$. $J = [168, 175]$. $b^* = 175$. $s_d = 5^{-1} - 1 \bmod 6 = 4$. Actual floor of runner 10 (residue 4, $q=1$) at $b^*$ is $\lfloor 10 \cdot 175/210 \rfloor = 8$, and $\mathrm{bad}(10, 8, 6) = \{1, 4\}$ — covers $s_d$. Runner 6 at floor 5 has $\mathrm{bad} = \mathbb{Z}/6\mathbb{Z}$ — covers all residues. **Every fibre in $J$ is unsafe.** The global $x_0(E) = 90$ via other fibres, so LRC still holds; only the proof path via $b^*$ fails.
- **Verified by:** hand + python harness this session.
- **Honest v10.11 precedent:** `lrc_proof_v10_11.md`:§11.3 labels the same lemma as "**Late-window bridge template; under repair**" with explicit text: "*The intended conclusion is that, **after the actual-speed/residue bridge is rebuilt**, the residue $s_d$ is uncovered on $J$*". **v10.12 is therefore a regression:** it promotes an under-repair template to "proved" without performing the repair.
- **Upstream dependencies:** Paper's §5.3 actual-speed definition (sound); floor-state formula (sound for residue-only but proof needs actual-speed lift).
- **Downstream dependents:** Proposition 11.3-FINAL (Tier 1 and Tier 2 for composite dropped-unit); §12.1 Theorem 12.1 Case A (when absent residue is unit); all composite-$n$ dropped-unit Tier 1 claims in `lrc_proof_v10_12.md`:§13.
- **Salvage status:** **S2 / S3 hybrid.** For tuples with all non-divisible actual speeds $< n$, the proof goes through unchanged (true statement, used correctly). For tuples with $q \geq 1$ non-unit runners, the lemma is false as stated. The repair requires:
  (i) a stronger actual-speed floor formula at $b^*$ — this gives $\{\rho_e^{-1}(q+1) - 1, \rho_e^{-1}q - 1\}$ for units, and coset-of-$H_g$ for non-units at different offsets than the current proof admits;
  (ii) separate handling of divisible runners (not done in v10.12). Since $b^* = (n-1)L/n$ is a floor-reset of the divisible runner, a different witness fibre may be needed.

### ERR-C-02 — Theorem 9.2c (Dropped-Runner Targeting) representative/actual conflation

- **Location:** `lrc_proof_v10_12.md`:§9.2c, lines 558–574.
- **Statement (as written):** "for composite $n \geq 4$ and non-unit $d$ absent from $E_{\mathrm{non}}$: ∃ $m$ such that the $m$-th floor-reset of $e_u := n - u$ has no CG1 coverers and unique CG2 runner $= d$; hence departing residue is uncovered."
- **Defect:** The uniqueness step "CG2 confines $e$ to $[n-e_u, n-1]$, which has length exactly $e_u$, so the unique element $\equiv d \pmod{e_u}$ is $d$ itself" is stated in representative form. The integrity note at line 552 admits: "Theorems 9.2b–9.2d below still retain the older representative-form shorthand, so they remain working templates rather than fully re-audited final statements." The actual-speed criterion (Lemma 9.2a′, line 519) requires $\sigma_{e_u}(e, m) \equiv \rho_e + u \pmod n$ where $\sigma = em \bmod e_u$. Multiple actual speeds with different residues $\rho_e$ can satisfy this, not just residue $\rho_e \equiv d$.
- **Counterexample (hand-verified and python-checked):** $n = 6$, $d = 4$ (non-unit, dropped), $e_u = 5$, $m = 2$, $r_{\rm dep} = 1$. Replace residue-2 runner (actual speed 2) with actual speed 8 (residue 2, $q=1$). $E = \{1, 8, 3, 5, 6\}$, $L = 120$, floor-reset fibre $b = 2L/5 = 48$. Runner 8 at $b=48$: $\sigma_{e_u}(8, 2) = 16 \bmod 5 = 1$; actual CG2 requires $\sigma \equiv \rho_e + u \pmod n = 2 + 5 \equiv 1 \pmod 6$ — **satisfied**. $\mathrm{bad}(8, 3, 6) = \{1, 4\}$ covers $r_{\rm dep} = 1$. $b = 48$ is unsafe; paper claimed it would be safe.
- **Verified by:** hand + python harness this session; LRC conclusion $x_0(E) = 56 \geq 1$ still holds globally via other fibres.
- **Upstream dependencies:** Lemma 9.2a (representative) — used as-if-complete by Theorem 9.2c; Lemma 9.2a′ (actual, correctly stated) — unused by Theorem 9.2c.
- **Downstream dependents:** All Tier-1 invocations in composite branches: §11 Sub-case B2 ($n$ odd multi-prime), §11 Sub-case B3 ($n = p^k$), Corollary 11.0, §12.1 Case B; also the Tier-2 amplifications in Theorems 9.3b and 9.3f.
- **Salvage status:** **S2.** The algebraic structure of the argument (unique $\sigma$ representative in $[u, n-1]$ mod $e_u$) is correct for representatives. For actual speeds, a multi-speed version is needed — either (a) re-choose $m$ to satisfy actual-speed CG2 uniquely (parameter-search), or (b) carry through with multiple actual-speed CG2 coverers and show at least one actual "virtual-d" collision is absent. The paper's §9.2b integrity note already anticipates this; the repair just has not been written out.

### ERR-C-03 — §2.7 Theorem 2.4 (general-prime Runner Incompatibility) inherits Lineage-B gaps

- **Location:** `lrc_proof_v10_12.md`:§2.7, lines 197–207.
- **Statement (as written):** For prime $p \geq 11$, closing $I_{(p-3)/2}$ forces $a_2 \geq A_2(p) = 2(p-1)/(p-2)$; closing $I_{p-2}$ forces $a_2 \leq B_2(p) = (2p+1)(p-1)^2/((p^2-3p-1)(p+1))$; these are incompatible since $A_2 - B_2 = (p-1)(p^2-9p-4)/[(p-2)(p^2-3p-1)(p+1)] > 0$.
- **Defect:** The algebraic difference is correct (identity $p^2 - 9p - 4 = 2p^3 - 4p^2 - 8p - 2 - (2p^3 - 5p^2 + p + 2)$ verified). But the *bounds themselves* $A_2(p)$ and $B_2(p)$ rest on the same enumerative structure as Lemmas 3.1/3.2 of `lrc_n11_incompatibility_v1.md`, where this review previously found **ERR-B-01** (Lemma 3.1 Step 2 misses runner 8 at $k=2$) and **ERR-B-02** (Lemma 3.2 Step 1 misses runners 5, 7, 8 at various $k$).
- **Propagation:** The general-prime generalisation re-runs the same enumeration *schema* that leaked at $p=11$; the gaps have not been closed at the general $p$ level either.
- **Salvage status:** **S2/S3.** The $p=11$ bounds are computationally certified tight, so ERR-B-01/B-02 probably admit a cascade-completeness patch (in the style of Theorem PU Chain B). The general-prime generalisation in v10.12 §2.7 inherits both the algebraic strength and the enumeration debt. Must be rebuilt alongside the Lineage-B repair.

### Clean parts of v10.12 (no new defects found in this pass)

- **§3 Theorem 3.1 (Irrational).** Standard equidistribution argument; sound.
- **§4 Theorem 4.1 (Case 1, $n \nmid e_i$ for all $i$).** Analytic argument; sound as far as audited.
- **§5.2 Proposition 5.1 ($L = n, 2n$).** Direct inspection for small cases.
- **§5.3 Lemma 5.1a (Exact base-fibre patcher criterion).** Uses correct actual-speed formula. Sound.
- **§5.3 Proposition CT.1-FINAL.** Uses actual CG1/CG2 throughout (Lemma 9.2a′); proof by strict monotonicity of $b^{(k)}$. The chain-transfer termination argument is sound.
- **§5.3 Lemma 5.2 for prime $n$.** Combines Lemma 5.2a (small-speed, sound) with CT.1-FINAL (large-speed, sound). **Prime dropped-unit branch is genuinely proved in v10.12** (this is the one Lineage-C result that survives cleanly).
- **§8.3 Theorem 8.3 (Extreme divisible runners).** Uses $L \geq \operatorname{lcm}(n, 2n, n-1) = n(n-1)$ for odd prime $n \geq 5$ (correct lcm arithmetic, unlike ERR-A-03/A-04 in v11.2). Argument is sound.
- **§9.2d-II, 9.2d-III (Large-Factor Witnesses, Universal Witness Pair).** Algebraic closed-form certificates for $p_{\min}$-driven witness speeds; sound at the representative level. May inherit the actual-speed caveat but the witness construction is a constructive existence, so if the witness *actual* speed is not in $E_{\rm non}$, the isolated event holds.
- **§9.3b, 9.3f (Multi-prime and prime-power quantitative bounds).** Analytic bounds on $B_{\rm safe}$; the chamber-width argument $|J| \geq L/(n(n-1))$ does not depend on the broken Lemma 11.3a. Sound.

---

## Lineage C — Salvage Map and Recommended Canonical Version

### Salvage table

| Error | Lineage | Salvage | Rebuild scope | Repair doc |
|---|---|---|---|---|
| ERR-C-01 | C | S2/S3 | Actual-speed lift of floor-state formula at $b^*$ + separate divisible-runner handling. Moderate — self-contained to §11.3. | `lrc_c_err_repair_v1.md` Part 1 |
| ERR-C-02 | C | S2 | CG1/CG2 only capture reset-triggered coverage; pre-existing bad-set coverage of $r_{\rm dep}$ ignored. Repair D: modified $m$ search verified to exclude pre-existing coverage. Large-$e_u$ existence proved; small-$e_u$ open. | `lrc_c_err_repair_v1.md` Part 2 |
| ERR-C-03 | B + C | S2/S3 | Requires cascade-completeness repair of Lemmas 3.1/3.2 in `lrc_n11_incompatibility_v1.md` — closes both ERR-B-01/02 at $p=11$ and ERR-C-03 at general $p$. Single repair, two downstream closures. | Blocked on ERR-B-01/02 |

**ERR-C-01 repair progress (2026-04-19):** Correct floor formula derived: $T_e(b^*) = e - q_e - 1$. Divisible runner $kn$ with $k \equiv 1 \pmod n$ has bad $= \mathbb{Z}/n\mathbb{Z}$ at $b^*$ (floor-reset event). Fix: use $\hat{b} = b^*-1$; divisible bad-set = ∅ there. Verified on counterexample ($n=6$, $e=6$, shift to $b=133$ confirms $s_d=4$ uncovered). General actual-speed condition $(\dagger)$ derived. Lemma 11.3a' (corrected statement) written.

**ERR-C-02 repair progress (2026-04-19):** Root cause refined: CG1/CG2 capture coverage TRIGGERED by floor-reset, not PRE-EXISTING coverage from runner's own floor state. Counterexample runner 8 fails CG1 and CG2 formally ($\sigma_f(8,2)=1 \not\equiv s+u=3 \pmod 6$) but has $r_{\rm dep}=1 \in \mathrm{bad}(8,3,6)=\{1,4\}$ independently. Repair D (modified $m$ search) defined; large-$e_u$ case existence proved by counting argument ($2(n-2)/e_u < 1$ when $e_u > 2(n-2)$). Small-$e_u$ open.

**ERR-B-01 repair progress (2026-04-19):** Runner 8 at $k=2$ confirmed as genuine missed candidate. Key lemma: runner 8 cannot cover $t^* = 69/275$ when at $a_8 \in [64/9, 748/99]$ (start of $B_{8,1} \geq 0.2527 > t^*$). Joint constraint: runner 2 at $J_9$-covering speed ($a_2 \leq 575/261$) also cannot cover $t^*$. Sub-cases D1 (runner 4 covers $t^*$) and D2 (runner 5 covers $t^*$) identified; not yet closed — require full slot-coverage analysis. See `lrc_n11_incompatibility_repair_v1.md`.

**ERR-B-02 repair progress (2026-04-19):** Runner 7 at $k=5$ ($a_7 \in [6.5, 6.7]$) closed: forces GF$(I_7) > 0$ since $a_7 < 6.923$ cannot cover $I_7$. Runner 8 at $k=6$ closed: mutually exclusive with ERR-B-01 runner-8 regime. Runner 5 at $k=3$ ($a_5 \in [4.3, 4.5]$) open: runner 5 covers $t^*$ in $I_2$ at this speed, no obvious gap exposed. See `lrc_n11_incompatibility_repair_v1.md`.

### Recommended canonical working version

- **Tier 1, prime $n$, dropped-unit:** `lrc_proof_v10_12.md` §5.3 (Lemma 5.2 + CT.1-FINAL) is the cleanest proved path. **Keep.**
- **Tier 1, composite $n$, dropped-unit:** `lrc_proof_v10_12.md` §11.3 Proposition 11.3-FINAL is broken (ERR-C-01). **Revert to v10.11's honest "template under repair" labelling**, not v10.12's "proved". Rebuild required.
- **Tier 1, composite $n$, dropped two non-units:** `lrc_proof_v10_12.md` §9.2c Theorem 9.2c has ERR-C-02 at actual speeds. **Mark as representative-form template**, not theorem-secure.
- **Tier 1, composite $n$, multi-div:** §12.1 Case B inherits ERR-C-02; Case A inherits ERR-C-01. **Both templates until rebuilds land.**
- **Tier 2 quantitative:** §9.3b, §9.3f analytic bounds survive. Usable as conditional statements given the Tier 1 repairs.
- **Lineage B (n=11 AP paper):** Keep `lrc_n11_ap_paper_v22.md` (or v30 frozen Zenodo preprint) but annotate ERR-B-01/02/03 as open audit items. Runner-2 Incompatibility at $p=11$ is computationally tight and likely defensible once cascade-completeness is written.

### Cross-version fingerprint (which version suffers which defect)

| Defect | v7.x | v8.x | v9.x | v10.0–10.10 | v10.11 | v10.12 | v11.0–11.2 |
|---|---|---|---|---|---|---|---|
| Unified Lemma 2.5 iff (ERR-A-01) | — | — | — | — | — | — | **✗** |
| §10 Lemma 10.2 floor formula missing $-q_e$ (ERR-A-02) | — | — | — | — | — | — | **✗** |
| §8 Thm 8.2 L-bound "$L<n(n-1)\Leftrightarrow L\in\{n,2n\}$" (ERR-A-03) | — | — | — | — | — | — | **✗** |
| §11 Thm 11.1 Case A L-bound (ERR-A-04) | — | — | — | — | — | — | **✗** |
| §12.2 "no computational certificate" disclosure (ERR-A-05) | — | — | — | — | — | — | **✗** |
| §11.3a late-window template | flag-only | flag-only | flag-only | flag-only | **flagged as template** | **promoted to proved (ERR-C-01)** | inherited in modified form |
| §9.2c representative form (ERR-C-02) | — | partial | partial | partial | flagged | **used as if proved (ERR-C-02)** | inherited |
| §2.7 Thm 2.4 general-prime Runner Incompatibility (ERR-C-03) | — | — | — | — | — | **✗** | — |
| Prime $n$ dropped-unit (Lemma 5.2 + CT.1) | template | template | template | template | **PROVED (v10.11)** | **PROVED (inherited)** | inherited |

**Reading the table:** The fatal v11.x defects are confined to the v11 line. The v10.12 promotion-to-proved of two still-representative templates (ERR-C-01, ERR-C-02) is a v10.12-specific regression; v10.11 correctly flagged both as templates. The prime dropped-unit branch (§5.3 Lemma 5.2 + CT.1-FINAL) is genuinely proved in v10.11 onwards and survives across all subsequent versions.

---

## Verification Checklist (for this review document)

- [x] ERR-A-01 counterexamples hand-computed and recorded.
- [x] ERR-A-02 counterexample hand-computed.
- [x] ERR-A-03/04 L-arithmetic hand-checked ($\operatorname{lcm}(n, 2n) = 2n$, not $2n(n-1)$).
- [x] ERR-B-01/02/03 enumeration gaps identified in Runner-2 Incompatibility at $p=11$.
- [x] ERR-C-01 counterexample at $n=6$, $E=\{7,2,3,10,6\}$ hand + python verified.
- [x] ERR-C-02 counterexample at $n=6$, $E=\{1,8,3,5,6\}$ hand + python verified.
- [x] ERR-C-03 inheritance from Lineage-B documented.
- [x] Cross-version fingerprint table built.
- [x] **Python-verified all 5 counterexamples (2026-04-19):** ERR-A-01a (b=6 safe, paper unsafe: CONFIRMED), ERR-A-01b (b=4 unsafe, paper safe: CONFIRMED), ERR-A-02 (floor=5, paper predicts 0, corrected formula matches: CONFIRMED), ERR-C-01 (runner 6 covers all residues via bad(6,5,6)=Z/6Z: CONFIRMED), ERR-C-02 (runner 8 has bad(8,3,6)={1,4} covering r_dep=1: CONFIRMED). Python code used correct Sol(e,j,n) coset implementation (gcd-quotient method). Note: earlier Python run had bug (only returned zero-coset); corrected version confirms all results.
- [x] **DeepSeek independently confirmed ERR-A-02** (floor formula): CONSISTENT/HIGH confidence.
- [x] **DeepSeek independently confirmed ERR-C-01** (divisible runner coverage at b*=175): CONSISTENT/HIGH confidence.
- [ ] Qwen cross-check of ERR classifications.
- [ ] Lineage B re-derivation of Theorem U, Runner-2 Incompatibility, Baton-pass.
- [x] Updated `lrc_proof_status.md` to reflect this verdict.
- [x] Updated `session_state.md` to reflect Lineage-C findings (2026-04-19).

---

## Next Actions

1. **Immediate:** Update `lrc_proof_status.md` Tier 1 verdict to reflect ERR-C-01/02 findings; update `session_state.md` to note Lineage-C audit delivered.
2. ~~Run DeepSeek independent verification~~ — **DONE via Python (2026-04-19)**: all 5 counterexamples confirmed; ERR-A-02 additionally confirmed by DeepSeek.
3. **Medium-term:** Rebuild §2.4 — **started**: `lrc_sec2_4_rebuild_v1.md` (2026-04-19) provides Lemma 2.5', correct framework, repair checklist. Next: integrate into a v11.3 or v10.13 draft.
4. **Medium-term:** Lineage B Theorem U re-derivation with runner-8 / runner-5,7,8 alternative scenarios.
5. **Medium-term:** Lineage C actual-speed lift of §9.2c and §11.3a.
6. **Long-term:** Produce v11.3 (or revert to v10.12-based v10.13) with all four Lineage-A errors fixed and re-verified.
