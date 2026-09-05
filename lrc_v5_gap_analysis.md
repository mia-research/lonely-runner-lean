# LRC v5 Draft — Gap Analysis and Mismatch Report

**Date:** 2026-03-07
**Purpose:** Identify unintentional gaps and mismatches in the v5 unified proof draft

---

## 1. Issues Raised by the External Review (of v3) — Status in v5

| # | Review Issue | v3 Status | v4 Fix | v5 Status | Remaining? |
|---|---|---|---|---|---|
| 1 | Lemma 8.3 (z=0 safety overclaimed at all floor states) | FLAWED | Retired; replaced by FLOOR-SAFE chain | v5 §8.2 uses Unit Residue Isolation correctly | **PARTIALLY RESOLVED — see Gap A below** |
| 2 | Near-complete template assumed for general tuples | FLAWED | Z0S + U-FORCE work for all tuples | v5 §10.1, §11 use U-FORCE correctly | **RESOLVED** |
| 3 | Counting bridge asserted without proof | MISSING | Proposition O3 proved | v5 §9 provides analytic argument | **RESOLVED** |
| 4 | M₁ < n² bound wrong | WRONG | Corrected to M₀ < n² unconditionally | v5 §9.4 uses correct bound | **RESOLVED** |
| 5 | Prop 4.1 for L=2n unproved | MISSING | Not explicitly addressed in v4 | v5 §4.2 provides sketch proof | **PARTIALLY RESOLVED — see Gap B** |
| 6 | General case reduction missing | MISSING | Z0S handles it | v5 §12 case analysis is exhaustive | **RESOLVED** |

---

## 2. Gaps and Mismatches Identified in v5

### Gap A: Unit Residue Isolation at General z=0 Events (CRITICAL)

**The problem:** Lemma 8.2 (Unit Residue Isolation) in v5 proves that at a z=0 event for unit runner $e_u$, the residue $r_u$ is uncovered by other runners. The proof is clean at **floor 0** (using the Sole Cover bijection). But the Z0S.3 master bound sums over ALL z=0 events for $e_u$ (at floors $m = 1, 2, \ldots, e_u - 1$), not just floor 0.

**At floor $m > 0$:** Other runners are NOT at floor 0. They may have advanced to floor states where their bad sets cover $r_u = -(m) \cdot e_u^{-1} \bmod n$ (which is different from $-e_u^{-1}$ at floor 0). The Sole Cover argument does NOT directly apply at higher floors.

**What v3 did wrong:** v3's Lemma 8.3 claimed z=0 safety at all floor states — the review correctly flagged this as flawed.

**What the closure documents say:** `lrc_o1_o2_formal_closure_v1.md` states the Z0S.1 count is $e_u - 1$ and the "Non-Coincidence note" discusses coincident events. But the proof of safety at each z=0 event **implicitly assumes Unit Residue Isolation holds at all floors**, not just floor 0. The document says: "by Unit Residue Isolation (which is proved for each runner individually), the fibre is safe for at least one of the two runners."

**Is this actually a gap?** This is the **same flaw** the reviewer identified in v3's Lemma 8.3. The closure documents do not fully resolve it — they assert that each z=0 event produces a safe fibre, but the proof only works at floor 0.

**However:** The Z0S.3 bound $B_{\rm safe} \geq \varphi(n)(n-2)/2 + 2$ may still hold if we can show that z=0 events at higher floors also produce safe fibres. The key question: at $b = mL/e_u$, runner $e_u$ transitions from floor $m-1$ to floor $m$. The departing residue is $r = -(m-1) \cdot e_u^{-1} \bmod n$ (which was in bad$(e_u, m-1, n)$ but not in bad$(e_u, m, n)$). Is this residue covered by another runner at that fibre?

**Possible resolution routes:**
1. Show the departing residue at each z=0 event is distinct from all other runners' bad-set elements (hard in general).
2. Use a weaker bound: only count z=0 events where the departing residue is provably uncovered (e.g., at floor 0 only). This gives $B_{\rm safe} \geq \varphi(n) - 1 + 2 = \varphi(n) + 1$, which still $\geq \varphi(n)$ but **not necessarily $\geq n$** for the run cap.
3. Use a different structural argument that doesn't rely on z=0 safety at arbitrary floors.

**Severity: HIGH.** If only floor-0 z=0 events are safe, then Z0S.3 gives $B_{\rm safe} \geq \varphi(n) + 1$ (from T3 endpoints + one z=0 per runner at floor 0), NOT $\varphi(n)(n-2)/2 + 2$. The run cap ($\geq n$) would fail for small $\varphi(n)$ composites.

**WAIT — correction.** At floor 0, each unit runner $e_u$ has exactly ONE z=0 event (at $b = L/e_u$, corresponding to $m = 1$, where floor goes from 0 to 1). At this event, the departing residue is $r = 0 \cdot e_u^{-1} = 0$... no. Let me recompute.

At $b = L/e_u$ (the first z=0 event): floor goes from 0 to 1. bad$(e_u, 0, n) = \{0, -e_u^{-1}\}$. bad$(e_u, 1, n) = \{-e_u^{-1}, -2e_u^{-1}\}$. The departing residue is $0$ (in bad at floor 0, not in bad at floor 1). The entering residue is $-2e_u^{-1}$.

Residue 0 departing: is residue 0 covered by other runners? At the fibre $b = L/e_u$, other runners have floor $\lfloor e' \cdot L/(e_u \cdot L) \rfloor = \lfloor e'/e_u \rfloor$. For $e' < e_u$: floor 0. For $e' > e_u$: floor $\geq 1$.

At floor 0, every unit runner $e'$ has $0 \in \text{bad}(e', 0, n)$. So residue 0 IS covered by all other runners at floor 0. The departing residue 0 is NOT the useful one — it's still covered.

So the z=0 event doesn't expose residue 0 (it's still covered by other runners). What about $-e_u^{-1}$? That residue STAYS in bad$(e_u, 1, n)$. So neither departing nor staying residue is exposed.

**This means the z=0 event at $b = L/e_u$ does NOT produce a safe fibre through the departing-residue mechanism.** The claim that each z=0 event produces a safe fibre is wrong in general.

**REVISED ASSESSMENT:** The Z0S.3 identity as stated appears to have the SAME flaw as v3's Lemma 8.3. The counting of safe fibres from z=0 events is not correctly justified.

**But wait — the closure document's Non-Coincidence note says something different.** It counts z=0 events as safe because "at each such b, the residue −(m−1)·e_u^{−1} mod n was solely covered by e_u immediately prior, and is exposed at b." Let me re-examine.

At $b = mL/e_u$ (z=0 event for $e_u$, floor $m-1$ to $m$):
- bad$(e_u, m-1, n) = \{-(m-1)e_u^{-1}, -me_u^{-1}\}$
- bad$(e_u, m, n) = \{-me_u^{-1}, -(m+1)e_u^{-1}\}$
- Departing: $-(m-1)e_u^{-1}$
- Entering: $-(m+1)e_u^{-1}$

The claim is that $-(m-1)e_u^{-1}$ was solely covered by $e_u$ and is now exposed. But "solely covered" means no other runner's bad set contains this residue at fibre $b$. This is the part that needs proof.

For the Sole Cover argument to work at general $m$: we need that the residue $-(m-1)e_u^{-1} \bmod n$ is not in any other runner's bad set at fibre $b = mL/e_u$. This is NOT guaranteed by the floor-0 bijection argument.

**Conclusion: Gap A is REAL and CRITICAL. Z0S.3 as stated is not fully proved.**

---

### Gap B: Proposition 4.1 for L = 2n (MINOR)

The proof sketch in v5 §4.2 is incomplete. It says "by direct analysis" and "the band safety argument (Lemma T3)" without giving the full argument. Specifically:

- For $L = 2n$: $|B_{\rm div}| = (n-2) \cdot 2 + 1 = 2n - 3$. The runners include one with speed $n$ or $2n$. Need to verify that at least $n-1$ of the $2n-3$ fibres are safe.
- T3 gives 2 safe fibres (first and last). Need $n-3$ more from the interior.

This is likely true but needs explicit verification, especially for small $n$.

**Severity: LOW.** Can be resolved by direct computation for small $n$ and structural argument for large $n$.

---

### Gap C: The Counting Bridge for Small $M$ in Proposition 9.4 (MODERATE)

The v5 counting bridge (§9.5) uses the density argument: safe density $\geq (n-3)/n$ across $B_{\rm div}$. The calculation gives:

$$x_0 \geq \frac{(n-3)(n-2) \cdot 2}{n} - O(n)$$

For $n = 5$: $12/5 = 2.4 > 4$? **NO!** $12/5 = 2.4 < 4 = \varphi(5)$.

**Wait:** For $n = 5$, $\varphi(5) = 4$, and $2(n-3)(n-2)/n = 2 \cdot 2 \cdot 3/5 = 12/5 = 2.4 < 4$. So the density bound does NOT give $x_0 \geq \varphi(n)$ for $n = 5$.

This means the Proposition 9.4 proof is incomplete for $n = 5$ (and potentially $n = 7$).

Actually, re-reading: v5 says "For $n = 5$: $2 \cdot 2 \cdot 3/5 = 12/5 > 4 = \varphi(5)$." This is **FALSE**: $12/5 = 2.4 < 4$.

**Severity: MODERATE.** The density argument for small $n$ (especially $n = 5$) needs a different approach. The v3 proof handled this via the $t_M = 0$ argument (showing that bad$(M, 0, n) = \{0, -M^{-1}\}$ kills at most 1 miss element since 0 is already covered). That argument gives $x_0 \geq 1$ per fibre, which combined with $|B_{\rm div}|$ fibres gives many safe fibres.

For $n = 5$, prime, $|E_{\rm div}| = 1$: $|E_{\rm fix}| = 2$ runners. On I = (L/5, L/4), both runners at floor 0. miss(0) has $5 - (1 + 2) = 2$ elements. At fibres with $t_M = 0$: bad$(M, 0, 5) = \{0, -M^{-1}\}$. Since 0 is already covered, the net kill on miss(0) is at most 1. With $|\text{miss}(0)| = 2 > 1$, the fibre is safe. Number of $t_M = 0$ fibres: $\geq L_0 - L_0M/5 = L_0(1 - M/5)$ for $M < 5$. For $M \geq 5$: use the density of safe $t_M$ classes ($\geq 3/5$ safe) across all of $B_{\rm div}$.

This needs to be formalized more carefully.

---

### Gap D: Composite $n$, $|E_{\rm div}| = 1$ — Case Exhaustiveness (MODERATE)

In v5 §12, the composite $n$ with $|E_{\rm div}| = 1$ case invokes both G4B-COMP-CAP (Theorem 10.1) and G4.OT (Theorem 10.2). But:

- **Theorem 10.1** requires "all $\varphi(n)$ units in $E_{\rm non}$." With $|E_{\rm div}| = 1$, $E_{\rm non}$ has $n-2$ elements from $\{1, \ldots, n-1\}$ (one element dropped to make room for the divisible runner). If the dropped element is a non-unit, all units are in $E_{\rm non}$. If the dropped element IS a unit, then $E_{\rm non}$ has only $\varphi(n) - 1$ units.

- When the dropped runner is a unit, the U-FORCE hypothesis fails. G4.OT (Theorem 10.2) handles this case (Cases i/ii/iiia/iiib). But G4.OT currently only handles $n \geq 10$ in the document title scope. **What about composite $n \in \{4, 6, 8, 9\}$?**

- $n = 4$: 318 tuples verified computationally (from v4's table). Analytic proof?
- $n = 6$: Handled by combination of Cases i/ii/iiia (Sole Cover applies) and Sub-case B (U-FORCE + Z0S). But Z0S has Gap A.
- $n = 8, 9$: Similar.

**Severity: MODERATE.** The G4.OT scope threshold ($n \geq 10$) creates a gap for small composite $n$ with $|E_{\rm div}| = 1$. The arguments should work for all $n \geq 4$ but this needs to be stated explicitly. The Cases i/ii/iiia don't depend on $n \geq 10$; the Sole Cover bijection works for all $n$. Sub-case B (both dropped non-units) needs the Z0S identity which has Gap A.

---

### Gap E: Section 9 Floor Change Handling (MINOR)

v5 §9.2–9.3 define miss(k) using the floor state at the START of period k. But within a period, fixed runners' floor states change (at most 1 change per runner per period). The miss set can shift mid-period. v5 doesn't account for this explicitly.

v4's working paper (§7.4) handles this with a "2(n-3) additional bad fibres" correction, but v5 omits this discussion.

**Severity: MINOR.** The correction factor is absorbed into the density argument for large $M$ and doesn't affect the qualitative result.

---

### Gap F: The Irrational Branch m=1 Sub-case (MINOR)

v5 §2, Step 4 states each class has $|C_\ell| \leq n-2$ because $m \geq 2$. But the case $m = 1$ (all speeds rational multiples of a single irrational) is not handled. v4's Sections 2–3 have a remark about this but omit the proof "for brevity."

**Severity: LOW.** The $m = 1$ case reduces to a one-dimensional Kronecker argument and is standard. It should be included or explicitly cited.

---

## 3. Summary of Gaps by Severity

| Gap | Description | Severity | Status |
|---|---|---|---|
| **A** | Z0S.3 — Unit Residue Isolation at general z=0 events | **HIGH** | Same issue as v3 Lemma 8.3; not resolved |
| **C** | Counting bridge density argument fails for n=5 | **MODERATE** | Arithmetic error in v5 |
| **D** | G4.OT scope doesn't cover small composite n | **MODERATE** | Need explicit extension |
| **B** | L=2n proof incomplete | **LOW** | Direct computation suffices |
| **E** | Floor change corrections omitted | **MINOR** | Absorbed by density argument |
| **F** | Irrational m=1 sub-case | **LOW** | Standard; needs citation |

---

## 4. Recommended Fixes

### For Gap A (CRITICAL):
The Z0S.3 identity needs either:
(a) A proof that each unit z=0 event produces a safe fibre (even at non-zero floors), OR
(b) A weaker but sufficient bound using only floor-0 z=0 events + structural arguments.

Route (a) requires showing that the departing residue $-(m-1)e_u^{-1}$ at floor $m$ is not in any other runner's bad set at the same fibre. This is a local algebraic property that may follow from a "desynchronization" argument: at fibre $b = mL/e_u$, other runner $e'$ has floor $\lfloor me'/e_u \rfloor$, and one needs $-(m-1)e_u^{-1} \notin \text{bad}(e', \lfloor me'/e_u \rfloor, n)$. This is not obviously true for all runners.

Route (b): At floor 0, EACH unit runner $e_u$ has its first z=0 event at $b = L/e_u$. At this event, the departing residue is $0$ (which is covered by every other runner at floor 0), so this doesn't help either.

Actually, the Sole Cover argument works differently: on the interval $(L/n, L/(n-1))$, ALL runners are at floor 0, and the miss set has $\geq 2$ elements. The FIBRE ITSELF is safe (not because a z=0 event exposes something, but because the miss set is non-empty). The safe fibres are the fibres in this interval, not z=0 events.

**The Z0S approach and the Sole Cover approach are DIFFERENT mechanisms.** The Sole Cover approach gives safe fibres in the initial interval without needing z=0 events at all. The Z0S approach counts z=0 events as safe fibres. If the Z0S approach has Gap A, the proof can still work via the Sole Cover/density approach (Sections 6, 9) for prime n, but needs a different argument for composite n.

For composite $n$ with $|E_{\rm div}| \geq 2$ and both dropped non-units: the current proof route is entirely through Z0S.3. If Z0S.3 falls, we need an alternative for this case.

**Alternative for composite n, |E_div| ≥ 2:** At floor 0 (FLOOR-SAFE): $D(0) \geq \varphi(n)$. So fibre $b_0$ (the first fibre of $B_{\rm div}$) is safe. This gives $x_0 \geq 1$, which suffices for LRC. The stronger bound $x_0 \geq \varphi(n)$ requires more, but for the conjecture we only need $x_0 > 0$.

**IMPORTANT REALIZATION: LRC only requires $x_0 > 0$, not $x_0 \geq \varphi(n)$.** If we can show $x_0 \geq 1$ in every branch, the conjecture holds. The $\varphi(n)$ lower bound is a stronger result but not necessary for the conjecture itself.

With this weaker target:
- FLOOR-SAFE gives $B_{\rm safe} \geq 1$ (fibre $b_0$ is safe) for any tuple with all units in $E_{\rm non}$. ✓
- The Sole Cover bijection gives $x_0 \geq 1$ for any tuple with a dropped unit. ✓
- These two together cover all cases (either a unit is dropped, or no unit is dropped — if no unit is dropped, all units are in $E_{\rm non}$).

**So Gap A may not block the conjecture, only the stronger bound $x_0 \geq \varphi(n)$.**

### For Gap C:
Fix the arithmetic: $2(n-3)(n-2)/n$ is NOT $> n-1$ for $n = 5$. Use the $t_M = 0$ argument from v3 (bad$(M, 0, n) = \{0, -M^{-1}\}$; 0 is already covered; net kill on miss(0) is $\leq 1$; with $|\text{miss}(0)| \geq 2$, every $t_M = 0$ fibre is safe).

### For Gap D:
Extend G4.OT scope statement to all composite $n \geq 4$ (the arguments don't depend on $n \geq 10$).

---

## 5. Conclusion

**The proof of LRC ($x_0 > 0$ for all $n$) appears sound** if we target $x_0 \geq 1$ rather than $x_0 \geq \varphi(n)$:
- Irrational branch: proved (Weyl).
- Case 1: proved (arithmetic witnesses).
- Case 2, dropped unit: proved (Sole Cover gives miss interval → $x_0 \geq 1$).
- Case 2, no dropped unit (all units in $E_{\rm non}$): proved (FLOOR-SAFE gives safe fibre at $b_0$).

**The stronger bound $x_0 \geq \varphi(n)$ has Gap A** (Z0S.3 safety at non-zero floors unproven). This affects Sections 8, 10, 11.

**Recommendations:**
1. For the LRC paper: target $x_0 > 0$ (sufficient for the conjecture).
2. State $x_0 \geq \varphi(n)$ as a conjecture/partial result for the stronger bound.
3. Fix Gap C (arithmetic error in density argument for $n = 5$).
4. Resolve or clarify Gap A before claiming $x_0 \geq \varphi(n)$.
