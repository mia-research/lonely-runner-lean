# Slot-Economy Theorem: Dynamic Proof Completion

**Date:** 2026-03-24
**Status:** INVALID AS WRITTEN — not in the canonical proof chain.
**Depends on:** Lemma U, Lemma P0, Lemmas C1–C15 (all in `lrc_n11_dynamic_checkpoint_lemmas_v1.md`), Lemma 0 (`lrc_v15_lemma0_verify.py`).

> **Correction (2026-03-26).** This note is retained as a historical theorem
> attempt, not as a live certifier of the `n = 11` proof. The staircase
> induction does not control productive-step count once extra `11`-multiples
> recycle blocker roles, so the 20-step argument is not universal. Use
> `lrc_n11_canonical_status_ledger_v2.md` and
> `lrc_n11_static_core_theorem_v1.md` for current canonical status.

---

## 1. Setup and Goal

The dynamic proof needs to show: for any configuration S of 10 distinct positive integer speeds containing at least one multiple of 11, there exists a time t such that every runner in S is isolated (‖p·t‖ ≥ 1/11 for all p ∈ S). It does this by bounding the ILE terminal time T_ILE(S) by t*(q), where q is defined below, and then applying Lemma 0 to verify t*(q) precedes every dangerous window.

**Notation (inherited).**

- `τ_p(t)` = next isolation-entry time of runner p after a blocking time t (Lemma U).
- `τ_max(t, S)` = max{τ_p(t) : p ∈ S, p blocks at t}.
- Staircase positions: `s_0 = 0`, `s_1, s_2, ...` = the ILE trajectory for E_ext(q) (defined below).
- `t*(q) = (55q+1)/(121q)` = terminal staircase position.
- Pacemaker checkpoints: `r/11` for r = 1,...,5.

---

## 2. Key Preparatory Fact: τ_p is Non-Decreasing

> **Lemma M (Monotonicity of τ_p).**
> For any runner p and times t₁ ≤ t₂: τ_p(t₁) ≤ τ_p(t₂).

**Proof.**

Fix p. Write f = {p·t} for the fractional part. The function τ_p(t) is the first time t' > t when {p·t'} enters the blocking band [0, 1/11).

**Case (i): t is in the lower bad zone** (f ∈ [0, 1/11)). Then τ_p(t) = t + (1/11 − f)/p. As t increases by dt, f increases by p·dt (to first order), so:

```
τ_p(t + dt) = (t + dt) + (1/11 − (f + p·dt))/p = t + (1/11 − f)/p = τ_p(t).
```

So τ_p is **constant** within each lower blocking interval.

**Case (ii): t is in the upper bad zone** (f ∈ (10/11, 1)). Then τ_p(t) = t + (12/11 − f)/p. Same computation: τ_p constant within each upper blocking interval.

**Case (iii): t is safe** (f ∈ [1/11, 10/11]). Then τ_p(t) = start of the next blocking interval, which is a fixed value T_next ≥ t that stays constant until t reaches T_next.

In all cases, τ_p(t) is a **non-decreasing step function** of t (it stays constant within blocking intervals and safe arcs, and can only jump upward when entering the next blocking interval). □

**Corollary M.1.** If t₁ ≤ t₂ and p blocks at t₁, then τ_p(t₁) ≤ τ_p(t₂) ≤ τ_max(t₂, {all p}).

---

## 3. The Staircase Reference Trajectory

Let 11q be the smallest multiple of 11 in S. The **reference staircase** for E_ext(q) = {1, 3, 4, 5, 6, 7, 8, 9, 10, 11q} has the following certified trajectory (by Lemmas P0 and C1–C15):

```
Pacemaker at 1/11:
  s_1  = 1/11 + 1/(121q)  = (11q+1)/(121q)         [Lemma P0, r=1]
Off-pacemaker:
  s_2  = 6/55             [C1:  runner 10]
  s_3  = 4/33             [C2:  runner 9]
  s_4  = 3/22             [C3:  runner 8]
  s_5  = 12/77            [C4:  runner 7]
  s_6  = 2/11             [C5:  runner 6, pacemaker arrival]
Pacemaker at 2/11:
  s_7  = 2/11 + 1/(121q)  = (22q+1)/(121q)          [Lemma P0, r=2]
Off-pacemaker:
  s_8  = 12/55            [C6:  runner 5]
  s_9  = 23/99            [C7:  runner 9]
  s_10 = 3/11             [C8:  runner 4, pacemaker arrival]
Pacemaker at 3/11:
  s_11 = 3/11 + 1/(121q)  = (33q+1)/(121q)          [Lemma P0, r=3]
Off-pacemaker:
  s_12 = 23/77            [C9:  runner 7]
  s_13 = 17/55            [C10: runner 10]
  s_14 = 4/11             [C11: runner 3, pacemaker arrival]
Pacemaker at 4/11:
  s_15 = 4/11 + 1/(121q)  = (44q+1)/(121q)          [Lemma P0, r=4]
Off-pacemaker:
  s_16 = 17/44            [C12: runner 8]
  s_17 = 23/55            [C13: runner 5]
  s_18 = 34/77            [C14: runner 7]
  s_19 = 5/11             [C15: runner 9, pacemaker arrival]
Pacemaker at 5/11:
  s_20 = 5/11 + 1/(121q)  = (55q+1)/(121q) = t*(q)  [Lemma P0, r=5, TERMINAL]
```

The terminal position `t*(q) = s_20` is a **witness** for E_ext(q): at this time runner 11q has fractional part {11q·t*(q)} = 1/11 (on the left boundary of the safe zone), and the 15 checkpoint lemmas confirm that all other runners in E_ext(q) are simultaneously safe there (each off-pacemaker step terminates when the current blocker exits, leaving a safe window).

---

## 4. The Slot-Economy Theorem

> **Theorem SET (Slot-Economy).**
> Let S be any set of 10 distinct positive integer speeds with smallest multiple of 11 equal to 11q. Then
>
> ```
> T_ILE(S) ≤ t*(q) = (55q+1)/(121q).
> ```

**Proof.**

We show the ILE trajectory of S is dominated step-by-step by the reference staircase {s_k}. Formally, we prove:

> **Inductive claim:** For every ILE step k (k = 0, 1, 2, ..., 20) and every time t at which the ILE of S is positioned after its k-th advance, t ≤ s_k.

**Base case.** Both ILEs start at t = 0 ≤ s_0 = 0. □

**Inductive step.** Suppose the ILE of S is at some t ≤ s_k. We bound its next advance.

---

**Case A: t = r/11 for some r ∈ {1,...,5} (pacemaker checkpoint).**

By Lemma P0, runner p blocks at r/11 iff 11 | p, and the maximum next-entry time over all present multiples of 11 is r/11 + 1/(121·q_min), where q_min is the smallest present multiple. Since 11q is the smallest multiple of 11 in S: q_min = q. Hence:

```
τ_max(r/11, S) = r/11 + 1/(121q) = s_{k+1}   (the corresponding pacemaker step).
```

So the ILE of S advances to exactly s_{k+1}. Equality holds. □

---

**Case B: t is an off-pacemaker position (t ≤ s_k, t ≠ r/11).**

We need to show τ_max(t, S) ≤ s_{k+1}, where s_{k+1} is the next staircase value (determined by the corresponding checkpoint lemma C(j)).

Let p ∈ S be any runner blocking at t. We split into two sub-cases.

**Sub-case B1: p also blocks at s_k.**

By Lemma M (monotonicity), τ_p(t) ≤ τ_p(s_k).

By the checkpoint lemma C(j) at position s_k: among ALL blocking runners at s_k (for any configuration), τ_max(s_k, {all p}) ≤ s_{k+1}. In particular, τ_p(s_k) ≤ s_{k+1}.

Therefore: τ_p(t) ≤ τ_p(s_k) ≤ s_{k+1}. □

**Sub-case B2: p blocks at t but not at s_k.**

Since p exits its blocking interval before reaching s_k, its exit time satisfies T_exit(p) ≤ s_k. But τ_p(t) = T_exit(p) (the time p exits the current blocking interval is exactly when the ILE can advance past p). Hence:

```
τ_p(t) = T_exit(p) ≤ s_k ≤ s_{k+1}.
```

(The last inequality holds because the staircase is non-decreasing: s_k ≤ s_{k+1} at every step.) □

**Combining both sub-cases:**

For every p ∈ S blocking at t (whether t is a pacemaker or off-pacemaker), τ_p(t) ≤ s_{k+1}. Therefore:

```
τ_max(t, S) = max{τ_p(t) : p ∈ S, p blocks at t} ≤ s_{k+1}.
```

This completes the inductive step. □

---

**Conclusion of the induction.**

By induction, the ILE of S satisfies: at every step k, the ILE position ≤ s_k ≤ s_{20} = t*(q).

Since the staircase terminates at s_{20} = t*(q) as a witness for E_ext(q), and every ILE advance of S is bounded by the staircase, the ILE of S terminates at or before t*(q):

```
T_ILE(S) ≤ t*(q) = (55q+1)/(121q).
```

□

---

## 5. Checkpoint Lemmas Are Universal (Not Configuration-Specific)

A key point: each checkpoint lemma C(j) states a bound that holds for **all** runners p ≥ 2, not just for runners in E_ext(q). The proof pattern is:

1. For large p (e.g., p ≥ 21): use Lemma U to give τ_p(s_k) < s_k + 2/(11p) ≤ s_{k+1} − ε.
2. For small p (2 ≤ p ≤ bound): check the finite list of residues modulo the denominator of s_k; identify exactly which p are blocking; compute their τ values; verify all ≤ s_{k+1}.

So the bound τ_max(s_k, S) ≤ s_{k+1} holds for ANY configuration S, not just E_ext(q). This is exactly what Sub-case B1 uses: τ_p(s_k) ≤ s_{k+1} for ALL p, regardless of which S they come from.

---

## 6. Completing the Dynamic Proof

**Theorem (Dynamic Front, closed).**
For any configuration S of 10 distinct positive integer speeds with smallest 11-multiple 11q (q ≥ 1), there exists a time t ≤ t*(q) at which every runner in S is isolated.

**Proof.**

By Theorem SET: T_ILE(S) ≤ t*(q).

By Lemma 0 (verified in `lrc_v15_lemma0_verify.py`): t*(q) < A_(q,1)_left for every q ≥ 1, where A_(q,1) is the leftmost dangerous window for runner 11q. Explicitly:

```
t*(q) < A_(q,1)_left   ⟺   Δ(q) = (6655q² + 4961q − 99)/[121q(121q+99)] > 0.
```

The numerator 6655q² + 4961q − 99 = 11(605q² + 451q − 9) has minimum value 11517 > 0 at q = 1, and is increasing, so Δ(q) > 0 for all q ≥ 1. □

Since the ILE terminates at T_ILE(S) ≤ t*(q) < A_(q,1)_left (the start of the dangerous window), no dangerous advance into D_(11q) = ((110q−1)/(121q), 10/11) ever occurs. The ILE finds its witness before entering the dangerous zone.

**Case: no 11-multiple present.** The standard covering argument from v14 applies (Lemma BST).

**Case: multiple 11-multiples present.** Let 11q₁ < 11q₂ < ··· be all 11-multiples in S. Apply the theorem with q = q₁ (the smallest). The pacemaker steps use q₁; larger 11-multiples are dominated at pacemaker steps (Lemma P0) and irrelevant at off-pacemaker steps.

This completes the dynamic front. □

---

## 7. What This Means for the v15 Proof Program

The slot-economy theorem closes **Lemma D3** (Staircase Envelope Dominance) entirely:
- The "greedy maximizer" claim (that E_ext(q) achieves the maximum T_ILE) is now replaced by the direct sub-case argument: for ANY p in ANY S, τ_p(t) ≤ s_{k+1} at each step.
- There is no need to argue E_ext(q) is the maximizer; we only need each step to be bounded, which the checkpoint lemmas provide universally.

The proof does NOT require E_ext(q) to be the unique maximizer, only that the staircase provides a valid UPPER BOUND on every step of every configuration.

**Status of the complete proof:**

| Component | Status |
|-----------|--------|
| Lemma U (step-size bound) | **PROVED** (in checkpoint doc) |
| Lemma P0 (pacemaker rigidity) | **PROVED** (in checkpoint doc) |
| Lemmas C1–C15 (off-pacemaker) | **PROVED** (in checkpoint doc) |
| Lemma M (monotonicity of τ_p) | **PROVED** (this document, §2) |
| Lemma 0 (gap formula Δ(q) > 0) | **PROVED** (lrc_v15_lemma0_verify.py) |
| Theorem SET (slot-economy) | **PROVED** (this document, §4) |
| **Dynamic front (Theorem D)** | **PROVED** (this document, §6) |
| Lemma S1 (runner-2 elimination) | **PROVED** (lrc_n11_boundary_defect_reduction_v1.md) |
| Theorem 4.1 (σ₂=+1 incompatibility) | **PROVED** (lrc_n11_incompatibility_v1.md) |
| Lemma S2 (σ₂=−1 runner-9 cascade) | **PROVED** (analytic, `lrc_n11_lemma_s2_proof_v2.md`) |

**The proof is complete.** All components are analytically proved with no computational dependencies. The full LRC n=11 proof is now closed.

---

## 8. Verification

The proof of the slot-economy theorem is analytic and requires no additional computation beyond the checkpoint lemmas and Lemma 0 (both already verified). To audit:

1. **Lemma M:** Check the three cases (lower bad zone, upper bad zone, safe zone) by direct computation of τ_p(t + dt) − τ_p(t).

2. **Case A (pacemaker):** Verify Lemma P0's formula: {11q · r/11} = {qr} = 0 for any integer q; τ_{11q}(r/11) = r/11 + 1/(121q).

3. **Case B1 (off-pacemaker, p also blocks at s_k):** Verify each checkpoint lemma C1–C15 covers ALL p ≥ 2, not just E_ext runners. Each proof in the document bounds "for p ≥ N: τ_p < s_{k+1}" and checks all 2 ≤ p < N by exhaustive residue computation.

4. **Case B2 (p exits before s_k):** Verify T_exit(p) ≤ s_k using: p is in blocking interval at t ≤ s_k but exits before s_k, so T_exit ≤ s_k < s_{k+1}.

5. **Lemma 0:** Run `lrc_v15_lemma0_verify.py` to confirm Δ(q) > 0 for q = 1,...,20.
