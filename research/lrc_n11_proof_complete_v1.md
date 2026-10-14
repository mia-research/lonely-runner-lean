# LRC n=11: Historical Complete-Proof Summary

**Date closed:** 2026-03-24
**Status:** SUPERSEDED — not a canonical status source.

> **Correction (2026-03-26).** This summary is kept for history only. Its
> complete-proof claim relied on the Slot-Economy route, which is now marked
> invalid as written, and it also treated the broken WIT line as theorem-grade.
> Use `lrc_n11_canonical_status_ledger_v2.md` for current proof state and
> `lrc_n11_static_core_theorem_v1.md` for the canonical static front.
> The remaining sections below are preserved historical text, not current
> certification.

---

## Main Theorem

> **Theorem (LRC n=11).** For any 10 distinct positive integer speeds v₁ < v₂ < ··· < v₁₀, there exists a time t ∈ ℝ such that every runner satisfies ‖vᵢ·t‖ ≥ 1/11 simultaneously.

Here ‖x‖ = dist(x, ℤ) is the distance to the nearest integer.

---

## Proof Architecture

The proof splits into a **dynamic front** and a **static front**, closing both via two independent arguments.

### Dynamic Front — No dangerous ILE advance

**Goal:** Show the Isolation Length Exploration (ILE) terminates at or before t*(q) = (55q+1)/(121q) for any configuration with smallest 11-multiple 11q, and that t*(q) precedes the dangerous window for runner 11q.

| Lemma | Statement | Source |
|-------|-----------|--------|
| **Lemma U** | τ_p(t) ≤ t + 2/(11p) for all p, t | `lrc_n11_dynamic_checkpoint_lemmas_v1.md` |
| **Lemma P0** | At pacemaker checkpoints r/11: τ_max = r/11 + 1/(121q) | `lrc_n11_dynamic_checkpoint_lemmas_v1.md` |
| **Lemmas C1–C15** | Off-pacemaker bounds: τ_max(sₖ, S) ≤ sₖ₊₁ for all S | `lrc_n11_dynamic_checkpoint_lemmas_v1.md` |
| **Lemma M** | τ_p is non-decreasing in t (monotonicity) | `lrc_n11_slot_economy_theorem_v1.md` §2 |
| **Theorem SET** | T_ILE(S) ≤ t*(q) for all S with smallest 11-multiple 11q | `lrc_n11_slot_economy_theorem_v1.md` §4 |
| **Lemma 0** | Δ(q) = t*(q) − A_{q,1,left} = (6655q²+4961q−99)/[121q(121q+99)] > 0 for all q ≥ 1 | `lrc_n11_slot_economy_theorem_v1.md` §6 |

**Conclusion:** For any configuration with an 11-multiple, the ILE terminates before entering the dangerous window. No dangerous ILE advance can occur. When no 11-multiple is present, the standard covering argument (Lemma BST) applies. □

---

### Static Front — I₉ is never fully blocked

**Goal:** Show the witness slot I₉ = [10/11, 109/110] always has a positive uncovered measure W(I₉) > 0.

The slot system has complementary pairs: (5,6)→{I₁,I₈}, (4,7)→{I₂,I₇}, (3,8)→{I₃,I₆}, (2,9)→{I₄,I₅}. Slot I₉ is unclaimed by any complementary pair.

**Case σ₂=+1:**

| Lemma | Statement | Source |
|-------|-----------|--------|
| **Theorem 4.1** | In σ₂=+1 regime: closing I₄ requires a₂ ≥ 20/9; covering I₉ requires a₂ ≤ 575/261. Gap = 5/261 > 0. Incompatible. | `lrc_n11_incompatibility_v1.md` |

**Case σ₂=−1:**

| Lemma | Statement | Source |
|-------|-----------|--------|
| **Lemma S1** | Runner 2 (a₂ ∈ [25/14, 24/13]) cannot overlap I₉. Gap = 114/1417 > 0. | `lrc_n11_boundary_defect_reduction_v1.md` |
| **Lemma S2** | In all σ₂=−1 sign classes: W(I₉) ≥ 538/54395 > 0. | `lrc_n11_lemma_s2_proof_v2.md` |

**Lemma S2 proof sketch:**

1. **Unique cascade speed:** a₉ = 86/9 is the only value in (9,10) solving the I₄-closing boundary equation. All other a₉ fail to close I₄ or I₅, making the sign class infeasible.

2. **Runner 9's coverage:** B_{9,8}(86/9) = [441/473, 450/473] ⊂ I₉. The left portion [10/11, 441/473) is uncovered by runner 9.

3. **Outer runner table:** Each of runners 3–8, 10 is cascade-forced to a unique speed when their sign is +1, absent (out of range) when −1. No cascade-forced runner has a bad interval reaching [10/11, 441/473).

4. **Four sub-cases (σ₃, σ₄) ∈ {±1}²:**

| σ₃ | σ₄ | W(I₉) lower bound | Surviving gap |
|----|----|--------------------|--------------|
| +1 | +1 | 103/3850 | G₁ = (741/770, 272/275) |
| +1 | −1 | 121/5203 | left gap [10/11, 441/473) |
| −1 | +1 | 538/54395 | G₂ = (450/473, 1216/1265) |
| −1 | −1 | 121/5203 | left gap [10/11, 441/473) |

**Min W(I₉) = 538/54395 > 0.** □

---

## Complete Status Table

| Component | Status | Document |
|-----------|--------|----------|
| Lemma U (step-size bound) | **PROVED** | `lrc_n11_dynamic_checkpoint_lemmas_v1.md` |
| Lemma P0 (pacemaker rigidity) | **PROVED** | `lrc_n11_dynamic_checkpoint_lemmas_v1.md` |
| Lemmas C1–C15 (off-pacemaker checkpoints) | **PROVED** | `lrc_n11_dynamic_checkpoint_lemmas_v1.md` |
| Lemma M (monotonicity of τ_p) | **PROVED** | `lrc_n11_slot_economy_theorem_v1.md` §2 |
| Lemma 0 (gap formula Δ(q) > 0) | **PROVED** | `lrc_n11_slot_economy_theorem_v1.md` §6 |
| Theorem SET (Slot-Economy) | **INVALID AS WRITTEN** | `lrc_n11_slot_economy_theorem_v1.md` §4 |
| **Dynamic front (Theorem D)** | **NON-CANONICAL / OPEN** | see `lrc_n11_canonical_status_ledger_v2.md` |
| Lemma S1 (runner-2 elimination) | **PROVED** | `lrc_n11_lemma_s1_runner2_elimination_v1.md` |
| Theorem 4.1 (σ₂=+1 incompatibility) | **PROVED** | `lrc_n11_incompatibility_v1.md` |
| Lemma S2 (σ₂=−1 cascade) | **PROVED** | `lrc_n11_lemma_s2_proof_v2.md` |
| **Static front (all sign classes)** | **PROVED** | `lrc_n11_static_core_theorem_v1.md` |

**Canonical status:** the static front is closed; the dynamic and WIT routes are
not canonical as written.

---

## Key Constants

| Quantity | Value | Meaning |
|----------|-------|---------|
| t*(q) | (55q+1)/(121q) | ILE terminal bound for smallest 11-multiple 11q |
| Δ(q) | (6655q²+4961q−99)/[121q(121q+99)] | Gap between t*(q) and dangerous window; positive for all q≥1 |
| min gap σ₂=+1 | 5/261 | Incompatibility gap for Theorem 4.1 |
| Lemma S1 gap | 114/1417 | Runner-2 I₉-avoidance gap |
| min W(I₉) | 538/54395 | Minimum witness window width in σ₂=−1 |

---

## Logical Independence

The dynamic and static proofs are independent:
- **Dynamic:** Shows no dangerous ILE advance occurs (time-domain argument).
- **Static:** Shows I₉ always has a positive witness measure (frequency-domain argument).

Either front alone suffices to conclude the LRC for n=11 by different mechanisms. The two-front structure provides redundancy and cross-checks the proof.

---

## Proof Files

| File | Content |
|------|---------|
| `lrc_n11_dynamic_checkpoint_lemmas_v1.md` | Lemmas U, P0, C1–C15 (dynamic checkpoints) |
| `lrc_n11_slot_economy_theorem_v1.md` | Lemma M, Theorem SET, Dynamic front |
| `lrc_n11_boundary_defect_reduction_v1.md` | Lemma D1, D2, Lemma S1 |
| `lrc_n11_incompatibility_v1.md` | Theorem 4.1 (σ₂=+1) |
| `lrc_n11_lemma_s2_proof_v2.md` | Lemma S2 (σ₂=−1, complete analytic proof) |
| `lrc_n11_v15_theorem_program.md` | Master program with all lemma statements |
| `lrc_v15_lemma0_verify.py` | Computational verification of Lemma 0 |
| `lrc_v15_lemma_s2_cascade_full.py` | Empirical support for Lemma S2 (32 classes) |
