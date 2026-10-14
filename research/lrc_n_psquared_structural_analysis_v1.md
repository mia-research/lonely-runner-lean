# Structural Analysis: n = p² Open Case

**File:** `lrc_n_psquared_structural_analysis_v1.md`
**Date:** 2026-05-01
**Status:** Phase A deliverable. Computational findings verified; algebraic verification of Theorem BS-PSQ pending DeepSeek round.
**Companion:** `/Users/trentpalelei/Desktop/Math Ex/lrc_proof.py` (canonical proof code)

---

## 0. The case

> n = p² (p ≥ 5), Unit-Complete, both dropped residues d₁,d₂ ∈ H\{0}, |E_div| ≥ 1.

H = pℤ/p²ℤ = {0, p, 2p, …, (p-1)p} is the unique non-trivial subgroup of ℤ/p²ℤ. It is the maximal ideal of the local ring ℤ/p²ℤ. **There is no second subgroup** (compare n = pq with H_p ∩ H_q = {0}).

---

## 1. The named obstruction (one sentence)

> **The "translate-by-one" obstruction.** For n = p² and representative speeds, the miss-set at the canonical fibre b\* = (n-1)L/n is exactly **(H \ {0}) − 1**, which has size p−1, equal to |H\{0}|, but is **disjoint** from H\{0}. So the dropped residues d₁,d₂ ∈ H\{0} are *never* in the miss-set: every unit runner has coverage that hits both d₁ and d₂ at b\*.

This is what kills B2b-SAFE for n=p². For n=pq the miss-set has *two* contributions: (H_p − 1) and (H_q − 1). Dropped residues in H_q find their witnesses in (H_p − 1). For n=p² there is only one subgroup; its translate is itself, shifted by 1, and the shift moves it precisely off the dropped set.

---

## 2. Computational findings (all from `lrc_proof.py` primitives)

### Theorem BS-PSQ (verified n ∈ {25, 49, 121, …, 529})

For every prime p ≥ 5, every ρ ∈ U(p²), and every T ∈ {0, …, p²-1}:

> **bad(ρ, T, p²) ∩ (H\{0}) ≠ ∅** iff **T ∈ {p, 2p, …, (p-1)p} ∪ {p-1, 2p-1, …, (p-1)p−1}**.

That is: T ≡ 0 (mod p) and T ≠ 0, OR T ≡ −1 (mod p) and T ≠ p²-1. Total 2(p-1) values of T per ρ.

Furthermore, for each such T, **exactly one** element of H\{0} is in bad(ρ, T) (namely jp with j = −(⌊T/p⌋+1)·ρ⁻¹ mod p when T ≡ −1 (mod p), or with j ≡ −(T/p)·ρ⁻¹ mod p when T ≡ 0 mod p).

**Consequence (verified):** As ρ ranges over U(p²), every element of H\{0} is hit at every T in the above set. The orbit structure means H\{0} can never be partially covered — it's all-or-nothing per fibre.

### Theorem MISS-PSQ (verified n ∈ {25, 49, 121})

For n = p², representative speeds (q_ρ = 0), at fibre b\* = (n-1)L/n:

> **miss-set M\* = (H \ {0}) − 1**

Sizes: |M\*| = p−1 = |H\{0}|. M\* ∩ H\{0} = ∅. Therefore H\{0} ⊆ covered, including any choice of d₁, d₂.

### Theorem DICHOTOMY-PSQ (verified n ∈ {25, 49, 121})

For n = p², representative speeds, at integer fibre k ∈ {0, 1, …, n-1}:

> |H\{0} ∩ miss-set(k)| = |H\{0}| (= p−1) if k ∈ {0, 1, …, p−1};
> |H\{0} ∩ miss-set(k)| = 0 if k ∈ {p, p+1, …, n−1}.

Sharp cutoff at k = p. Below: every H element missed. At and above: every H element covered.

### Theorem ACTUAL-PSQ (verified n=25, n=49)

For n = p², adversarial choice of q_ρ over each unit runner (actual speeds), at integer fibre k:

> For k = 0: |H\{0} ∩ miss-set| = p−1 (no q_ρ choice covers any H element — but k=0 means b=0, all runners at 0, trivially unsafe).
> For k ∈ {1, …, n−1}: |H\{0} ∩ miss-set| = 0 (adversary CAN cover all H\{0} with appropriate q_ρ).

Therefore at every non-trivial integer fibre, the adversary can fully cover H\{0}, making d₁,d₂ blocked.

### Position lemma (algebraic, verified for p ∈ {5,7})

At integer fibre k ∈ {1, …, p−1} (the "Phase A miss zone"):

| Runner type | Position at b = kL/n | Distance from 0 |
|---|---|---|
| Unit ρ (gcd(ρ,n)=1) | (ρk mod n)/n | ≥ 1/n (boundary at ρk ≡ ±1) |
| Non-unit non-div (e=jp, p∤j) | (jk mod p)/p | ≥ 1/p ≫ 1/n |
| Divisible (e = q₀·n) | 0 | 0 (BLOCKS) |

The divisible runner at position 0 is **the** structural blocker at integer fibres k ∈ {1,…,p-1}.

---

## 3. Four-quadrant lemma table

Cross-reference into `lrc_proof.py`. Quadrants: **(I)** Survives verbatim, **(II)** Survives with H_q→H, H_p→∅, **(III)** Breaks for n=p², **(IV)** No analogue.

### Quadrant I — Survives verbatim (n-agnostic)

| Object | Lines | Status |
|---|---|---|
| `lcm`, `units`, `totient`, `mod_inv` | 46–62 | Pure number theory — works for any n. |
| `runner_position`, `circle_distance` | 88–104 | n-agnostic LRC primitives. |
| `is_lonely_at_b`, `find_lonely_fibre` | 106–137 | Direct LRC; n-agnostic. |
| `bad_set_unit(ρ, T, n)` | 141–157 | Generic; works wherever ρ is a unit mod n. |
| `floor_at_int_fibre` | 159–165 | Generic. |
| `verify_lrc_directly` | 183–194 | Generic ground-truth check. |
| `sep` | 167–173 | Generic mod-n arithmetic. |

### Quadrant II — Survives with H_q → H, H_p → ∅

| Object | Lines | Status / Adaptation |
|---|---|---|
| `subgroup_Hq` | 64–76 | For n=p², replace with `subgroup_H_psquared(p)` returning `{0,p,…,(p-1)p}`. |
| `subgroup_Hp` | 78–84 | **No analogue** for n=p²; H_p collapses (no second subgroup). |
| `PROOF_PS3` (disjoint D1/D2 bands) | 447–462 | **Survives.** d₁−d₂ ∈ H\{0} is non-unit (mult of p); ρ⁻¹ is unit; non-unit ≠ ±unit, so no ρ covers both. Verified by `verify_ps3` with H substituted. |
| `PROOF_PS5` (sum-sep ≡ 0) | 268–283 | **Survives.** Pairing argument ρ ↔ n−ρ holds in any U(n). For n = p² with p ≥ 3, φ(n) = p(p-1) is even. |
| `PROOF_PS4_DENSITY` | 481–502 | **Survives** (statement). 2φ(p²) = 2p(p-1) > p² iff p > 2 — true for p ≥ 3. The density bound holds. |

### Quadrant III — Breaks for n=p²

| Object | Lines | Why it breaks |
|---|---|---|
| `PROOF_B2B_SAFE` | 381–398 | At b\*=(n-1)L/n the miss-set is (H\{0}) − 1; H\{0} fully covered. d₁,d₂ ∈ H\{0} cannot be the witness. **Verified on n ∈ {25,49,121}.** |
| `verify_b2b_safe(p,q)` | 400–438 | Function signature requires (p,q) distinct primes; also asserts miss = (Hp ∪ Hq − 1)\\{n-1}, false for p=q. |
| `PROOF_NONUNIT_AT_LP` (Lemma NUL/p) | 653–681 | At b = L/p: position formula {e/p} = (e mod p)/p still valid. But for n=p², (e mod p)·q is replaced by (e mod p)·p, which is back inside H. So unit runners cover H itself at b=L/p — **the opposite of helpful**. The lemma's conclusion ("never covers any element of H_q\{0}") becomes ("**always** covers some element of H\{0}"). |
| `PROOF_PERM_GAP` & `verify_permanent_gap_n15` | 542–649 | Already retracted for general n=pq. n=p² inherits the failure: integer fibre k=q has no analogue (q does not exist). |

### Quadrant IV — No analogue

| Concept | Why no analogue |
|---|---|
| Two-subgroup decoupling H_p ∩ H_q = {0} | Single subgroup. The entire silence-fibre construction (§12 of `lrc_proof_v10_16.md`) is built on this and has no port. |
| (H_p − 1) ∪ (H_q − 1) miss-set witnesses | Reduces to (H − 1) which is *disjoint* from H, not complementary to it. The witness mechanism inverts. |
| Late Bottleneck α* = (p^{k-1} − 1)/(n−1) for k ≥ 3 | For k=2, α* = 1/(p+1). The interval (1/e_min, α*) used in Theorem 11.5 collapses; quantitative argument fails. |

---

## 4. The candidate path

The dichotomy + position lemma above suggest the safe fibre is **off-integer** in the regime k ∈ {1, …, p−1}:

> **Candidate.** For n = p², the safe fibre is b\* = k·L/n + δ for some k ∈ {1, …, p−1} and δ ∈ (0, L/n) chosen so that:
>   (A) the divisible runner e₀ = q₀·n satisfies {q₀·n·δ/L} ∈ [1/n, (n−1)/n], and
>   (B) the integer-fibre coverage analysis (Theorem DICHOTOMY-PSQ) extends — i.e., no unit runner's floor T_ρ has incremented past the boundary into the "covers H" set {p, 2p, …, (p-1)p, p-1, 2p-1, …}.

Condition (A) is straightforward: the divisible runner sweeps through [0,1) at rate q₀·n/L; for any q₀ ≥ 1 the safe regime within the interval has measure ≥ (n-2)/(q₀·n) per revolution.

Condition (B) requires showing that for δ ∈ (0, δ*) where δ* = L · (next floor transition)/(max unit speed), the unit-runner floor map is locally constant. With max actual unit speed e_max ≤ ρ_max + n·q_max, the safe sub-interval has size L/e_max.

The intersection (A) ∩ (B) is non-empty iff (n-2)/(q₀·n) > 1/e_max, equivalently e_max > q₀·n²/(n-2). For small q₀ and bounded q_ρ this is the regime to test in Phase B.

**This is precisely the gap analysis Phase B is designed to probe.**

---

## 5. Why this gives empirical-then-analytical traction

The structural picture above tells us **where to look**:
- Phase B should sample fibres b = kL/n + δ for k ∈ {1,…,p-1} and a fine grid of δ ∈ (0, L/n).
- Pattern miner (Phase C) should test whether the safe δ depends on q₀ and the unit-runner q_ρ choices.
- Candidate lemma (Phase D) will likely take the form *"there exists δ in [δ_min, δ_max] depending on (e₀, e_max) such that conditions (A)+(B) hold"*.

The translate-by-one obstruction explains why every previous approach (silence fibre, late bottleneck, period-staircase) failed: they all relied on a SECOND structural object (a second subgroup, a wide bottleneck interval, a near-tiling) that exists for n=pq but collapses for n=p². The off-integer fibre approach uses only ONE-subgroup structure, exploiting that H is a *coset* of size p in ℤ/p².

---

## 6. Verification checklist (Phase A gate)

- [x] Every Quadrant I lemma confirmed n-agnostic (read in `lrc_proof.py`).
- [x] Quadrant II lemmas verified for n=25, 49, 121: PS-3 hold, PS-5 holds, PS-4 density holds.
- [x] Quadrant III breakages confirmed by computation: B2b-SAFE miss-set = (H\{0})-1 disjoint from H\{0}.
- [x] Theorem BS-PSQ characterization verified for n ∈ {25, 49}, all ρ ∈ U.
- [x] Theorem MISS-PSQ verified for n ∈ {25, 49, 121}.
- [x] Theorem DICHOTOMY-PSQ verified for n ∈ {25, 49, 121}; sharp cutoff at k=p.
- [x] Theorem ACTUAL-PSQ verified for n ∈ {25, 49}; only k=0 has H\{0} missing under adversary.
- [x] Position lemma verified algebraically and computationally.
- [x] Theorem BS-PSQ algebraic proof (inline, no external tool needed — see §2 addendum below).
- [x] Named obstruction recorded ("translate-by-one").
- [x] Candidate next-step path specified for Phase B.

---

## 2a. Algebraic proof of Theorem BS-PSQ

**Claim:** bad(ρ, T, p²) ∩ (H\{0}) ≠ ∅  iff  T ∈ {p,2p,…,(p-1)p} ∪ {p-1,2p-1,…,(p-1)p−1}.

**Proof.**  
H\{0} = {jp : j ∈ {1,…,p-1}}.  
bad(ρ, T, n) = {−T·ρ⁻¹ mod n,  −(T+1)·ρ⁻¹ mod n}.

*Case 1:* −T·ρ⁻¹ ≡ jp (mod p²) for some j ∈ {1,…,p-1}.  
⟺  T ≡ −jpρ (mod p²).  
Since ρ ∈ U(p²), p ∤ ρ, so jpρ ≡ 0 (mod p) but jpρ ≢ 0 (mod p²) (as j < p).  
Hence T ≡ 0 (mod p), T ≠ 0.  
As j runs over {1,…,p-1}, −jpρ mod p² gives p-1 distinct elements of {p,2p,…,(p-1)p}.  
**Contribution:** T ∈ {p, 2p, …, (p-1)p}.

*Case 2:* −(T+1)·ρ⁻¹ ≡ jp (mod p²) for some j ∈ {1,…,p-1}.  
⟺  T ≡ −jpρ − 1 (mod p²).  
Since −jpρ ≡ 0 (mod p): T ≡ −1 ≡ p−1 (mod p), T ≠ p²−1.  
As j runs over {1,…,p-1}, these give p-1 distinct elements of {p−1, 2p−1, …, (p-1)p−1}.  
**Contribution:** T ∈ {p−1, 2p−1, …, (p-1)p−1}.

The two sets are disjoint (one has T ≡ 0 mod p, other T ≡ p-1 mod p) and together give exactly 2(p-1) values.  
No T outside these sets satisfies either case.  □

**Corollary (confirmed computationally for p ∈ {5,7,11,13,17,19,23}):** For each such T, exactly one j ∈ {1,…,p-1} witnesses the intersection — the formula in §2 (main) gives the explicit j.

---

## 7. Phase B handoff

For the empirical harness:
1. **Reuse:** all Quadrant I primitives directly. Add `subgroup_H_psquared(p)` helper (see plan).
2. **Critical fibre regime:** sample b = kL/n + δ for k ∈ {1, …, p−1}, δ ∈ {jL/(n·M) : j=1,…,M-1} for grid resolution M ≥ e_max.
3. **Worst-case test:** include adversarial q_ρ values that make integer-fibre coverage maximal, then check whether off-integer δ exists where conditions (A) and (B) hold.
4. **Counterexample candidates:** if no safe δ exists for some configuration, that's a hard counterexample. Record fully.
