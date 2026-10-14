# Theorem B2b-UNIT-SAFE — Actual Speeds, Safe q_ρ Range

**Status:** PROVED 2026-05-18  
**Scope:** n=pq (distinct odd primes p < q), q_ρ ∈ [0, ⌊(q-3)/2⌋] for ALL unit runners  
**Closes:** B2b sub-case for "safe" actual speeds (extending B2b-SAFE from representative speeds)

---

## Statement

For n = pq (p < q distinct odd primes), let (q_ρ)_{ρ∈U(n)} be ANY assignment
with all q_ρ ∈ [1, ⌊(q-3)/2⌋].  Let d₁, d₂ ∈ H_q\{0} = {q, 2q, ..., (p-1)q}
with d₁ ≠ d₂.  Then **every** j ∈ J₁ = {j ∈ [1,n-1] : gcd(j,n)=1} is safe:
no unit runner blocks d₁ or d₂ at any k=1 band fibre r = n+j.

Together with B2b-SAFE (q_ρ = 0 for all runners), this closes the sub-case
**q_ρ ∈ [0, ⌊(q-3)/2⌋]** for all unit runners.

---

## Proof

Immediate corollary of Lemma PS-BLOCK-THRESH (§1.4c, proved 2026-05-07):

For any unit runner ρ with q_ρ ≤ ⌊(q-3)/2⌋ and any j ∈ J₁:
- T_ρ(n+j) ∈ [q_ρ, 2q_ρ+1].
- Since q_ρ ≥ 1: T ∈ [1, 2⌊(q-3)/2⌋+1] ⊆ [1, q-2].
- Blocking any d = i·q ∈ H_q requires T ≡ 0 (mod q) or T ≡ q-1 (mod q).
- Both congruences are impossible for T ∈ [1, q-2]. □

---

## Computational Verification

Verified exhaustively by `verify_b2b_unit_safe(p,q)` for n ∈ {21,33,35,55,77}:

| n  | p | q  | safe range q_ρ | J₁ size | pairs | result       |
|----|---|----|-----------------|---------|-------|--------------|
| 21 | 3 | 7  | [1, 2]          | 12      | 1     | ALL safe ✅   |
| 33 | 3 | 11 | [1, 4]          | 20      | 1     | ALL safe ✅   |
| 35 | 5 | 7  | [1, 2]          | 24      | 6     | ALL safe ✅   |
| 55 | 5 | 11 | [1, 4]          | 40      | 6     | ALL safe ✅   |
| 77 | 7 | 11 | [1, 4]          | 60      | 15    | ALL safe ✅   |

---

## Limitation: Dangerous q_ρ Sub-case OPEN

The theorem does NOT extend to runners with q_ρ ≥ ⌈(q-1)/2⌉ ("dangerous" range).

**Counterexample** (n=21, d₁=7, d₂=14):
```
q_map = {1:14, 2:8, 4:15, 5:19, 8:9, 10:1, 11:6, 13:14,
         16:11, 17:9, 19:5, 20:7}
```
Result: ALL 12 j ∈ J₁ blocked. All q_ρ ≥ 1; most in dangerous range (q_ρ > 2 = (q-3)/2).

**Key insight**: Dangerous runners (large e_ρ) have small _continuous_ bad-measure
(≤ 4L/e_ρ per runner, total ≈ 0.34L for this q_map). They concentrate bad-sets
precisely on the J₁ integer fibres while leaving most of [0,L) safe. The k=1
integer fibres can all be blocked even though safe continuous time ≥ 0.66L exists.

This rules out a discrete-fibre proof for the dangerous sub-case; a
different argument is needed.

---

## Dependency Graph

```
PS-BLOCK-THRESH (§1.4c)
    ↓
B2b-UNIT-SAFE (this theorem)  ← closes q_ρ ∈ [1,(q-3)/2] sub-case
    +
B2b-SAFE (§1.5, q_ρ=0)       ← closes representative speeds
    =
Sub-case closed: q_ρ ∈ [0,(q-3)/2] for all unit runners in n=pq B2b

Remaining open: dangerous q_ρ ≥ (q-1)/2
```
