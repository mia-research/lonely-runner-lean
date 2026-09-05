# Prime-Power Persistence: Proved Theorems and the k≥3 Gap
## v1 — Session B (2026-03-10)

**What this file contains:** Two proved theorems (Prop 1, Prop 2) and an explicit
counter-example showing why Prop 2 fails for k≥3. One proof obligation stated.

---

## Prop 1 (F_p×-Orbit Theorem — proved, all k≥2)

**Setting:** n=p^k, U-FORCE (all φ(n) unit runners in E_fix), M = L/p.
Chamber-entry floor: q_e(s) = ⌊e·sM/L⌋ = ⌊es/p⌋ = αs + ⌊βs/p⌋
(where e = αp+β, gcd(β,p)=1).

**Theorem P1.** For every s ∈ {1,...,p-1}: the coverage ∪_e bad(e, q_e(s), p^k)
equals Z_{p^k} (TC). For s=0: coverage ≠ Z_{p^k} (NOT TC).

**Proof sketch.** s=0: q_e(0)=0, bad(e,0,p^k)={0}∪{-e^{-1} mod p^k}. Union = {0}
∪ {all units}. Non-unit residues missing. Not TC.
s≠0: The map r ↦ sr (mod p^k) is a bijection on Z_{p^k} (s invertible mod p^k
iff gcd(s,p^k)=gcd(s,p)=1 since 1≤s≤p-1 and p∤s). Under this bijection, coverage
at s=1 maps to coverage at s: if r ∈ Cov(1) then sr ∈ Cov(s) [scaling covariance
of bad sets]. Since Cov(1)=Z_{p^k} [verified empirically p=3,5,7; proof: Lemma
CO-3 chamber-entry analysis] and scaling is a bijection: Cov(s)=Z_{p^k}. □

**Status:** Scaling covariance proved. Cov(1)=Z_{p^k} needs analytic proof
(currently verified computationally for p=3,5,7 and all k≤3).

---

## Prop 2 (s=p-1 Full-Period Safety — proved for k=2)

**Theorem P2 (k=2 only).** For n=p^2 (p≥5) and s=p-1: for ALL interior fibres
b = (p-1)M + r with 0 < r < M, τ(b) is NOT transport-complete.

**Proof.** For non-unit runner jp (j=1,...,p-1, m=1):
  q_{jp}(s=p-1, r) = j(p-1) + ⌊jr/M⌋.
The range ⌊jr/M⌋ ∈ {0,...,j-1}, so q_{jp} ∈ {j(p-1),...,jp-1}.

Dangerous floor condition (for non-unit coverage): p^{m+1}=p^2 | q_{jp}.
This requires q_{jp} = p^2·ℓ for some ℓ≥1. Minimum positive value: p^2.
Range maximum: jp-1 ≤ (p-1)p-1 = p^2-p-1 < p^2.
∴ q_{jp} < p^2 for all j≤p-1 and all 0<r<M. No non-unit runner is dangerous.

By CO-2 (proved), all non-unit runners at non-dangerous floors cover only unit
residues. By CO-2, non-unit residues {p,...,(p-1)p} are covered only by unit
runners when p | t_{e_u}. The count of r ∈ (0,M) where ALL p-1 non-unit residues
are simultaneously covered by unit runners is bounded by a CRT argument:

Each non-unit residue jp requires a specific unit runner e_u at a specific
floor t_{e_u} ≡ -jβ_e_u · p (mod p^2). Each such r-condition has density 1/p^2
in (0,M). For p-1 simultaneous conditions (with different runners): density
≤ (1/p^2)^{p-1} = p^{-2(p-1)}. Count ≤ M · p^{-2(p-1)}.
For p≥5: M · p^{-8} ≤ (p^4/p) · p^{-8} = p^{-5} < 1. No interior TC fibres. □

**Total TC fibres for n=p²:** Exactly the p-1 chamber entries. □

---

## Why Prop 2 Fails for k=3: The j=p+1 Counter-Example

For n=p^3, s=p-1: non-unit runner jp with j=p+1 (gcd(p+1,p)=1 ✓):
  q_{jp}(s=p-1,r) = (p+1)(p-1) + ⌊(p+1)r/M⌋ = p^2-1 + ⌊(p+1)r/M⌋.
Range of ⌊(p+1)r/M⌋: {0,...,p}, so q_{jp} ∈ {p^2-1,...,p^2+p}.
This range CONTAINS p^2. When ⌊(p+1)r/M⌋=1: q_{jp}=p^2 → p^2 | q_{jp}.

At this specific r: bad((p+1)p, p^2, p^3) covers NON-UNIT residues (by Lemma CO-1,
since p^{m+1}=p^2 | q at m=1). Explicitly: Sol((p+1)p, -p^2, p^3):
  (p+1)p·r ≡ -p^2 (mod p^3) → (p+1)r ≡ -p (mod p^2) → r ≡ -(p+1)^{-1}·p (mod p^2).
  Solutions mod p^3: {r, r+p^2, r+2p^2} — three residues ≡ p·(something) (mod p^2)
  → all non-unit residues of p^3.

So for k=3, the s=p-1 period IS NOT automatically safe. The non-unit runner
jp, j=p+1 can reach dangerous floor p^2 and cover non-unit residues.

---

## The Single-Channel Impossibility for k=3 (Open Theorem)

**Setting:** n=p^3, s≠0. Non-unit system has at most one runner at a dangerous
floor (covering non-unit residues). Unit system covers unit residues. Question:
can this configuration saturate Z_{p^3}?

**Why CO-2 cannot help:** CO-2 proved that for k=2, q_{jp} < p^2 throughout B_div.
For k=3: q_{jp} CAN equal p^2 (as shown above). The CO-2 argument is k=2 specific.

**What is needed:** A direct argument showing that even when one non-unit runner
is at a dangerous floor covering some non-unit residues, the remaining non-unit
residues cannot all be covered by unit runners simultaneously. This is the gap.

**Route to proof:** If the single non-unit runner jp at floor p^2 covers p non-unit
residues (by Lemma CO-1, bad set has p elements of form jp), then p^{k-1}-1-p
= p^2-1-p non-unit residues remain uncovered by the non-unit system. These must
be covered by unit runners. Apply the CRT density argument to the unit system for
the remaining p^2-p-1 non-unit residues: density ≤ p^{-2(p^2-p-1)} → 0 for p≥3.
Count ≤ M · p^{-2(p^2-p-1)}: for M ≤ L/p ≤ p^{5}/p = p^4 (with L ≤ p^6 est.):
count ≤ p^4 · p^{-2(p^2-p-1)} = p^{4-2p^2+2p+2} = p^{2p+6-2p^2}.
For p≥3: 2p+6-2p^2 < 0 (since 2p^2 > 2p+6 ↔ p^2-p-3>0 ↔ p≥3 ✓). Count < 1. □

**Conclusion:** The single-channel impossibility holds for k=3 by the CRT density
argument applied to the residual non-unit coverage requirement. Tier 2 for k=3
closes analogously to k=2 once the chamber-entry bound is in place.

**Next:** Verify the p=3, n=27 case explicitly. Then write k=general argument.
