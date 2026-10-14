# Transport Completeness for n = p^k: Corrected Framework
## v2 — Session B (2026-03-10)

**What changed from v1:** Floor variable corrected to q_e(b)=⌊eb/L⌋. Full
coverage decomposition replaces unit-only TC. k=2 separated from k≥3.
Bounded persistence dropped; chamber density theorem is the new target.

---

## 1. Setup and Corrected Definitions

Let n=p^k (p odd prime, k≥2), U-FORCE (all φ(n) unit runners in E_fix).
Let L = lcm(E_fix), M = L/p (period length), B_div = {b ∈ ℤ : L/n < b < (n-1)L/n}.

**Correct floor state.** For any runner e ∈ E_fix:
    q_e(b) = ⌊eb/L⌋    [runner e's lap count at position b]

(NOT ⌊b/e⌋. The v1 variable was wrong; see lrc_transport_kge3_failure_note_v1.md.)

**Chamber entry.** For s ∈ {0,...,p-1}: chamber entry b_s = sM = sL/p.
    q_e(sM) = ⌊esM/L⌋ = ⌊es/p⌋ = αs + ⌊βs/p⌋   where e = αp+β, β∈{1,...,p-1}.

**Increment formula** (the engine for all persistence arguments):
    q_e(sM+δ) = ⌊es/p⌋ + ⌊{es/p} + eδ/L⌋,    0 ≤ δ < M,
where {x} = x - ⌊x⌋ is the fractional part.
Proof: ⌊e(sM+δ)/L⌋ = ⌊es/p + eδ/L⌋ = ⌊es/p⌋ + ⌊{es/p} + eδ/L⌋. □

---

## 2. Full Coverage Decomposition

For each b ∈ B_div, write the coverage set as
    C(b) = C_unit(b) ∪ C_non(b)
where C_unit(b) = ∪_{e unit} bad(e, q_e(b), n) and
      C_non(b)  = ∪_{e non-unit, e∈E_fix} bad(e, q_e(b), n).

**Classification of C_non by Primitives 3 and 4:**
For non-unit runner e_i = j_i p^{m_i} (gcd(j_i,p)=1, 1≤m_i≤k-1):

  MODE A (Transparency, Primitive 3): p^{m_i} ∤ q_e and p^{m_i} ∤ (q_e+1)
  → bad(e_i, q_e, n) = ∅. Contributes NOTHING to C_non.

  MODE B (Unit coset, Primitive 4): p^{m_i} | q_e but p^{m_i+1} ∤ q_e
  → bad(e_i, q_e, n) ⊆ {unit residues}. C_non ⊆ units.

  MODE C (Non-unit residues): p^{m_i+1} | q_e or p^{m_i+1} | (q_e+1)
  → bad(e_i, q_e, n) contains non-unit residues {jp : p | r}.
  Requires q_e ≡ 0 (mod p^{m_i+1}) — a STRONGER divisibility condition.

**Key asymmetry between k=2 and k≥3:**
  k=2: For all b ∈ B_div with q_{e_i}≥1: max q_{e_i} ≤ p^2-p-1 < p^2.
  → MODE C NEVER occurs for k=2. C_non covers only unit residues. [Theorem CO-2]

  k≥3: Runner jp with j≥p+1 can reach q_{jp} = p^2 in B_div.
  → MODE C can occur. C_non may cover non-unit residues. [CO-3 §5]

**Definition TC** (using full coverage):
  b is transport-complete (TC) if C_unit(b) ∪ C_non(b) = Z_{p^k}.
  A fibre is safe iff it is NOT TC.

---

## 3. The k=2 Case: Period Classification Theorem

**What is known (proved):**
  P1. All chamber entries sM (s≠0) are TC (F_p×-orbit theorem).
  P2. In B_div, MODE C never occurs (CO-2). C_non covers only unit residues.
  P3. TC ↔ C_unit covers all p-1 non-unit residues (since C_non cannot help).

**What needs to be proved:**
  **Theorem 7.1 (Period Classification for k=2, to prove):**
  For each drop pair {a,b} (both non-units of Z_{p^2}), at most 2 values of
  s ∈ {1,...,p-1} give a "fully dangerous" period [sM,(s+1)M) ⊂ B_div.

**Why this closes Tier 2 for k=2:**
  Fully dangerous periods have length M = L/p. With at most 2 fully dangerous
  periods: dangerous fibres ≤ 2M = 2L/p.
  |B_div| ≈ (p²-2)L/p². Safe ≥ (p²-2)L/p² - 2L/p = L(p²-2-2p)/p² = L(p-1)(p-2)/p².
  With L ≥ (p²-1)(p²-2) ≈ p^4: safe ≥ p^2(p-1)(p-2) >> p(p-1) = φ(p²). ✓

**Evidence:** For p=5: each drop pair gives at most 2 fully dangerous periods
(verified for all drop pairs of Z_25). Structural reason: the "fully dangerous"
condition requires the drop pair to contain the Cond-2 partner of every aligned
unit runner in the period — a very strong condition.

**Proof route:** Show that a period [sM,(s+1)M) is fully dangerous only when the
drop pair {a,b} satisfies: for every unit e_u with aligned floor in (sM,(s+1)M),
the Cond-2 partner e* = e_u·⌊q_{e_u}/⌋ - p^2 is in {a,b}. Since {a,b} has only
2 elements, at most 2 values of s can satisfy this simultaneously.

---

## 4. The k≥3 Case: Chamber Density Theorem

**The bounded persistence theorem is FALSE.** (See lrc_transport_kge3_failure_note_v1.md.)
Dangerous intervals can extend Ω(L/n) fibres from chamber entries.

**What needs to be proved:**
  **Theorem 6.1 (Chamber Density for k≥3, to prove):**
  For n=p^k (k≥3) under U-FORCE B3b:

    |{b ∈ B_div : b is TC}| ≤ (1 - 1/p) · |B_div|.

**Why this closes Tier 2 for k≥3:**
  Safe fibres ≥ |B_div|/p ≈ (p^k-2)L/p^{k+1}.
  With L ≥ (n-1)(n-2) ≈ p^{2k}: safe ≥ p^{2k-k-1}(p^k-2) ≈ p^{k-1} >> φ(p^k) = p^{k-1}(p-1). ✓
  (More precisely: safe ≥ (p^k-2)L/p^{k+1} ≥ (p^k-2)p^{2k}/(p^{k+1}) = (p^k-2)p^{k-1} >> φ.) ✓

**Proof route (sketch):**
  TC requires C(b) = Z_{p^k}. In particular, EVERY non-unit residue jp (j=1,...,p^{k-1}-1)
  must be covered. Non-unit residue jp is covered only via MODE C (some non-unit runner
  at floor ≡ 0 mod p^{m+1}) or unit coverage at p-aligned floor.

  For MODE C to cover jp at b: runner jp^m at floor p^{m+1}·ℓ covers specific
  non-unit residues. The set of b where this holds is a union of intervals of
  total length ≤ L/p^{m+1} × (number of mode-C windows).

  Step 1: Total MODE C coverage of residue jp across all non-unit runners:
    ≤ 2 × Σ_{m=1}^{k-1} Σ_{j} L/(p^{m+1}) × 1 ≤ 2L × (k-1)/p^2 < L/p.

  Step 2: TC requires jp covered AND all other non-unit residues covered.
    The intersection of coverage conditions (CRT density) gives TC density
    ≤ Π_{j} (density jp is covered) ≤ (1 - 1/p)^{p^{k-1}-1} < (1-1/p)^p ≤ 1/e.
    For p≥3: 1/e < 1 - 1/p. So TC density < 1 - 1/p. □ (if independence holds)

  **Independence caveat:** The coverage conditions for different jp are NOT
  independent — they all depend on the same b through the floor map. Proving
  independence (or finding the correct correlation bound) is the main technical gap.

---

## 5. Two Hard Theorems and Proof Obligations

| Theorem | Case | Stated as | Status |
|---------|------|-----------|--------|
| 7.1 (Period classification) | k=2 | At most 2 fully dangerous s-periods per drop pair | Open |
| 6.1 (Chamber density) | k≥3 | TC density ≤ 1-1/p in B_div | Open; sketch above |

Both theorems need analytic proofs. The sketch in §4 gives the right density target
and mechanism (MODE C coverage being sparse + CRT density argument), but the
independence step requires either a correlation bound or a different approach
(e.g., the isolated z=0 event route from CO-3 §6, which avoids density altogether).

**Next test:** For n=27, drop {3,6}: compute total TC fibre count vs |B_div|.
If TC density < 2/3, Theorem 6.1 holds at density level 1-1/p = 2/3.
If TC density ≥ 2/3 for some drop pair: density 1-1/p is too optimistic; need
sharper density target or different counting method.
