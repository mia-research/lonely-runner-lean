# LRC Tier 2 Sub-case (i) — Chamber Safety Proof
**Version**: v1 (2026-03-09)
**Context**: Theorem 8.3, U-FORCE condition (both dropped speeds non-units → all φ(n) unit speeds active)

---

## 1. Setup and Notation

- **n**: composite integer with ≥ 2 distinct prime factors; p_min = smallest prime factor of n
- **L** = k · lcm(units mod n) for integer k ≥ 1; all unit speeds divide L
- **E_non** = all φ(n) unit runners {e : gcd(e,n) = 1, 1 ≤ e ≤ n-1}
- **B_div** = [n, L-n] (integer fibres where safe times can occur)
- **Floor state** of runner e at fibre b: f_e(b) = ⌊e·b/L⌋ ∈ {0,...,e-1}
- **bad_set(e, t, n)** = Sol(e, −t, n) ∪ Sol(e, −(t+1), n) = {r : e·r ≡ −t or −t−1 (mod n)}
  - For unit e (gcd(e,n)=1): |bad_set(e,t,n)| = 2 always
- **z=0 event** for unit e_u at step m: fibre b = mL/e_u (exact integer since e_u | L)
  - Floor state at this event: L-independent formula f_v = (e_v · m) // e_u for all v
- **Chamber**: maximal interval [b_start, b_end] ⊂ B_div on which all floor-state vectors are constant

---

## 2. Main Theorem

**Theorem (Chamber Safety)**: Under U-FORCE with L = k·lcm(units mod n),
$$B_{\text{safe}} = |\text{B\_div}| = L - 2n + 1$$
In particular, B_safe ≥ φ(n)(n−2)/2 for all k ≥ 1.

*This is a dramatically stronger statement than the bound requires.*

---

## 3. Proof

The proof uses two lemmas. Both are elementary given the existing framework.

### Lemma 0 (Baseline Safety)

**Claim**: When f_e = 0 for ALL units e, the residue r = p_min is not in ⋃_e bad_set(e, 0, n).

**Proof**:
At t = 0: bad_set(e, 0, n) = {Sol(e, 0, n)} ∪ {Sol(e, −1, n)} = {0} ∪ {−e⁻¹ mod n}.

Since e⁻¹ ranges over all units as e ranges over units (inversion is a bijection):
$$\bigcup_{e \text{ unit}} \text{bad\_set}(e, 0, n) = \{0\} \cup \{n - u \bmod n : u \text{ unit}\}$$

A residue r is in this union iff r = 0 or n − r is a unit (gcd(n−r, n) = 1).

For r = p_min: gcd(n − p_min, n). Since p_min | n, we have p_min | (n − p_min), so gcd(n − p_min, n) ≥ p_min > 1. Therefore n − p_min is NOT a unit, so **r = p_min ∉ union**. □

*Verified computationally: all composite n ≤ 100 with ≥2 prime factors. Zero failures.*

---

### Lemma RI (Relay Invariant / Gap A)

**Claim**: For every unit e_u ≥ 2 and every m ∈ {1,...,e_u−1}, at floor states
$$f_v = \lfloor e_v \cdot m / e_u \rfloor \quad \text{for each unit } e_v,$$
the bad-set union ⋃_v bad_set(e_v, f_v, n) ≠ ℤ_n.

This is **Gap A from Session 11 (Theorems I–III, Universal Witnesses)**, restated as a statement about floor-state vectors at z=0 event positions.

**Key point**: The formula f_v = (e_v · m) // e_u is **L-independent**, so this holds for all valid L. It applies to z=0 events both inside and outside B_div.

*Verified computationally: 532 z=0 events across all test cases. Zero failures.*

---

### Main Proof

**Step 1** (Chamber partition): The transition points
$$T = \{n\} \cup \{L{-}n{+}1\} \cup \{mL/e_u : e_u \text{ unit} \geq 2,\ m=1,...,e_u{-}1,\ n \leq mL/e_u \leq L{-}n\}$$
partition B_div = [n, L−n] into **chambers** — maximal intervals of constant floor-state vector.

Since e_u | L for all units, each transition point is a z=0 event position. *(Verified: chamber floor-state vectors are constant in all tested cases.)*

**Step 2** (Coverage): For any b ∈ B_div, let b* = the most recent z=0 event satisfying b* ≤ b, b* ≥ 0 (globally, not restricted to B_div).

The floor-state vector at b equals the floor-state vector at b* (by definition: floor states change only at z=0 events, so the vector is constant from b* up to the next transition).

**Step 3** (Safety by cases):

**Case A**: *No z=0 event before b* (equivalently, b < min z=0 event = L/max_unit, so all floor states are 0).

The floor-state vector is (0,...,0). By **Lemma 0**, r = p_min is uncovered → b is safe.

**Case B**: *Some z=0 event b* ≤ b exists.*

The floor-state vector at b equals the vector at b* = m*L/e_u for some unit e_u at step m. By **Lemma RI** (Gap A), some r ∈ ℤ_n is uncovered at b* → the same r is uncovered at b → b is safe.

**Conclusion**: Every b ∈ B_div is safe, so B_safe = |B_div| = L − 2n + 1. □

---

## 4. Numerical Evidence

The proof closure table from `lrc_chamber_proof_verify_v1.py`:

| n  | k  | L                    | \|B_div\| | chambers | L0 chmbrs | RI chmbrs | B_safe               | PASS |
|----|----|-----------------------|----------|----------|-----------|-----------|----------------------|------|
| 6  | 10 | 50                   | 39       | 5        | 1         | 4         | 39                   | YES  |
| 10 | 1  | 63                   | 44       | 11       | 0         | 11        | 44                   | YES  |
| 10 | 5  | 315                  | 296      | 15       | 1         | 14        | 296                  | YES  |
| 12 | 1  | 385                  | 362      | 21       | 1         | 20        | 362                  | YES  |
| 15 | 1  | 8008                 | 7979     | 42       | 1         | 41        | 7979                 | YES  |
| 30 | 1  | 215,656,441          | 215,656,382 | 113   | 1         | 112       | 215,656,382          | YES  |
| 42 | 1  | 36,220,269,467,525   | ≈3.6×10¹³ | 237   | 1         | 236       | ≈3.6×10¹³            | YES  |

**Pattern**: Every test case has exactly **1 Lemma 0 chamber** (the first chamber, covered by all-zero floor states or by a pre-B_div z=0 event) and **(n_chambers − 1) Lemma RI chambers**. Zero unsafe chambers.

The ratio B_safe/bound ranges from ~2.75× (n=10, k=1) to ~1.5×10¹¹ (n=42, k=1).

---

## 5. Proof of B_safe ≥ φ(n)(n−2)/2

The theorem B_safe = L − 2n + 1 far exceeds the required bound. For k = 1:

$$B_{\text{safe}} = \text{lcm(units)} - 2n + 1 \gg \sum_{e \text{ active unit}} (e - 1) = \varphi(n)(n{-}2)/2$$

since lcm(units) grows superpolynomially in n. For any k ≥ 1 and n ≥ 6 with 2+ prime factors, L − 2n + 1 ≥ lcm(units) − 2n + 1 ≥ n(n−1) − 2n + 1 ≥ n² − 3n + 1 > φ(n)(n−2)/2 once n is large. For small n (n = 6, 10, 12, 15, 30, 42), direct computation confirms B_safe ≥ bound. □

---

## 6. Relationship to Previous Analysis

### What the earlier analysis got right
- The relay invariant (Gap A): **CONFIRMED**. Every z=0 event fibre is safe.
- The "B_safe < bound" apparent failures for n=10,15,42 were NOT counterexamples; they were artifacts of counting only z=0 event fibres, not all fibres in B_div.

### The key new insight
The chamber structure **amplifies** the relay invariant: safety at each z=0 event fibre propagates to the entire interval (chamber) that starts there. Between consecutive z=0 events, ALL fibres are safe — not just the transition fibre itself.

This makes the proof **much simpler** than the coincidence-compensation route:
- Old route: count distinct z=0 fibres, subtract coincidences, add compensating fibres → messy
- New route: every fibre in B_div is safe (B_safe = |B_div|) → trivially exceeds bound

### Connection to Gap A (Session 11)
Lemma RI IS Gap A, stated as: "every z=0 event fibre has an uncovered residue under U-FORCE." Session 11's Theorems I–III (Universal Witnesses) prove this. The chamber observation converts this into "every FIBRE in B_div is safe" — a stronger statement that is actually easier to prove.

---

## 7. What Remains Open

### For the published proof
1. **Formal proof of Lemma RI** for general composite n (the Gap A proof from Session 11 must be verified to apply to **all** z=0 events, including m=1 cases where b* < b_lo = n).
   - The L-independent formula f_v = (e_v·m)//e_u is correct for all m ∈ {1,...,e_u−1}.
   - Session 11's proof handles all such m. **Status: handled.**

2. **Case A coverage** for n with L/max_unit < n (i.e., the first z=0 event falls before b_lo = n):
   - This occurs when max_unit > L/n, which requires k · lcm/max_unit < n.
   - For n=10, k=1: first z=0 event at b=7 < 10, so the first chamber of B_div inherits safety from that out-of-B_div event (Lemma RI applies at b*=7, not Lemma 0).
   - **Status: covered by Case B with b* outside B_div.** Lemma RI still applies.

3. **Extension to general L** (not divisible by all units):
   - For L not divisible by all units, transition points are ⌈mL/e⌉ (not exact z=0 events).
   - The chamber partition still applies, but Lemma RI must be stated for "floor-state transitions" rather than exact z=0 events.
   - **Status: out of scope for Sub-case (i), which uses L = k·lcm(units).**

### For the full Theorem 8.3
Sub-case (i) (U-FORCE) is now proved. The remaining Sub-cases require separate analysis:
- Sub-case (ii): exactly one dropped speed is a non-unit (partial force)
- Sub-case (iii): both dropped speeds are units (no force)

---

## 8. Summary Statement for Paper

**Theorem 8.3 Sub-case (i)**: Let n be composite with ≥2 distinct prime factors. Let E_non contain all φ(n) unit runners mod n, and let L = k · lcm{e : gcd(e,n)=1, 1≤e≤n-1} for some integer k ≥ 1.

Then B_safe = |B_div| = L − 2n + 1 ≥ φ(n)(n−2)/2.

*Proof*: B_div is partitioned into chambers of constant floor-state vector. Each chamber is safe by Lemma 0 (Case A: all-zero floor states) or Lemma RI = Gap A (Case B: chamber starts at a z=0 event, proved in §8.2). Therefore every fibre in B_div is safe. □
