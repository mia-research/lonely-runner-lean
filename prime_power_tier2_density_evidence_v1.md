# Prime-Power Tier 2: Density Program Evidence
## v1 — Session C (2026-03-11)

**Purpose.** Record the complete empirical output of the chamber-density
computation program (`prime_power_batch_analysis.py`) across five prime
powers, assess the density-program conjectures against the data, and
state what the evidence forces the correct proof target to be.

---

## 1. Data Collection

Script: `prime_power_batch_analysis.py` (corrected floor variable
`q_e(b) = floor(eb/L)` throughout).

For each prime power `n = p^k` and each non-unit drop pair `{a, b}`
(both dropped runners multiples of `p`), the script computes:

- `C_bad / M` where `M = L/p`   (the "dangerous-over-M ratio")
- `|S_drop|`                    (number of fully dangerous chambers)
- max `C_bad(C_s) / (L/p^2)`   (worst partial-chamber ratio)

Derived statistics:

    |B_div| / M  =  p(n-2)/n   (exact formula from b_lo, b_hi)
    TC density   =  (C_bad/M) / (|B_div|/M)
    safe fraction  =  1 - TC density

---

## 2. Results by Prime Power

### n = 25 (p = 5, k = 2)   — all 6 non-unit drop pairs

| Statistic              | Value      |
|------------------------|------------|
| Pairs analysed         | 6 / 6      |
| max C_bad/M            | 3.099      |
| mean C_bad/M           | 2.962      |
| |B_div|/M              | 4.600      |
| max TC density         | 0.674      |
| 1 - 1/p                | 0.800      |
| min safe fraction      | 0.326      |
| 1/p                    | 0.200      |
| max |S_drop|           | 2          |
| |S_drop| distribution  | {1:4, 2:2} |
| max partial/(L/p²)     | 3.413      |

**Theorem 7.1 ("at most 2 fully dangerous periods" for k=2) holds for p=5. ✓**
Safe fraction is comfortably above 1/p = 0.2 in all cases.

---

### n = 27 (p = 3, k = 3)   — all 28 non-unit drop pairs

| Statistic              | Value              |
|------------------------|--------------------|
| Pairs analysed         | 28 / 28            |
| max C_bad/M            | 2.214              |
| mean C_bad/M           | 1.650              |
| |B_div|/M              | 2.778              |
| max TC density         | 0.797              |
| 1 - 1/p                | 0.667              |
| min safe fraction      | 0.203              |
| 1/p                    | 0.333              |
| max |S_drop|           | 1                  |
| |S_drop| distribution  | {0:24, 1:4}        |
| max partial/(L/p²)     | 2.440              |

Worst pairs (|S_drop| = 1): {3,9}, {3,12}, {9,12} → S_drop={1};
{6,18} → S_drop={2}.
All involve dropping a runner divisible by p² = 9.

**Note:** max C_bad/M = 2.214 > p−1 = 2. The lower band [L/n, M)
contributes ~0.21M of dangerous fibres beyond the two inner chambers.

---

### n = 49 (p = 7, k = 2)   — all 15 non-unit drop pairs

| Statistic              | Value                     |
|------------------------|---------------------------|
| Pairs analysed         | 15 / 15                   |
| max C_bad/M            | 5.877                     |
| mean C_bad/M           | 5.139                     |
| |B_div|/M              | 6.714                     |
| max TC density         | 0.875                     |
| 1 - 1/p                | 0.857                     |
| min safe fraction      | 0.125                     |
| 1/p                    | 0.143                     |
| max |S_drop|           | 4                         |
| |S_drop| distribution  | {1:2, 2:5, 3:6, 4:2}      |
| max partial/(L/p²)     | 5.629                     |

**Theorem 7.1's "at most 2" claim fails for p=7. Max |S_drop| = 4.**
For k=2 the correct proof is CO-3, not the period classification route.

---

### n = 125 (p = 5, k = 3)   — all 276 non-unit drop pairs

| Statistic              | Value                              |
|------------------------|------------------------------------|
| Pairs analysed         | 276 / 276                          |
| max C_bad/M            | 4.608                              |
| mean C_bad/M           | 3.713                              |
| |B_div|/M              | 4.920                              |
| max TC density         | 0.937                              |
| 1 - 1/p                | 0.800                              |
| min safe fraction      | 0.063                              |
| 1/p                    | 0.200                              |
| max |S_drop|           | 3                                  |
| |S_drop| distribution  | {0:211, 1:44, 2:17, 3:4}           |
| max partial/(L/p²)     | 4.733                              |

Worst pairs (|S_drop| = 3):

| Drop pair  | C_bad/M | S_drop   | partial_max |
|------------|---------|----------|-------------|
| (5, 25)    | 3.740   | {1,2,3}  | 1.851       |
| (5, 30)    | 3.937   | {1,2,3}  | 2.341       |
| (10, 50)   | 4.342   | {1,3,4}  | 2.111       |
| (25, 30)   | 4.417   | {1,2,3}  | 3.543       |

Pattern: worst pairs include a runner divisible by p² = 25 (namely 25, 50).

---

### n = 343 (p = 7, k = 3)   — 20 / 1128 pairs (first-column sample)

| Statistic              | Value              |
|------------------------|--------------------|
| Pairs analysed         | 20 / 1128          |
| max C_bad/M            | 5.895              |
| mean C_bad/M           | 5.524              |
| |B_div|/M              | 6.959              |
| max TC density         | 0.847              |
| 1 - 1/p                | 0.857              |
| min safe fraction      | 0.153              |
| 1/p                    | 0.143              |
| max |S_drop|           | 5                  |
| |S_drop| distribution  | {0:6,1:2,2:2,3:7,4:2,5:1} |
| max partial/(L/p²)     | 6.732              |

---

## 3. Cross-Case Summary Table (k = 3)

| n (p^k) | p | k | max C_bad/M | p−1 | max TC density | 1−1/p | min safe frac | 1/p  | max |S_drop| | p−1 |
|---------|---|---|-------------|-----|----------------|-------|---------------|------|--------------|-----|
| 27      | 3 | 3 | 2.214       | 2   | 0.797          | 0.667 | 0.203         | 0.333 | 1           | 2   |
| 125     | 5 | 3 | 4.608       | 4   | 0.937          | 0.800 | 0.063         | 0.200 | 3           | 4   |
| 343     | 7 | 3 | 5.895       | 6   | 0.847          | 0.857 | 0.153         | 0.143 | 5           | 6   |

**Observation A (C_bad grows with p).** For fixed k=3:
  `max C_bad/M ≈ p − 1.0`  (ratio close to 1 in each case).
The constant C_k independent of p claimed in the density program does
NOT exist for k=3. C_bad/M grows linearly with p.

**Observation B (Theorem 6.1 status is non-monotone).**
- n=27: TC density 0.797 > 1−1/3 = 0.667. **Theorem 6.1 violated.**
- n=125: TC density 0.937 > 1−1/5 = 0.800. **Theorem 6.1 violated.**
- n=343: TC density 0.847 < 1−1/7 = 0.857. **Theorem 6.1 holds** (sample).

The bound `safe ≥ (1/p)|B_div|` is too optimistic for small/moderate p.

**Observation C (Safe fraction is always positive).**
Across all 345 fully-enumerated pairs and 20 sample pairs, `safe > 0`
in every case. Minimum safe fraction = 0.063 (n=125, 4 pairs).
No pair has all of B_div dangerous.

**Observation D (|S_drop| ≤ p−2 empirically).**
- n=27: max |S_drop| = 1 = p−2. (p−1 = 2 chambers total.)
- n=125: max |S_drop| = 3 = p−2. (p−1 = 4 chambers total.)
- n=343: max |S_drop| = 5 = p−2. (p−1 = 6 chambers total.) [sample]

This suggests |S_drop| ≤ p−2 (at least one chamber is never fully
dangerous). If true analytically, the fully-dangerous contribution is
at most (p−2)M, leaving safe ≥ |B_div| − (p−2)M − partial ≈ M > 0.

**Observation E (Structural pattern for worst pairs).**
The largest |S_drop| values appear when the drop pair includes a runner
divisible by p² (the "second non-unit level"). Dropping p² removes the
Mode-C floor protection that would otherwise limit coverage. Pairs not
involving a p²-multiple tend to have |S_drop| = 0.

---

## 4. Implications for the Density Program

### 4.1 What the density program got right

1. The O_k(L/p) scale is correct in the sense that C_bad/|B_div| < 1 always.
2. The decomposition into Type I (fully dangerous) and Type II (partial)
   chambers is the correct structural framework.
3. The partial-chamber ratio max C_bad(C_s)/(L/p²) is bounded by ≈ p−1
   empirically (itself growing with p), consistent with Theorem D3 only
   when E_k is allowed to depend on p.

### 4.2 What the density program got wrong

**The constant C_k independent of p does not exist for k = 3.**
Empirically C_bad/M ≈ p−1 for all tested prime powers, so
`C_bad = O(pM) = O(L)`, not `O(L/p)`.

Specifically:
- Theorem D2 fails to bound |S_drop| by a p-independent constant D_k.
  For k=3: max |S_drop| grows as p−2.
- Theorem D3 fails to bound C_bad(C_s)/(L/p²) by a p-independent E_k.
  For k=3: partial ratios grow as ≈ p−1 as well.

### 4.3 What survives

1. **Safe > 0 in all tested cases.** No drop pair makes all of B_div
   dangerous. Minimum safe fraction: 6.3%.

2. **Tier 2 closes by LCM dominance alone.** For n = p^k with k ≥ 3:

       B_safe ≥ δ × L,    δ = 1 − max(C_bad/|B_div|) > 0.

   Empirically δ ≥ 0.063. Since L is super-exponential in p^k (L ≥
   lcm of all units of Z_{p^k}, which contains all primes ≤ p^k), and
   φ(n)(n−2)/2 = p^{2k−1}(p−1)/2 is polynomial in p^k, we have

       B_safe ≥ 0.063 × L  >>  φ(n)(n−2)/2.

   This closes Tier 2 for all tested (n, drop pair) without needing
   C_k to be independent of p.

3. **|S_drop| ≤ p−2 empirically.** If this can be proved analytically
   (one chamber always "non-fully-dangerous"), it would give:

       B_safe ≥ |B_div| − (p−2)M − max_partial × M/p
              ≥ M × [|B_div|/M − (p−2) − max_partial/p]

   and for large enough p this is still positive. Combined with the
   LCM lower bound, Tier 2 follows.

---

## 5. Revised Proof Targets

The density program's target `C_bad ≤ C_k × L/p` (constant C_k) is
refuted. The corrected targets are, in increasing order of ambition:

### Target T1 (Minimal — probably sufficient for Tier 2)

> For every prime power `n = p^k` (k ≥ 3) in U-FORCE B3b, and every
> non-unit drop pair, `B_safe ≥ 1`.

This follows from any proof that at least one fibre in B_div is safe.

If T1 can be proved AND the LCM lower bound `L ≥ f(n, k)` is
established where f grows faster than φ(n)(n−2)/2, Tier 2 closes.

The LCM bound is essentially free: L = lcm(active ∪ {n}) and active
contains all primes ≤ p^k not equal to p, so L ≥ primorial(p^k)/p ≥
exp(p^k (1−o(1))), far exceeding φ(n)(n−2)/2 = O(p^{2k}).

### Target T2 (Structural — |S_drop| ≤ p−2)

> For every prime power `n = p^k` (k ≥ 3) in U-FORCE B3b, and every
> non-unit drop pair, there exists at least one s ∈ {1,...,p−1} such
> that chamber C_s is NOT fully dangerous.

This is consistent with all data. It implies T1 (and more: gives a
safe mass ≈ M from the partially-dangerous residuals in C_s).

The structural reason T2 might hold: the chamber index s is determined
modulo p (via the F_p^×-orbit structure), and the "fully dangerous"
condition requires the drop pair to simultaneously "cancel" every
uncovered residue in the chamber. With only 2 dropped runners, not all
p−1 orbital chambers can be cancelled simultaneously.

### Target T3 (Tight — matches empirical safe fraction)

> For every prime power `n = p^k` (k ≥ 3) in U-FORCE B3b, and every
> non-unit drop pair,
>
>     B_safe ≥ L × (p^k − 2p) / p^{k+1}.

This is the trivial lower bound from the chamber structure. It is
consistent with all data (safe fraction ≥ 0.063 in all cases, and the
trivial bound gives 0.057 for n=125). This would give Tier 2 since
L >> φ(n)(n−2)/2 × p^{k+1}/(p^k − 2p).

---

## 6. Next Computational Task

Run the full 1128-pair analysis for n = 343 to verify:
1. Does |S_drop| reach p−1 = 6 (would refute T2)?
2. Does min safe fraction drop below the n=125 minimum of 6.3%?
3. Does max C_bad/M approach p−1+ε (≈ 6) confirming the growth law?

Command: `python3 prime_power_batch_analysis.py --n 343 --outfile prime_power_n343_batch.csv`

(Estimated runtime: 1–4 hours given |B_div| for n=343 involves integers
of 100+ digits, × 1128 pairs.)

---

## 7. What to Do Next Analytically

### Immediate: Prove Target T2 (or refute it with n=343 data)

T2 says: the F_p^× orbit structure prevents all p−1 chambers from
being simultaneously fully dangerous. Proof sketch:

A chamber C_s is fully dangerous iff for every non-unit residue r, the
residue r is covered by C(sM). Coverage at b = sM (entry) is given by
the F_p^×-orbit: Cov(sM) = s · Cov(M) (mod p^k). So the fully-dangerous
condition at entry is: s · Cov(M) = Z_{p^k}. This holds for all s ≠ 0
(Prop 1). But full-chamber dangerousness requires TC to persist
throughout [sM, (s+1)M), not just at the entry.

The persistence question is: for which s does TC survive the first floor
change inside C_s? If at least one s has a floor change that breaks TC,
T2 holds.

### Intermediate: Prove the LCM lower bound (Lemma D4 from density program)

`L ≥ lcm({1 ≤ m ≤ p^k − 1 : p does not divide m})`.

This is already essentially obvious: the active set includes all units
of Z_{p^k}, and L is their lcm (possibly larger if non-unit runners are
also included). The lemma follows directly from the definition of L.

Then combine with T1/T2/T3 to close Tier 2.

### Long-term: The isolated z=0 event route (CO-3 §6)

Alternative to the density/chamber program entirely. From CO-3
lrc_coset_orphaning_v1.md §6: each z=0 event (floor state where some
specific residue is uncovered) gives a safe fibre. If there are ≥ φ(n)
such events in B_div, Tier 2 follows directly. This approach doesn't
require controlling C_bad/|B_div| at all.

The adaptation for k ≥ 3 requires identifying which z=0 events remain
valid when Mode C runners are active. This is the direction flagged in
CO-3 §6 but not yet written up.
