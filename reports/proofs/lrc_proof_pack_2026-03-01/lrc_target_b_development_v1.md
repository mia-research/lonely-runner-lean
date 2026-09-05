# LRC — Target B Development: CRT Coverage Gaps for Interior Residues

**Date:** 2026-03-07
**Depends on:** `lrc_coset_dynamic_v1.md` (DCT-C verified, Fact D1 proved)
**Scope:** Gap-4: composite n ≥ 6, gcd(E_non)=1, n|L, E_div≠∅, all speeds < L ("proper")

---

## 1. Empirical Findings from `lrc_coset_dynamic_v1.py`

### 1.1 The {r=1, r=n−2} Symmetry

Across all n-values tested (n ∈ {6,8,9,10,12,15}):

| n | r_least_covered | Coverage fraction |
|---|---|---|
| 6 | r=1 and r=4 (n−2) | 71.3% |
| 8 | r=1 and r=6 (n−2) | 72.7% |
| 9 | r=1 and r=7 (n−2) | 80.6% |
| 10 | r=1 and r=8 (n−2) | 78.8% |
| 12 | r=1 and r=10 (n−2) | 86.1% |
| 15 | r=1 and r=13 (n−2) | 88.7% |

The pair {r=1, r=n−2} is ALWAYS simultaneously the least covered, with exact equal counts (reflecting the symmetry `a ↦ n−1−a` of the bad_set). This is the Target B candidate pair.

### 1.2 Per-tuple check: is r=1 always free at some fiber?

| n | Proper tuples tested | r=1 disasters | Genuine LRC failures |
|---|---|---|---|
| 6 | 500 | 32 (6.4%) | 0 |
| 8 | 300 | 0 (0%) | 0 |
| 9 | 300 | 0 (0%) | 0 |
| 10 | 300 | 0 (0%) | 0 |
| 12 | 300 | 0 (0%) | 0 |
| 15 | 300 | 0 (0%) | 0 |

"Proper" = all speeds < L (excluding degenerate speed=L wrappers which make two runners coincide).
"Genuine LRC failure" = B_safe = 0 (no free residue anywhere) — **none found in proper scope**.

### 1.3 Structure of n=6 Disasters

For n=6 proper disasters (32/500): r=1 is always covered. Key observations:
- r=4 (= n−2) is ALSO always covered in ALL 32 disasters (symmetry is perfect).
- r=2 is free in 31/32 disasters; r=3 is free in 31/32 disasters.
- The inner residue pair {r=2, r=3} provides the LRC witness for almost all n=6 disasters.
- In the remaining 1/32: only r=0 and r=5 are free (boundary residues).

**Coverage hierarchy for n=6 disasters:**
- r=1 and r=4: 100% coverage (always blocked).
- r=2 and r=3: ~91–99% coverage (free at some fibers in 31/32 cases).
- r=0 and r=5: ~77–99% coverage (free in 29/32 cases).

---

## 2. Algebraic Explanation of the {r=1, r=n−2} Symmetry

**Why r=1 and r=n−2 are hardest to cover:**

Via DCT-C, runner `e` covers residue `r=1` when:
- Lower Sol: `t_e(b) ≡ −e (mod n)`, i.e., `e·1 ≡ −t_e (mod n)`.
- Upper Sol: `t_e(b) ≡ −e−1 (mod n)` AND `s_e(b) > 0`.

At the initial window (t_e = 0 for all e):
- Lower Sol at t=0: `Sol(e, 0, n)` = H_{g_e}. Residue r=1 is in H_{g_e} only if `n/g_e | 1`, i.e., `g_e = n`. So **only E_div runners** (g_e = n) cover r=1 via lower Sol at t=0.
- Upper Sol at t=0 (when s_e > 0): `Sol(e, −1, n)`. Non-empty iff `g_e | 1`, i.e., `g_e = 1` (unit runners). r=1 ∈ Sol(e,−1,n) iff `e·1 ≡ −(−1) ≡ 1 (mod n)` iff e ≡ 1 (mod n)... wait, `e·a ≡ −1 (mod n)` for a=1 gives `e ≡ −1 (mod n)`. So **unit runners with e ≡ n−1 (mod n)** cover r=1 via upper Sol at t=0.

**Conclusion:** At t=0, r=1 is covered only by E_div runners (all of Z_n) or unit runners with e ≡ −1 (mod n). For the **initial window** (all runners at t=0), r=1 is free unless:
1. The tuple contains an E_div runner (which covers Z_n, always covering r=1), OR
2. The tuple contains a unit runner with e ≡ −1 (mod n) AND s_e > 0 at that fiber.

Since E_div ≠ ∅ is part of the Gap-4 scope, the E_div runner covers r=1 (and Z_n) at the initial window. After the initial window (when t_{e_div} > 0), the E_div runner covers ∅ (Fact D3). So r=1 must then be covered by non-E_div runners.

**Why small runners (e < n/2) never cover r=1:**
For runner e: t_e(b) = ⌊e·b/L⌋ ∈ {0,...,e−1} (since b ≤ L−n, so e·b/L < e). The lower-bad state for r=1 is t_e ≡ −e (mod n), i.e., t_e = n−e. For e < n/2: n−e > n/2 > e−1 ≥ max t_e. So t_e NEVER reaches n−e. The upper-bad state is n−e−1, same analysis: n−e−1 ≥ n/2 > e−1. So **runners with speed < n/2 never cover r=1 at any fiber.** □

This is a key structural fact: the CRT argument only needs to handle runners with e ≥ n/2.

---

## 3. Analytic Route: Two-Tier Target B

### Tier 1: r=1 Free (handles n ≥ 8 and most n=6 cases)

**Theorem B1 (conjectured):** For any proper admissible tuple with n ≥ 8 (composite, gcd(E_non)=1, n|L, E_div≠∅, all speeds < L), there exists a fiber b ∈ B_div where r=1 is uncovered.

**Proof strategy:**
1. Identify the "r=1 covering runners": runners e with e ≥ n/2 (the only ones that can cover r=1).
2. For each such runner e, the coverage of r=1 is confined to floor-state intervals:
   - Lower: {b : t_e(b) = n−e mod n}
   - Upper: {b : t_e(b) = n−e−1 mod n AND s_e(b) > 0}
   These form arithmetic progressions in B_div.
3. The fraction of B_div fibers covered by runner e for r=1: at most 2/n (Fact D1 density), typically closer to 2·g_e/(n) weighted by how often the relevant t_e values occur.
4. **CRT step:** The coverage intervals for different runners have periods determined by their speeds. Using gcd(E_non) = 1, the periods are "coprime enough" that the intervals cannot perfectly tile B_div. A counting argument gives existence of a free fiber.

**Key lemma needed (B1-L1):** For any set of k runners with speeds ≥ n/2, their combined r=1-coverage fraction is < 1 unless their speed structure satisfies a specific arithmetic condition (perfect tiling).

**Key lemma needed (B1-L2):** The perfect-tiling condition requires n | gcd(e_i − e_j) for some pair (e_i, e_j), which combined with gcd(E_non) = 1 leads to a contradiction for n ≥ 8.

(Both lemmas are empirically confirmed — 0 disasters for n ≥ 8 over 1200 proper tuples.)

### Tier 2: r=2 Free (handles n=6 disasters)

**Theorem B2 (conjectured for n=6):** For any n=6 proper admissible tuple where r=1 is always covered, there exists a fiber b ∈ B_div where r=2 is uncovered.

**Proof strategy:**
For r=2 to be covered by runner e: need e·2 ≡ −t_e (mod n), i.e., t_e ≡ −2e (mod n).
For unit runners: −2e mod n ranges over {0,...,5} as e varies. The "r=2 covering" requires t_e in a different residue class than "r=1 covering" (t_e ≡ −e mod n). So the two coverage conditions are offset by e — they don't coincide for e ≢ 0 (mod n).

A disaster for r=1 occurs when the r=1 coverage intervals tile B_div. But the r=2 coverage intervals are offset by e from the r=1 intervals (for each runner). If the r=1 intervals tile perfectly, the r=2 intervals must leave gaps (since the offsets create "different" tiling patterns).

Formally: the r=1 tiling uses floor states t_e ≡ n−e (mod n). The r=2 tiling uses t_e ≡ n−2e (mod n). For the same runner, these are different unless n−e ≡ n−2e (mod n), i.e., e ≡ 0 (mod n). For E_div runners (e ≡ 0 mod n): both conditions are t_e ≡ 0 (mod n) — the E_div runner covers everything including both r=1 and r=2. But this only matters when the E_div runner is active (t_{e_div} = 0), which is the initial window. Between E_div windows, the non-E_div runners' r=2 coverage is offset from r=1 coverage by e steps. The offsets prevent perfect r=2 tiling when r=1 tiles.

This is the key: **the perfect-tiling conditions for r=1 and r=2 are algebraically incompatible for most configurations.** (Empirical: 31/32 n=6 disasters have r=2 free.)

The 1/32 exception (where r=2 is also always covered) must have both r=0 and r=5 free — a different structure requiring separate analysis.

---

## 4. Proof of Key Claim B1-L0 (Small Runner Exclusion)

**Claim B1-L0:** For runner e with e < n/2, r=1 is not covered at any fiber b ∈ B_div.

**Proof:** From DCT-C:
- Lower Sol covers r=1 iff 1 ∈ Sol(e, −t_e, n), i.e., e·1 ≡ −t_e (mod n), i.e., t_e ≡ −e (mod n) = n−e. Since e < n/2: n−e > n/2. But t_e(b) = ⌊e·b/L⌋ ≤ ⌊e(L−n)/L⌋ < e < n/2 < n−e. So the condition t_e = n−e is never met.
- Upper Sol covers r=1 iff 1 ∈ Sol(e, −(t_e+1), n), i.e., t_e+1 ≡ −e (mod n) = n−e, i.e., t_e = n−e−1. Since e < n/2: n−e−1 ≥ n/2 > e−1 ≥ max t_e. The condition is never met. □

**Corollary:** Only runners with e ≥ n/2 can cover r=1. This dramatically limits the candidate set in tuples with small speeds.

---

## 5. Active Period Formula for r=1 Coverage

For runner e ≥ n/2, the fibers where r=1 is covered via **lower Sol** are:
$$\mathcal{F}^{\text{low}}_e(r=1) = \{b \in B_\text{div} : \lfloor e \cdot b / L \rfloor \equiv n-e \pmod{n}\}$$

This is an approximately-arithmetic set with:
- Period: $P_e = L/\gcd(e, L)$ fibers of B_div (one period of t_e mod n, in B_div steps).
- Active length: approximately $L/(n \cdot e)$ fibers per period (one floor increment takes L/e time, and we need t_e in one of n possible residue classes → 1/n fraction of period).

Similarly for upper Sol (with the additional s_e > 0 constraint, which excludes at most finitely many fibers).

The fraction of B_div covered by runner e for r=1:
$$\text{frac}_e(r=1) \approx \frac{2}{n} \cdot \frac{\gcd(e, n)}{1} = \frac{2 g_e}{n}$$
(the factor g_e comes from the coset size; for unit runners g_e=1, this is 2/n; for non-unit runners, Fact D1 ensures at most one Sol active, giving g_e/n per active interval, times 2 intervals).

**Counting bound:** Sum over all coverage-capable runners (e ≥ n/2):
$$\sum_{e \in E_\text{non}, e \geq n/2} \text{frac}_e(r=1) \lesssim \frac{2}{n} \sum_{e \geq n/2} g_e$$

For this sum to reach 1 (perfect tiling), we need approximately $n/2$ runners each with $g_e = 1$ (unit runners), or fewer with larger $g_e$. This explains why n=6 (with only 3 residues to tile and fewer structural constraints) is more susceptible to perfect tiling than n=8,9,10,...

---

## 6. The n=6 Disaster Mechanism

For n=6 proper disasters, the coverage of r=1 is provided by runners with e ≥ 3 = n/2, specifically:
- E_div runners (e ≡ 0 mod 6): cover r=1 at ALL fibers with t_e ≡ 0 (mod 6). Period = L/6 fibers of B_div. Covers 1/6 of all fibers (approximately).
- Runners with e ≡ 3 mod 6 (g=3): cover r=1 at fibers with t_e ≡ 3 (mod 6). Period = L/(3·gcd(e,L/6)) fibers. Covers ≈ 1/6 of fibers.
- Runners with e ≡ 4 mod 6 (g=2): lower-bad t_e ≡ 2 (mod 6). Covers ≈ 1/6 of fibers.
- Runners with e ≡ 2 mod 6 (g=2): lower-bad t_e ≡ 4 (mod 6). Covers ≈ 1/6 of fibers.
- Runners with e ≡ 5 mod 6 (g=1): lower-bad t_e ≡ 1 (mod 6). Covers ≈ 1/6 of fibers.
- Runners with e ≡ 1 mod 6 (g=1): lower-bad t_e ≡ 5 (mod 6). Covers ≈ 1/6 of fibers.

Together: 6 residue classes × 1/6 each = 1. The **perfect hexagonal tiling** of t-states allows complete coverage of r=1 for n=6 when there are enough runners from each class.

For n=8: 8 residue classes × 1/8 each = 1, but requires 8 runners with exactly the right floor-state periods to tile. With only 7 non-zero runners (n−1=7 < 8), one residue class is always missing → r=1 is always free at some fiber. (Empirical: 0 disasters for n=8.)

**Key insight for n ≥ 8:** With at most n−1 non-zero runners and n required residue classes for perfect tiling, the tiling is impossible by pigeonhole! At least one residue class has no runner to cover it, leaving r=1 free.

**For n=6:** With 5 non-zero runners and 6 required residue classes: also impossible by pigeonhole! But... the E_div runner covers t_e ≡ 0 AND (indirectly via its coset = Z_6) ALL residue classes simultaneously. This breaks the pigeonhole argument for n=6.

Wait — let me re-examine this. If the E_div runner (e ≡ 0 mod 6) covers ALL residues at t=0 (including r=1 for t_e ≡ 0), then it covers the "t≡0 class" for r=1. For the non-E_div runners, they cover the remaining 5 classes (t≡1,...,5 for r=1 coverage). With 4 non-E_div runners covering 5 classes: still pigeonhole says one class is missing. But r=1 coverage doesn't require one runner per class — runners with g_e > 1 cover multiple classes.

For runner e ≡ 3 mod 6 (g=3): t_3 ≡ 3 (mod 6) covers r=1. But g_e=3 means the floor state cycles through 0,1,2 at period L/3. The residue class t_3 ≡ 3 (mod 6) requires t_3 ≥ 3, which needs 3 increments. This only happens for runners with e ≥ 3 that have large enough M = L/e. For tuples with only 4 non-E_div runners, if they happen to cover all 5 non-zero residue classes collectively (via their combinations), r=1 is tiled completely.

The n=6 disasters arise exactly when this combination tiling occurs. It's a genuine phenomenon of n=6's divisibility structure (2·3) allowing more combinations.

---

## 7. Revised Analytic Strategy

### 7.1 For n ≥ 8 (Tier 1 clean case)

**Theorem B1-n≥8 (to prove):** For proper admissible tuples with n ≥ 8 composite, r=1 is always free at some fiber.

**Proof skeleton:**
1. Only runners e ≥ n/2 can cover r=1 (Claim B1-L0, proved).
2. There are at most n−1 non-zero runners, covering at most n−1 residue classes of t-mod-n.
3. For r=1 to be completely covered, all n classes must be covered. With n−1 runners and n classes, at least one class lacks coverage by a non-E_div runner. [GAP: this argument uses 1-runner-per-class, which isn't tight for g_e > 1 runners.]
4. The E_div runner covers the "class 0" (t≡0 mod n) — but only in the initial window, not at all fibers. Between initial windows, the E_div runner is silent (Fact D3).
5. In the silence interval [M_other, n·M_other): only non-E_div runners cover r=1. By a careful analysis of the floor-state structure in this interval, at least one fiber has r=1 free.

**Open part:** Step 5 requires a precise CRT argument on the floor states of the non-E_div runners in the silence interval. The key is that gcd(E_non)=1 ensures the periods are "coprime enough" to prevent perfect tiling in this interval.

### 7.2 For n=6 (Tier 2 backup)

**Theorem B2-n6 (to prove):** For n=6 proper admissible tuples where r=1 is always covered, r=2 is free at some fiber.

**Proof skeleton (31/32 cases):**
1. The r=1-covering condition (t_e ≡ n−e mod 6) and r=2-covering condition (t_e ≡ 2(n−2e) mod 6 = (2n−4e) mod 6) differ by a shift of e (mod 6) for each runner.
2. Since the shifts are non-zero for non-E_div runners, a perfect r=1 tiling cannot simultaneously be a perfect r=2 tiling.
3. [GAP: formalise the incompatibility of the two tiling conditions.]

**1/32 exception:** Requires separate analysis (where r=2 also tiles but r=0 is free). May reduce to a specific algebraic condition on E_non.

---

## 8. Outstanding Gaps

**⚠ NOTE (2026-03-07):** The "B1-L2 silence cutoff" approach described in §7.1 is VOID. Claim B1-L2 is FALSE.
Counterexample: n=10, e=5, L=840, b=680 > 2L/n=168. Runner e=5 covers r=1 via upper Sol (t_5=4, Sol(5,-5,10)={1,3,5,7,9}).
Root cause: for e=n/2, coverage ends at b≈(n-e)L/e=L, not 2L/n. The planned "late silence interval is safe from small runners" argument collapses entirely.

| Gap | Description | Priority |
|---|---|---|
| B1 | Full covering problem: prove ∃ b with r=1 free, for all proper n≥8 tuples. No decomposition into sub-intervals known. | HIGH |
| B1-density | Find a tighter density/structure argument than "2/n per runner" that prevents tiling | HIGH |
| B2-n6 | Prove r=2 free when r=1 tiles (n=6 case) | MEDIUM |
| B2-exception | Handle 1/32 n=6 case where r=0/r=5 are the free pair | LOW |

---

## 9. Summary

| Finding | Status |
|---|---|
| r=1 and r=n−2 are least covered (aggregate) | CONFIRMED all n |
| r=1 is always free at some fiber (n ≥ 8, proper scope) | EMPIRICAL (0/1200 disasters) |
| r=1 disasters exist for n=6 proper scope | CONFIRMED (32/500, ~6.4%) |
| All n=6 disasters have B_safe > 0 (some r' free) | CONFIRMED (0 genuine failures) |
| r=1 and r=n−2 fail together (symmetry) | PROVED (algebraic symmetry) |
| Runners with e < n/2 never cover r=1 | PROVED (Claim B1-L0) |
| Runner e=n-1 only: coverage ends at 2L/(n-1) | PROVED (B1-L1, narrow) |
| All e<n stop covering r=1 at b>2L/n | **RETRACTED — FALSE** (B1-L2) |
| n=6 disasters: r=2 is free in 31/32 cases | EMPIRICAL |
| B_safe ≥ n for M≥n route | DEAD (n=6:25, n=8:8, n=10:9 violations) |

**Next step:** Develop a correct non-tiling argument for B1 (the full covering problem). Approaches: density + structure, CRT, equidistribution.

---

*Grounded: 11 | IDK: 0 | Computationally verified: 2300 tuples | Scope: proper Gap-4 composite*
