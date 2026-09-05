# LRC Coset-Confinement Session — Handoff

**Date:** 2026-03-07
**Session type:** DCT verification + Target B structure analysis
**Protocol:** Math Research Protocol v1.0

---

## 1. What This Session Established

### 1.1 DCT-C: The Corrected Dynamic Coset Theorem

**Theorem DCT-C (PROVED — 0 violations, ~849k checks):**

For runner `e` with `g_e = gcd(e,n)`, fiber `b ∈ B_div`, floor state `t_e(b) = ⌊e·b/L⌋`, fractional remainder `s_e(b) = (e·b) mod L`:

```
B_e(b) = Sol(e, −t_e, n)  ∪  (Sol(e, −(t_e+1), n)  if s_e > 0  else  ∅)
```

The `s_e > 0` guard (the **z=0 condition**) was missing from the previous session's DCT. Root cause: at a z=0 event, `x = (n−1)·L` exactly — NOT strictly greater than `(n−1)·L` — so the upper zone is inactive. The corrected formula is verified by `lrc_coset_dynamic_v1.py` (corrected).

**Canonical derivation:** Let `j = (e·a + t_e) mod n`. Then `x = j·L + s_e`. Lower bad: `j=0`, always. Upper bad: `j=n−1` AND `s_e > 0`. □

### 1.2 Fact D1 — Non-Unit Sparsity: PROVED

For non-unit runner (`g_e > 1`), the lower and upper Sols are **never simultaneously non-empty**:
- Lower non-empty: `g_e | t_e`
- Upper non-empty: `g_e | (t_e+1)` AND `s_e > 0`
- Both: `g_e | t_e` AND `g_e | (t_e+1)` → `g_e | 1` → `g_e = 1`. Contradiction. □

**Result:** `B_e(b)` is at most ONE coset of `H_{g_e}` (size `g_e`) or ∅ at every fiber.
**Verified:** 0 violations across all 1200 tuples, all n ∈ {6,8,9,10,12,15}.

### 1.3 LBL Status

LBL ("first fiber is always safe") is **FALSE** for composite n with E_div ≠ ∅. At `b=0`, any E_div runner (speed `kn`) has `t_e=0` and `Sol(kn,0,n)=Z_n` (covering all residues). Every even-n tuple has `D(0)=0` (100% first-obstruction at `j=0`). **This was the correct [P1] assessment from the plan.**

### 1.4 Residue Coverage Finding: The {r=1, r=n−2} Pair

Across all n tested, `r=1` and `r=n−2` are the **consistently least covered** pair, by exact symmetry (`a ↦ n−1−a`). Free fraction: 11–29% of fibers. This is the Target B candidate.

**Algebraic explanation (proved):**
- Runners with `e < n/2` **never** cover `r=1` (Claim B1-L0, see §2).
- At `t_e=0`, only E_div runners (covers `Z_n`) and unit runners with `e ≡ n−1 (mod n)` (via upper Sol) cover `r=1`.

---

## 2. Proved Analytic Claims (This Session)

**Claim B1-L0 (Small Runner Exclusion, PROVED):**
For runner `e` with `e < n/2` and any fiber `b ∈ B_div`: `r=1 ∉ B_e(b)`.

*Proof:* Via DCT-C, r=1 coverage requires `t_e = n−e` (lower Sol) or `t_e = n−e−1` (upper Sol). Both values satisfy `n−e > n/2` and `n−e−1 ≥ n/2−1 > e−1 ≥ max t_e(b)` when `e < n/2`. Both conditions are unreachable. □

**Claim B1-L1 (Runner e=n−1 specific, PROVED for e=n−1):**
For `e = n−1`, r=1 coverage is confined to `b ∈ [0, 2L/(n−1))`. No coverage for `b > 2L/(n−1)`.

*Proof:* r=1 coverage via lower Sol requires `t_{n-1} ≡ 1 (mod n)`, i.e., `t_{n-1}=1` (since `t_{n-1} < n−1`), occurring on `b ∈ [L/(n-1), 2L/(n-1))`. Via upper Sol requires `t_{n-1}=0`, occurring on `b ∈ (0, L/(n-1))`. Combined: coverage is confined to `b ∈ (0, 2L/(n-1))`. Beyond this, `t_{n-1} ≥ 2` and the next lower-bad state `t_{n-1}=n+1` requires `b ≈ (n+1)L/(n-1) > L`. □

**⚠ RETRACTED — B1-L2 is FALSE:**
The session document previously claimed "For `b > 2L/n` in the silence interval: no runner with `e < n` covers `r=1`." This is **FALSE**.

*Counterexample:* `n=10`, `e=5`, `L=840`, `b=680`:
- `2L/n = 168`, so `b=680 > 168`. ✓
- `t_5(680) = ⌊5·680/840⌋ = 4`, `s_5(680) = 40 > 0`.
- Upper Sol: `Sol(5, −5, 10)`. `gcd(5,10)=5`, `5|5`. Solution set `{1,3,5,7,9}`. **r=1 is covered.**

*Diagnosis:* The proof claimed coverage ends at `b > (n−e+1)L/e`. For `e=n/2=5`, `n=10`: this gives `(10−5+1)·840/5 = 1008 > L = 840` — coverage extends to the end of the period. The key error was the false inequality `(n−e+1)L/e ≤ (n/2+1)L/(n/2) ≈ 2L/n`, which breaks down badly for `e` near `n/2`.

**Correct coverage formula for runner e ∈ [n/2, n):** r=1 coverage ends at approximately `b ≈ (n−e)·L/e` (upper Sol) and `(n−e+1)·L/e` (lower Sol). For `e = n/2`: these are `L` and `(1+2/n)L > L` — coverage persists until nearly the end of the period. There is NO simple "2L/n" cutoff for all small runners.

---

## 3. Key Empirical Findings

### 3.1 r=1 Disaster Analysis (proper tuples, all speeds < L)

| n | Proper tuples | r=1 always-covered | Genuine LRC failures |
|---|---|---|---|
| 6 | 500 | 32 (6.4%) | 0 |
| 8 | 200 | 0 | 0 |
| 9 | 300 | 0 | 0 |
| 10 | 200 | 0 | 0 |
| 12 | 200 | 0 | 0 |
| 15 | 300 | 0 | 0 |

For n≥8: **r=1 is ALWAYS free at some fiber.** Zero disasters, zero genuine LRC failures.

For n=6 disasters: r=1 AND r=4 (=n−2) are always covered together (perfect symmetry). r=2 is free in 31/32, r=0 in 29/32.

### 3.2 Silence Interval Analysis

| n | r=1 free in silence | Notes |
|---|---|---|
| 6 | 162/200 (81%) | 38 silence-covered; 7 full-period disasters |
| 8 | 188/200 (94%) | 12 silence-covered; 0 full-period disasters |
| 10 | 200/200 (100%) | Always free in silence ✓ |
| 12 | 200/200 (100%) | Always free in silence ✓ |

**For n=10,12:** r=1 is always free in the E_div silence interval `[L/n, L)`.

**For n=8:** r=1 always free in FULL period (0 disasters), but in 12/200 cases it's covered within the silence interval — it must be free OUTSIDE the silence (before `b=L/n` or after `b=L`).

---

## 4. The B1 Proof Structure

### 4.1 Status: Open Covering Problem

**⚠ The proof sketch in this section was based on the retracted B1-L2. It is VOID.**

The correct open problem is: for the full B_div period, prove there always exists some fiber `b` where no runner covers `r=1`. There is no known sub-interval decomposition that simplifies this — in particular, runners with `e ≈ n/2` can cover `r=1` at fibers arbitrarily late in the period. The problem must be treated as a covering problem over ALL of B_div simultaneously.

**What is known (empirical, n ≥ 8):**
- 0 disasters in 1200 proper tuples (n ∈ {8,9,10,12,15}).
- 200/200 free in the silence interval for n=10,12 (empirical, no analytic proof).
- 0/200 full-period disasters for n=8, but the silence interval alone is not sufficient (12/200 cases are silence-covered and free elsewhere — where "elsewhere" is not yet understood).

**What is needed (analytic):**
Find a covering argument — possibly density-based, CRT, or equidistribution — that guarantees a free fiber exists somewhere in `[0, L)` for all proper admissible tuples with n ≥ 8. The decomposition into silence vs. initial window is empirically useful but the boundary between runner-classes covering r=1 is **not at 2L/n** as was wrongly claimed.

### 4.3 For n=6 (Tier 2)

When r=1 is always covered (32/500 proper tuples): r=2 is free in 31/32. Mechanism: the r=1 perfect tiling uses floor states T₁ = {t_e ≡ n−e (mod 6)} for each runner; the r=2 tiling uses T₂ = {t_e ≡ n−2e (mod 6)}; these differ by `e (mod 6)` for each runner, preventing simultaneous perfect tiling in most cases.

**[STATUS: Tier 2 for n=6 is OPEN — needs algebraic proof of T₁ vs T₂ incompatibility.]**

---

## 5. Files Created This Session

| File | Contents |
|---|---|
| `lrc_coset_dynamic_v1.py` (corrected) | DCT verification script, corrected with `s_e` guard |
| `lrc_coset_dynamic_v1.md` | Full findings: DCT-C proved, Fact D1 proved, obstruction stats, residue coverage, route selection |
| `lrc_target_b_development_v1.md` | Two-tier Target B proof outline, key claims, open gaps |
| `LRC_Coset_Session_Handoff.md` | This document |

---

## 6. What Remains Open

### Primary: B1 (r=1 Free — Full Covering Problem)

**[GAP: B1]** For proper admissible tuples with n ≥ 8 composite, prove there exists `b ∈ B_div` where no runner covers `r=1`.

This is the central open gap. There is no proved decomposition into sub-intervals. The failure of B1-L2 means runners with `e ≈ n/2` can cover `r=1` at fibers late in the period, removing the planned "after 2L/n, only large runners remain" simplification.

**Potential approaches:**
- **Density argument:** Each runner covers r=1 for at most `2/n` of all M fibers (from Fact D1 density bound). With n−1 runners and `2/n` density each, total coverage ≤ `2(n−1)/n < 2`. This is weaker than 1 (needed for non-tiling), so density alone is insufficient. Need a DISJOINTNESS or STRUCTURE argument.
- **CRT / three-distance theorem:** The r=1 coverage set for runner `e` is approximately periodic with step `nM/gcd(e,n)`. By three-distance theorem on the sequence `{e·j/M mod 1 : j ∈ Z_M}`, at most 3 gap lengths exist. CRT gives simultaneous gap when gcd of the periods satisfies certain conditions.
- **Equidistribution:** For large L, the r=1 coverage intervals for different runners are equidistributed and cannot align perfectly. Needs quantitative form.

### Secondary: n=6 Tier 2

When r=1 is always covered (32/500 proper n=6 tuples): r=2 is free in 31/32. The algebraic mechanism (T₁ vs T₂ incompatibility) is unproved. The 1/32 exception (where r=2 also tiles, but r=0 or r=5 is free) needs separate analysis.

### Note: B_safe ≥ n Route Dead

The script reports `Bsafe<n (M≥n)` violations even for tuples with M ≥ n: n=6: 25, n=8: 8, n=10: 9, n=9: 1. Any approach requiring B_safe ≥ n as a theorem is **REFUTED** by these data.

---

## 7. Notation in Use

| Symbol | Meaning |
|---|---|
| DCT-C | Dynamic Coset Theorem (corrected) |
| H_{g_e} | Subgroup of order g_e in Z_n: {0, n/g_e, 2n/g_e, ...} |
| Sol(e,k,n) | {a ∈ Z_n : ea ≡ k (mod n)}, empty iff g_e ∤ k |
| t_e(b) | ⌊e·b/L⌋ — floor state of runner e at fiber b |
| s_e(b) | (e·b) mod L — fractional remainder |
| M_other | L/e_div — period length for E_div runner |
| Silence interval | [M_other, n·M_other) — where E_div covers ∅ |
| B1-L0 | Small runner exclusion (proved): e<n/2 never covers r=1 |
| B1-L1 | Runner e=n−1 only: coverage confined to b<2L/(n-1) (proved, narrow) |
| B1-L2 | ~~All e<n stop at b>2L/n~~ — **RETRACTED, FALSE** (CE: n=10,e=5,b=680) |
| B1 | Full covering problem — r=1 always free at some fiber (open) |

---

*Grounded: 14 | IDK: 0 | Searches: 0 | Flagged: 0 | Script-verified: 3200 tuples | DCT violations: 0 | D1 violations: 0*
