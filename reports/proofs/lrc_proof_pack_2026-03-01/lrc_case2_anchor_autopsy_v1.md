# Case-2 Anchor Autopsy (v1)

## Overview
Following the C2-main(C) disproof (n=12 counterexample), this document investigates
the anchor approach and canonical case structure to identify viable proof routes.

---

## 1. B_safe confirmed for n=12 counterexample

Tuple: `n=12`, `E=(12,10,5,4,7,3,6,1,8,3,11)`
- `L=9240`, `N=110880`, `E_div=[12]`, `|E_non|=10`
- `|B_div|=7701` (confirmed matches autopsy)
- **`|B_safe|=3782`** — this is `3782 >> n-1=11` ✓
- `C_bad=3919` (large, but irrelevant to B_safe ≥ n-1)

**Conclusion:** B_safe ≥ n-1 holds trivially for this tuple (the aggregate bound C2-main(C)
fails, but the target B_safe ≥ n-1 is satisfied with massive margin).

---

## 2. Anchor analysis for n=12 counterexample

Anchor fibers: `b_j = jL/n = j*770` for `j=1,...,11`.

**All 11 anchors are in B_div** (since E_div has only one runner with f=1, so
no anchor b_j = j*770 is excluded by divisible constraint for j=1,...,11). ✓

**But only 6 of 11 anchors are in B_safe:**

| j | b_j | |A_{b_j}| | In B_safe? |
|---:|---:|---:|---:|
| 1 | 770 | 0 | ✗ BAD |
| 2 | 1540 | 0 | ✗ BAD |
| 3 | 2310 | 2 | ✓ |
| 4 | 3080 | 4 | ✓ |
| 5 | 3850 | 1 | ✓ |
| 6 | 4620 | 0 | ✗ BAD |
| 7 | 5390 | 1 | ✓ |
| 8 | 6160 | 4 | ✓ |
| 9 | 6930 | 2 | ✓ |
| 10 | 7700 | 0 | ✗ BAD |
| 11 | 8470 | 0 | ✗ BAD |

**Conclusion:** The naive anchor approach (all n-1 anchors are in B_safe) fails for this tuple.
However, B_safe=3782 >> n-1=11, so the target is satisfied through OTHER fibers.

### Why some anchors are bad
- j=1: b=770, k=a*9240+770. For a=0: e*770 < L=9240 for ALL e≤11 (max=11*770=8470<9240).
  Every non-divisible runner makes a=0 dangerous simultaneously.
- j=6: b=4620=L/2. Each a gets exactly ONE bad runner (q_a=1 for all a), forming a
  perfect 1-cover of Z_12 by the 10 non-divisible runners.
- j=11: mirror of j=1 (a=11 has e*k mod nL just above (n-1)L for small e).

---

## 3. Canonical case: C_bad = 0 always

For `E = (1,...,1,n)` with `L=n`:

| n | L | B_div | B_safe | C_bad |
|---:|---:|---:|---:|---:|
| 3 | 3 | 2 | 2 | 0 |
| 4 | 4 | 3 | 3 | 0 |
| 5 | 5 | 4 | 4 | 0 |
| 6 | 6 | 5 | 5 | 0 |
| 7 | 7 | 6 | 6 | 0 |

**Direct proof for canonical case:**
- `B_div = {1,...,n-1}` (n-1 consecutive integers)
- For each `b ∈ {1,...,n-1}`, each speed-1 runner gives `B_1(b) = {0, n-1}` only
  (since `1*(an+b) ∈ [n, n(n-1)]` iff `1 ≤ a ≤ n-2`)
- All n-2 copies of speed-1 give the SAME bad set `{0, n-1}`
- Hence `A_b = {1,...,n-2} ≠ ∅` for every b ∈ B_div
- `C_bad = 0`, `B_safe = n-1`. ✓

**This is the tight case** where `min B_safe = n-1` is achieved.

---

## 4. Non-canonical cases: large C_bad but B_safe >> n-1

Example: `n=5`, `E=(1,3,4,5)`, `L=60`:
- `B_div=37`, `B_safe=8`, `C_bad=29` (78% of fibers are bad!)
- But `B_safe=8 ≥ n-1=4` ✓ (φ(5)=4)

Example: `n=5`, `E=(2,3,4,5)`, `L=60`:
- `B_div=37`, `B_safe=37`, `C_bad=0` (no bad fibers)

Example: `n=12`, counterexample: `B_div=7701`, `B_safe=3782`, C_bad=3919 (~51% bad).

**Pattern:** Large L brings larger B_div; even if C_bad ≈ B_div/2, B_safe remains >> n-1.

---

## 5. Structural insight: when is B_safe exactly n-1?

From exhaustive scans (n=3..7), the minimum B_safe = n-1 is achieved ONLY when:
1. `L = n` (smallest possible Case-2 L value)
2. Single divisible speed `e_r = n` (f=1)
3. All other speeds divide n (so L=n forces E_non speeds to be 1)

This is the canonical case `E = (1,...,1,n)`. All other Case-2 tuples have larger B_safe.

---

## 6. Proof strategy implications

**Split into two regimes:**

### Regime 1: `B_div = n-1` (canonical tight case)
Proof: C_bad = 0 (all fibers safe). Direct proof via speed-1 runner analysis. ✓

### Regime 2: `B_div ≥ n` (non-tight cases)
Need: `B_safe = B_div - C_bad ≥ n-1`, i.e., `C_bad ≤ B_div - (n-1)`.

For large B_div (e.g., B_div=7701 for n=12), even C_bad ≈ B_div/2 leaves B_safe >> n-1.

**Key challenge:** The intermediate range where B_div is just slightly above n-1 (e.g., B_div = n or n+1). Need to show C_bad ≤ B_div - (n-1) in this range.

**Observation:** B_div = n can occur when L = n^2/(n-1) * something... actually for L=n (canonical) B_div=n-1; for L=2n with f=1, |B_div| = (n-2)*2 + 1 = 2n-3 ≥ n for n ≥ 4.

For any B_div ≥ n: we need at least n-1 safe fibers. By a counting argument, at least one anchor fiber must be safe in any case where all n-1 anchor fibers are in B_div. But we showed (n=12) that 5 anchors can be bad.

**Revised anchor strategy:** Not "all n-1 anchors safe" but rather "at least n-1 fibers overall safe." The ANCHOR PROOF works when:
- `|B_div| = n-1` (all fibers must be safe, proved by canonical case argument)
- `|B_div| >> n-1` (trivially many safe fibers exist)

The **critical gap** remains: `n ≤ B_div ≤ 2(n-1)` (intermediate regime). Need to show C_bad ≤ B_div - (n-1) in this range. Likely requires a more careful CRT-based analysis.

---

## 7. Key questions for next investigation

1. **What is the minimum B_div possible in Case-2 excluding the canonical L=n case?**
   I.e., what is the second-smallest possible B_div?

2. **For `B_div` just above n-1, can C_bad be close to B_div - (n-1)?**
   Exhaustive scan of tuples with L=2n, L=3n, etc.

3. **Is there a CRT-based argument showing that for any B_div ≥ n, at least n-1 fibers
   are safe?** This would close the intermediate regime.

---

## Artifacts
- Script: (inline Python in session)
- This document: `lrc_case2_anchor_autopsy_v1.md`
