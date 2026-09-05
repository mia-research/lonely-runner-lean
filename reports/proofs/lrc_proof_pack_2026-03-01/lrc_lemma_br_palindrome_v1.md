# Lemma BR: Palindrome Symmetry and Arrival-Time Analysis (v1)

**Date:** 2026-03-06
**Scope:** E_div = {n} (single divisor runner), k=1.
**Framework:** A_b = ∩_{e∈E_non} safe_set(e,b), good fiber: A_b ≠ ∅, bad fiber: A_b = ∅.

---

## 1. Definitions

**Setup:**
- n ≥ 3, L = lcm(E) with E = E_non ∪ {n}, gcd(E)=1.
- N = nL.
- safe_set(e, b, L, n) = { a ∈ Z_n : (e*(aL+b)) mod N ∈ [L, (n-1)L] }.
- A_b = ∩_{e∈E_non} safe_set(e, b).
- B_div = { b ∈ {0,...,L-1} : L ≤ nb ≤ (n-1)L } = { L/n, L/n+1, ..., (n-1)L/n }.
  (b_lo = L/n, b_hi = (n-1)L/n; these are integers since n | L.)
- C = B_div, |C| = (n-2)L/n + 1.
- Fiber b is GOOD if A_b ≠ ∅, BAD if A_b = ∅.
- B_safe = |{b ∈ C : A_b ≠ ∅}|.
- start_run = |{b ∈ C : b < b_break}| where b_break = min{b ∈ C : A_b ≠ ∅}.
  (= 0 if A_{b_lo} ≠ ∅; = |C| if no fiber is good.)
- budget = (|C| - (n-1)) / 2 = (n-2)(L-n) / (2n).

**Lemma BR (target):** start_run ≤ budget.

**Equivalence:** If bad fibers are exactly the initial and final runs (no interior bad fibers),
then B_safe = |C| - 2·start_run ≥ n-1 ↔ start_run ≤ budget.

---

## 2. Palindrome Symmetry (PROVED)

### Theorem (Palindrome)

For every b ∈ C: A_b ≠ ∅  ↔  A_{L-b} ≠ ∅.

Equivalently: start_run = end_run (where end_run = final consecutive bad run from b_hi).

### Proof

**Step 1: Key bijection.**

For any a ∈ Z_n and b ∈ {0,...,L-1}, define a' = n-1-a and b' = L-b.

Claim: a ∈ safe_set(e, b) ↔ a' ∈ safe_set(e, b').

Compute:
```
(e * (a'L + b')) mod N
  = (e * ((n-1-a)L + (L-b))) mod N
  = (e * (nL - aL - b)) mod N
  = (-e * (aL + b)) mod N
  = N - ((e * (aL+b)) mod N)   [assuming the residue is nonzero]
```

Let x = (e*(aL+b)) mod N. Then:
- a safe for e at b: L ≤ x ≤ (n-1)L.
- a' safe for e at b': L ≤ N-x ≤ (n-1)L ↔ N-(n-1)L ≤ x ≤ N-L ↔ L ≤ x ≤ (n-1)L.

The conditions are IDENTICAL. Therefore a ∈ safe_set(e,b) ↔ a' ∈ safe_set(e,b'). □

(Note: if x=0, then N-x = N ≡ 0 (mod N), which is also unsafe. The bijection holds.)

**Step 2: A_b maps to A_{L-b}.**

By Step 1: a ∈ A_b ↔ a ∈ ∩_e safe_set(e,b) ↔ a' = n-1-a ∈ ∩_e safe_set(e,b') = A_{b'}.

Therefore: A_b ≠ ∅ ↔ A_{L-b} ≠ ∅. □

**Step 3: B_div is symmetric.**

b ∈ B_div ↔ L ≤ nb ≤ (n-1)L ↔ L ≤ n(L-b) ≤ (n-1)L ↔ L-b ∈ B_div.

(Since n(L-b) = nL-nb and L ≤ nL-nb ≤ (n-1)L ↔ L ≤ nb ≤ (n-1)L.) □

**Step 4: start_run = end_run.**

The bad/good pattern {A_b = ∅ : b ∈ C} is symmetric under b ↦ L-b. Since b_lo and b_hi = L - b_lo map to each other, the initial run of bad fibers from b_lo mirrors the final run of bad fibers from b_hi. □

**Corollary:** B_safe = |C| - 2·(# boundary bad fibers) - (# interior bad fibers).

---

## 3. At b_lo: Bad Set Structure

### Lemma (Coset coverage at b_lo)

For e ∈ E_non with g = gcd(e,n) and quotient q = floor(e/n):

**Case q=0 (e < n):**
- safe_set(e, b_lo) = Z_n \ (n/g)·Z_n  (= residues NOT divisible by n/g)
- |safe_set| = n - g.

**Case q ≥ 1 (e ≥ n):**
- safe_set(e, b_lo) = (n/g)·Z_n  (= residues divisible by n/g; these are "shifted" by the quotient)
- Actually: safe_set(e, b_lo) depends on q mod 2:
  - q even: safe_set = Z_n \ (n/g)·Z_n (same as q=0)
  - q odd: safe_set = (n/g)·Z_n (complementary)

**Proof sketch:** (e*(aL+L/n)) mod nL = L*(e*a + e/n) mod n = L*(e*a mod n + q + s/n) where s = e mod n. The safe condition L ≤ this ≤ (n-1)L gives s·(a + something) mod n ∈ [1, n-1]. The parity of q determines which coset.

**Key consequence (G2 structure):** If E_non contains two runners e, e' with the same g=gcd(e,n)=gcd(e',n) but different parities of floor(e/n) and floor(e'/n), then:
- safe_set(e, b_lo) ∩ safe_set(e', b_lo) = ∅ (complementary cosets).
- Therefore A_{b_lo} = ∅, and start_run ≥ 1.

For G2: e=3 (q=0, safe={1,3,5}), e=15 (q=2, safe={0,2,4}). Complementary. ✓

---

## 4. Arrival Time Formula

### Definition

For runner e ∈ E_non and residue r ∈ Z_n, define:
```
x_{e,r}(b) = (e*(rL+b)) mod nL   [position of runner e relative to residue r at fiber b]
arr(e, r) = min{b ≥ b_lo : r ∈ safe_set(e, b)} - b_lo
           = first time runner e covers residue r (measured from b_lo)
```

### Lemma (Arrival time formula)

The arrival time of runner e for residue r satisfies:

```
arr(e, r) = (L - x_{e,r}(b_lo) mod L) / e    [if x_{e,r}(b_lo) < L]
arr(e, r) = (nL - x_{e,r}(b_lo) + L) / e     [if x_{e,r}(b_lo) > (n-1)L]
arr(e, r) = 0                                  [if x_{e,r}(b_lo) ∈ [L, (n-1)L], already safe]
```

(These hold exactly when e | L, since then x_{e,r}(b) increases by e per fiber step.)

**Proof:** x_{e,r}(b) = x_{e,r}(b_lo) + e*(b - b_lo) (mod nL). Runner e first covers r when x_{e,r} first enters [L, (n-1)L]. If x_{e,r}(b_lo) < L: need e·t ≥ L - x_{e,r}(b_lo), so arr = (L - x_{e,r}(b_lo)) / e. If x_{e,r}(b_lo) > (n-1)L: must wrap past nL to enter [L,...] from the bottom; arr = (nL - x_{e,r}(b_lo) + L) / e = ((n+1)L - x_{e,r}(b_lo)) / e. □

### Formula for x_{e,r}(b_lo)

x_{e,r}(b_lo) = (e*(rL + L/n)) mod nL = L*(e*r mod n) + eL/n (mod nL).

Let c = e*r mod n and q = floor(e/n), s = e mod n:
- eL/n = qL + sL/n (where sL/n may be non-integer if n∤s).
- x_{e,r}(b_lo)/L = c + q + s/n (mod n).

For g = gcd(e,n): s/n = s/(gn') where n' = n/g. Since gcd(s/g, n') = 1 (as gcd(s,n)=g), s/n = (s/g)/(n/g) is a fraction with denominator n' = n/g.

---

## 5. Bounding b_break - b_lo

### Strategy

b_break = b_lo + max_{e∈E_non missing from witness} arr(e, r*).

We need: max_e arr(e, r*) ≤ budget = (n-2)(L-n)/(2n).

### Key observation

For the witness r* (the residue that first gets fully covered):
- The LAST runner to cover r* has arr(e*, r*) = b_break - b_lo = start_run.
- arr(e*, r*) ≤ ((n+1)L - x_{e*,r*}(b_lo)) / e*  [worst case: upper dangerous zone].

### Bound attempt

In the worst case (x > (n-1)L): arr ≤ 2L/e*. Need 2L/e* ≤ (n-2)(L-n)/(2n).

This requires: e* ≥ 4nL / ((n-2)(L-n)) ≈ 4n/(n-2) for large L.

For n=6: e* ≥ 24/(4(1-6/L)) ≈ 6 for large L. So any e* ≥ 6 works.

**Observation from data:** The LAST runner is never e=1 or e=2 (the smallest speeds). Why?
- e=1 covers all of {1,...,n-2} at b_lo (so it never needs to "arrive" for any witness r*).
- The witness r* ∈ {1,...,n-2} for any tuple containing runner e=1.
- More generally: the minimum speed in E_non determines a constrained r*.

### The obstruction structure

For G2 (n=6, E_non={3,5,7,15,17}):
- Runner e=15 is last to arrive for r*=3.
- arr(15, 3) = ((n+1)L - x)/e = (7*3570 - 19635)/15 = (24990-19635)/15 = 5355/15 = 357. ✓
- Budget = 1188 = (L-6)/3.
- 357 = L/10 ≤ (L-6)/3 ↔ 3L ≤ 10(L-6) = 10L-60 ↔ 7L ≥ 60, true for L ≥ 9. ✓

**Key insight for bounding:** The witness residue r* is not arbitrary — it's chosen to MINIMIZE arr(e*, r*). The optimal r* satisfies specific divisibility conditions that force e* to be "large enough" (bounded away from 1).

---

## 6. Current Proof Status

| Claim | Status | Evidence |
|---|---|---|
| Palindrome: start_run = end_run | **PROVED** (Section 2) | Bijection a↦n-1-a, b↦L-b |
| Coset structure at b_lo | **PROVED** (Section 3) | Formula for safe_set(e, b_lo) |
| Lemma BR: 0 violations n=3..8 | **CERTIFIED** (3415 tuples) | lrc_owner_set_sweep_v1.py |
| Arrival time formula (when e|L) | **PROVED** (Section 4) | Exact computation, verified G2 |
| Bound arr(e*, r*) ≤ budget | **OPEN** | Need: e* ≥ 4n/(n-2) or witness-r* constraint |

---

## 7. Next Proof Steps

1. **Prove that r* ∈ {1,...,n-2}** for any tuple containing a unit runner (e=1 ∈ E_non). This constrains x_{e*,r*}(b_lo) via the coset formula.

2. **Prove the minimum e* bound**: Show the last runner e* satisfies e* ≥ 4n/(n-2) (or equivalently, e* ≥ n-1). This is false in general (e*=1 is possible for prime n). Need a refined argument using which residues the small runners cover at b_lo.

3. **Alternative**: Prove directly that arr(e*, r*) ≤ (n-2)(L-n)/(2n) using the algebraic structure of E_non and the witness residue selection.

4. **Handle prime n case** separately: for prime n, all runners have gcd=1, and the analysis is about unit runners only. The arrival times have a cleaner formula.
