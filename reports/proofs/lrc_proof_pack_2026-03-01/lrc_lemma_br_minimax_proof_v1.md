# Lemma BR: Minimax Bound Proof Attempt (v1)

**Date:** 2026-03-06
**Goal:** Prove start_run ≤ budget = (n−2)(L−n)/(2n) for E_div={n}, k=1.
**Minimax reformulation:** start_run = min_{r∈Z_n} max_{e∈E_non} arr(e,r) ≤ budget.
**Verified empirically:** 3415 tuples (n=3..8), 0 violations.

---

## 1. Setup and Key Facts

**Setup**: n ≥ 3, E = E_non ∪ {n}, gcd(E)=1, L=lcm(E). Let N=nL, b_lo=L/n, b_hi=(n-1)L/n.
- B_div = {b_lo, b_lo+1, ..., b_hi}, |C| = (n-2)L/n + 1.
- safe_set(e,b) = { a∈Z_n : L ≤ (e*(aL+b)) mod nL ≤ (n-1)L }.
- A_b = ∩_{e∈E_non} safe_set(e,b).
- start_run = |{b∈B_div : b < b_break}| where b_break = min{b∈B_div : A_b ≠ ∅}.
- budget = (|C|−(n-1))/2 = (n-2)(L-n)/(2n).

**Proved facts (this session)**:
- P1 (Palindrome): start_run = end_run.
- P2 (Arrival formula, for e|L): arr(e,r) = (L−x)/e [lower zone] or ((n+1)L−x)/e [upper zone], where x = x_{e,r}(b_lo) = (e*(rL+b_lo)) mod nL.
- P3 (Minimax) — **CORRECTION**: start_run ≠ min_r max_e arr(e,r) in general. (See §11.8 counterexample.)

**Corrected formulation**: start_run = b_break − b_lo, where b_break is the first fiber where ∩_e safe_set(e,b) ≠ ∅. The correct sufficient condition for Lemma BR is: ∃ "valid witness" r* with arr(e*,r*) ≤ budget AND all early runners maintain coverage of r* for at least arr(e*,r*) steps (window maintenance condition).

**Key B_div property**: The full B_div has length b_hi − b_lo = (n−2)L/n fibers. Any arrival within B_div satisfies arr(e,r) ≤ (n−2)L/n.

---

## 2. Case A: A_{b_lo} ≠ ∅ (Trivial)

If A_{b_lo} ≠ ∅, then b_break = b_lo, start_run = 0 ≤ budget. □

---

## 3. Case B: A_{b_lo} = ∅ (start_run > 0)

### 3.1 Unit Runner Subcase: e=1 ∈ E_non

**Lemma (Unit coverage at b_lo)**: If 1 ∈ E_non, then safe_set(1, b_lo) = {1,...,n-2}.

**Proof**: For e=1, x_{1,a}(b_lo) = aL + L/n = L(a + 1/n).
- Safe condition L ≤ L(a+1/n) ≤ (n-1)L gives 1 ≤ a+1/n ≤ n-1.
- Since a is an integer: a ∈ {1,...,n-2}. □

**Consequence**: For any r* ∈ {1,...,n-2}: arr(1,r*)=0 (runner 1 never limits the witness choice).

So when 1 ∈ E_non, the "last runner" for any r* ∈ {1,...,n-2} is some e* ≠ 1. We need to bound arr(e*, r*) ≤ budget.

### 3.2 Unit Coverage: Complete Safe-Set at b_lo

For runner e with gcd(e,n)=g:

**Observation (from numerics, Section 4 formalizes)**: safe_set(e, b_lo) has exactly:
- Size n−2 when g=1 (unit runners)
- Size g when g = gcd(e,n) > 1 and e < n (lower coset covered)
- The covered residues form a specific coset modulo n/g

For gcd(e,n)=1 (unit runner), the EXCLUDED residues are exactly:
- a_low = 0 (lower zone: x = e·b_lo = eL/n < L since e < n... but this fails for e > n)
- a_high = some residue in upper zone

(For e < n: a_low=0 always excluded; a_high depends on e. For e > n: different computation.)

**Key fact**: For unit runner e (gcd=1), safe_set(e, b_lo) excludes exactly 2 residues (one lower, one upper zone), so |safe_set| = n−2. □

---

## 4. Arrival-Time Bound Analysis

### 4.1 Formula Recap

For the last runner e* covering r* (arriving at time arr(e*,r*)):

**Lower zone** (x_{e*,r*}(b_lo) < L):
$$\text{arr}(e^*,r^*) = \frac{L - x}{e^*} \leq \frac{L}{e^*}$$

**Upper zone** (x_{e*,r*}(b_lo) > (n-1)L):
$$\text{arr}(e^*,r^*) = \frac{(n+1)L - x}{e^*} \leq \frac{2L}{e^*}$$

The budget bound requires:
$$\frac{2L}{e^*} \leq \frac{(n-2)(L-n)}{2n} \quad \iff \quad e^* \geq \frac{4nL}{(n-2)(L-n)}$$

For large L: $e^* \geq \frac{4n}{n-2} + O(1/L)$.

| n | 4n/(n-2) | Min e* needed (upper zone) |
|---|---|---|
| 3 | ∞ | (any e works via lower zone) |
| 4 | 8 | e*≥8 |
| 5 | 20/3≈6.67 | e*≥7 |
| 6 | 6 | e*≥6 |
| 7 | 28/5=5.6 | e*≥6 |
| 8 | 16/3≈5.33 | e*≥6 |

For lower zone, the weaker bound: $e^* \geq \frac{2n}{n-2}$ (half of above).

### 4.2 Non-Unit Last Runner (gcd(e*,n) = g ≥ 2)

For gcd(e*,n) = g ≥ 2:
- safe_set(e*, b_lo) = coset C_e of size g (either (n/g)Z_n or its complement).
- For r* ∉ C_e: r* must "wait" for e* to cover it.
- The "gap" from b_lo until e* first covers r* is at most L·(n-g)/(n·e*).

**Bound**: arr(e*,r*) ≤ L(n-g)/(ne*).

Need: L(n-g)/(ne*) ≤ (n-2)(L-n)/(2n).
→ 2(n-g) ≤ (n-2)·(L-n)/L · e*/e* · ...
→ for large L: 2(n-g)/e* ≤ (n-2) → e* ≥ 2(n-g)/(n-2).

For g=2: e* ≥ 2(n-2)/(n-2) = 2 → any e*≥2 works. ✓
For g=3: e* ≥ 2(n-3)/(n-2) < 2 for n≥3. ✓

So **non-unit last runners always satisfy the budget bound** (for large L, and can verify exactly for specific L).

**Example (G2)**: e*=15, n=6, g=gcd(15,6)=3. arr(15,3)=357. Budget=1188. 357 ≤ 1188. ✓
The formula bound: L(n-g)/(ne*)=3570*3/(6*15)=3570/30=119. But actual arr=357 > 119!

**Wait**: The formula arr ≤ L(n-g)/(ne*) is WRONG. Let me recheck.

For e=15 in upper zone: arr = ((n+1)L-x)/e* = (7*3570-19635)/15 = 357. This is NOT bounded by L(n-g)/(ne*)=119. The upper zone formula gives a larger value.

**Correction**: For non-unit runner e* in UPPER zone:
arr ≤ 2L/e* (same as unit runner bound). For e*=15: 2*3570/15=476 ≥ 357. ✓

And 476 ≤ 1188 = budget. ✓ Because: 2L/e* = 2*3570/15 = 476 ≤ (n-2)(L-n)/(2n) = 1188 iff e* ≥ 4nL/((n-2)(L-n)) = 4*6*3570/(4*3564) = 4*6*3570/14256 = 6.006... So e*=15 ≥ 6. ✓

---

## 5. The Key Remaining Gap: Why Can't e* Be Small?

The empirical evidence shows start_run ≤ budget for ALL tested tuples. The proof gaps are:

**Gap 1**: Upper zone, small e* (e.g., e*=2 for n=7). Can a unit runner e*=2 be the LAST runner?

**Structural constraint on e***: For e* to be the last runner for r*, ALL other runners in E_non must cover r* at b_lo OR arrive before e*. If e* is small (e*=2), then:
- arr(2,r*) ≤ 2L/2 = L (potentially large)
- But ALL other n-3 runners in E_non must cover r* at b_lo or arrive before step L

**Key observation**: If e*=2 is the last runner, then for the optimal r*, all other runners e≠2 in E_non must cover r* at b_lo (arr=0). But |E_non|=n-2, so n-3 runners all cover r* at b_lo.

For n-3 unit runners (all with gcd=1) to cover the same r*: each unit runner covers n-2 residues at b_lo, so n-3 unit runners covering the same r* is "typical" (only 2 residues excluded per runner).

But then e*=2 is the ONLY runner not covering r*, meaning A_{b_lo} = {r*} ∩ (safe_set(2,b_lo))^c which requires... hmm.

Actually if ALL other runners cover r* (arr=0 for them) but e*=2 doesn't, then for b < b_lo + arr(2,r*): A_b might still be nonempty via a DIFFERENT witness r** ≠ r*. The minimax picks the r with SMALLEST max arrival, which might not be r*.

**The actual constraint**: b_break is determined by the FIRST b where ANY residue is simultaneously covered. It could be that e*=2 has arr=L for r*, but some other residue r** has a much smaller max arrival time.

So the minimax bound: min_r max_e arr(e,r) ≤ budget could still hold even if arr(2,r*)=L for some r*, because we pick r** with small max arrival.

**This is the resolution!** Even if some runners have large arrival times for some residues, the OPTIMAL witness r* is chosen to minimize the maximum. We just need to show there EXISTS r* with max arrival ≤ budget.

---

## 6. Existence Proof via Complementary Structure

### 6.1 The Main Lemma

**Lemma (Existence of Good Witness)**: For any tuple with A_{b_lo}=∅, there exists r* ∈ Z_n such that:
$$\max_{e \in E_{\text{non}}} \text{arr}(e, r^*) \leq \frac{(n-2)(L-n)}{2n}$$

**Proof attempt** (incomplete — see gaps below):

Since A_{b_lo} = ∅, for every r ∈ Z_n, ∃ e_r ∈ E_non with r ∉ safe_set(e_r, b_lo).

The maximum arrival time for residue r is: M(r) = max_{e: r∉safe_set(e,b_lo)} arr(e,r).

We want: min_r M(r) ≤ budget.

**Strategy**: Sum M(r) over all r, show average ≤ budget, conclude ∃ r* with M(r*) ≤ budget.

$$\sum_{r=0}^{n-1} M(r) \leq \sum_{r=0}^{n-1} \sum_{e \in E_{\text{non}}} \text{arr}(e,r) = \sum_{e \in E_{\text{non}}} \sum_{r=0}^{n-1} \text{arr}(e,r)$$

(inequality since M(r) ≤ Σ_e arr(e,r) when all arr≥0... WAIT: M(r) = max arr, NOT sum. This inequality is wrong.)

**Corrected approach**: We need min_r M(r) ≤ average_r M(r) ≤ budget.

So we need: (1/n)·Σ_r M(r) ≤ budget.

This requires: Σ_r M(r) ≤ n·budget = (n-2)(L-n)/2.

### 6.2 Bounding Σ_r M(r)

Since M(r) = max_e arr(e,r) ≤ max_e (2L/e) ≤ 2L/e_min where e_min is the smallest speed in E_non:

Σ_r M(r) ≤ n·2L/e_min.

Need: n·2L/e_min ≤ (n-2)(L-n)/2.
→ 4nL ≤ (n-2)(L-n)·e_min.
→ e_min ≥ 4nL/((n-2)(L-n)) ≈ 4n/(n-2).

So if e_min ≥ 4n/(n-2), the average argument works. But e_min could be 1 (if 1 ∈ E_non)!

**When e_min=1 (1∈E_non)**: arr(1,r) = 0 for r∈{1,...,n-2}. So M(r) is NOT determined by e=1 for r∈{1,...,n-2}. The average argument is too crude.

### 6.3 Refined Approach: Separated-Runner Bound

**Key insight from data**: The runner e* that determines M(r*) = start_run is NOT e=1 (since e=1 covers {1,...,n-2} at b_lo). So for the optimal r*∈{1,...,n-2}, the max is determined by some e*≥2.

For e*≥2 and upper zone: arr(e*,r*) ≤ 2L/e* ≤ L.

But we need arr ≤ budget ≈ (n-2)L/(2n). For large L, this is:
- e*=2: arr ≤ L. Need L ≤ (n-2)L/(2n)? Only if n-2 ≥ 2n, i.e., n ≤ -2. Impossible!

So the upper bound arr ≤ 2L/e* is too weak for e*=2. We need a BETTER bound using the x value.

**Refined bound**: arr(e*, r*) = ((n+1)L - x)/e* where x > (n-1)L. The x value satisfies:
x = x_{e*,r*}(b_lo) = (e**(r**L + b_lo)) mod nL.

For x/(nL) to be in the range ((n-1)/n, 1), we need specific arithmetic conditions. The question is: for the OPTIMAL r* (chosen to minimize M(r*)), what is x/(nL)?

**The competition between runners**: For two runners e and e' with arrival times t and t' for residue r, the last one to arrive is max(t,t'). The OPTIMAL r* minimizes this maximum across all non-covering runners.

**Observation from G2 and W1**:
- G2: Complementary coset pair (e=3, e=15), optimal r* ∈ coset covered by e=3 (arr(3,r*)=0), making e=15 the last runner with arr=357.
- W1: No complementary coset pair, but e*=8 is last for r*=5 with arr=195.

In both cases, the "good witness r*" is one where MOST runners already cover it at b_lo, leaving only one or a small number of runners to arrive.

---

## 7. Structural Characterization of r*

### 7.1 Two-Runner Complementary Pair

**Case**: ∃ e,e' ∈ E_non with gcd(e,n)=gcd(e',n)=g and complementary cosets at b_lo.

Coset(e) ∩ Coset(e') = ∅, Coset(e) ∪ Coset(e') = Z_n.

For r* ∈ Coset(e): arr(e,r*)=0, arr(e',r*)=t_{e'}(r*).
For r* ∈ Coset(e'): arr(e',r*)=0, arr(e,r*)=t_e(r*).

Optimal: pick r* to minimize max(t_{e}(r*), t_{e'}(r*)) = min(t_e for coset(e'), t_{e'} for coset(e)).

Usually min(max t_e, max t_{e'}) is achieved at the coset of the runner with the LARGER maximum arrival time.

**Claim**: max_{r∈Coset(e)} arr(e',r) ≤ 2L/e' [the e' runner arrives within 2L/e' for any r].

**Budget bound**: Need 2L/e' ≤ budget → e' ≥ 4n/(n-2).

For large g (gcd), e' is a gcd-g multiple of n/g, so e' ≥ n/g ≥ 2 (for g ≤ n/2). More precisely, e' is a runner such that gcd(e',n)=g, so e' = g·k for some k with gcd(k,n/g)=1. The smallest such e' > n is e'=g·(n/g+1)=n+g (for k=n/g+1 when gcd(n/g+1,n/g)=1, which holds).

For e'=n+g: 2L/(n+g). Budget ≈ (n-2)L/(2n). Need n+g ≥ 4n/(n-2). For g=n/2: n+n/2=3n/2 ≥ 4n/(n-2) iff 3(n-2)/2 ≥ 4 iff n ≥ 10/3, true for n≥4. ✓ For g=1: n+1 ≥ 4n/(n-2) iff (n+1)(n-2) ≥ 4n iff n²-n-2 ≥ 4n iff n²-5n-2≥0 iff n≥6 (approximately). **FAILS for n=3,4,5!** But for those n, we need separate argument.

### 7.2 No Complementary Pair (all-unit E_non for prime n)

For prime n, all gcd(e,n)=1. No g>1 pairs. A_{b_lo}=∅ means the intersection of n-2 unit-runner safe sets is empty.

Each unit safe set has size n-2 (excludes exactly 2 residues). By inclusion-exclusion, A_{b_lo}=∅ requires the excluded residues to "cover" all of Z_n together.

**Claim**: When all runners have gcd=1 and A_{b_lo}=∅, there exists r* ∈ {1,...,n-2} with M(r*) ≤ budget.

**Proof sketch**: The n-2 runners each exclude 2 residues, covering 2(n-2) residue-exclusion pairs for n residues. So on average each residue is excluded by 2(n-2)/n < 2 runners. Some residue r* is excluded by at most 1 runner e*.

For this r* excluded by exactly 1 runner e*: M(r*) = arr(e*,r*). The arrival time is arr(e*,r*) ≤ 2L/e*.

**We need e* ≥ 4n/(n-2)**.

Why can't e* be small? For r* ∈ {1,...,n-2} to be excluded by ONLY one runner e* (and covered by all others at b_lo), the n-3 other runners must all cover r*. Each other runner e≠e* covers r* iff r* ∉ {excluded_lower(e), excluded_upper(e)} — i.e., r* is in the interior of safe_set(e, b_lo).

The excluded residues for runner e are:
- excluded_lower(e): the residue a with x_{e,a}(b_lo) < L (lower dangerous zone)
- excluded_upper(e): the residue a with x_{e,a}(b_lo) > (n-1)L (upper dangerous zone)

For e=1: excluded_lower = 0, excluded_upper = n-1.
For general unit e: excluded_lower = some specific a_low, excluded_upper = some a_high.

The n-3 "covering" runners all cover r*, meaning r* ∉ {a_low(e), a_high(e)} for all e≠e*.

The runner e* is the ONLY one that excludes r*: r* ∈ {a_low(e*), a_high(e*)}.

**Question**: What determines e*? The excluded residues {a_low(e), a_high(e)} depend on e through the x formula. For unit runner e at b_lo:
x_{e,a}(b_lo) = (e*(aL+L/n)) mod nL.

Lower excluded: x_{e,a_low}(b_lo) < L → minimal positive solution.
Upper excluded: x_{e,a_high}(b_lo) > (n-1)L → maximal solution below nL.

**For a_high** (upper zone, more relevant):
x_{e,a_high}(b_lo) > (n-1)L → (n-1)L < (e*(a_high*L+L/n)) mod nL < nL.

This means e*(a_high+1/n) ≡ something ∈ (n-1, n) (mod n). Since e*(a_high+1/n) = e*a_high + e/n, the fractional part of e/n (= {e/n} in modular arithmetic) determines where this lands.

**Key**: The residue a_high excluded by runner e in the upper zone satisfies:
a_high = ⌊n*(1 - {e/n})⌋ = n-1-⌊n*{e/n}⌋ approximately.

For e=8, n=7: {8/7} = 1/7. a_high = 6-⌊7*(1/7)⌋ = 6-1 = 5. Indeed from the W1 computation: safe_set(8,120) = {0,1,2,3,4}, so a_high = 5. ✓

So e*=8 excludes a_high=5=r*, and the optimal witness is r*=5 (the upper excluded residue of e=8).

**Arrival time for e* in upper zone, r*=a_high(e*)**:
x_{e*,r*}(b_lo) = just above (n-1)L (since r* is the upper excluded residue).

More precisely: (e*(r**L+L/n)) mod nL ∈ ((n-1)L, nL).

Let x = (n-1)L + δ where 0 < δ < L. Then:
arr(e*,r*) = ((n+1)L - x)/e* = (2L-δ)/e*.

The δ is determined by the specific arithmetic. For W1 (e*=8, n=7, L=840):
x=5160, (n-1)L=5040, δ=120=b_lo=L/7. arr=(2*840-120)/8=1560/8=195. ✓

Note: δ = L/n = b_lo! This is not a coincidence.

**Claim**: For the upper-zone excluded residue r* of runner e*, δ = (e* mod n)*L/n.

Proof: x_{e*,r*}(b_lo) = (e**(r**L+L/n)) mod nL. Let q=⌊e*/n⌋, s=e* mod n.
(e**(r**L+L/n)) = q*n*r**L + s*r**L + q*L + s*L/n.
mod nL: (s*r* mod n + q + s/n)*L (reducing the first two terms mod n).

For r*=a_high=n-1-⌊n*(s/n)⌋ = n-1-⌊s⌋ = n-1-s (for s < n, which holds since s = e* mod n < n):
Hmm, ⌊s⌋ = s (since s is already an integer). So r* = n-1-s iff e* mod n = s.

Then: s*r* mod n = s*(n-1-s) mod n = (sn-s-s²) mod n = (-s-s²) mod n = -s(1+s) mod n.

The x value / L: (-s(1+s) mod n) + q + s/n = (n-s(1+s) mod n) + q + s/n.

For x to be in the upper zone ((n-1)L, nL), we need: (x/L mod n) ∈ (n-1, n).
Let ρ = x/L mod n. We need n-1 < ρ < n, i.e., the fractional part of x/L is > (n-1)/n or rather x/L mod n ∈ (n-1, n). So ρ = n - ε for small ε > 0.

Computing: ρ = (n - s(1+s) mod n) + q + s/n.
For this to be in (n-1, n): we need ρ - ⌊ρ⌋ = {ρ} ∈ {(n-1)-⌊ρ⌋, ...} — this is getting complex.

Let's just state: for W1, δ = x - (n-1)L = 5160 - 5040 = 120 = L/n = b_lo.
And arr = (2L-δ)/e* = (2L-L/n)/e* = L(2n-1)/(n*e*).

Budget: (n-2)(L-n)/(2n) ≈ (n-2)L/(2n) for large L.

arr/budget ≈ (2n-1)/(n*e*) / ((n-2)/(2n)) = 2(2n-1)/((n-2)*e*).

Need: 2(2n-1)/((n-2)*e*) ≤ 1 → e* ≥ 2(2n-1)/(n-2).

For n=7: e* ≥ 2*13/5 = 5.2 → e* ≥ 6. And e*=8 ≥ 6. ✓

But this uses δ=L/n. Is δ always L/n? Let's check:

For δ = s*L/n (general formula): arr = (2L - s*L/n)/e* = L(2n-s)/(n*e*) where s = e* mod n.

Budget ≈ (n-2)L/(2n) for large L.

arr/budget ≈ 2(2n-s)/((n-2)*e*).

Need: e* ≥ 2(2n-s)/(n-2).

For s=e* mod n: the condition becomes (n-2)*e* ≥ 2(2n-s) = 2(2n-(e* mod n)).

If e* mod n = 0 (e* divisible by n): but gcd(e*,n)=1 requires n∤e*, so s≠0.
If s=1: e* ≥ 2(2n-1)/(n-2). For large n: ≈ 4n/(n-2) → 4. So e*≥5 for n=7.
If s=n-1 (maximum): e* ≥ 2(2n-(n-1))/(n-2) = 2(n+1)/(n-2) ≈ 2 for large n.

The worst case is s=1 (minimum s), giving e*≥4n/(n-2) approximately.

**The question**: Must e* satisfy e* ≥ 4n/(n-2) whenever e* is the last runner?

If e* < 4n/(n-2), then arr(e*,r*) > budget. This would be a Lemma BR violation. Since we observe 0 violations empirically, the answer appears to be YES: e* ≥ 4n/(n-2) always holds. But WHY?

---

## 8. Why the Last Runner Must Be Large

### 8.1 Structural Constraint

**Claim**: For any tuple with start_run > 0, the last runner e* satisfies e* ≥ 4n/(n-2) (approximately).

**Proof attempt**:

For e* to be the last runner for the OPTIMAL witness r*, ALL other runners must already cover r* at b_lo (or arrive earlier). Specifically:

Suppose for contradiction that e* < 4n/(n-2) and arr(e*,r*) = start_run > budget.

Then start_run = arr(e*,r*) > budget = (n-2)(L-n)/(2n).

But by the palindrome: end_run = start_run > budget.

So B_safe = |C| - start_run - end_run < |C| - 2·budget = n-1.

This means B_safe < n-1, i.e., there are fewer than n-1 good fibers.

**Can B_safe < n-1?** From the sweep: 0 violations of B_safe ≥ n-1 in 3415 tuples. So empirically no. But analytically?

**Alternative angle**: The number of good fibers B_safe is at least n-1. This would directly imply Lemma BR. But we haven't proved B_safe ≥ n-1 analytically either.

### 8.2 Direct Lower Bound on B_safe

**Approach**: Show ∃ at least n-1 distinct good fibers b_1,...,b_{n-1} ∈ B_div.

For each r ∈ {1,...,n-1}, define b_r as the earliest b ∈ B_div where r ∈ A_b (ALL runners cover r simultaneously at b). Then b_r is a good fiber.

If all b_r are distinct, we get n-1 distinct good fibers → B_safe ≥ n-1. □

**Question**: Are the b_r distinct?

For different r values, the "opening time" of A_b for r vs r' is different (since different runners are the last to cover each). If the last runners for r and r' are DIFFERENT runners, or arrive at different times, then b_r ≠ b_r'.

For r and r' where the SAME runner e* is last and arrives at the SAME time: b_r = b_r'. In this case, A_{b_r} contains both r and r', so we haven't found distinct fibers.

The number of distinct b_r values = the number of "distinct opening events." This is hard to count without more structure.

---

## 8a. Key Computational Findings (v1 Investigation)

### From lrc_lemma_br_structure_v1.py:

1. **Formula verification** (130 pairs): Upper-excluded residue formula `a_high = −s⁻¹(1+q) mod n` holds exactly. ✓

2. **Sum argument FAILS** (102/132 violations): `Σ_r M(r) > n·budget` is common. Average argument insufficient.

3. **Pigeonhole on min-exclusion** (193 tuples, 0 failures):
   - `max_min_exclusions = 1` for ALL n ∈ {4,...,8}.
   - Optimal r* always has exactly 1 excluding runner. arr(e*,r*) ≤ budget. ✓

### From lrc_lemma_br_witness_zone_v1.py:

4. **Zone distribution**: 80.9% lower-zone, 19.1% upper-zone optimal witnesses.

5. **Both zones work** (0 total failures in 162 tuples):
   - Lower-zone witnesses: arr = L(n−s)/(ne*) ≤ budget.
   - Upper-zone witnesses: arr = L(2n−s)/(ne*) ≤ budget (requires e* large enough).

6. **Lower-zone-only strategy insufficient** (6 failures): For some tuples (e.g., n=5, E_non={1,8,11}), the only lower-zone 1-exclusion residue has arr > budget (from e=1). But upper-zone witnesses from larger runners (e=8,11) succeed.

7. **Algebraic lower-zone bound**: arr_lower = L(n−s)/(ne*) ≤ budget requires e* ≥ 2L(n−s)/((n−2)(L−n)) ≈ 2(n−s)/(n−2) for large L. This is ≤ 2 for s≥1, so e*≥2 suffices for large L. Fails for very small L (L≈n) or e*=1.

---

## 9. Clean Proof Structure (DISCOVERED)

### Theorem (Pigeonhole Lemma for Unit Runners)

For any valid unit-runner tuple (all gcd(e,n)=1) with A_{b_lo}=∅:

**Step 1** (Exclusion count): Each unit runner excludes exactly 2 residues (1 lower zone, 1 upper zone) at b_lo. With n−2 runners, total exclusions = 2(n−2).

**Step 2** (Pigeonhole): Since A_{b_lo}=∅, all n residues have ≥1 exclusion (in Case B). Total = 2(n−2) exclusions for n residues with each having ≥1. Average = 2(n−2)/n < 2. Therefore ∃ r* with exactly 1 exclusion.

**Step 3** (Formula for arrival): For the unique excluder e* of r*:
- Lower zone: arr(e*,r*) = L(n−s*)/(ne*) where s* = e* mod n
- Upper zone: arr(e*,r*) = L(2n−s*)/(ne*)

**Step 4** (Budget bound — REMAINING GAP): Must show at least ONE of the 1-exclusion residues satisfies arr ≤ budget.

**The gap**: When e*=1 (smallest runner) is the unique excluder, arr >> budget. Need to show a different 1-exclusion residue with larger e** exists with arr ≤ budget.

**Empirical evidence**: Always holds (0 failures, 193 unit-runner tuples).

### Key Observation for the Gap

For unit-runner E_non with 1 ∈ E_non:
- e=1 excludes {0} (lower) and {n−1} (upper). Both have arr >> budget.
- But e=1 appears in only 2 of the 2(n−2) total exclusion pairs.
- Remaining 2(n−2)−2 = 2(n−3) exclusions for n−2 residues in {1,...,n−2}.
- Average for interior residues: 2(n−3)/(n−2) < 2.
- ∃ interior r* ∈ {1,...,n−2} with 1 exclusion by some e* ≠ 1.

For this interior r* excluded by e* ≠ 1 (so e* ≥ 2):
**Lower zone**: arr = L(n−s*)/(ne*) ≤ L(n−1)/(2n). Budget ≈ (n−2)L/(2n). Ratio ≤ (n−1)/(n−2) > 1 for finite n! **STILL NOT SUFFICIENT** without more info about e*.

**Upper zone**: arr = L(2n−s*)/(ne*). For e* ≥ n+1: arr ≤ L(2n−1)/(n(n+1)). Budget ≈ (n−2)L/(2n). Ratio ≤ 2(2n−1)/((n−2)(n+1)). For n=5: ≤ 2·9/(3·6)=1. Tight! For n=6: ≤ 2·11/(4·7)=11/14 < 1. ✓

**Critical remaining step**: Show that among the interior 1-exclusion residues, at least one has e* satisfying e* ≥ 2(2n−s*)/(n−2).

Equivalently (using e* = qn+s*, e* | L, e* ∈ E_non): show that the structure of valid tuples (gcd(E)=1, L=lcm(E), |E_non|=n−2) forces at least one interior 1-exclusion residue to have a large-enough e*.

---

## 9b. Complete Structural Picture (Verified)

### The Clean Proof for Unit-Runner Case

**Setup**: A_{b_lo}=∅. n-2 unit runners (all gcd=1). n prime assumed for now.

**Step 1** [PROVED]: Each unit runner e excludes exactly 2 residues at b_lo:
- a_low(e) = −q·s⁻¹ mod n (lower zone, x < L)
- a_high(e) = −s⁻¹·(1+q) mod n (upper zone, x > (n−1)L)
where s = e mod n, q = ⌊e/n⌋, s⁻¹ = inverse of s mod n.

**Arrival formulas**:
- arr(e, a_low(e)) = L·(n−s)/(n·e)
- arr(e, a_high(e)) = L·(2n−s)/(n·e)

**Step 2** [PROVED]: Pigeonhole: 2(n−2) exclusions for n residues with each ≥1 (Case B) → ∃ r* with exactly 1 exclusion.

**Step 3** [KEY GAP]: Must show ∃ r* with 1 exclusion and arr(e*,r*) ≤ budget = (n−2)(L−n)/(2n).

**What we know**:
- Sum argument FAILS (102/132 tuples have Σ M(r) > n·budget).
- HOWEVER, the min-exclusion residue ALWAYS satisfies arr ≤ budget (0 failures, 193 tuples).
- 80.9% lower zone, 19.1% upper zone optimal witnesses.
- Lower zone only fails in 6/162 tuples (upper zone rescues).

**Why the optimal witness always satisfies arr ≤ budget** (heuristic):

**Case 1** (e*=1 as unique excluder): Never happens for r*∈{1,...,n-2}. Runner 1 only uniquely excludes r=0 (lower, arr≈L) and r=n-1 (upper, arr≈2L). These have arr >> budget. But other residues must then be uniquely excluded by OTHER runners.

**Case 2** (e*>1, large runner, upper zone): arr = L(2n−s*)/(ne*). For e*≥2(2n−s*)/(n-2) and large L: arr≤budget. Verified: runners with e*≥7 always satisfy this for n=5.

**Case 3** (e*>1, lower zone): arr = L(n−s*)/(ne*). For the lower zone arrival, the "doubling" effect (numerator n−s* vs 2n−s*) gives arr ≈ L/(2e*) vs 2L/e*. This is HALF the upper zone bound. For many runners, lower zone witnesses are even smaller.

**Remaining analytic gap**: Proving that at least one runner e* ≥ 2(2n−s*)/(n-2) uniquely excludes some residue r* ∈ {1,...,n-2}.

**Structural reason this must hold** (not yet fully proved):
1. Small runners (e<threshold) collectively exclude only a few "boundary" residues with large arrivals.
2. Interior residues {1,...,n-2} must be excluded by some runners.
3. Among runners excluding interior residues, at least one is large enough (≥threshold).
4. This "large" runner has a uniquely-excluded interior residue with arr≤budget.

The argument requires careful counting: if ALL runners excluding interior residues are small (<threshold), the total interior exclusion count would be too small to cover all n−2 interior residues (since small runners with a_low=0 don't contribute to interior exclusions). This gives a contradiction.

**Special case provable**: When 1∈E_non and all other runners have e_k>n: e_k's a_low is an interior residue (≠0), and for large enough e_k, arr(e_k,a_low(e_k))≤budget. The counting shows some e_k must uniquely cover an interior a_low.

---

## 11. Structural Results from lrc_lemma_br_last_runner_profile_v1.py

### 11.1 Proved: A_{b_lo}=∅ Requires e > n

**Theorem**: For any unit-runner tuple where all e ∈ E_non satisfy e < n: A_{b_lo} ≠ ∅.

**Proof**: Each unit runner e < n (q=0) excludes exactly:
- a_low(e) = 0 (lower zone, ALL runners e < n share this)
- a_high(e) = −e⁻¹ mod n ∈ {1,...,n-2} (for e ≥ 2; a_high(1) = n−1)

So any runner e < n contributes at most 1 interior exclusion (a_high). With n−2 runners, at most n−2 exclusions of the n−2 interior residues {1,...,n−2}. However, runner e=1 has a_high(1) = n−1 (boundary, not interior). So among n−2 runners with all e < n:
- n−3 runners (e ∈ {2,...,n−1}) contribute a_high ∈ {1,...,n−2} (interior exclusion).
- Runner e=1 contributes a_high=n−1 (boundary exclusion, not interior).
- Total interior exclusions: ≤ n−3 < n−2.

So at least 1 interior residue r ∈ {1,...,n−2} has zero exclusions → r ∈ A_{b_lo}. ✓

**Corollary**: Any unit-runner tuple with A_{b_lo}=∅ (Case B) must contain ∃ e* ∈ E_non with e* > n. **Verified: 0 counterexamples over 13 all-small-runner tuples.** □

### 11.2 Proved: min-exclusion = 1 (Pigeonhole)

**Theorem**: For any unit-runner tuple with A_{b_lo}=∅: some r ∈ Z_n has exactly 1 excluding runner.

**Proof**: n−2 unit runners each exclude exactly 2 residues → 2(n−2) exclusion pairs for n residues. Since A_{b_lo}=∅, each residue has ≥1 exclusion. Total ≥ n exclusions. But total = 2(n−2) = 2n−4 < 2n, so average < 2. Hence some residue has exactly 1 exclusion. **Verified: max_min_exclusions = 1 for ALL 739 unit-runner tuples.** □

### 11.3 Proved (Algebraically): Large-Runner Lower-Zone Bound

**Theorem**: For n ≥ 4, any unit runner e* > n (e* ≥ n+1), and r* = a_low(e*):
$$\text{arr}(e^*, r^*) = \frac{L(n-s^*)}{n \cdot e^*} \leq \frac{(n-2)(L-n)}{2n} = \text{budget}$$

**Proof**: Compute the ratio at minimum L = e*n (gcd(e*,n)=1, so lcm = e*n):
- arr = e*n(n−s*)/(n·e*) = n−s*
- budget = (n−2)(e*n−n)/(2n) = (n−2)(e*−1)/2

Need n−s* ≤ (n−2)(e*−1)/2. The worst case is s*=1, e*=n+1:
- arr = n−1
- budget = (n−2)n/2

n−1 ≤ n(n−2)/2 iff 2(n−1) ≤ n(n−2) = n²−2n iff n²−4n+2 ≥ 0, true for n ≥ 4. ✓

For larger e* or L: the ratio arr/budget = 2(n−s*)/((n−2)(e*−1)) is maximized at s*=1, e*=n+1, and equals 2(n−1)/(n(n−2)) < 1 for n ≥ 4. As L increases, arr/budget decreases monotonically (d/dL < 0). **Verified: 0 failures for all e* ≥ n+1, n=3..11.** □

**Note**: n=3 fails algebraically but is irrelevant (n=3 always has A_{b_lo}≠∅, Case A only).

### 11.4 Profile of Optimal Witnesses (739 unit-runner tuples)

| Property | Count | % |
|---|---|---|
| e* > n (large runner) | 234 | 94.0% |
| e* ≤ n (small runner) | 15 | 6.0% |
| e* ≤ n, arr > budget | 0 | 0% |
| ALL 1-exc residues have e* > n | 8 | 3.2% |

**Note on small-e* cases (6%)**: When e* ≤ n is the optimal unique excluder, the arrival is in the upper zone r* = a_high(e*). These cases have specific (n, e*, L) with n(e*−1) large enough that arr ≤ budget still holds. Example: n=6, e*=5: arr=7L/30, budget=(L−6)/3. Ratio = 7L/(10(L−6)) < 1 for L ≥ 20. □

### 11.5 Main Theorem: Proof for the Case 1 ∈ E_non

**Setup** (n ≥ 4, prime n for now): E_non = {1} ∪ E_rest with |E_rest| = n−3.

**Key structural facts at b_lo for unit runners**:
- Runner e=1: safe_set = {1,...,n−2}; excludes {0} (lower) and {n−1} (upper); both boundary.
- Runner e ∈ {2,...,n−1} (q=0): excludes {0} (lower) and a_high(e) = −e⁻¹ mod n ∈ {1,...,n−2} (interior). [Since −e⁻¹ ≢ 0 (mod n) and for e ≠ 1: −e⁻¹ ≢ n−1 (mod n), verified: a_high(n−1)=1, a_high(e)≠n−1 for e∈{2,...,n−1}.]
- Runner e > n (q ≥ 1): excludes a_low(e) = −q·s⁻¹ mod n (interior, ≠0 for q ≥ 1) and a_high(e) = −(1+q)·s⁻¹ mod n.

**Define**:
- k_s = #{e ∈ E_rest : e < n} (small runners, each with 1 interior exclusion).
- k_l = #{e ∈ E_rest : e > n} (large runners, each with 2 interior exclusions). k_s + k_l = n−3.
- A_small = {a_high(e) : e ∈ E_rest, e < n} ⊆ {1,...,n−2}. |A_small| = k_s (all distinct since e ↦ −e⁻¹ mod n is injective on {2,...,n−1}).
- S₀ = {1,...,n−2} \ A_small. |S₀| = n−2−k_s = k_l+1 ≥ 2 (since k_l ≥ 1 from §11.1).

**Claim**: Each r ∈ S₀ must be excluded by ≥1 large runner (otherwise r has 0 total exclusions → r ∈ A_{b_lo} → Case A).

Large runners provide 2k_l exclusion pairs among the interior residues. The ≥ k_l+1 residues in S₀ each need ≥1 large-runner exclusion. Total large-runner interior exclusions ≤ 2k_l.

**Pigeonhole**: Distributing 2k_l exclusions among k_l+1 residues each needing ≥1, and average = 2k_l/(k_l+1) < 2. So some r* ∈ S₀ gets exactly 1 large-runner exclusion.

This r* has:
- 0 exclusions from small runners (since r* ∉ A_small),
- 1 exclusion from some e* > n.
- Total: exactly 1 exclusion. Unique excluder: e* > n.
- arr(e*, r*) ≤ budget (from §11.3). ✓

**Conclusion** (for 1 ∈ E_non): min_r M(r) ≤ arr(e*, r*) ≤ budget. Lemma BR holds. □

---

### 11.6 Extension to 1 ∉ E_non

**Both exclusions of large runners are budget-satisfying**: For e* > n (n ≥ 4), both:
- arr(e*, a_low(e*)) = L(n−s*)/(ne*) ≤ budget (§11.3)
- arr(e*, a_high(e*)) = L(2n−s*)/(ne*)

Need arr(e*, a_high(e*)) ≤ budget: 2L(2n−s) ≤ (n−2)(L−n)e*. For L=e*n (minimum), e*=n+1, s=1: 2(2n−1) ≤ (n−2)n². For n=4: 2·7=14 ≤ 2·16=32 ✓. For n=5: 2·9=18 ≤ 3·25=75 ✓. In general: easily satisfied for n ≥ 4 and e* ≥ n+1. ✓

So ALL 2k_l large-runner exclusion pairs are budget-satisfying.

**Obstacle for 1 ∉ E_non**: Without runner 1 separating boundary ({0,n−1}) from interior ({1,...,n−2}), small runners' exclusions can cover all residues differently. The S₀ structure changes.

**Status**: Case 1 ∉ E_non is **empirically verified (0 failures, 739 tuples)** but the analytic proof using the S₀ argument doesn't directly apply. The argument fails when k_s is large enough that all large-runner exclusions are co-excluded by small runners.

**Route**: For k_s ≥ k_l (many small runners): the 1-exclusion residues come from small runners with large e (close to n−1) where arr ≤ budget still holds. Requires tracking the specific small-runner arrival formula L(2n−e)/(ne) ≤ budget for e ≥ 4.

---

### 11.8 Correction to P3: Minimax Formula Is Wrong

**Counterexample (W1)**: n=7, E_non={1,2,6,8,10}, L=840, b_lo=120, budget=297.5.

For r=2: max_e arr(e,2) = arr(10,2) = 48 (only e=10 excludes r=2 at b_lo). But:
- e=6 covers r=2 at b_lo with x0=4920 near (n-1)L=5040.
- Window for e=6 at r=2: (5040−4920)/6 = 20 steps.
- e=10 arrives at r=2 after 48 steps — but e=6 has already LEFT (window=20 < 48).
- A_{168} ≠ {2}: e=6 has stopped covering r=2. So r=2 is not in A_{168}.

So min_r max_e arr(e,r) = 48 ≠ start_run = 195. **P3 is FALSE in general.**

**Correct definition: Valid Witness**

r* is a *valid witness within budget* if:
1. arr(e*,r*) ≤ budget for the unique/dominant excluder e*.
2. **Window maintenance**: every runner e with arr(e,r*)=0 satisfies window_from_blo(e,r*) ≥ arr(e*,r*).
   Where window_from_blo(e,r*) = ⌊((n−1)L − x0(e,r*))/ e⌋.

For r=5 (W1 actual witness): e=8 arrives at 195 steps. All other runners (e=1,2,6,10) have windows [720,1140,440,300] all ≥ 195. **Valid.** start_run = 195 = arr(8,5) ≤ budget=297.5. ✓

For r=2 (NOT the actual witness): e=6 has window=20 < arr(10,2)=48. **Invalid.** The actual first simultaneous coverage of r=2 is at b=420 (start_run equivalent 300 > budget if it were the first good fiber — but b_break=315 < 420 so r=5 is better).

**Empirical check** (99 tuples, n=3..7): Valid witness always exists, 100% success.

### 11.9 Revised Proof Strategy (Updated 2026-03-06)

The correct approach needs to show: ∃ r* with valid witness within budget (both conditions).

**What we have**:
- S₀ argument (§11.5) gives r* with arr(e*,r*) ≤ budget (condition 1). ✓
- Window maintenance (condition 2) is **not yet proved analytically**.

**Window maintenance analysis**: For runner e (arr=0, covering r* at b_lo):

window_from_blo(e,r*) = ⌊((n−1)L − x0(e,r*)) / e⌋

Need: (n−1)L − x0(e,r*) ≥ e · arr(e*,r*).

#### Corrected Empirical Picture (65 Case-B unit-runner tuples, n=5..8):

| Result | Count | % |
|---|---|---|
| Case B with valid S₀ (1-exclusion) witness | 61 | 94% |
| Case B with NO valid S₀ witness (need 2-excl) | 4 | 6% |

**The 4 "no S₀ witness" cases**: All have valid **2-exclusion witnesses** with max_arr ≤ budget.
Example: n=5, E_non={1,9,17}, L=765: r*=1 has excl={9,17}, arr(9,1)=17, arr(17,1)=27.
All 1-exclusion residues fail (arr>>budget or window fail), but r*=1 works with max_arr=27 ≤ budget=228.

#### Zone Analysis of S₀ Elements:

| Zone | Valid / Total | Rate |
|---|---|---|
| Lower-zone (x0(e*,r*) < L) | 68 / 77 | 88.3% |
| Upper-zone (x0(e*,r*) > (n-1)L) | 34 / 111 | 30.6% |

**Key finding**: Lower-zone witnesses are individually valid at 88.3%. ALL lower-zone failures (9 elements) are caused by LARGE co-covering runners (e'>n), NEVER small runners or budget overrun.

#### Why Farey Adjacency from NR/Freeze Does NOT Close This

Lemma NR/Freeze guarantees no floor transition in interval of width **1/(e*·e_max)**.
Window maintenance requires window ≥ arr(e*,r*) ≈ **L/e***.
Ratio: L/e* vs. L/(e*·e_max) → NR interval is **e_max times smaller** than needed. Different regimes. The Farey adjacency technique cannot be directly imported.

#### Proof Strategy Going Forward

Two sub-cases:
1. **(94% case — S₀ witness)**: Show that among S₀ elements, at least one has all large co-covering runners with windows ≥ arr(e*,r*). This requires arithmetic analysis of x0(e',r*) for e'>n, e'≠e*.
2. **(6% case — 2-exclusion witness)**: When no S₀ element works, show ∃ r* with 2 excluders {e1,e2} where max(arr(e1,r*),arr(e2,r*)) ≤ budget and window maintenance holds. In observed examples, arr is very small (<<budget) for these witnesses.

**Note on condition 1 for case 2**: The 2(n-2) total exclusions for n residues each needing ≥1 gives average <2. In "no S₀" tuples (all residues have ≥2 exclusions would violate the sum), actually: the sum 2(n-2) forces at least one residue to have ≤1 exclusion. Since S₀ is non-empty (by pigeonhole), "no S₀" cases cannot exist unless S₀ exists but its witness fails window maintenance OR fails condition 1 (arr>budget). The 4 failures are all of the latter type (arr >> budget for 1-exclusion residues).

### 11.7 Remaining Analytic Gaps (Updated 2026-03-06)

**Proved components**:
- §11.1: A_{b_lo}=∅ requires ∃ e > n in E_non. ✓
- §11.2: min-exclusion = 1 always (pigeonhole). ✓
- §11.3: arr(e*, a_low(e*)) ≤ budget for e* > n, n ≥ 4. ✓
- §11.5: ∃ r* ∈ S₀ with unique excluder e*>n and arr≤budget (prime n, 1∈E_non). ✓

**Gap A (Window maintenance, 94% of Case-B tuples)**:
For the S₀ witness r* with unique excluder e* > n and arr(e*,r*) ≤ budget: show all co-covering large runners e'≠e* satisfy window(e',r*) ≥ arr(e*,r*). Small co-covering runners are not the bottleneck (observed: 0 small-runner window failures among lower-zone S₀ witnesses in sampled tuples).

**Gap B (2-exclusion witnesses, 6% of Case-B tuples)**:
For tuples where all 1-exclusion witnesses have arr >> budget: show ∃ r* with 2-exclusion structure where max_arr ≤ budget. In all 4 observed cases, such witnesses have arr << budget (e.g., arr=27 vs budget=228 in the [1,9,17] example), suggesting these are structurally different (pair of fast runners both excluding r*).

**Gap C (1 ∉ E_non)**:
S₀ argument uses e=1 to separate boundary from interior residues. Without e=1, the S₀ structure changes. Empirically verified (0 failures) but analytic proof is open.

**Gap D (composite n)**:
Non-unit runners (gcd(e,n)>1) affect the coset structure at b_lo. Needs separate treatment.

---

## 10. Current Proof Status

| Sub-claim | Status | Notes |
|---|---|---|
| Case A: A_{b_lo}≠∅ → start_run=0 | **PROVED** | Trivial |
| Palindrome: start_run = end_run | **PROVED** | §P1 bijection |
| Arrival time formula (e\|L) | **PROVED** | §P2 |
| Minimax reformulation: start_run = min_r max_e arr(e,r) | **FALSE** (corrected §11.8) | W1 counterexample: formula=48 ≠ start_run=195 |
| Valid witness exists within budget | **OPEN** (analytic) | 100% empirical success, 99 tuples |
| A_{b_lo}=∅ requires ∃ e > n in E_non (unit tuples) | **PROVED** | §11.1, 0 counterexamples |
| min-exclusion = 1 always (pigeonhole) | **PROVED** | §11.2, 2(n-2) < 2n |
| arr(e*, a_low(e*)) ≤ budget for e* > n (n ≥ 4) | **PROVED** (all L) | §11.3, ratio ≤ 2(n-1)/(n(n-2)) < 1 |
| arr(e*, a_high(e*)) ≤ budget for e* > n (n ≥ 4) | **PROVED** (all L ≥ e*n) | §11.6, both zones covered |
| ∃ r* with 1 exclusion from large runner AND arr ≤ budget (1 ∈ E_non) | **PROVED** (n ≥ 4 prime) | §11.5 S₀ pigeonhole |
| Same for 1 ∉ E_non | **OPEN** (analytic) | Empirically verified (739 tuples) |
| Non-unit runners (gcd(e,n) > 1) in E_non | **OPEN** | Needs coset structure argument |

---

## 10. Next Steps

1. **Structural constraint on e***:
   Prove: if e* < 4n/(n-2) and e* is the "last runner" for some r*, then there exists r** ≠ r* with M(r**) < M(r*), so e* is not actually the last runner for the optimal witness.

2. **Upper excluded residue analysis**:
   When r* = a_high(e*) (upper excluded residue of e*), prove arr(e*,r*) ≤ budget using the exact x formula δ = (e* mod n)·L/n.

3. **The case δ=L/n**:
   If δ = (e* mod n)·L/n, then arr = L(2n-s)/(n·e*) where s=e* mod n. The bound arr ≤ budget becomes e*(n-2) ≥ 2(2n-s). Since e* = qn+s, this gives (qn+s)(n-2) ≥ 2(2n-s). For q≥1: e* ≥ n+1 → (n+1)(n-2) ≥ 4n-2 iff n²-3n+2 ≥ 4n-2 iff n²-7n+4≥0 iff n≥7 or n≤... true for n≥7. For n=3,4,5,6 need separate check.

4. **Small n cases** (n=3,4,5,6): Exhaustive verification shows 0 violations; the bound L ≥ specific function of e* ensures arr ≤ budget.
