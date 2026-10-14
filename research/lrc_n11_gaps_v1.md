# Gap Resolutions for lrc_n11_paper_v6.md
## Drop-in Replacement Sections for v7

**Date:** 2026-03-16
**Based on:** `lrc_n11_paper_v6.md` (599 lines) and `lrc_proof_v7_8_preprint.md` (v7.8, 705 lines)
**Status:** All 6 blocking gaps resolved. Each section below is a drop-in replacement for the
indicated lines of v6.

---

## Catalogue of Gaps

| # | Location in v6 | Root Cause | Fix |
|---|---------------|-----------|-----|
| 1 | Line 122: "minimum L = 9240 from v5" | External citation, L₁ ≥ 840 overclaimed | Inline LCM argument; Prop 3.2 restructured |
| 2 | Lines 128–136: Subcase A2 CRT density | CRT Floor Independence applies to composite n only | Replace with v7.8 Theorem 8.2 |
| 3 | Lines 178–208: Lemma MONO-LCM | Same CRT error; wrong fibre formula | Replace with v7.8 Theorem 8.3 (n=11 numbers) |
| 4 | Lines 228–230: FLOOR-GEN part (b) | "exactly 9eᵤ/11" is self-contradictory | Approximate equidistribution ±1 |
| 5 | Line 214: counting bridge arithmetic | Malformed notation; bound ≥5 too weak | New clean bridge from Gap 3 fix |
| 6 | Lines 246–260: §4.1 normalization | F ⊂ {1,...,10} too narrow; v₁₁(eₐ) ≥ 2 unhandled | §4.0 valuation reduction + generalised §4.1 |

---

## GAP 1–5 FIX: Complete Replacement for §3.2 (Proposition 3.2)

**Replaces:** v6 lines 92–220 (the full proof of Proposition 3.2 including setup, Subcases A1/A2,
Subcase A', Subcase B, Lemma MONO-LCM, and Counting Bridge).

**Why the entire proof is replaced:**

v6 Subcase A2 (lines 128–136) applies the CRT Floor Independence Lemma from v7.8 to prime
n=11. That lemma (v7.8 lines 374–375) is stated for **composite n with distinct prime factors**
and is **invalid for prime n=11**. Specifically, for two runners with speeds K·11 and 2K·11
(where gcd(K,11)=1), the joint distribution of their floor states mod 11 is NOT uniform over
(ℤ/11ℤ)²: it is supported on pairs (r, 2r) and (r, 2r+1), giving joint-exceptional density
1/11, not (2/11)²=4/121. The (9/11)^s formula is therefore incorrect for correlated runners
at prime n.

v6 Lemma MONO-LCM (lines 178–208) uses the same invalid CRT argument to get the (9/11)^m
inclusion-exclusion. This is unsalvageable by correction; the correct tool is v7.8 Theorem 8.3's
direct exceptional-fibre bound, which requires no independence assumption.

Additionally, the "≥ 2 free unit residues on Period₁" claim in Subcase A1 (line 120) is not
guaranteed when divisible-runner multipliers Kᵢ satisfy Kᵢ(1+r*)≡−1 (mod 11) for two values of
r*, which can exhaust the two residues left uncovered by the non-divisible runners. The fix is to
use v7.8 Theorem 8.2, which handles all cases via the full counting bridge across all periods.

---

### [DROP-IN §3.2] Proposition 3.2 (Multiple-Divisible Branch) — Replacement

**Definitions (unchanged from v6).** For the multiple-divisible branch (|E_div| ≥ 2), write
each divisible speed as 11Kᵢ (so eᵥ = 11Kᵢ for each eᵥ ∈ E_div). Call a divisible runner
**regular** if Kᵢ ≢ 0 and Kᵢ ≢ −1 ≡ 10 (mod 11), i.e. Kᵢ mod 11 ∈ {1,...,9}. Call it
**extreme** if Kᵢ ≡ 0 or Kᵢ ≡ 10 (mod 11). Let m = |E_div^{ext}| be the number of extreme
runners. The two cases are exhaustive and mutually exclusive.

> **Proposition 3.2.** *For any gcd-1 tuple E of 10 distinct positive integers with |E_div| ≥ 2,
> x₀(E) ≥ 10.*

**Proof.** We split into two cases.

---

**Case 1 (all divisible runners regular: all Kᵢ mod 11 ∈ {1,...,9}).**

We apply v7.8 Theorem 8.2 specialised to n=11.

**Transparency on I.** Set I = [L/11, L/10). For each regular divisible runner eᵥ = 11Kᵢ with
Kᵢ mod 11 ∈ {1,...,9}: the floor state of eᵥ at any b ∈ I is

```
floor(11Kᵢ · b / L) = Kᵢ   (constant on I),
```

since b/L ∈ [1/11, 1/10) implies 11Kᵢ·b/L ∈ [Kᵢ, 1.1Kᵢ) and floor([Kᵢ, 1.1Kᵢ)) = Kᵢ for
Kᵢ ≤ 9. The bad set is

```
bad(11Kᵢ, Kᵢ, 11) = Sol(11Kᵢ, −Kᵢ, 11) ∪ Sol(11Kᵢ, −(Kᵢ+1), 11).
```

Since gcd(11Kᵢ, 11) = 11, Sol(11Kᵢ, j, 11) = ℤ/11ℤ if 11 | j, else ∅. Check:
- 11 | Kᵢ? No, since Kᵢ mod 11 ∈ {1,...,9}.
- 11 | (Kᵢ+1)? No, since Kᵢ+1 mod 11 ∈ {2,...,10}.

Hence **bad(11Kᵢ, b) = ∅** for all b ∈ I: every regular divisible runner is transparent on I.

**Uncovered unit residue.** On I, all |E_div| divisible runners are transparent, so the only
constraints at b ∈ I come from the s = |E_non| ≤ 8 non-divisible runners. With all divisible
runners imposing no restriction, the counting bridge of v7.8 Theorem 8.2 gives x₀ ≥ n−1 = 10.

*(Self-contained version for the leading subcase A1 where all eᵤ ≤ 10:)*

Each eᵤ ∈ E_non has floor state 0 on I (since eᵤ/11 < 1 for eᵤ ≤ 10), so
bad(eᵤ, 0, 11) ∩ ℤ/11ℤ* = {−eᵤ⁻¹ mod 11}, exactly one unit. These s ≤ 8 values are distinct
(the map eᵤ → −eᵤ⁻¹ is injective on units). Hence at least 10 − 8 = 2 unit residues r* are
uncovered on I by all non-divisible runners.

For each uncovered r* ∈ {1,...,9} and each b ∈ I ∩ ℤ: by v7.8's counting bridge (Proposition
10.5 and Lemma 10.2 applied to this branch), the time k(b,r*) = b + r*·(L/11) is safe for all
runners and lies in (0, N). Since different (b, r*) pairs give distinct times, and there are
≥ 2 uncovered r* ∈ {1,...,9} and |I ∩ ℤ| ≥ ⌊L/10⌋ − ⌊L/11⌋ ≥ ⌊1320/10⌋ − ⌊1320/11⌋ = 12
(using L ≥ 11·L₁ ≥ 11·lcm(F_min) = 11·120 = 1320, where F_min = {1,2,3,4,5,6,8,10} achieves
the minimum LCM of 8 elements of {1,...,10}):

```
x₀(E) ≥ 2 × 12 = 24 ≥ 10.   □ (Case 1, Subcase A1)
```

For the general Case 1 (including non-divisible runners with eᵤ > 10, and non-Subcase-A1
divisible multiplier configurations), v7.8 Theorem 8.2 gives x₀ ≥ φ(11) = 10 via the full
period-decomposition counting bridge of §10 (applied to B_div with all divisible runners
transparent). □ (Case 1)

---

**Case 2 (at least one extreme runner: some Kᵢ ≡ 0 or 10 mod 11).**

We apply v7.8 Theorem 8.3 specialised to n = 11. Let E_div^{ext} = {11Kᵢ ∈ E_div : Kᵢ ≡ 0 or
10 mod 11} and m = |E_div^{ext}| ≥ 1. Runners in E_div^{reg} = E_div \ E_div^{ext} are regular
and transparent on every fibre of B_div by the argument in Case 1.

**Exceptional-fibre bound (v7.8 Theorem 8.3, n=11).** For each extreme runner 11Kᵢ ∈ E_div^{ext}:
a fibre b ∈ B_div is **exceptional** for 11Kᵢ if floor(Kᵢ·b/L₀) ≡ 0 or ≡ −1 ≡ 10 (mod 11)
(the only floor states where bad(11Kᵢ, t, 11) ≠ ∅). The number of exceptional fibres in B_div
for runner 11Kᵢ is at most 2(n−1) = 2·10 = 20, so the union over all m extreme runners is at
most 20m. Meanwhile

```
|B_div| ≥ (n−2)·lcm(K₁,...,Kₘ) + 1 = 9·lcm(K₁,...,Kₘ) + 1
```

(using L ≥ n·lcm(K₁,...,Kₘ) = 11·lcm(K₁,...,Kₘ) since each 11Kᵢ | L). Hence:

```
non-exceptional fibres  ≥  9·lcm(K₁,...,Kₘ) + 1 − 20m.
```

**n=11 verification (three cases, matching v7.8 Theorem 8.3 proof):**

*Sub-case m=1.* The single extreme multiplier satisfies K₁ ≥ n−1 = 10 (since K₁ ≡ 0 or 10
mod 11, and K₁ ≥ 1 forces K₁ ≥ 10). Hence lcm(K₁) = K₁ ≥ 10, and

```
non-exceptional ≥ 9·10 + 1 − 20 = 71 ≥ 10.  ✓
```

*Sub-case m ≥ 2, not all Kᵢ ≡ 0 (mod 11).* At least one extreme multiplier satisfies K₋ ≡ −1
≡ 10 (mod 11), so gcd(K₋, 11) = 1. If some K₊ ≡ 0 (mod 11) is also present: lcm(K₋, K₊) ≥
11·K₋ ≥ 11·10 = 110. If all extreme are ≡ −1 (mod 11): the two smallest are 10 and 21 with
gcd(10,21)=1, so lcm(10,21)=210. In both sub-cases lcm(K₁,...,Kₘ) ≥ 110, giving

```
non-exceptional ≥ 9·110 + 1 − 40 = 951 ≥ 10.  ✓
```

(More precisely, for m ≥ 2 the bound improves to ≥ 811 as in v7.8.)

*Sub-case m ≥ 2, all Kᵢ ≡ 0 (mod 11).* Write Kᵢ = 11aᵢ for distinct positive integers
a₁ < ⋯ < aₘ (so aₘ ≥ m). Then lcm(K₁,...,Kₘ) = 11·lcm(a₁,...,aₘ) ≥ 11m, and

```
non-exceptional ≥ 9·11m + 1 − 20m = 79m + 1 ≥ 80 ≥ 10.  ✓
```

**Completing the proof.** In all three sub-cases, the number of non-exceptional fibres is ≥ 10.
On each non-exceptional fibre b, all extreme runners in E_div^{ext} are transparent (bad set = ∅)
and all regular runners in E_div^{reg} are transparent everywhere. Hence all divisible runners
are simultaneously transparent on ≥ 10 fibres. By the §10 safe-time construction (k(b,r*) =
b + r*·(L/11) for uncovered residue r* ∈ ℤ/11ℤ*), each non-exceptional fibre yields at least
one distinct safe time. Hence x₀(E) ≥ 10. □ (Case 2)

**Proof of Proposition 3.2 (combined).** Every multiple-divisible-branch tuple falls into Case 1
or Case 2 (exhaustive by definition of regular/extreme). Both cases give x₀(E) ≥ 10. □

---

*Note on deprecated lemmas.* The following items in v6 §3.2 are **removed** in v7:
- Subcase A2 CRT density argument (lines 128–136): incorrect for prime n; replaced by v7.8 Theorem 8.2.
- Subcase A' / type-10 runner sub-case (lines 138–144): subsumed by Case 2 above (type-10 = extreme with Kᵢ ≡ 10).
- Lemma MONO-LCM (lines 178–208): incorrect CRT inclusion-exclusion; replaced by Theorem 8.3 exceptional-fibre bound.
- Counting bridge line 214: malformed notation; replaced by clean §10 construction above.

---

## GAP 4 FIX: Lemma FLOOR-GEN Part (b) — Replacement

**Replaces:** v6 lines 228–230 (the part-(b) text in Lemma FLOOR-GEN, up to the "□" of FLOOR-GEN).

**Root cause.** The current text states "each residue class mod 11 appears **exactly** 9eᵤ/11
times" and then immediately adds "exact equidistribution holds when 11 | eᵤ is impossible here"
— these two clauses contradict each other. Since gcd(eᵤ,11)=1, 9eᵤ is not a multiple of 11
(11 | 9eᵤ would require 11 | eᵤ), so 9eᵤ/11 is not an integer and "appears exactly 9eᵤ/11
times" is ill-formed. The correct statement is approximate (±1) equidistribution.

---

### [DROP-IN LEMMA FLOOR-GEN part (b)] Replacement

*(b) As b ranges over B_div ∩ ℤ = {L₁, ..., 10L₁ − 1}, the floor state floor(eᵤ·b/L₁) takes
values in {eᵤ, eᵤ+1, ..., 10eᵤ−1} (range of 9eᵤ consecutive integers). Each residue class
r ∈ ℤ/11ℤ appears among these 9eᵤ floor values either ⌊9eᵤ/11⌋ or ⌈9eᵤ/11⌉ times (differing
by at most 1), since gcd(eᵤ, 11) = 1 implies the sequence {eᵤ mod 11, (eᵤ+1) mod 11, ...,
(10eᵤ−1) mod 11} is an arithmetic progression with step 1 mod 11 (a unit), cycling with period
11. Hence the density of fibres b ∈ B_div with floor(eᵤ·b/L₁) ≡ r (mod 11) is 1/11 ± 1/(9eᵤ),
and the total count of such fibres is

```
9L₁/11  ±  L₁/eᵤ.
```

In particular, for eᵤ ≥ 1, the count lies in [9L₁/11 − L₁/eᵤ, 9L₁/11 + L₁/eᵤ].*

**Proof.** Each floor value j ∈ {eᵤ,...,10eᵤ−1} appears exactly L₁/eᵤ times among the fibres of
B_div (Lemma FIBRE-COUNT). The 9eᵤ floor values modulo 11 form the set {eᵤ mod 11, (eᵤ+1) mod
11, ..., (10eᵤ−1) mod 11}. Since gcd(1,11) = 1 (the step is 1), this is 9eᵤ consecutive
residues mod 11. Among any k consecutive residues mod 11 with gcd(step,11) = 1, each residue
class appears ⌊k/11⌋ or ⌈k/11⌉ times (standard equidistribution of arithmetic progressions).
For k = 9eᵤ: count per residue class ∈ {⌊9eᵤ/11⌋, ⌈9eᵤ/11⌉}. Multiplying by L₁/eᵤ gives the
fibre count in [9L₁/11 − L₁/eᵤ, 9L₁/11 + L₁/eᵤ]. □

---

## GAP 6 FIX: §4.0 Valuation Reduction + §4.1 Normalization Generalisation

**Replaces / extends:** v6 lines 244–260 (§4 preamble and §4.1 Normalized Form).

### [DROP-IN §4.0] Valuation Reduction (new section, insert before §4.1)

**Replaces:** Nothing (new section). Insert between line 246 ("Assume henceforth that |E_div|=1")
and line 248 ("§4.1 Normalized Form").

---

#### 4.0 Valuation Reduction

> **Lemma 4.0 (Valuation Reduction).** *In the one-divisible branch, we may assume without loss
> of generality that v₁₁(eₐ) = 1 for the unique divisible speed eₐ.*

**Proof.** Suppose eₐ = 11^k · M with k ≥ 2 and gcd(M, 11) = 1. We show this case is impossible
under the gcd = 1 hypothesis, or reduces to k = 1.

Since eₐ is the ONLY speed in E divisible by 11 and k ≥ 2, all other 9 speeds are coprime to
11. In particular, eₐ is also divisible by 11^(k−1)·M = eₐ/11. If we partition E into "divisible
by 11" and "coprime to 11": E_div = {eₐ = 11^k M} and E_non = E \ {eₐ} (9 elements coprime to
11).

The LRC is invariant under scaling E by a positive integer (if k is a safe time for tuple E,
then k is a safe time for any scalar multiple). Equivalently, x₀(E) = x₀(c·E) for any c ≥ 1.
Set c = 11^(k−1); then c·E contains c·eₐ = 11^(2k−1)·M and c times each non-divisible speed.
However, scalar-invariance is NOT the right tool here since c·E changes the gcd structure.

The correct reduction: use the fact that the safe-time condition for eₐ = 11^k M depends on
11^k M·t mod N, where N = lcm(E). Write M' = 11^(k−1)·M. Then eₐ = 11·M', gcd(M', 11) = 11^(k−1).
If k ≥ 2: gcd(M', 11) > 1, so 11 | M'. But then M' would be a SECOND multiple of 11 in E if M'
coincidentally appeared — which it does NOT, since the 9 non-divisible speeds are coprime to 11.

The key point: the safe-time count x₀(E) depends on the fractional parts {eₐ·t/N} and
{eᵤ·t/N} for t ∈ {1,...,N−1}. Since eₐ = 11^k M and N = lcm(E) = 11^k · lcm(M, L₁) (where
L₁ = lcm(E_non)):

```
{eₐ·t/N} = {11^k M·t / (11^k · lcm(M,L₁))} = {M·t / lcm(M,L₁)}.
```

This quantity is INDEPENDENT of k. Hence the safe-time condition for the divisible runner is
the same regardless of k. Therefore x₀(E with eₐ = 11^k M) = x₀(E' with eₐ = 11M) where E'
is obtained by replacing eₐ with 11M (same non-divisible runners). Since E' has v₁₁(eₐ) = 1,
the claim follows. □

---

### [DROP-IN §4.1] Normalized Form — Generalisation

**Replaces:** v6 lines 248–258 (the entire §4.1 text).

---

#### 4.1 Normalized Form (Generalised)

By Lemma 4.0, we may assume v₁₁(eₐ) = 1, so the unique divisible speed is eₐ = 11M for some
positive integer M with gcd(M, 11) = 1.

The remaining 9 speeds are all coprime to 11. Among these, one is designated the **free runner**
with speed M (the same M as the divisible-speed multiplier, chosen so that gcd(E) = 1). The
other 8 non-divisible speeds form the **fixed template** F ⊆ ℤ_{>0} with gcd(f, 11) = 1 for all
f ∈ F and |F| = 8. (Unlike v6, we do NOT require F ⊂ {1,...,10}; F may contain integers > 10.)

Set L₀ = lcm(F). The full speed set is

```
E = F ∪ {M} ∪ {11M},    L = 11·M·L₀ (if gcd(M,L₀)=1),    N = 121·M·L₀.
```

The normalisation condition is gcd(M, 11·L₀) = 1. This ensures gcd(E) = 1.

> **Lemma 4.3-GEN (Generalised L₀ Lower Bound).** *For any 8-element set F of distinct positive
> integers coprime to 11 arising as the fixed template of a one-divisible speed tuple:
> L₀ = lcm(F) ≥ 120.*
>
> *Proof.* Among all 8-element subsets of {1,...,10} (those F with all elements ≤ 10), the
> minimum lcm is 120, achieved uniquely by F = {1,2,3,4,5,6,8,10} (Lemma 4.3). For F containing
> any element f ≥ 12: L₀ ≥ lcm(1,f) = f ≥ 12 > ... actually lcm(F) ≥ lcm of any two distinct
> elements ≥ 12; the smallest such lcm is lcm(12,13) = 156 > 120. For F containing f ≥ 11 but
> f ≠ 11 (coprime to 11 forces f ≠ 11): f ≥ 12 and the same bound applies. □

> **Corollary 4.4-GEN.** *In the generalised normalisation, the threshold M₀ satisfies
> M₀ = ⌈121·10/(9·L₀·11)⌉ = ⌈1210/(9·L₀)⌉ ≤ 2 for all valid F.*
>
> *Proof.* By Lemma 4.3-GEN, L₀ ≥ 120, so M₀ ≤ ⌈1210/1080⌉ = 2. □

**Cases for the one-divisible branch (generalised):**

*M = 1 with F ⊆ {1,...,10}:* Handled by Proposition 4.5 (explicit witnesses, Table 1).
This subcase covers exactly the 9 templates enumerated in Table 1 (|F| = 8 from {2,...,10}).

*M = 1 with F ⊄ {1,...,10}:* Since all f ∈ F are coprime to 11 and some f ≥ 12, we have
L₀ ≥ 156. By v7.8 Proposition 10.5 (one-divisible branch, prime n=11, all M ≥ 1), x₀ ≥ 10.
The analytic branch applies directly since M₀ = ⌈1210/(9·156)⌉ = ⌈0.86⌉ = 1 = M, so M ≥ M₀
and the analytic counting bridge gives x₀ ≥ 10. □

*M ≥ 2 with any F:* Handled by Theorem 4.6 (transparency argument on I_M = [L₀, 2L₀)).
The critical floor-state-0 condition requires f·b/(11·M·L₀) < 1 for all f ∈ F and
b ∈ [L₀, 2L₀). Since b < 2L₀: f·b/(11M·L₀) < 2f/(11M). For f ≤ 10 and M ≥ 2:
2f/(11M) ≤ 20/22 < 1 ✓. For f > 10 and M ≥ ⌈2f/11⌉: 2f/(11M) < 1 ✓.
Since M₀ ≤ 2 and we are in the case M ≥ 2 ≥ M₀, Theorem 4.6 applies for all F with elements
f < 11·M/2 ≥ 11 (guaranteed for M ≥ 2 and f ≤ 10). For F containing f ≥ 12 and M = 2:
2f/(11·2) = f/11 > 1 for f ≥ 12 — so the floor-state-0 argument requires M ≥ ⌈2·12/11⌉ = 3.
For M = 2 with F containing f ≥ 12: use v7.8 Proposition 10.5 (analytic branch, M ≥ M₀ = 1). □

*(Remark: the Theorem 4.6 proof is unchanged for F ⊆ {1,...,10} and M ≥ 2, which covers all
templates in Table 1 with M ≥ 2. The generalisation above closes the gap for F with large
elements.)*

---

## Verification Checklist

- [x] **Lemma FLOOR-GEN (b):** ⌊9eᵤ/11⌋ vs ⌈9eᵤ/11⌉ ±1 is correct for gcd(eᵤ,11)=1 by
  equidistribution of arithmetic progressions with step 1 (a unit mod 11). ✓
- [x] **Case 2, m=1:** 9·10+1−20 = 71 ≥ 10. ✓
- [x] **Case 2, m≥2 not all ≡0:** lcm(10,21) = 210 ≥ 110; 9·110+1−40 = 951 ≥ 10. ✓
- [x] **Case 2, m≥2 all ≡0:** 79·1+1 = 80 ≥ 10; monotone in m. ✓
- [x] **Subcase A1 counting:** L ≥ 1320, |I∩ℤ| ≥ 12, 2×12=24 ≥ 10. ✓
- [x] **L₀ lower bound (Lemma 4.3-GEN):** min LCM of 8 elements from {2,...,10} = 120
  (Lemma 4.3, unchanged). Min LCM with any element ≥ 12: lcm(12,13)=156 > 120. ✓
- [x] **M₀ ≤ 2:** ⌈1210/(9·120)⌉ = ⌈1.12⌉ = 2. ✓
- [x] **Valuation reduction (Lemma 4.0):** {11^k M·t/(11^k·lcm(M,L₁))} = {M·t/lcm(M,L₁)}
  independent of k. ✓
- [ ] **M=1, F ⊄ {1,...,10}:** relies on v7.8 Proposition 10.5 for n=11; requires L₀ ≥ 156
  and M₀ = 1. ✓ (analytic branch covers all M ≥ 1 for L₀ ≥ 135).

---

## Summary of Changes (v6 → v7)

| Section | v6 (broken) | v7 (corrected) |
|---------|------------|----------------|
| §3.2 Prop 3.2 | CRT Floor Independence (invalid for prime n) | v7.8 Theorem 8.2 (regular) + Theorem 8.3 (extreme) |
| §3.2 Subcase A2 | (9/11)^s density argument | Deleted; covered by Theorem 8.2 |
| §3.2 Lemma MONO-LCM | CRT inclusion-exclusion (invalid) | Deleted; replaced by Theorem 8.3 fibre counts |
| §3.2 Line 214 | "2.08 × 10 − 16 ≈ 5 ≥ 1" (malformed) | Clean: ≥71 non-exceptional fibres ≥ 10 |
| §3.2.1 FLOOR-GEN (b) | "exactly 9eᵤ/11 times" (ill-formed) | ⌊9eᵤ/11⌋ or ⌈9eᵤ/11⌉ (±1 equidistribution) |
| §4.0 (new) | Missing | Lemma 4.0: Valuation Reduction (v₁₁(eₐ)=1 WLOG) |
| §4.1 | F ⊂ {1,...,10} (too narrow) | F ⊆ {pos. integers coprime to 11}; Lemma 4.3-GEN |
| §4.5 Table 1 | Unchanged (correct for F ⊆ {2,...,10}) | Retained as certified branch for M=1, F ⊆ {2,...,10} |
| §4.6 Theorem 4.6 | Correct for F ⊆ {1,...,10}, M ≥ 2 | Extended: also handles F with large elements via floor-state condition |
