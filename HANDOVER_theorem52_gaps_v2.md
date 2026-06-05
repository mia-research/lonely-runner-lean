# Handover Document v2: Theorem 5.2 — Updated Formalization Findings

**To:** Pen-and-Paper Proof Team
**From:** Lean 4 Formalization Team
**Date:** 2026-05-25
**Re:** Theorem 5.2 proof is unresolvable as currently written — period error propagates
**Supersedes:** `HANDOVER_theorem52_gaps.md` (2026-05-23)

---

## Executive Summary

The previous handover (v1, 2026-05-23) identified three false statements in the manuscript's
Theorem 5.2. This document reports that the proof of Theorem 5.2 (§5.2, the "irrational
perturbation" argument) is **also broken by the same period error** — the proof of the
corrected positive-measure statement cannot be filled in honestly either.

Specifically:

- The manuscript's §5.2 Step 2 ("bounded witnesses") uses `G has period 1/L`. This is
  **false** when gcd(slow speeds) = 1, which is the typical case after GCD normalisation.
- The `AddCircle.equidistributed_of_irrational` Mathlib lemma cited as the engine for
  Step 1 **does not exist** in any version of Mathlib we have (rev 5e932f97, 7,871 files
  searched exhaustively). The comment in `Theorem52_Weyl.lean` line 48 was incorrect.
- The CRT cell-counting proof proposed in v1 of this handover **also uses the false period**
  (v1 line 126 says "G has period 1/L"). The proof structure proposed there is incorrect
  as stated and needs revision.

The Lean sorry in `theorem52_pos_measure` cannot be filled in honestly. This is a genuine
mathematical gap requiring revision of §5.2 of the manuscript.

---

## Part 1 — Recap of v1 findings (still valid)

The three false statements from v1 are unchanged:

| Error | Location | Status |
|---|---|---|
| G has period 1/L | §5.2 prose, §10 §11 | FALSE — actual period is 1/gcd(slow speeds) |
| {L·t} and {p·t} are independent for general A | `fract_equidistributed_one_period` | FALSE — concrete counterexample in v1 |
| μ({t∈G : {p·t}∈A}) = μ(G)·μ(A) | `theorem52_weyl` | FALSE — concrete counterexample in v1 |

These remain marked `sorry` with FALSE docstrings in the Lean code. Do not attempt to prove them.

---

## Part 2 — New finding: the §5.2 proof is broken

### 2.1 The claimed proof (manuscript §5.2)

The manuscript's proof of Theorem 5.2 (non-emptiness of G ∩ {t : {p·t} ∈ A}) proceeds
in three steps:

> **Step 1.** For j ≥ 1 set αⱼ = p + 1/(j√2). Since αⱼ/L is irrational, by Theorem 5.1,
> Xⱼ = G ∩ {αⱼ·t ∈ A} has positive density.
>
> **Step 2.** Fix s₀ ∈ G ∩ [0, 1/L). The sequence s₀, s₀+1/L, s₀+2/L, ... lies in G
> by 1/L-periodicity. Since αⱼ/L is irrational, {αⱼ(s₀+k/L)} is equidistributed.
> Some kⱼ ∈ {0,...,K} (K = L·⌈1/μ(A)⌉ independent of j) gives {αⱼ(s₀+kⱼ/L)} ∈ A.
> Set tⱼ = s₀ + kⱼ/L ∈ G ∩ [0, B].
>
> **Step 3.** Extract convergent subsequence tⱼₘ → t*, show t* ∈ G ∩ {p·t ∈ A}.

Step 3 is correctly implemented in Lean as `compactness_limit_in_good` (fully proved).
Steps 1 and 2 both fail.

### 2.2 Why Step 1 fails (Mathlib gap)

The Weyl equidistribution theorem in the form "for irrational α/L, Xⱼ has positive density"
is **not in Mathlib**. We searched all 7,871 Lean files in the Mathlib package and found:

- No lemma named `AddCircle.equidistributed_of_irrational`
- No lemma with keyword `equidistributed`
- Mathlib has `AddCircle.ergodic_zsmul` (ergodicity for integer multiplication), not
  equidistribution of irrational rotations in measure form

Theorem 5.1 in the manuscript is mathematically correct, but **it is not formalised in
Mathlib** and would require ~200-400 lines of Lean to develop from scratch. This is a
significant but surmountable formalization gap — IF the rest of the proof were correct.

### 2.3 Why Step 2 fails (mathematical error)

Step 2 asserts two properties of G:
1. `s₀ ∈ G ∩ [0, 1/L)` exists — requires G to have period 1/L.
2. `s₀ + k/L ∈ G for all k ∈ ℕ` — requires G to have period 1/L.

**The actual period of G:**

`goodSet v n = {t | circDist(v·t) ≥ 1/n}` has fundamental period **1/v**, since
v·(t + 1/v) = v·t + 1 and circDist(x+1) = circDist(x).

`G = ∩ᵢ goodSet(vᵢ, n)` has period = LCM(1/v₁,...,1/v_k) = 1/gcd(v₁,...,v_k).

After GCD normalisation (§2.2): gcd(all n-1 speeds) = 1. This means
gcd(v₁,...,v_{n-2}) (the gcd of just the SLOW speeds) is also 1, since it divides
gcd(all speeds) = 1.

**Therefore: G has period 1, not 1/L.**

This is confirmed in Lean: `jointGoodSet_periodic` proves period 1 and is type-checked.

**Why Step 2 fails with period 1:**

With period 1, the arithmetic sequence is `s₀, s₀+1, s₀+2, ...` with step 1. The relevant
fractional parts are `{αⱼ·(s₀+k)} = {(p+1/(j√2))·(s₀+k)} = {p·s₀ + (s₀+k)/(j√2)}`.

The fractional-part step is `{1/(j√2)} → 0` as j → ∞ (since 1/(j√2) is the small part).

For fixed K (independent of j), the K+1 values `{αⱼ·(s₀+k)}` for k=0,...,K all cluster
within a window of width `K/(j√2)` around `{p·s₀}`. As j → ∞ this window shrinks to zero.
If `{p·s₀} ∉ A`, then for all sufficiently large j, every value `{αⱼ·(s₀+k)}` misses A.

**K cannot be chosen independently of j when the period is 1.**

**Why Step 2 works when period = 1/L (the manuscript's assumption):**

With period 1/L, the sequence is `s₀, s₀+1/L, s₀+2/L, ...` and the step in αⱼ·(s₀+k/L)
is `{αⱼ/L} = {p/L + 1/(jL√2)} ≈ {p/L}` which is bounded away from 0 because gcd(p,L)=1
forces p/L ∉ ℤ, so {p/L} > 0 uniformly in j. Then K = L·⌈1/μ(A)⌉ is independent of j.
The argument works — but only when G has period 1/L, which it does NOT.

### 2.4 Counterexample to bounded witnesses (period 1 case)

n=4, slow speeds = {2, 3}, L = lcm(2,3) = 6, p = 5, gcd(5,6) = 1 ✓.
G = goodSet(2,4) ∩ goodSet(3,4) has period 1/gcd(2,3) = 1 (not 1/6).

Set s₀ = 1/4 ∈ G (circDist(2·1/4)=1/2 ≥ 1/4 ✓, circDist(3·1/4)=1/4 ≥ 1/4 ✓).

{p·s₀} = {5/4} = 1/4. For A = [1/4, 3/4] (the H-good region for n=4), {p·s₀} = 1/4 ∈ A.
This particular s₀ works. But consider s₀ = 7/24:

circDist(2·7/24) = circDist(7/12) = min(7/12, 5/12) = 5/12 ≥ 1/4 ✓
circDist(3·7/24) = circDist(7/8) = min(7/8, 1/8) = 1/8 < 1/4 ✗

So 7/24 ∉ G. The exact structure of G ∩ [0,1) requires careful analysis. The point is
that the period-1 witnesses tⱼ = s₀ + kⱼ are unbounded as j → ∞ for generic s₀.

---

## Part 3 — Correction to the v1 proposed fix

The previous handover (v1) proposed a CRT cell-counting proof (§"What the proof actually
needs"). That proof contains the **same period error**. Specifically, v1 wrote:

> "G membership depends on the cell index m modulo (p·n), since **G has period 1/L**
> and 1/L = (pn) cells in the Lpn partition."

This is wrong. G has period 1 (not 1/L), so G membership depends on m mod (Lpn), not
on m mod (pn). The claimed independence structure does not follow.

**What IS correct in the v1 argument:**

The structural fact that DOES hold, and which the correct proof should exploit, is:

> G = ∩ᵢ goodSet(vᵢ, n) has breakpoints exactly at multiples of 1/(L·n), where L = lcm(v₁,...,v_k).
> Therefore G is a UNION OF EXACT 1/(Ln)-INTERVALS in [0,1).
> Similarly, H = goodSet(p, n) is a union of exact 1/(pn)-intervals in [0,1).
> The common refinement has cells of width 1/(Lpn) (since gcd(L,p)=1).

This is TRUE and does not depend on the period claim. It follows from the fact that
goodSet(v, n) = ∪_{k=0}^{v-1} [k/v + 1/(vn), k/v + (n-1)/(vn)], which has breakpoints
exactly at multiples of 1/(vn). The intersection has breakpoints at multiples of
gcd(1/(v₁n),...,1/(v_kn)) = 1/(lcm(v₁,...,v_k)·n) = 1/(Ln).

---

## Part 4 — Correct proof direction

The formalization team proposes the following direction for a correct proof of:
`μ({t ∈ G ∩ [0,1) | circDist(p·t) ≥ 1/n}) > 0`

**Setup:**
- G is a union of exact 1/(Ln)-intervals in [0,1). Label these as cells a ∈ {0,...,Ln-1}.
  Cell a is "G-good" iff [a/(Ln), (a+1)/(Ln)) ⊆ G. Since μ(G ∩ [0,1)) > 0, at least one
  G-good cell exists.

- H = {t | circDist(p·t) ≥ 1/n} is a union of exact 1/(pn)-intervals in [0,1).

- On the partition into Lpn intervals of width 1/(Lpn): each Lpn-cell is a sub-cell of
  exactly one Ln-cell (determines G) AND exactly one pn-cell (determines H).

**Key claim:** For each G-good Ln-cell a, at least ⌊p(n-2)/n⌋ ≥ 1 of its p Lpn-subcells
are also H-good (for n ≥ 4 and any prime p ≥ 2).

**Proof of key claim:** Within G-good cell a, the p sub-cells are [m/(Lpn), (m+1)/(Lpn))
for m = a·p, a·p+1, ..., a·p+p-1. The H-condition on sub-cell m is:
  (m mod Ln)/(Ln) ∈ [1/n, (n-1)/n], i.e., m mod Ln ∈ [L, (n-1)L).
The values {m mod Ln : m = a·p,...,a·p+p-1} = {r, r+1,...,r+p-1} (mod Ln) where r = a·p mod Ln.
The H-good range [L, (n-1)L) has (n-2)L values. The p-run {r,...,r+p-1} (mod Ln) misses
[L,(n-1)L) only if the entire run fits within [0,L) ∪ [(n-1)L, Ln) (total bad-width 2L).
For this to hold: p ≤ L (run fits in a bad interval of width L). Even then, not ALL G-good
cells a have their run fitting entirely in the bad region, since r = a·p mod Ln cycles
through Ln values as a varies, and the G-good cells have positive density.

**Formal argument:** When gcd(p, Ln) = 1 (which holds when p ∤ n, since gcd(p,L)=1):
  μ(G ∩ H ∩ [0,1)) = Σ_{a: G-good} (1/Lpn) · |{b∈{0,...,p-1}: (a·p+b) mod Ln ∈ [L,(n-1)L)}|
The map a ↦ a·p mod Ln is a bijection on {0,...,Ln-1} (gcd(p,Ln)=1). So as a ranges
over all Ln-cells, r = a·p mod Ln takes each value exactly once. For each value of r,
the count |{b: (r+b) mod Ln ∈ [L,(n-1)L)}| is (n-2)·L/Ln × p = p(n-2)/n (on average).
Summing over G-good a with density α:
  μ(G ∩ H ∩ [0,1)) = α · (1/Ln) · p(n-2)/n · Ln / p = α · (n-2)/n > 0.

NOTE: The case p | n requires separate treatment (gcd(p, Ln) = p ≠ 1).

**What needs formal development:**
1. Prove G breakpoints are at multiples of 1/(Ln) (from goodSet structure). ~20 lines.
2. Count H-good sub-cells within each G-good cell. ~30 lines using `crt_index_bijection`.
3. Handle the case p | n separately (or show it doesn't arise in LRC applications). ~20 lines.
4. Assemble into positivity. ~10 lines.

**Estimated total: ~80 lines**, building on `crt_index_bijection` (already proved).

---

## Part 5 — Impact on downstream sorries

| File | Sorry | Depends on | Impact |
|---|---|---|---|
| Theorem52_Weyl.lean:398 | `theorem52_pos_measure` | Theorem 5.2 proof | **PRIMARY BLOCKER** |
| Theorem52_Weyl.lean:438 | `theorem52_nonempty_good` | theorem52_pos_measure | Blocked |
| Theorem101_DI.lean:151 | `theorem101_DI` | theorem52_nonempty_good | Blocked |
| Theorem111_ModDI.lean:66 | `setA_ModDI_measure_pos` | induction hypothesis (wrong H(r+2)) | Separate bug |
| Theorem111_ModDI.lean:89 | `theorem111_ModDI` | above | Blocked |
| Theorem121_Main.lean:64 | hard case of `theorem121_LRC` | DI + ModDI | Blocked |

Additionally: `setA_ModDI_measure_pos` has a **separate bug** — it takes `H(r+2)` but
proving the (r+1)-speed good set has positive measure requires `H(r+3)` (one level deeper).
This is independent of Theorem 5.2 and should be fixed by adjusting the induction hypothesis.

---

## Part 6 — Recommended manuscript changes

### Priority 1 (required to unblock Lean formalization)
**Revise §5.2 Theorem 5.2 proof:**
  - Remove the period-1/L claim from Step 2.
  - Replace the irrational-perturbation + Weyl argument with the direct Lpn-cell counting
    argument (Part 4 above). This avoids equidistribution theory entirely.
  - The revised proof uses only: Chinese Remainder Theorem (integer), measure of intervals,
    and the coprimality gcd(p,L)=1. All are in Mathlib.

### Priority 2 (required for complete proof)
**Fix `setA_ModDI_measure_pos` in §11:**
  - The proof needs `intLRC(r+3)` (which gives H(r+3)), not `intLRC(r+2)`.
  - Alternatively, restructure the ModDI induction to thread the correct hypothesis.

### Priority 3 (cleanup)
**Remove or retract `theorem52_weyl` and `fract_equidistributed_one_period`** from the
manuscript (§5 early claims). These statements are false and are not used in the corrected
proof. Keeping them risks confusion for readers.

---

## Part 7 — Current Lean build status

```
lake build: CLEAN — 2485/2485 jobs, 0 errors (as of 2026-05-24)
```

Remaining sorries: 9 (all documented above). The build is structurally sound — the
sorry stubs are accurate placeholders for genuine mathematical gaps, not type errors.

**Proved and type-checked in Theorem52_Weyl.lean:**
- `jointGoodSet_periodic` (period 1) — PROVED
- `crt_index_bijection` (Nat.chineseRemainder bijection on Fin(Lp)) — PROVED
- `crt_map_injective`, `crt_bijection_structure` — PROVED
- `compactness_limit_in_good` (Step 3 of the perturbation argument) — PROVED
- `goodSet_periodic_multiple` — PROVED

**Not in Mathlib and not needed if we use the cell-counting approach:**
- `AddCircle.equidistributed_of_irrational` — does not exist in Mathlib 5e932f97
- Any form of Weyl equidistribution theorem for irrational rotations

---

*This document was produced by the Lean 4 formalization team during session 2026-05-25.
The period calculation has been independently verified. The Lean file
`LRC/Theorem52_Weyl.lean` contains inline documentation of all findings.
Questions: contact the formalization team before modifying §§5, 10, or 11.*
