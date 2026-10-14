# Bridge Scratch: Resolution & Draft Action Items
**Date:** 2026-05-21  
**Purpose:** (1) Show the Bridge theorem is not needed; (2) document the correct
proofs of LR, DI, DI-MOD; (3) list every edit required in lrc_proof_v11_draft.md.

---

## 1. The Bridge theorem is unnecessary

### 1.1 What Bridge was meant to do

The draft defined Bridge as: if ∃j with V/(n-1) ≤ v_j ≤ (n-1)v_1, produce a
good time.  The naive construction t* = 1/(nv_j) makes all fast runners (≥ v_j)
good, but makes slow runners (< v_j) bad: v_i t* = v_i/(nv_j) < 1/n.  So the
naive construction fails for the slow group.

### 1.2 Why it is not needed

The "bridge runner" v_j (if it exists) is just another slow runner.  The hard
case is:

    V > (n-1)v_1  and  V ≤ (n-1)v_{n-2}.

Within this range, the largest prime p of V either:
  (a) is coprime to every slow runner → Theorem DI applies to the full set
      {v_1,...,v_{n-2},V}, regardless of whether some v_j sits in [V/(n-1),(n-1)v_1].
  (b) divides some slow runner → Theorem DI-MOD applies similarly.

Cases (a) and (b) are exhaustive.  The Bridge condition is a property of the
*speed magnitudes*, not of the prime structure of V.  DI and DI-MOD care only
about the prime structure of V relative to the slow runners.  A "bridge runner"
v_j with V/(n-1) ≤ v_j ≤ (n-1)v_1 is handled seamlessly inside DI or DI-MOD:
p either divides v_j or it does not, and the proof proceeds exactly as before.

**Conclusion: §8 (Bridge) is eliminated.  EXH-1 reduces to three cases: BSR |
LR | hard case.  The hard case is fully covered by DI and DI-MOD.**

---

## 2. Corrected proof of Theorem LR

### 2.1 The bug in the current draft

Step 3 of the draft LR proof states:

> "Since each bad interval of V has width 2/(nV) < 2δ = |I|, the interval I
> cannot be entirely contained in any single bad interval of V.  Therefore I
> must contain a point of G_V."

The first sentence is correct.  The second is **wrong**.  I could be covered
by the *union* of multiple bad intervals even if no single bad interval covers
it.  The argument shows only that |I| > (width of one bad component), which
is necessary but not sufficient to guarantee I ∩ G_V ≠ ∅.

### 2.2 The correct argument: uniform density

G_V = {t : ‖Vt‖ ≥ 1/n} is periodic with period 1/V.  In each period [k/V,
(k+1)/V), the good sub-interval [( k+1/n)/V, (k+(n-1)/n)/V] has length
(n-2)/(nV).  Hence the density of G_V is exactly (n-2)/n in every sub-interval
of ℝ, regardless of length:

    μ(G_V ∩ [a,b]) = (b-a)·(n-2)/n    for every a < b.         (★)

This follows directly from the fact that 1_{G_V}(t) is a periodic step function
with period 1/V and mean (n-2)/n, and the Riemann integral of such a function
over any interval [a,b] equals (b-a)·(mean).

**Proof of LR (corrected Step 3):**

    μ(G_V ∩ I) = |I| · (n-2)/n = 2δ · (n-2)/n > 0    (since δ > 0, n ≥ 3).

Hence G_V ∩ I ≠ ∅.  Combined with I ⊆ G_s (Step 2), we get G_s ∩ G_V ≠ ∅.  □

Note: this argument requires only δ > 0 (which comes from PM-MEAS) and n ≥ 3;
it does NOT require comparing δ with 1/V.  The condition V > (n-1)v_{n-2} is
still needed — it is used to obtain the specific δ = 1/(n(n-1)v_{n-2}) from
PM-MEAS.  Actually, PM-MEAS gives δ > 0 for any n ≥ 3 regardless of V; the LR
condition does not appear in the corrected Step 3 at all.

Wait — where does V > (n-1)v_{n-2} enter?  Re-examine: PM-MEAS is applied to
the n-2 slow runners using H(n-1); it gives δ ≥ 1/(n(n-1)v_{n-2}) > 0 always.
The LR condition V > (n-1)v_{n-2} is NOT needed for the corrected step 3.

So: **Theorem LR holds for ALL V** (not just V > (n-1)v_{n-2}).

But then what use is the LR condition?  Answer: LR is not needed as a separate
theorem at all!  The uniform-density argument shows G_s ∩ G_V ≠ ∅ whenever G_s
has positive measure — which is given by PM-MEAS from H(n-1).  But this would
prove LRC(n) directly from LRC(n-1) with no induction on V — something that
cannot be right, because we have NOT handled the condition on V (the V-runner's
good set G_V is always non-empty with density (n-2)/n, but G_s might be empty
if the slow runners' constraints are not satisfied for the inductive level).

Ah — the issue is that G_s depends on the *threshold* 1/n for the slow runners
(for the n-runner problem), while PM-MEAS invokes H(n-1) which gives threshold
1/(n-1) for the (n-1)-runner sub-problem on the n-2 slow runners.  So G_s is
well-defined and PM-MEAS applies unconditionally.

**So the uniform density argument actually gives:**

    G_s ∩ G_V ≠ ∅  always (for any V, any slow runners),

provided only that G_s has positive measure.  But PM-MEAS gives μ(G_s) > 0 for
any n ≥ 3, any slow runners, from H(n-1).  So:

**Observation: BSR, LR, and Bridge are ALL unnecessary.**  PM-MEAS + uniform
density gives G_s ∩ G_V ≠ ∅ directly, without any case split on V.

But this can't be right as a complete proof — we have only handled the case
where V is arbitrary but the slow runners are given.  What about the condition
on V itself as a runner?  Let me re-examine.

G_s = {t : ‖v_j t‖ ≥ 1/n  ∀j = 1,...,n-2}.  (Threshold 1/n, n-runner problem.)
G_V = {t : ‖Vt‖ ≥ 1/n}.                      (Threshold 1/n, n-runner problem.)

PM-MEAS: μ(G_s) > 0  (from H(n-1), applying LRC(n-1) to n-2 slow runners;
gives threshold 1/(n-1) > 1/n, so open neighbourhood of width δ > 0).

Uniform density: μ(G_V ∩ I) = |I|·(n-2)/n > 0 for any interval I ⊆ G_s.

Therefore G_s ∩ G_V ≠ ∅.  This is valid for ALL V and proves LRC(n) from
H(n-1) alone — no condition on V, no DI, no DI-MOD, no BSR!

But wait — THIS IS JUST THE STANDARD INDUCTION!  If LRC(n-1) → LRC(n) directly
via this argument, then LRC holds for all n by induction on n, with no secondary
induction on V needed at all.

Is this correct?  Let me verify for n=3:

n=3, slow runners = {v_1}.  H(2): LRC(2) holds for 1 runner: ∃t with ‖v_1 t‖ ≥ 1/2.
G_s = {t : ‖v_1 t‖ ≥ 1/3}.  PM-MEAS: from H(2), t** with ‖v_1 t**‖ ≥ 1/2 > 1/3.
Neighbourhood I = (t**-δ, t**+δ) ⊆ G_s with δ = 1/(3·2·v_1) = 1/(6v_1).
G_V = {t : ‖Vt‖ ≥ 1/3}, density 1/3 in every period.
μ(G_V ∩ I) = 2δ · (1/3) > 0.  Done.

This works!  And it IS correct.  Let me think about whether this invalidates all
of DI and DI-MOD.

**Key question: Is LRC(n-1) → LRC(n) provable by PM-MEAS + uniform density?**

YES.  The argument:
1. PM-MEAS from H(n-1): G_s has positive measure; contains open interval I.
2. G_V has density (n-2)/n in every interval.
3. μ(G_V ∩ I) = |I| · (n-2)/n > 0.
4. ∃t ∈ G_s ∩ G_V.  Done.

This is a COMPLETE PROOF of LRC(n) from LRC(n-1), for all n ≥ 3!

**Wait — is this actually correct?  This seems too simple.**

Let me double-check step 2.  G_V = {t : ‖Vt‖ ≥ 1/n} for INTEGER V.  This IS
a periodic set with period 1/V and density (n-2)/n.  Step 2 is valid.

Step 3: μ(G_V ∩ I) = |I| · (n-2)/n.  For this to be valid, I needs to be any
interval (not necessarily a full period).  The uniform density formula (★)
above is valid for ANY interval [a,b] because:

    μ(G_V ∩ [a,b]) = ∫_a^b 1_{G_V}(t) dt.

The function 1_{G_V}(t) is periodic with period 1/V and integral (n-2)/(nV)
per period.  For the integral over [a,b]:

    ∫_a^b 1_{G_V}(t) dt  = ?

This equals (b-a)·(n-2)/n ONLY if either:
  - b-a is an integer multiple of 1/V (full periods), OR
  - we can use the fact that the partial-period contribution is exactly
    (fractional period) · (density within that fraction).

For a general interval [a,b] NOT aligned with the period, the integral is
NOT exactly (b-a)·(n-2)/n.  It equals (b-a)·(n-2)/n plus a correction term
that depends on the phase alignment of [a,b] with the period 1/V.

For example: n=3, V=4.  G_V has period 1/4 with good sub-intervals
[1/12, 2/12] and [3/12+1/12, 3/12+2/12] = ... let me compute.

Good set for V=4, n=3: {t : {4t} ∈ [1/3, 2/3]}.
Per period [0,1/4]: good sub-interval [1/12, 2/12] = [1/12, 1/6].  Length 1/12.
Period = 1/4.  Density = (1/12)/(1/4) = 1/3 = (n-2)/n ✓.

Now take interval I = [1/12 + ε, 1/6 - ε] (inside one good sub-interval).
μ(G_V ∩ I) = |I| = 1/12 - 2ε.  And |I| · (n-2)/n = (1/12 - 2ε) · 1/3 ≠ |I|.
So the formula μ(G_V ∩ I) = |I|·(n-2)/n is WRONG here.

In this case, I is entirely inside G_V, so μ(G_V ∩ I) = |I| > |I|·(1/3).

What if I = [1/6 + ε, 1/6 + ε + δ] (inside the bad sub-interval [1/6, 1/4])?
Then μ(G_V ∩ I) = 0 < |I|·(1/3).

So the formula μ(G_V ∩ I) = |I|·(n-2)/n is NOT an equality — it's just the
Cesàro mean.  It holds in the limit as |I|→∞ but not for every finite interval.

**This means the "uniform density" argument (★) is WRONG as stated.**  The
correct statement is that the AVERAGE density of G_V over long intervals equals
(n-2)/n, but for a specific short interval I, the density could be 0 (if I
falls entirely inside a bad sub-interval of V).

So the simple PM-MEAS + density argument does NOT directly give G_s ∩ G_V ≠ ∅
for an arbitrary short interval I.  The interval I from PM-MEAS has a specific
location (near t**), and G_V might happen to be zero in I.

**The earlier "LR proof" draft analysis was therefore wrong (or only approximate).
The corrected LR proof must compare |I| with the PERIOD of V (or use a different
argument).**

Let me re-examine the correct LR proof.

### 2.3 The actually correct LR argument

**Given**: I ⊂ G_s has length |I| = 2δ = 2/(n(n-1)v_{n-2}).
**LR hypothesis**: V > (n-1)v_{n-2}, so 1/V < 1/((n-1)v_{n-2}).

The period of G_V is 1/V.  The bad sub-intervals of G_V have length 2/(nV).
The good sub-intervals have length (n-2)/(nV).

**Claim**: |I| ≥ 1/V.  Proof: |I| = 2/(n(n-1)v_{n-2}) and 1/V < 1/((n-1)v_{n-2}).
Is |I| ≥ 1/V?  i.e., 2/(n(n-1)v_{n-2}) ≥ 1/V, i.e., 2V ≥ n(n-1)v_{n-2}.
Since V > (n-1)v_{n-2}: 2V > 2(n-1)v_{n-2}.  Is 2(n-1)v_{n-2} ≥ n(n-1)v_{n-2}?
Only if 2 ≥ n, i.e., n ≤ 2.  **FALSE for n ≥ 3.**

So |I| < 1/V is possible.  The window might be shorter than a full period of V.

**Alternative**: Show |I| > (length of bad sub-interval of G_V) = 2/(nV).

|I| = 2/(n(n-1)v_{n-2}) vs 2/(nV).  Since V > (n-1)v_{n-2}: V/(n-1)v_{n-2} > 1,
so 1/((n-1)v_{n-2}) > 1/V, hence |I| = 2/(n(n-1)v_{n-2}) > 2/(nV).  ✓

So |I| > (bad sub-interval width).  This means I cannot be entirely contained in
a single bad component of G_V.  But I COULD be covered by two adjacent bad
components (skipping the good gap between them) IF the good gap is smaller than |I|.

The good gap between consecutive bad components is (n-2)/(nV).  The bad component
width is 2/(nV).  Two consecutive bad components span 2/(nV) + (n-2)/(nV) + 2/(nV)
= (n+2)/(nV) in total (start of first to end of second).

For I (length |I| = 2/(n(n-1)v_{n-2})) to fit ENTIRELY INSIDE the union of two
consecutive bad components (i.e., to straddle the good gap), I would need to
start inside the first bad component and end inside the second bad component,
covering neither good gap's endpoint.  The gap between consecutive bad components'
starts is 1/V.  For I to straddle the gap without intersecting any good point,
I must start in the first bad component and end in the second bad component, i.e.:
  - I ⊆ (first bad component) ∪ (second bad component)
  - I ∩ good gap = ∅

The good gap = [k/V + 1/(nV), (k+1)/V - 1/(nV)] has width (n-2)/(nV).
For I to miss the good gap entirely, I must either end before the gap starts
(i.e., I is entirely in the first bad component — but we showed |I| > 2/(nV),
so I can't fit in one bad component) OR start after the gap ends (entirely in
second bad component — same argument, contradicts |I| > 2/(nV)).

Wait, I claim: if |I| > bad-component width = 2/(nV), then I must extend past
the end of any bad component it starts in.  So if I starts in the first bad
component, it extends into the good gap or the second bad component.  If it
extends into the good gap, it intersects the good gap → G_V ∩ I ≠ ∅.  Done.

If I starts in the first bad component and ends AFTER the good gap (in the second
bad component), then I must CROSS THE GOOD GAP → G_V ∩ I ≠ ∅.  Done.

So: any interval I of length > 2/(nV) (the bad component width) that starts
in a bad component must cross EITHER the following good gap OR pass through it.
Either way, I ∩ G_V ≠ ∅.

What if I starts in a good gap?  Then I ∩ G_V ≠ ∅ trivially (I contains its
start point which is in G_V).

**Conclusion**: Any interval I with |I| > 2/(nV) satisfies I ∩ G_V ≠ ∅.

And the LR condition V > (n-1)v_{n-2} gives exactly:
  2/(nV) < 2/(n(n-1)v_{n-2}) = |I|,

i.e., |I| > (bad component width).  ✓

**So the ORIGINAL draft logic was correct for the right reason** — but the
statement "I cannot fit in a single bad interval → I intersects G_V" needs to
be replaced by the cleaner:

> If |I| > (bad component width), then any sub-interval of I of length
> (bad component width) + ε must either start outside all bad components
> or cross a bad component boundary.  An interval starting in a bad component
> of width W < |I| must extend past that component into the good region or into
> the next bad component, which it can only reach by crossing the good gap.

The rigorous version: Let [a, a+|I|] = I.  Let J = [k/V-1/(nV), k/V+1/(nV)]
be any bad component with J ∩ I ≠ ∅.  Since |I| > 2/(nV) = |J|:
  - If a < k/V - 1/(nV): a ∈ I is not in J, and (k/V - 1/(nV)) ∈ J ∩ I; but
    there exist points in I before J → some of these are in G_V (the interval
    [a, k/V-1/(nV)) ⊆ G_V ∩ I).  Done.
  - If a ≥ k/V - 1/(nV) (I starts inside J): then a + |I| ≥ k/V - 1/(nV) + |I|
    > k/V - 1/(nV) + 2/(nV) = k/V + 1/(nV) = right endpoint of J.  So I extends
    past J.  The point k/V + 1/(nV) ∈ I is the right endpoint of J; any point
    in I ∩ (k/V + 1/(nV), k/V + 1/(nV) + ε) for small ε > 0 is in G_V.  ✓

This covers all cases.  **The correct draft argument should be:**

> Since |I| = 2δ > 2/(nV) (from the LR condition V > (n-1)v_{n-2}), I is
> longer than any single connected component of B_V = G_V^c.  Therefore I
> cannot be contained in any single bad component.  In particular, either I
> contains a point of G_V directly (if I starts in G_V), or I starts in a bad
> component and must extend past it (since |I| > bad component width) into a
> point of G_V.  In either case, G_V ∩ I ≠ ∅.

This is the correct reasoning.  The earlier draft statement was morally right
but logically incomplete (it said "can't fit in one bad interval → must
intersect G_V", which is the correct deduction — it just needed the above
case analysis to make it rigorous).

---

## 3. Corrected proof of Theorem DI

### 3.1 The bug

The current draft (Step 1) defines:
    G' = {t : ‖v_j t‖ ≥ 1/n ∀j ≤ n-2, ‖qt‖ ≥ 1/n}

and uses secondary induction H(n,q) to show G' ≠ ∅.  Then in Step 4, it
applies W-INT with period lcm(v_1,...,v_{n-2},q) = M.  The coprimality
check requires gcd(p,M)=1, i.e., p ∤ q.  But if p²|V, then q = V/p is
divisible by p, so gcd(p,q)=p≠1 and the check fails.

The draft "resolves" this by recursion (apply the theorem again with V→q),
but this creates a non-trivial secondary induction that needs careful
justification.

### 3.2 The clean fix

Do NOT include q in the good set G_s.  Use only:

    G_s = {t : ‖v_j t‖ ≥ 1/n ∀j = 1,...,n-2}.

This is the good set for the slow runners alone.  Its period is
L = lcm(v_1,...,v_{n-2}).  By the LR hypothesis:

  gcd(p, L) = 1  (from the DI hypothesis: p ∤ v_j for all j=1,...,n-2).

Define A = {φ ∈ [0,1) : ‖qφ‖ ≥ 1/n}.  By Lemma FI:
  {Vt} = {pqt} = {q · {pt}}  (FI with a=q, b=p).
So ‖Vt‖ ≥ 1/n  iff  {pt} ∈ A.

μ(G_s) > 0: from PM-MEAS (H(n-1) → G_s has positive measure). ✓
μ(A) = (n-2)/n > 0 (A is the good set for a single runner q, threshold 1/n). ✓
gcd(p, L) = 1. ✓

By W-INT: ∃t₀ ∈ G_s with {pt₀} ∈ A.

Check:
  - ‖v_j t₀‖ ≥ 1/n for j = 1,...,n-2: from t₀ ∈ G_s. ✓
  - ‖Vt₀‖ = ‖q{pt₀}‖ ≥ 1/n: since {pt₀} ∈ A. ✓  (by FI-NORM)

No secondary induction H(n,q) needed at all.  No p²|V sub-case.

**Note on secondary induction**: the double-induction structure (primary on n,
secondary on V) remains in the proof as a whole (DI-MOD uses H(r+2) which is
primary), but DI itself uses only:
  - H(n-1) for PM-MEAS (primary induction)
  - No secondary induction
  - No invocation of any H(n,q)

---

## 4. Corrected proof of DI-MOD

### 4.1 The bug

Step 3 of the current draft claims: gcd(p,q)=1 "since p is the largest prime
of V=pq".  This is FALSE when p²|V: then q=V/p and p|q.

The bug arises because G_ind includes q as a runner, forcing the period of
G_ind to include q, and then gcd(p,q)=1 is needed for W-INT.

### 4.2 The clean fix

Remove q from G_ind.  Define:

    G_ind = {t : ‖v_j t‖ ≥ 1/n  for all j ∈ S_ind},

where S_ind = {v_j : p ∤ v_j} (the slow runners NOT divisible by p).

Period of G_ind: L_ind = lcm(v_j : j ∈ S_ind).
gcd(p, L_ind) = 1: since p ∤ v_j for all j ∈ S_ind.  ✓ (by definition of S_ind)
No gcd(p,q)=1 needed.

The target set A = {φ : ‖w_k φ‖ ≥ 1/n ∀k = 1,...,r  AND  ‖qφ‖ ≥ 1/n}
includes q (q is in A because we need ‖Vt₀‖ = ‖q{pt₀}‖ ≥ 1/n).

μ(G_ind) > 0: PM-MEAS applied to S_ind using H(|S_ind|+1) (primary induction,
since |S_ind|+1 = n-1-r ≤ n-2 < n). ✓
μ(A) > 0: A is the good set for {w_1,...,w_r,q} with threshold 1/n.  Apply
H(r+2) (primary induction, since r+2 ≤ n-1 < n by EXH-3).  PM-MEAS gives
strict inequality 1/(r+2) > 1/n, so A has positive measure. ✓

W-INT: gcd(p, L_ind) = 1. ✓

Verification:
  - j ∈ S_ind: ‖v_j t₀‖ ≥ 1/n from t₀ ∈ G_ind. ✓
  - v_{j_k} = pw_k: {v_{j_k}t₀} = {pw_k t₀} = {w_k·{pt₀}} (FI, a=w_k, b=p)
                   → ‖v_{j_k}t₀‖ = ‖w_k φ₀‖ ≥ 1/n since φ₀ ∈ A. ✓
  - V = pq: {Vt₀} = {pqt₀} = {q·{pt₀}} (FI, a=q, b=p)
           → ‖Vt₀‖ = ‖qφ₀‖ ≥ 1/n since φ₀ ∈ A. ✓

Note: the condition on q (‖qt₀‖ ≥ 1/n) is NOT used — q is not an original
runner.  The only q-condition needed is ‖qφ₀‖ ≥ 1/n (φ₀ = {pt₀} ∈ A). ✓

---

## 5. Action list for lrc_proof_v11_draft.md

The following surgical edits are required (in section order):

| # | Section | Edit |
|---|---------|------|
| 1 | §4 PM-MEAS remark | Remove mention of Bridge theorem (§8) |
| 2 | §7 LR Step 3 | Replace faulty one-liner with rigorous interval argument |
| 3 | §8 Bridge | Replace entire theorem with a remark explaining elimination |
| 4 | §9 EXH-1 | Remove Bridge from case list; simplify to BSR | LR | hard case |
| 5 | §10 DI | Rewrite proof: use G_s alone (no G', no H(n,q)), fix FI direction, remove p²|V sub-case |
| 6 | §11 DI-MOD Step 1 | Remove q from G_ind; use S_ind only |
| 7 | §11 DI-MOD Step 3 | Replace gcd(p,q)=1 claim with gcd(p,L_ind)=1 by definition |
| 8 | §12 Main | Remove Bridge from case list |
| 9 | Audit table | Update all statuses; mark §7,§10,§11 CLEAN; §8 ELIMINATED |

---

## 6. Summary of proof architecture (post-fixes)

PRIMARY induction on n (base n=3).  Within each n, no secondary induction is
needed in the BSR/LR/DI theorems.  DI-MOD uses primary induction H(r+2) and
H(|S_ind|+1), both with strictly smaller indices.

The secondary induction on V (mentioned in §2.5) is a *structural* description
but not used in BSR, LR, or DI.  In DI-MOD it reduces through the prime
factorisation: the instance H(r+2) is applied to {w_1,...,w_r,q} which are
smaller values.  The secondary induction terminates naturally.

Actually, re-examine: does DI-MOD invoke H(n,q) at any point?  No — it uses:
  - H(|S_ind|+1) for G_ind: |S_ind|+1 ≤ n-1 (primary). ✓
  - H(r+2) for A: r+2 ≤ n-1 (primary). ✓
No secondary induction on V.

Therefore the double induction statement in §2.5 is overstated — primary
induction on n suffices.  The secondary induction on V should be downgraded
to "used for context only" or removed.

**Final proof outline (clean):**

1. Normalise: integer speeds, gcd=1.
2. Induction on n. Base: n=3 (direct).
3. For n ≥ 4, given H(m) for all m < n:
   - PM-MEAS: H(n-1) → G_s has positive measure (contains interval I).
   - LR argument: |I| > bad-component width of G_V → G_s ∩ G_V ≠ ∅.

Wait — but this says LRC(n) follows from LRC(n-1) for ALL V, not just large V.
The LR argument works because |I| > 2/(nV) iff V > (n-1)v_{n-2}.  For small V
(V ≤ (n-1)v_{n-2}), |I| ≤ 2/(nV), and the LR argument fails.

So the case split IS needed: for large V use LR; for small V use BSR (explicit
construction); for intermediate V use DI/DI-MOD.  The clean partition is:

  Case A (BSR): V ≤ (n-1)v_1.  Explicit t* = 1/(nv_1).
  Case B (LR): V > (n-1)v_{n-2}.  Interval argument (|I| > bad-width of G_V).
  Case C (hard): (n-1)v_1 < V ≤ (n-1)v_{n-2}.
    Sub-case C1 (DI): gcd(p, lcm(slow)) = 1.  Weyl on G_s.
    Sub-case C2 (DI-MOD): p | v_{j₀} for some j₀.  Weyl on G_ind with A.

This is the correct, complete, clean partition.  No Bridge theorem.

---

*File status: complete.  Apply the 9 edits above to lrc_proof_v11_draft.md.*
