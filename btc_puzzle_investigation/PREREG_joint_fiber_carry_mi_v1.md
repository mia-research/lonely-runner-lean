# PREREG — Joint-Fiber → GLV Carry Mutual-Information Leakage Test (v1)

**Status: FROZEN pre-registration. No data seen. Do not edit after first data touch — bump to v2.**
Date frozen: 2026-08-13. Scope curve: secp256k1 (j=0, CM by Z[ω], p≡7 mod 12, n prime,
GLV λ³≡1 mod n, λ≡2 mod 3, β³≡1 mod p).

---

## 0. VERDICT ON THE PROPOSED PRIMARY STATISTIC — ILL-POSED

**Proposed:** `I( c ; (I₁,I₂) )`, c = ⌊d·λ^j / n⌋, from the single public point P=[d]G.

**Ruling: ILL-POSED. Not to be run as stated. Reasons (two, independent):**

1. **Estimation / power saturation.** c ranges over ~256 bits (0 ≤ c < λ ≈ n ≈ 2^256).
   No estimator of `I(c; ·)` from any feasible sample (N ≤ ~10^6) has resolving power: the
   plug-in MI estimator saturates at log₂N because every sampled key gives a *distinct* c and
   generically a *distinct* (I₁,I₂). A saturated estimator is **invariant under the matched
   shuffle** (real ≈ log₂N, shuffled ≈ log₂N), so z≈0 arises **by construction** — a false null
   with zero power. This is the cubic-moment-null failure mode (N=82 needing effect size f=1.0),
   re-instantiated at 256-bit target entropy.

2. **Tautology / DLP-equivalence.** (I₁,I₂)=g(P) is a deterministic *public* function of P=[d]G,
   and c is a deterministic function of d. P determines d **up to the DLP**; therefore
   H(c | I₁,I₂) is not a leakage measure. Any nonzero plug-in MI is either the log₂N saturation
   artifact of (1) or information **locked behind the DLP**, not sub-DLP extractable structure.
   A single-point joint-fiber statistic cannot separate "genuine sub-DLP leak" from "tautological
   determinism," so it cannot answer the question it is posed to answer. (Same family as the
   residue-vs-component r=v−w tautology, z=+5000, where the shuffle control does not expose it.)

**The pre-registration below is therefore of the REPAIRED, non-tautological two-key variant.**
The original statistic is graded **ILL-POSED (this document)**; no data is to be taken on it.

**Aside — I₂' = e₂ = e₁² − χ₂(−1)p excluded, one line:** e₁,e₂ are trace-of-Frobenius / zeta
invariants of the *curve* (functions of t=p+1−n, a single constant for fixed secp256k1); they have
**zero per-point variance ⇒ zero per-point discriminating power**. Excluded.

---

## THE REPAIRED TEST — cross-channel carry-leak (coordinate channel → scalar-carry channel)

### 1. OBJECT

Whether the **coordinate-channel** flap bit eps(x_P) — an exact integer function of the
x-coordinate **alone**, no d in its path (established, RESULT_linchpin_s_gate_v2.md) — predicts a
**scalar-channel** GLV coupling-carry bit ε(d), computed by a *disjoint* map (scalar arithmetic in
Z/n via λ), above the estimable floor. Neither map is computed from the other; a correlation would
be a genuine cross-ring leak, not a definitional identity.

Object is the **cross-channel dependence** between two disjoint public/secret-derived maps of the
same key, NOT a proxy. It is NOT the DLP; it is a decisional bit-predictivity question.

### 2. STATISTIC (exactly one primary)

**PRIMARY (targeted, df=1):**
`Î_prim = Î( ε ; b_eps )`, the plug-in mutual information (bits) of the coupling-carry bit
ε∈{0,1} against the flap-present indicator `b_eps = [ eps(x_P) ≠ 0 ]∈{0,1}`, from exact rational
counts on a 2×2 table. Aimed AT the μ₃-forced flap (the predicted structure), df=1 for power at
N=82 — deliberately NOT a max-over-cells (upward-biased, low power).

Distribution under H₀: the matched permutation distribution of Î_prim (Section 3). The float log is
used ONLY as a monotone scalar ranked against that null (never thresholded on data); the reported
p-value is the exact integer count `#{perm : Î_perm ≥ Î_prim} / #perm`.

**SECONDARY (pre-registered, weaker power, NOT verdict-driving):** the joint-fiber
`Î_sec = Î( ε ; Φ )`, Φ=(j, s_neg, eps) the 18-cell public discrete state (j∈{0,1,2} GLV orbit index
from I₁ phase; s_neg∈{0,1} negation parity from I₁ magnitude; eps∈{0,+,−}). Reported for the joint
question; df=17 ⇒ higher MI_min; ranked against the SAME null. It never overrides Î_prim.

### 3. MATCHED CONTROL (null)

**Null:** b_eps (resp. Φ) carries no information about ε beyond the forced μ₆/μ₃ + GLV symmetries.

**Construction — μ₆-canonicalized, orbit-deduplicated label permutation:**
- **Precondition (enforced before the test):** canonicalize each key to its μ₆-orbit representative
  (fold out the 6-fold GLV-orbit × negation symmetry: d ↦ canonical of {±λ^a d mod n : a∈{0,1,2}}),
  then **dedup** so no two retained keys share a GLV orbit or negation pair. Report the post-dedup N.
- **Null draws:** permute the target labels ε across the retained (deduped) keys; leave each key's
  b_eps / Φ **untouched**. Rank Î_real against ≥ 10^4 such permutations (exact for small N).

**What it preserves / destroys.** Preserves each key's per-point μ₃-forced eps value (the readout's
by-definition symmetry is never touched — this is exactly the fix for the "6–7σ soft-shadow"
null-mismatch, where a shuffle destroyed a by-definition symmetry). Preserves the eps marginal and
the ε Bernoulli marginal. Destroys ONLY the cross-key pairing between the two channels. Because keys
are deduped to one-per-orbit, permutation never re-injects within-orbit forcing → a "pass" cannot be
the forced symmetry reappearing. The null is μ₆-invariant on the readout side by construction.

*Note on validity:* a fresh-random-key surrogate is INVALID here (if the leak is a property of
random keys it would appear in fresh keys too, so it cannot serve as the H₀ for this coupling).
The label-permutation-on-deduped-keys null is the correct matched control.

### 4. PLANTED CONTROL (must fire)

Two synthetic plants replacing the real b_eps with a known noisy copy of ε:
- **Strong plant (MUST fire):** `b_plant = ε XOR Bernoulli(q=0.25)` ⇒ true MI ≈ 1−H₂(0.25) ≈ 0.189
  bits. Expected G ≈ 2·N·MI·ln2. At N=82: G ≈ 21.6, df=1 ⇒ permutation p ≈ 0. At N=10^4: p ≈ 0.
  Expected fired Î ≈ 0.189 bits (±estimator bias, shared with null so rank-unbiased).
- **Floor plant (calibration):** `b_plant = ε XOR Bernoulli(q≈0.41)` ⇒ true MI ≈ 0.10 bits, set to
  the primary-arm MI_min at N=82; used to confirm the instrument resolves at its stated floor.

**Rule:** if the strong plant does NOT fire (permutation p > α) at a given N, the instrument is dead
at that N ⇒ the real-key result on that arm is VOID, no null claimed.

### 5. POWER

KS floor: O(√p / n) ≈ 2^128 / 2^256 = **2^−128** — the true per-key character-sum bias predicted by
Kohel–Shparlinski. No feasible sample approaches this; the test can only find GROSS leakage.

Detectable MI at 80% power, α=0.01, df=1 (noncentrality λ_nc ≈ (z_{0.995}+z_{0.8})² ≈ 11.7):
`MI_min ≈ λ_nc / (2 N ln2) ≈ 8.43 / N` bits.
- Real arm, N=82 (pre-dedup upper bound; report post-dedup): **MI_min ≈ 0.103 bits**
  (⇔ |φ-correlation| ≳ 0.37 on a balanced binary pair). Anything subtler is BELOW power.
- Constructed arm, N=10^4: MI_min ≈ 8.4×10⁻⁴ bits. N=10^6: MI_min ≈ 8.4×10⁻⁶ bits
  (⇔ |φ| ≳ 0.0012) — still ~2^122 above the KS floor.
- SECONDARY (18-cell, df=17): MI_min ≈ (χ²_crit,17 + noncentral offset)/(2N ln2) ≈ 0.2–0.3 bits at
  N=82 (report exact); much weaker — reason it is not verdict-driving.

**A null is therefore scoped to "MI < MI_min(N)", NEVER "no leak" — the KS floor is uncrossed.**

### 6. SCOPE (inherited by every number the run emits)

- Curve: secp256k1 only. Maps: eps/s per RESULT_linchpin_s_gate_v2.md; I₁=χ₃(x)·y per its
  established definition; χ₃ via integer power-residue a^((p−1)/3) mod p.
- Target: single GLV coupling-carry bit ε with **fixed known d₁**, chosen so r₁:=(d₁λ mod n)=⌊n/2⌋
  (d₁ = ⌊n/2⌋·λ⁻¹ mod n) ⇒ ε balanced, P(ε=1)=r₁/n≈1/2.
- **Real arm:** solved BTC-puzzle keys with known private scalars, AFTER μ₆-dedup — report exact
  post-dedup N (nominally ≤ 82).
- **Constructed arm:** MT19937 → select-bitlen → scalar pipeline (project known-generator set),
  N stated explicitly; identical maps.
- Every reported MI/p carries (arm, N, MI_min).

### 7. FALSIFICATION (written before the run)

- **Of the LEAK hypothesis:** strong plant fired AND Î_prim within the matched null (p>0.05) on
  BOTH arms at stated N ⇒ scoped NULL: "no coordinate-flap → coupling-carry leak with MI ≥ MI_min(N)
  on secp256k1 at these N." Does NOT close the channel (2^−128 ≪ MI_min).
- **Of the TEST (voids the run, no null claimed):** strong plant does NOT fire at a given N.
- **Positive voided:** real Î exceeds null but the orbit-dedup precondition was violated
  (same-orbit / negation-pair keys retained) ⇒ forced-symmetry artifact; re-run after dedup.

### 8. EXACTNESS

Signal path int/Fraction only:
- r₁, r₂=(d·λ mod n): int. ε = [ r₂ ≥ n − r₁ ]: integer comparison.
- s(x), eps(x): exact integer Eisenstein lift (RESULT_linchpin_s_gate_v2.md); eps∈{0,+,−} from
  integer sign; s<3/16 gate by integer cross-product (no true division).
- j, s_neg: from I₁=χ₃(x)·y — χ₃ integer power-residue, y-parity integer.
- Counts int; p̂ Fraction; ε balance and ratio compares by integer cross-product.
- **Float carve-out (justified):** the log₂ inside MI and the ordering of Î values. Analytic
  monotone applied to already-exact rational counts, used ONLY to produce a scalar RANKED against
  the matched permutation null (constraint 1 permits exactly this). No key-derived value is
  thresholded by a float; the reported p-value is an exact integer permutation count. Tie risk in
  the float rank is negligible and carries no key in path.

### 9. PRE-COMMITMENT (grade slots, filled before the run)

| Outcome | Conclusion | Grade |
|---|---|---|
| Strong plant fires + Î_prim p<0.05 on BOTH arms + dedup clean | Candidate cross-channel carry leak; MI=… bits [95% CI], scope secp256k1, N=…; NOT PROVED. Next probe: cell-wise decompose which of j/s/eps carries it; replicate on fresh constructed keys | **EMPIRICAL** |
| Strong plant fires + Î_prim p<0.05 on ONE arm only | Arm-scoped positive, explicit non-replication flag; treat as likely power/artifact until reconciled (test-on-both-sets) | **EMPIRICAL (non-replicating)** |
| Strong plant fires + Î_prim p>0.05 BOTH arms | MI < MI_min(N); no gross flap→carry leak at scope. State POWER (MI_min) + SCOPE. Explicitly NOT a closure (KS floor 2^−128 uncrossed) | **VERIFIED-scope (null)** |
| Strong plant does NOT fire | Instrument dead at N; test uninformative, needs larger N; no grade on real data | **VOID** |
| Original single-point I(c;(I₁,I₂)) | Power-saturation + DLP-tautology; not run | **ILL-POSED** |

SECONDARY Î_sec (18-cell joint fiber): reported with its own MI_min and permutation p under the
same null; informs the "which channel" follow-up but NEVER overrides the primary verdict.

---

## DISJOINTNESS ARGUMENT (one paragraph, load-bearing)

The feature b_eps = [eps(x_P)≠0] is computed from x_P **as a field element in F_p** via the
Eisenstein lift (μ₃/CM structure of the point's coordinate) — established to have **no d and no λ in
its computational path**. The target ε = [ (d·λ mod n) ≥ n − r₁ ] is computed from the scalar d **in
the ring Z/n** via multiplication by λ and an integer threshold set by the known d₁. The two maps
reach the common secret d by **disjoint operations in disjoint rings** (coordinate field F_p vs
scalar ring Z/n); neither is a component of the other, and there is no identity of the r=v−w form
linking them. They touch the same λ-structure only abstractly (Z[ω] acts on both), which is *why the
correlation is worth testing* and *not* a tautology: extracting ε from x_P would require inverting
the coordinate-to-scalar map, i.e. the DLP. Hence a correlation surviving the μ₆-matched,
orbit-deduped permutation null is a genuine sub-question, and its ABSENCE at MI_min(N) is a scoped
null, not a closure. (The known d₁ only *selects the threshold* to balance ε for maximal estimable
entropy; d is never re-injected into the feature.)
