# PREREG — Semaev H2 order-3 structure control (do-not-close #4): β-orbits vs generic order-3 orbits

**Date:** 2026-08-24
**Author:** experiment-designer (pre-registration, written BEFORE any V3 data is seen)
**Gate status:** MANDATORY pre-run gate (CLAUDE.md §2 / btc CLAUDE.md exact-arithmetic rule).
**Instrument (frozen):** `semaev_elimination_v1.py` — `measure_system(F, 0, 7, m, tval, Vroots, Dmax)`,
whose `quo = I.vector_space_dimension()` counts (with multiplicity, over the algebraic closure) the
solutions of `{ S_{m+1}(x_1..x_m, tval)=0 } ∪ { ∏_{r∈V}(x_i−r)=0, i=1..m }` — i.e. the ordered
m-tuples of factor-base elements whose points sum (up to y-sign, via the Semaev polynomial) to the
target x-coordinate `tval`. `quo` is an exact non-negative integer.
**Target claim under test:** M26's CM label — that the reproducible boost
`R2 = log quo(Vinv) − log quo(Vrnd) ≈ 1.6–2.2×` is **β/CM-specific**, not generic order-3-orbit
closure. Do-not-close #4 (v14 §I): "β-orbits vs random order-3 orbits of the same shape."

---

## 0. OBJECT (named, and the tautology check)

**Object measured:** the elliptic curve E: y² = x³ + 7 over F_p (p ≡ 1 mod 3, j=0, CM by ω), and the
**decomposition count** `quo` the Semaev index-calculus system assigns to a size-3k factor base. The
statistic compares three factor bases on the SAME curve, SAME target, SAME seed x-coords:

- **Vinv** — k orbits of the CM map β (a primitive cube root of unity in F_p, the x-action of the
  GLV/CM endomorphism): orbit(x) = {x, βx, β²x}.
- **V3(φ)** — k orbits of a **generic split order-3 Möbius map** φ ∈ PGL₂(F_p), φ ≠ β,β²:
  orbit(x) = {x, φ(x), φ²(x)}. Structure-matched to Vinv (§ well-posedness (a)).
- **Vrnd** — 3k elements with no orbit structure (the instrument's existing control; used only as a
  REPRODUCTION anchor for R2, not as the discriminator).

**Feature/target disjointness.** The feature (which map closes the base: β vs φ) and the target
(`quo`, a curve-group decomposition count) are built from disjoint inputs: `quo` is a property of the
curve's group law via S_{m+1}; the closure map is a property of the factor-base construction. The two
are **not** co-constructed — swapping β for φ changes the base but not the S_{m+1} oracle. So this is
NOT a residue-vs-component tautology. The one genuine coupling (β-orbits are curve-endomorphism
orbits that sum to O) is the CM MECHANISM under test, exposed in § well-posedness (c), not a hidden
tautology.

---

## 1. STATISTIC (exactly one)

Grid (pre-committed in §4): S instances (prime × target-seed) × K generic order-3 maps per instance.
For instance s and map φ_i, the instrument returns integers `quo(Vinv_s)` and `quo(V3_s(φ_i))`.

**Primary statistic — signed-win count with the CM map designated:**

    W_obs = Σ_s Σ_i [ 1{ quo(Vinv_s) >  quo(V3_s(φ_i)) }
                    − 1{ quo(Vinv_s) <  quo(V3_s(φ_i)) } ]

(ties, quo equal, contribute 0 and are counted separately as `n_tie`).

**Distribution under the null:** see §2. Significance is an **exact Monte-Carlo permutation p-value**
(integer count ratio), NOT a parametric z. `W_obs` large-positive ⟺ β beats generic order-3 ⟺ the
boost is β/CM-specific.

**Magnitude descriptor (NOT the decider):** `R3_med = median_{s,i} [ log quo(Vinv_s) − log quo(V3_s(φ_i)) ]`,
reported alongside for effect size. `log` is a monotone float carve-out (analytic size only; the sign
comparisons that drive `W_obs` use raw integer `quo`, so no float enters the decision path).

Rationale for choosing a pooled signed-win over a max-over-cells: a max of noisy per-instance ratios
is upward-biased and low-power; the signed-win pools the aimed-at contrast (β vs generic order-3) into
one exchangeable statistic.

---

## 2. MATCHED CONTROL / NULL

**Construction shared by Vinv and every V3(φ) (only the map differs):**
Fix the seed x-coords = the m decomposition x-coords `xs` (so every base CONTAINS the true target
decomposition ⇒ all quo ≥ that solution ⇒ the comparison is fair) PLUS (k−m) common random padding
seeds r_1..r_{k−m}. Then:
Vinv = ∪_seeds {seed, β·seed, β²·seed}; V3(φ) = ∪_seeds {seed, φ(seed), φ²(seed)}.
Both have exactly k size-3 orbits, |V| = 3k, contain `xs`, same target `tval`, same curve #E.
This is TIGHTER than the instrument's own Vinv/Vrnd (which pad independently); the only degree of
freedom that varies is β ↔ φ.

**The matched permutation null.** Under H0 ("β is not special among split order-3 maps"), the
collection {β, φ_1, …, φ_K} is exchangeable per instance. Null draw b:
within each instance s, pick a uniformly random member m*_s ∈ {β, φ_1,…,φ_K} to play the role of "the
designated map," recompute the signed-win count W_perm^{(b)} with `quo(base under m*_s)` in the
distinguished slot vs the K others. Repeat B times.
One-sided exact p = (1 + #{ b : W_perm^{(b)} ≥ W_obs }) / (1 + B).

- **Preserves:** curve, #E, target, seed x-coords, |V|=3k, k size-3 orbits, split-order-3 projective
  orbit geometry, the entire multiset of `quo` values in the ensemble, all ties.
- **Destroys:** ONLY the label "which order-3 map is the curve's CM map β."

**Why matched, not a shuffle.** A naïve shuffle of factor-base ELEMENTS would destroy the order-3
orbit structure that BOTH Vinv and every V3 have by construction — an invalid null (it breaks the
symmetry the readout has by definition, exactly the μ₆ null-mismatch failure this project has hit).
Permuting the MAP LABEL destroys only the CM-vs-generic distinction and nothing else.

**#E-confound immunity (contrast to H-5).** The H-5 seam was `quo ∝ 1/#E` under one-sided #E-matching
ACROSS curves. Here Vinv and every V3 live on the SAME curve with the SAME #E and the SAME target, so
`quo ∝ 1/#E` is identical across the compared bases and cannot produce W_obs. R3 is #E-invariant by
construction.

---

## 3. WELL-POSEDNESS RESOLUTIONS (the three checks; each is a design decision, stated before the run)

**(a) "Random order-3 map on x-coords" — which group, and is it well-defined with the consistency
requirement?** The three candidates evaluated:

| candidate | order-3 elements are… | verdict |
|---|---|---|
| multiplicative x→ax | a³=1, a≠1 ⇒ a∈{β,β²} | IS the CM family — cannot serve as a non-CM control |
| affine AGL₁ x→ax+b | a³=1, a≠1 ⇒ a∈{β,β²}, b free; = β recentered to fixed point b/(1−β) | **DEGENERATE for this purpose**: multiplier is STILL β. Isolates "β at origin vs β off-origin" (fixed-point alignment), NOT "generic vs CM." Rejected. |
| set-permutation (product of k 3-cycles) | any 3-cycle; orbit = 3 arbitrary elements | **DEGENERATE**: "closed under SOME order-3 permutation" is a property EVERY 3k-set has ⇒ V3-perm ≡ Vrnd and R3-perm ≡ R2. Carries zero new information. Rejected. |
| **Möbius PGL₂ x→(ax+b)/(cx+d)** | since p≡1 mod 3, 3∤(p+1) ⇒ NO non-split order-3; ALL order-3 are split, conjugate to x→βx, with two F_p fixed points | **CHOSEN**: the only candidate that is a genuine algebraic order-3 map generically distinct from β while retaining algebraic orbit structure. |

**Chosen construction of φ:** sample g ∈ GL₂(F_p) uniformly (mod scalars, non-degenerate), set
φ = Möbius(g · diag(β,1) · g⁻¹). This is exactly order 3 and split; its fixed points g(0), g(∞) are
generically ≠ {0,∞}. **Reject-and-resample** φ if: it normalizes the diagonal torus (φ ∈ {β,β²}, a
~2/p event); or a fixed point coincides with any seed x-coord (would collapse an orbit to size <3);
or any resulting orbit has size <3 or overlaps another (keep exactly k disjoint size-3 orbits, |V|=3k).
**Consistency preserved:** V3 is built by φ-closing the SAME seeds `xs`, so xs ⊆ V3 exactly as
xs ⊆ Vinv — the decomposable target's x-coords are present, the system is consistent, quo ≥ the real
decomposition for every base. **Instance-level rejection (pre-committed, before quo is read):** if a
seed x-coord equals a β-fixed point (x=0) or lands in a degenerate β-orbit, drop the whole instance
BEFORE computing any quo — this is a mechanical, disclosed drop that keeps Vinv and V3 structurally
identical.

**(b) Is quo(V3) forced equal to (or systematically shifted from) quo(Vinv) by an algebraic reason
(e.g. any order-3 closure induces the same |V|/3 shrink)?** NO.
- All three bases have |V| = 3k; orbit structure changes WHICH tuples solve, not |V|, so there is no
  differential "|V|/3 shrink" between Vinv, V3, Vrnd — the shrink concern applies to comparing a
  k-element base to a 3k-element base, not here.
- `quo` is NOT invariant under a Möbius change of x-coordinate: S_{m+1} is tied to the curve's own
  x-map, and the ONLY Möbius maps that preserve `quo` are the curve automorphisms x→β^i x (from
  μ₆ = Aut(E) at j=0). A generic φ is PGL₂-conjugate to β but that conjugation does NOT preserve
  `quo`. Hence quo(V3(φ)) is free to differ — the control is **discriminating, not forced**.
- **Verified by the planted β/β² tie** (§ PLANTED): inserting φ=β and φ=β² into the ensemble MUST
  return quo exactly equal to quo(Vinv). If it does not, the pipeline is broken (abort, §6 outcome 4).

**(c) The endomorphism confound — is it a nuisance to remove or the mechanism to detect?** EXPOSE it.
β is the x-action of the GLV/CM endomorphism λ (λ²+λ+1 ≡ 0 mod N). A β-orbit {x, βx, β²x} is
{x(P), x(λP), x(λ²P)}, and P + λP + λ²P = (1+λ+λ²)P = O — **each β-orbit is a relation-triple (three
points summing to O)**. Generic φ-orbits are x-coords of curve points with UNRELATED discrete logs
whose points do NOT sum to O. This is NOT a confound to subtract — it IS the CM mechanism, and R3 is
built to detect precisely it. **Mandatory mechanistic readout (guards "a bound is not a verdict"):**
for every base in the ensemble, count `n_rel` = number of its orbits that are relation-triples
(points summing to O; = k for Vinv, ≈0 for generic V3). Report whether `quo` tracks `n_rel` across
the ensemble. If W_obs is significant AND quo tracks n_rel ⇒ the CM effect is EXPLAINED (CM = the
factor base carries k free relations). If W_obs is significant but quo does NOT track n_rel ⇒ a SECOND
mechanism is present — NAME it, do NOT close. Structure lives in this mechanism split, not in the
magnitude alone.

---

## 4. SCOPE (every number the run emits inherits this)

- **Curve:** y² = x³ + 7 over F_p, j=0, CM by ω. **Primes** (all ≡ 1 mod 3): p ∈ {211, 307, 421,
  631, 907, 1093}. (211, 307 anchor to the instrument's demo rows.)
- **m = 3** (Semaev S4; matches the demo and keeps `quo` computable). m=4 is EXPLORATORY only, not in
  the confirmatory grid.
- **k ∈ {2, 3}** ⇒ |V| ∈ {6, 9}. k=2 anchors to the instrument's `mu3_lever_test(..., k=2)`; k=3 is
  the power arm (larger `quo`, fewer ties).
- **Instances:** J = 3 independent target seeds per prime ⇒ **S = 18** instances per k (minimum
  acceptable S = 8 if wall-clock forces truncation; truncation is a disclosed deviation).
- **Maps per instance:** **K = 30** generic split order-3 Möbius maps (per-instance rank floor
  1/(K+1) ≈ 0.032; pooled over S gives the resolution).
- **Permutation draws:** **B = 999** ⇒ global p-floor 1/(1+B) = 0.001.
- **Dmax** = the instrument's own `2^(m−1) + m·(3k) + 5` (unchanged, so the quo oracle is byte-identical).
- **Wall-clock estimate:** per k, S·(K+1) ≈ 18·31 ≈ 560 `quo` calls; each ~2 s (k=2) to ~10 s (k=3)
  over these small primes ⇒ ~20 min (k=2) to ~90 min (k=3); both k ≈ 1–3 h. **Time-box each `quo`
  call at 60 s**; a call that exceeds it drops that instance (mechanical, disclosed; decided before
  the value is seen).
- **Exactness (EXACTNESS section):** field elements, β, φ (as integer matrices mod p), orbit members,
  and `quo` are exact ints. `W_obs`, `n_tie`, `n_rel`, and the permutation p-value are integer
  counts / integer ratios. The ONLY float is `R3_med` (a log-ratio descriptor), which never enters
  the sign comparisons or the p-value — allowed monotone carve-out, no key in the path. Passes
  `check_no_float.sh` intent (no float in the signal/decision path).

---

## 5. POWER (with an explicit floor)

**Test used for power:** the pooled signed-win reduces, on the non-tied comparisons, to a sign test
of `θ = P(quo(Vinv) > quo(V3(φ)))` against 1/2.
- N_eff = number of non-tied (s,φ) comparisons, ≤ S·K = 18·30 = 540.
- To detect a per-comparison win probability θ at one-sided α = 0.01 with power 0.8:
  N_eff·(θ−½)² ≈ (z_.99 + z_.8)²·¼ ≈ (2.33+0.84)²·¼ ≈ 2.5, so **θ−½ ≈ √(2.5 / N_eff)**.
  - N_eff = 200 ⇒ detectable θ ≈ 0.61.
  - N_eff = 540 ⇒ detectable θ ≈ 0.57.
- If the CM effect is as large as the measured R2 ≈ 1.6–2.2× suggests, θ ≳ 0.8 ⇒ detection prob ≈ 1.
- If the boost is generic (β exchangeable with φ), θ = ½ ⇒ W_obs typical ⇒ correct non-detection at
  false-positive rate α.

**Explicit floors:**
1. **p-value floor:** minimum achievable exact permutation p = 1/(1+B) = **0.001**.
2. **Tie floor (power guard, MANDATORY):** the statistic can only separate the alternatives if `quo`
   has resolution. If `n_tie / (S·K) ≥ 0.50` on an arm, that arm is **UNDERPOWERED — abstain**,
   escalate to larger k/|V| (bigger `quo`), and emit NO conclusion for that (p,k). This is the exact
   failure the small-quo regime (values in {1,2,3}) would cause; it must be checked and reported
   before any verdict. This is the one way the statistic could fail to separate the alternatives, and
   the guard forecloses it.
3. **Reproduction floor:** the run must first reproduce R2 = log quo(Vinv) − log quo(Vrnd) ≈ 1.6–2.2×
   on the anchor rows (p=211/307, k=2). If R2 does not reproduce, the instrument has drifted and the
   whole test is VOID (abort before interpreting R3).

---

## 6. PLANTED (positive) CONTROL — the test must fire

Two planted checks, both pre-committed:

**P-a (pipeline integrity, must be exact):** insert φ = β and φ = β² into the ensemble as if they were
"generic" draws. Because β,β² are the curve automorphisms, `quo(V3(β)) = quo(V3(β²)) = quo(Vinv)`
EXACTLY. If either differs, the construction is buggy ⇒ ABORT (outcome 4). This also confirms
well-posedness (b): the two quo-preserving Möbius maps are exactly the CM ones.

**P-b (substantive sensitivity, known effect of known SIZE):** build V_plant(j) = the same base but
with `j` of the k padding orbits replaced by GENUINE relation-triples (each three points R,S,T with
R+S+T=O), the remaining (k−j) padding orbits generic-φ. Sweep j = 0,1,…,(k−m). **The test must show
`quo(V_plant(j))` increasing (or at least detectably non-flat) in j** — i.e. `quo` responds to the
number of relation-triples in the base. **If quo is flat in j, the instrument cannot see relation
structure ⇒ the null is UNINFORMATIVE ⇒ STOP (outcome 4); no conclusion about M26.** This validates
that the mechanism of §(c) is one the instrument can register at all, of a size we control.

---

## 7. FALSIFICATION (written before the run)

The hypothesis under test is M26's CM label. It is **FALSIFIED** if, with the planted controls fired
(instrument demonstrably sensitive) and the tie-guard passed (arm powered):

> the exact permutation p-value for W_obs is ≥ 0.05 (one-sided) AND |R3_med| is below the resolvable
> log-ratio floor (≈ |log(1 + 1/median quo)|).

That outcome says β is exchangeable with a generic split order-3 map: the R2 boost is reproduced by
generic order-3-orbit closure, NOT by β. M26's CM label is then removed.

---

## 8. PRE-COMMITTED DECISION RULE (each outcome → conclusion)

Preconditions for ANY substantive conclusion: R2 reproduces (§5 floor 3), P-a exact, P-b fires,
tie-guard passed on the arm. Otherwise → outcome 4 or 5.

1. **W_obs upper tail, exact p ≤ 0.01, R3_med > 0 above floor, tie-rate < 0.5, planted fired:**
   → **β/CM-SPECIFIC CONFIRMED.** M26's CM label SURVIVES, upgraded to
   `[VERIFIED — matched control]` "CM-specific vs generic split order-3, scope {these primes, k, m}."
   Do-not-close #4 discharged (CM-affirming). Attach the §(c) mechanism reading: state whether quo
   tracks n_rel (CM = relation-triples) or a second mechanism is present.
2. **W_obs consistent with null, p > 0.05, |R3_med| below floor, planted fired, tie-guard passed:**
   → **GENERIC ORDER-3 CLOSURE.** M26 DOWNGRADES to "structured-V closure, GENERIC (not
   CM-specific)"; the CM label is removed. Do-not-close #4 discharged (generic). This is a POSITIVE
   dissolution (the boost is real but its cause is re-identified), not a closure of the avenue.
3. **W_obs LOWER tail, p ≤ 0.01 the other way (generic V3 beats Vinv):**
   → **ANTI-CM ANOMALY.** Generic split order-3 orbits yield MORE decompositions than β-orbits. This
   refutes the CM-boost DIRECTION and is a distinct new structural fact. Do NOT close; NAME it (why
   would non-endomorphism orbits decompose better?) and open a follow-up probe. Report with power +
   scope.
4. **P-a inexact OR P-b flat (quo insensitive to relation structure):**
   → **NULL UNINFORMATIVE.** The instrument cannot register the object. ABSTAIN; no movement on M26;
   fix the pipeline or re-scope to larger k. (Abstention IS the finding — it does not close #4.)
5. **Tie-rate ≥ 0.5 on an arm (underpowered):**
   → **ABSTAIN on that (p,k).** Escalate to larger k/|V|; no conclusion for that arm. If ALL arms
   tie-out, #4 remains open and owed at larger |V|.
6. **0.01 < p ≤ 0.05 (upper tail):**
   → **SUGGESTIVE, NOT DECISIVE.** Report W_obs, R3_med, power, tie-rate; owe a larger-K / larger-S
   re-run before moving M26's grade. Do not upgrade or downgrade on this alone.

---

## 9. DESIGN-DEFECT FLAGS (self-audit; not scored on problems found)

- **Clean where clean:** the primary statistic (signed-win vs matched label-permutation null)
  SEPARATES the stated alternatives (generic θ=½ vs CM θ>½) provided the tie-guard passes; the null
  is matched (preserves order-3 orbit geometry and #E, destroys only the β-label); the planted
  controls (P-a exact tie, P-b relation-count monotonicity) can fire; power and its floor are stated.
- **Flagged as DEGENERATE and REJECTED (stated plainly):** the AGL₁ order-3 control (multiplier
  forced = β, so it does NOT isolate CM vs generic; it is a weaker "β-at-origin vs β-off-origin"
  control) and the set-permutation order-3 control (V3-perm ≡ Vrnd, R3-perm ≡ R2, zero new
  information). Only the Möbius/PGL₂ control is well-posed for the stated discrimination. A run that
  used AGL₁ or set-permutation as "the order-3 control" would be answering a different question or no
  question.
- **The one way the statistic fails to separate** is the small-`quo` tie regime; the mandatory
  tie-guard (§5 floor 2, §8 outcome 5) is the safeguard — without it, an underpowered null would be
  mis-read as "generic," so the guard is load-bearing.
- **#E-confound (the H-5 mechanism):** structurally excluded — all compared bases share the curve and
  target, so `quo ∝ 1/#E` is common-mode and cancels.
- **Not a tautology:** feature (closure map) and target (`quo`) are disjoint constructions; the one
  real coupling (β-orbits sum to O) is the mechanism under test, surfaced in §(c), not hidden.
