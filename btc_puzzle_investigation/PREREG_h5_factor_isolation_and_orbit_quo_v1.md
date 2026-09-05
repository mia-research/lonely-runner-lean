# PRE-REGISTRATION — H-5 factor isolation (Exp 1) + orbit-reduced quo (Exp 2)

**Status:** `[PRE-REGISTRATION — written before any Exp-1/Exp-2 data is seen]`
**Date:** 2026-08-24
**Instrument:** `semaev_cm_relation_yield_v4.py` (driver) over the frozen harness
`semaev_elimination_v1.py`. Statistic = the T1 relation-yield lever.
**Frozen inputs this pre-reg is sized on (data already on disk, NOT re-read for outcomes):**
`semaev_cm_relation_yield_v4.log` (the LEAKY headline run — per-prime `T1_j0` and `#Egap`
columns supply the effect-size variance), `_SCHEDULE_semaev_cm_relation_yield_v4.json`
(SHA-256 `f92cb4bb…`; the 24-prime × 7-curve schedule with orders), and
`RESULT_h5_V_signature_leak_derivation_v1.md` (prior context: F1/F2/F8 definitions and the
named μ₆-multiplicity candidate). Prior conclusions there are context, not constraints.

**Exact-arithmetic rule (binding, both experiments):** curve orders, `quo`, orbit counts,
variety points and solution tuples are exact Python ints. Floats appear ONLY as the monotone
statistics `logmean`/`log`-ratio that are ranked against a matched sign-flip permutation null.
No float ever thresholds the data. Confirmed for both designs below.

---

## 0. What the instrument actually computes (read from the code, not the narrative)

- `build_curves(p, n_noncm, seed=1000+p)` — deterministic in `p`: j0 = **first** `(A=0,B)` in
  `range(1,p)` ⇒ **B=1 always fixed** (μ=6, j=0); j1728 = first `(A,B=0)` (μ=4); 5 non-CM from
  `random.seed(1000+p)`. The j0 curve, the 5 non-CM curves, **and the nearest-#E match are
  identical across every |V| level** (only `Dmax`, `K` change). This is the invariance the
  frozen re-analysis turned on and it is what makes the prime-drop arm free.
- `cell_quo` → per curve `Q = logmean(qs)`, `qs = [quo]` over K decompositions where `dim==0`.
- `measure_system` → `quo = I.vector_space_dimension()` = # of ordered tuples
  `(x₁,…,x_m)∈V^m` with `S_{m+1}(x₁,…,x_m, tval)=0` (points sum, x-coord-level, to the target).
- `decomposable_target` (F8-LEAKY) → target + V built from `gens()[0]`-multiples (guarantees a
  consistent system).
- `match_nearest` (F2-LEAKY) → greedy nearest-#E control.
- `run` T1 statistic: `dj0.append(cj0['Q'] − noncm[i0]['Q'])`, pooled, sign-flip p-value
  (`signflip_p`, R=20000).

**Frozen LEAKY per-prime `T1_j0` variance (sign-flip null scale = rms/√n, n=24):**

| \|V\| | mean T1_j0 | SD | rms | SE_sf=rms/√24 | z_obs | pos | MDE(80%,α.05)=2.49·SE | floor=2·SE |
|---|---|---|---|---|---|---|---|---|
| 4 | 0.2074 | 0.241 | 0.314 | 0.0641 | 3.24 | 21/24 | 0.159 | 0.128 |
| 5 | 0.4094 | 0.337 | 0.526 | 0.1073 | 3.82 | 22/24 | 0.267 | 0.215 |
| 6 | 0.5668 | 0.445 | 0.715 | 0.1459 | 3.89 | 22/24 | 0.363 | 0.292 |
| 7 | 0.7042 | 0.507 | 0.862 | 0.1759 | 4.00 | 22/24 | 0.438 | 0.352 |
| 8 | 0.8335 | 0.550 | 0.992 | 0.2026 | 4.11 | 22/24 | 0.504 | 0.405 |

`#Egap` (|V|-invariant): mean 0.0244, sd 0.0246, max 0.0921. Pearson(T1_j0,#Egap)≈+0.05 (all |V|)
— the lever does not track the gap (consistent with the RESULT-file re-analysis). These are the
numbers every power floor below is sized from.

---

# EXPERIMENT 1 — factor isolation (F1 / F2-matching / F2-primedrop / F8)

**Object.** Attribute the LEAKY→CORRECTED collapse of the T1_j0 lever (0.207→0.834 vs ≈0) to
specific design factors. The three co-varying factors are F1 (twist B=1 vs randomized-B within
j=0), F2 (nearest vs #E-bracketed matching), F8 (`gens()[0]`-multiple vs `random_point`
sampling). **F2 is split into two objects that must not be conflated:** F2a = the matching
*rule*; F2b = the *prime-drop selection* bracketing entails (selection on the absolute position
of `#E_j0`, distinct from `#Egap`). Object is the T1 statistic itself and its factor
decomposition — not a proxy.

### 1.1 Statistic (exactly one per factor, named now)

All effects are **paired across the 24 frozen primes** and pooled with the instrument's own
`signflip_p` (one-sided where a direction is predicted, two-sided otherwise).

- **E_F1** = per-prime `Q_j0(B=1) − mean_{i=1..R_B} Q_j0(A=0, B=B_i)`, pooled, sign-flip
  (two-sided; H0: B=1 exchangeable with random j=0 twists). **Well-posed by cancellation:** the
  F1 effect on T1 is `[Q_j0(B=1)−Q_ctrl] − [Q_j0(randB)−Q_ctrl] = Q_j0(B=1)−Q_j0(randB)` — the
  control cancels exactly, so this is a *within-j=0-class* test and needs no matching. It asks
  the RESULT-file's F1 question directly: is B=1's sextic-twist class special among j=0 twists?
- **E_F2a** (on P_brk only) = per-prime `Q_bracket(p) − Q_nearest(p)`, pooled, sign-flip
  (two-sided). `Q_bracket` = linear interpolation of the two bracket curves' `logmean` quo at
  `#E_j0` (lower bracket = largest non-CM order ≤ #E_j0; upper = smallest ≥ #E_j0; weight by
  inverse #E-distance). Report the count of non-zero deltas (see defect D4).
- **E_F2b** = `mean(δ_nearest | dropped primes) − mean(δ_nearest | kept primes)`, with a
  **label-permutation** null (shuffle the bracketable/non-bracketable labels across the 24
  primes, count fixed by the schedule; two-sided). Equivalent report: `T1_leaky(P_all)` vs
  `T1_leaky(P_brk)`. **This arm is free** — it re-pools the frozen per-prime deltas over the
  schedule-defined subset; no quo is recomputed.
- **E_F8** = per-prime `Q_leaky(p) − Q_F8flip(p)` for the j0 curve (and, secondarily, the paired
  T1 with F8 flipped on all curves), pooled, sign-flip (two-sided).

**Attribution reconstruction check (registered now):** the total to be explained is
`T1_leaky_full − 0 ≈ T1_leaky_full` (CORRECTED ≈ 0). OFAT is adequate iff
`E_F1 + E_F2a + E_F2b + E_F8 ≈ T1_leaky_full` within the sign-flip CI; a large residual ⇒
interactions dominate ⇒ escalate to the 2³ factorial (defect D5).

**|V|-scaling discriminator (registered now):** record every effect at |V|∈{4,5,6}. The lever
grows 0.21→0.57. A carrying factor's effect must show the same growth; the #E-selection channel
is |V|-flat by the RESULT-file derivation, the μ₆-multiplicity channel grows with |V|. Which
effect's growth matches the lever's growth is itself a decision input.

### 1.2 Matched control (must share the instrument's forced symmetries)

- **F1:** R_B random j=0 twists at the **same prime, same K, same seeds (7000+k), same sampling
  (`gens`), same |V|**. They share μ=6 / GLV / j-invariant 0 / the prime / the summation-poly
  structure; they differ ONLY in sextic-twist class (B mod 6th powers). Destroys only the
  specific-twist choice — the exact forced-symmetry-preserving null.
- **F2a:** identical `Q_j0` and identical set of 5 non-CM `Q`; only the selection rule over
  already-computed controls differs. Preserves every quo; a pure selection contrast.
- **F2b:** the bracketability label is computed from the **frozen schedule's orders only**,
  independent of any quo — so the permutation null preserves the entire quo structure and
  destroys only the label↔δ association.
- **F8:** same curves, same primes, same matching; only the point-sampling in
  `decomposable_target` changes. Preserves curve identity and #E-matching; destroys only the
  factor-base/target sampling law.

### 1.3 Planted (positive) control — must fire or the null is uninformative

1. **Pipeline plant:** the re-run must reproduce the frozen log's `T1_j0` (perm_p<0.001,
   21–22/24 positive) — determinism (same seeds/schedule); if not, halt (nondeterminism).
2. **Negative control C4:** non-CM-vs-non-CM pair stays null (perm_p>0.1) as in the log.
3. **Injected factor plant:** add a constant c=+0.5 to every j0 `Q` in a shadow copy of one arm;
   the paired sign-flip must return mean≈+0.5, perm_p<0.001. If a paired test cannot detect a
   planted 0.5 shift at n=24, that arm is uninformative — full stop.

### 1.4 Power analysis (explicit floor)

Sign-flip null scale from §0. Paired factor tests **cancel shared structure**, so their
per-prime SD is **≤** the raw T1_j0 SD in §0 — the floors below are therefore **conservative**
(they over-state the required effect). Using the raw-T1 SE_sf as the bound:

| \|V\| | detectable factor effect, 80% power (2.49·SE) | hard floor (2·SE) |
|---|---|---|
| 4 | 0.16 | 0.13 |
| 5 | 0.27 | 0.21 |
| 6 | 0.36 | 0.29 |

At |V|=6 the total lever is 0.567; a factor carrying **≥50%** (≥0.28) is detectable at ~80%,
a factor carrying **<25%** (<0.14) sits below the |V|=6 floor and is resolved instead by the
cheaper |V|=4 arm (floor 0.13) and by the |V|-scaling/relative-magnitude logic — attribution is
by *which factor dominates and grows*, never by one arm's isolated significance. R_B=8 gives the
F1 within-class mean a √8 variance reduction on the "random-B" leg, so E_F1's floor is tighter
than the table (bounded by SE of `Q(B=1) − mean of 8`), which is the point of R_B=8.

### 1.5 Scope

- **Primes:** the frozen 24, p∈[523,823], p≡1 mod 3 (schedule SHA `f92cb4bb…`). No 256-bit, no
  ECDLP, no key claim. m=3 throughout.
- **|V| levels:** {4,5,6}. **Ceiling recommended = |V|=6.** The lever is already monotone and
  z≈3.9 at |V|=6; attribution needs the growth *shape*, not the largest |V|. |V|=7,8 cost
  1000–3400 s/cell (one |V|=8 cell hit 1204 s) for no attribution gain.
- **K:** 25 (unchanged) — keeps the per-prime variance the floors are sized on and preserves C6
  determinism.
- **R_B (F1):** 8 random-B j=0 twists per prime.
- **P_brk:** computed once from the frozen B=1 schedule (used for F2 only; see defect D7).
- **Wall-clock (per-cell rates from the log: ~10 s @|V|=4, ~24 s @|V|=5, ~59 s @|V|=6):**
  - Leaky re-run persisting all 7 curve Q's (delivers baseline + F2a + F2b + C6):
    24 primes × (70+168+413) s ≈ **4.3 h**.
  - F1 (R_B=8 extra j0-type cells, reuse B=1): 8×24×(10+24+59) s ≈ **5.0 h**.
  - F8 (7 curves, |V|∈{4,5} only): 24×(70+168) s ≈ **1.6 h**; conditional extend to |V|=6
    (+2.8 h) **only if** E_F8 exceeds its |V|=5 floor.
  - **Total ≈ 11 h** (≤ 14 h with the F8 extension). Overnight-feasible; K may be halved to
    ~5.5 h at the cost of √2 on every floor (not recommended — breaks C6 determinism).

### 1.6 Falsification condition

- The **"real j0/CM lever"** hypothesis (RESULT §5–6) is falsified if **E_F1 ≈ 0** (B=1 not
  special within the j=0 class, below the |V|=6 floor) **and** the lever is reconstructed by the
  artifact factors (E_F2a+E_F2b+E_F8 ≈ T1_leaky_full).
- The **"pure artifact"** hypothesis is falsified if **E_F1 dominates** (≥50% of the total, grows
  with |V|) while E_F2a, E_F2b, E_F8 are each below floor.
- The **OFAT design itself** is falsified (inadequate) if the reconstruction residual
  `T1_leaky_full − (E_F1+E_F2a+E_F2b+E_F8)` exceeds the pooled sign-flip CI ⇒ escalate to 2³.

### 1.7 Pre-committed decision rule (fill BEFORE the run)

| Outcome | Conclusion (scoped: p∈[523,823], m=3, \|V\|≤6, K=25) |
|---|---|
| E_F1 dominant, grows with \|V\|, F2a/F2b/F8 < floor | Lever is a **genuine sextic-twist-class / j=0 effect**, not an #E artifact. Feeds Exp 2 (independent vs duplicate). Grade: `[real-lever candidate, scoped]`. |
| E_F2b dominant | Lever is a **prime-selection artifact** (absolute-#E-position selection). Since §3 of the RESULT file shows the #Egap channel inert, flag as a *genuine puzzle* for follow-up. Grade: `[artifact — selection]`. |
| E_F2a dominant | **Greedy-matcher artifact** (nearest picks systematically low-Q controls). Grade: `[artifact — control construction]`. |
| E_F8 dominant | **Sampling artifact** (gens-subgroup bias; expect concentration on non-cyclic curves — defect D3). Grade: `[artifact — sampling]`. |
| No single factor dominant / reconstruction residual large | Interactions dominate; **escalate to the 2³ factorial** before any conclusion. Grade: `[inconclusive — OFAT inadequate]`. |
| Pipeline plant fails to reproduce the log, or C4 fires, or the +0.5 plant misses | **Instrument/test broken — halt.** No factor conclusion. |

---

# EXPERIMENT 2 — orbit-reduced quo (independent relations vs automorphism duplicates)

**Object.** Decide whether the j0 `quo` excess is **independent usable relations** (a genuine
yield lever that feeds yield→cost) or **duplicate relations** (same linear relation, useless for
index calculus). The reduction must be by a group action that is an action *on the fixed-target
solution set*. This is where the design must be checked before it can run.

### 2.1 Well-posedness resolution — the λ→λT target-shift (REQUIRED CHECK)

The proposed reduction "orbits under the μ3/GLV action" is **ILL-POSED as literally stated**, and
here is why, from the group law:

- The GLV endomorphism `λ:(x,y)↦(ζ₃x,y)` acts on points as `[μ]` with `μ²+μ+1≡0 (mod N)`.
  If `(P₁,…,P_m)` decomposes target `T` (`ΣP_i + T = O`), then `Σλ(P_i) + λ(T) = O`, so
  `(λP₁,…,λP_m)` decomposes `[μ]T` — a **different target**. On x-coordinates the target x-coord
  `tval` moves to `ζ₃·tval` (verified below via isobaric homogeneity). Since the instrument fixes
  one target x-coord per cell, **the fixed-target solution set is NOT closed under λ**; "orbits
  under μ3" are undefined there. The task's warning is correct.
- **Isobaric confirmation of the shift:** `S_{m+1}` for A=0 is isobaric of weight 4 under
  wt(x)=1, wt(B)=3; under `x_i→ζ₃x_i`, `t→ζ₃t`, `B→ζ₃³B=B`, one gets
  `S(ζ₃x,ζ₃t)=ζ₃⁴S(x,t)=ζ₃S(x,t)` (since ζ₃³=1 ⇒ ζ₃⁴=ζ₃). So `S(x,t)=0 ⇔ S(ζ₃x, ζ₃t)=0`: λ maps
  solutions of `tval` bijectively onto solutions of `ζ₃·tval`, never back to `tval`.
- `[-1]:(x,y)↦(x,-y)` fixes x ⇒ acts **trivially** on x-tuples ⇒ no reduction (task notes this).

**The subgroup that FIXES the target and acts non-trivially on x-tuples is the symmetric group
`S_m`** permuting the m summand coordinates: the summation polynomial is symmetric and the sum is
commutative, so `S_m` maps `tval`-solutions to `tval`-solutions. Two ordered tuples in one
`S_m`-orbit are the **same multiset of factor-base points = the same linear relation** — exactly
the "duplicate" that is useless for index calculus. `quo = vector_space_dimension` counts
**ordered** tuples, so it over-counts every distinct relation by `m!/|stabiliser|`.

**Corrected well-posed object (PRIMARY): S_m-orbit-reduced quo.**
`Q_orbit = mean_K |{ sorted-multiset(sol) : sol ∈ I.variety() }|` — the count of *distinct usable
relations*. Exact (integer). Also record `Q_raw = vector_space_dimension`; if `|variety| ≠
vector_space_dimension` the ideal is non-radical (multiplicity) — report it as structure, and use
`|variety|` for the orbit count.

**GLV/μ3 secondary is FORCED-CONSTANT — demoted (defect D2).** With V β-invariant (closed under
x→ζ₃x, as `mu3_lever_test` builds), the λ-bijection above **forces**
`quo(tval)=quo(ζ₃·tval)=quo(ζ₃²·tval)` exactly, so the target-x-orbit total is `3×` per target
and the joint (target,tuple)/μ3 quotient returns exactly `quo(tval)` — for **any** β-invariant-V
curve. The "3×" is algebraically forced and identical in structure for j0 and control ⇒ it
carries **zero** j0-vs-control information. It cannot separate the alternatives, so it is NOT a
discriminating arm. It is registered ONLY as a mechanical **forced-relation check**: verify
`quo(tval)=quo(ζ₃tval)=quo(ζ₃²tval)` holds exactly on β-invariant V; a failure is an instrument
bug ⇒ halt.

### 2.2 Statistic (exactly one discriminator)

- **Reported orbit lever:** `T2 = logQ_orbit(j0) − logQ_orbit(nearest-#E non-CM control)`, pooled
  over the 24 frozen primes, sign-flip p-value — the T1 pipeline with `Q_orbit` in place of `Q`.
- **PRIMARY discriminator (paired):** `D2(p) = T1(p) − T2(p) = log ρ_j0(p) − log ρ_ctrl(p)`,
  where `ρ = Q_raw/Q_orbit` is the per-curve duplicate ratio; pooled, sign-flip (one-sided ≥0,
  since duplicates can only inflate `Q_raw`). `D2` is the difference in log-duplicate-ratios
  between j0 and its matched control — it isolates whether j0's excess is *differentially*
  duplicate. `D2≈0` ⇔ excess survives; `D2≈T1` ⇔ excess is entirely S_m-duplicate.

### 2.3 Matched control (shares forced symmetries)

Same nearest-#E non-CM control as T1: same prime, matched #E, and — crucially — the summation
polynomial is symmetric for **every** curve, so `S_m` is a **forced symmetry the control shares
by construction**. The orbit reduction (sorted-multiset dedupe of `I.variety()`) is applied
**identically** to j0 and control. Preserves prime, #E-match, and the S_m symmetry; destroys only
the CM/μ=6 curve structure. (This avoids the classic failure of a null that destroys a symmetry
the readout has by definition — S_m is preserved on both sides.)

### 2.4 Planted (positive) control — must fire

1. **All-duplicate plant:** a target whose only solutions are the m! orderings of one multiset ⇒
   `Q_raw=m!`, `Q_orbit=1`, so `log ρ = log(m!)` and D2 must fire to ≈log(3!)=1.79 (m=3). If D2
   does not detect a construction that is 100% duplicate, the orbit-counter is broken — full stop.
2. **All-distinct plant:** solutions with pairwise-distinct multisets ⇒ ρ=1, D2≈0. Must return
   null.
3. **Forced-relation check (§2.1):** `quo(tval)=quo(ζ₃tval)=quo(ζ₃²tval)` on β-invariant V must
   hold exactly; failure ⇒ halt.

### 2.5 Power analysis (explicit floor)

Same n=24 sign-flip machinery; the |V|-level SE_sf floors of §0/§1.4 apply. Orbit reduction is a
smoothing, so `T2` and `D2` have per-prime SD ≤ the raw T1 SD ⇒ floors are conservative.
- If the excess **survives** (`T2 ≈ T1`), the test inherits T1's power: z≈3.8–3.9 at |V|=5–6,
  well-powered (detect T2≥0.2 at |V|=5, ≥0.29 at |V|=6).
- If the excess is **duplicate** (`T2→0`), the conclusion rests on the null band: `|T2|` below
  the |V|-floor (0.21 @|V|=5, 0.29 @|V|=6) **and** `D2` significantly >0. The paired `D2` is the
  higher-power arm because `log(m!)` for m=3 is 1.79 — a full-duplicate signal is ≈12·SE_sf@|V|=5,
  saturating power; partial duplication down to ρ_j0/ρ_ctrl ≈ 1.25 (D2≈0.22) is detectable at
  |V|=5. Floor for D2 ≈ 0.21 (|V|=5).

### 2.6 Scope

- Same frozen 24 primes, m=3, |V|∈{4,5,6}, K=25, schedule `f92cb4bb…`. No 256-bit/ECDLP claim.
- **Cost:** piggybacks on Exp-1's leaky re-run by additionally calling `I.variety()` + dedupe on
  the **two** relevant curves (j0, nearest control) per prime per K per |V|. `variety()` for
  quo~1–20 is cheap; standalone estimate ≈ 2/7 of a leaky run + enumeration overhead ≈ **1.5–2 h**
  (marginal if run inside the Exp-1 leaky re-run). |V| ceiling = 6, same rationale as Exp 1.

### 2.7 Falsification condition

- The **μ₆-multiplicity-duplicate** hypothesis (RESULT §6) is falsified if `D2 ≈ 0` (below floor)
  and `T2 ≈ T1` — the excess is NOT duplicates.
- The **real-lever** hypothesis is falsified if `D2 ≈ T1` and `T2 → 0` (below floor) — the excess
  is entirely S_m-permutation duplicates.
- The whole experiment is void (instrument bug) if the forced-relation check (§2.1) fails or an
  all-duplicate plant does not fire.

### 2.8 Pre-committed decision rule (fill BEFORE the run)

| Outcome | Conclusion (scoped: p∈[523,823], m=3, \|V\|≤6, K=25) |
|---|---|
| `D2 ≈ 0`, `T2 ≈ T1` (excess survives orbit reduction) | j0 excess = **distinct usable relations** ⇒ **real yield lever** ⇒ feeds yield→cost (N11/N12). Grade: `[real-lever candidate, scoped]`. |
| `D2 ≈ T1`, `T2 → 0` (excess is S_m-duplicate) | Excess = **permutation duplicates, useless for index calculus**. Grade: `[no lever — duplicate, scoped]`. |
| Intermediate (0 < T2 < T1) | Partial: report surviving fraction `T2/T1` and the duplicate fraction `1−exp(−D2)`. Grade: `[partial lever, scoped]`. |
| Forced-relation check fails, or plants misbehave | **Instrument bug — halt.** No relation conclusion. |

---

## 3. Design-defect flags (disclosure, not verdicts — this section is not scored on count)

- **D1 (Exp 2, resolved):** the literal "orbit-reduced quo under μ3/GLV" is **ill-posed** — λ maps
  a `tval`-solution to a `ζ₃·tval`-solution (target-shift, §2.1). Corrected object = `S_m`-orbit
  reduction (the target-fixing subgroup acting non-trivially on x-tuples). Registered as primary.
- **D2 (Exp 2, resolved by demotion):** the GLV/μ3 reduction on β-invariant V is a
  **forced constant** (`3×` algebraically forced by isobaric homogeneity; identical for j0 and
  control) ⇒ zero discriminating power ⇒ demoted to a mechanical forced-relation check, not an arm.
- **D3 (Exp 1, F8):** `random_point` vs `gens()[0]`-multiple sampling is **distributionally
  identical on cyclic E** (every point is a multiple of G) ⇒ E_F8≈0 **by construction** there;
  the real mechanism is the gens-subgroup bias on **non-cyclic** E(F_p). Not a broken control, but
  low prior power — **record each curve's group structure** and read E_F8 conditional on it.
- **D4 (Exp 1, F2a):** the nearest control frequently **coincides** with a bracket endpoint on
  P_brk ⇒ many small/zero `Δ_match` ⇒ low power. Mitigated by defining `Q_bracket` as the
  #E-interpolated value (never exactly `Q_nearest` unless brackets coincide); **must report the
  number of non-zero deltas** — a low count means the F2a arm is under-powered, not null.
- **D5 (Exp 1, OFAT):** one-factor-at-a-time misses interactions; justified over the 2³ factorial
  on cost (2³ ≈ doubles wall-clock) **and** on the registered reconstruction check
  (E_F1+E_F2a+E_F2b+E_F8 vs T1_leaky_full) that detects when interactions dominate and forces
  escalation. Chosen because the leading hypotheses (F1-real vs F2b-selection) are additive-first.
- **D6 (frozen log, informational):** `scaling_summary` crashed at line 186 (Sage symbolic-`sum`
  shadowing) so the log's pooled |V|=7,8 model-fit is absent; the **per-prime `T1_j0` data are
  intact** and are all this pre-reg uses. Not load-bearing (this design caps at |V|=6).
- **D7 (Exp 1, scoping):** P_brk (bracketability) depends on `#E_j0`, which **changes when B is
  randomized** (F1). E_F1 is computed control-free (within-class), so P_brk is used **only** for
  the F2 arms and is fixed on the B=1 schedule; the F1 and F2 subsets are kept in separate
  ledgers and never cross-pooled.

---

## 4. Owed gates / provenance

- This pre-registration is the **mandatory experiment-designer gate** before either run
  (btc CLAUDE.md §2). No grade may be promoted off Exp 1 / Exp 2 outputs until the run matches
  this spec (post-run audit checks: statistic unchanged, no silent filtering, plant fired, power &
  scope on every number, conclusion = the pre-committed cell).
- Both experiments reuse the frozen schedule SHA `f92cb4bb…`; the re-run must reproduce the log's
  per-prime `T1_j0` (C6) before any factor/orbit number is trusted.
- Scope on every number that either run produces: **p∈[523,823], p≡1 mod 3, m=3, |V|∈{4,5,6},
  K=25.** No 256-bit, ECDLP, or key-recovery claim is in scope.
