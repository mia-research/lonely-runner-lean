# Cycle 004 Extension Plan
Generated: 2026-02-27
Author: Cycle Coordinator (Claude Code)
Basis: Original Cycle 003 completion tasks + Deep-dive outlier analysis findings

This plan supersedes the informal P1–P4 list from `reports/cycle_003_completion_summary.md` with a fully tiered, dependency-ordered work plan.

---

## Summary of What Changed from the Original P1–P4 Plan

The deep-dive outlier analysis revealed four new findings that affect scope:

1. **The 10/n invariant is a new publishable claim** (from 000041 + 000052 cross-verification)
2. **CLAIM-LRC-000052 is two claims, not one** — arithmetic (valid, 10/n) and non-arithmetic (methodology gap)
3. **CLAIM-LRC-000047 fragility result is non-informative** — three new experiments are needed to properly test the RANDU hypothesis
4. **CLAIM-LRC-000041 random-family failures at n=6 are substantive** — not footnotes, they are the most mathematically important data points in the entire file

---

## Tier 0 — Immediate Administrative Fixes
*No new experiments. Execute before Cycle 004 quorum work begins.*

### T0.1 — Fix CLAIM-LRC-000032 Summary Text Error
**What:** The `lrc_statistical_validation.txt` source file's SUMMARY section states "Statistical significance: p≥0.01 with Bonferroni correction." This is inverted. The early-horizon comparisons ARE significant (p<0.01). The p≥0.05 result applies at T≥500 when all types converge.
**Action:** Annotate the measurement record for 000032. Do not modify the source file. Add a note to the claim dossier: "Source summary text has inverted significance statement; individual comparison rows are authoritative."
**File:** `reports/dossiers/cycle_002_promoted/06_CLAIM-LRC-000032.md`

### T0.2 — Change CLAIM-LRC-000062 Primary Stability Metric
**What:** The precision ladder flags 000062 as rank 27 (worst) due to `alt_sum_desc_abs ≈ 1.93e-6` causing amplified relative error. The actual timing data is stable. The metric is inappropriate for near-zero cancellation datasets.
**Action:** Update 000062 dossier to note that `l2_norm` and `max` are the primary stability indicators for this claim. Flag `alt_sum_desc_abs` as "not applicable (near-zero cancellation regime)" in the precision ladder artifact.
**File:** `reports/dossiers/cycle_002_promoted/27_CLAIM-LRC-000062.md`

### T0.3 — Narrow CLAIM-LRC-000047 Claim Scope
**What:** The claim encompasses both boundary_hits (valid) and fragility (non-informative). Zero fragility is generically expected for any non-rational-periodic generator — it cannot distinguish RANDU from PCG64, so it does not test the stated hypothesis about RANDU's lattice defect.
**Action:** Update 000047 dossier. Retain: "RANDU boundary hit counts are statistically identical to PCG64 and MT19937 (t=−0.13, t=0.24, both non-significant)." Remove from claim scope: fragility_eps_star = ∞ as evidence. Add annotation: "Fragility result non-informative; see Cycle 005 RANDU Extension Experiments for proper tests."
**File:** `reports/dossiers/cycle_002_promoted/08_CLAIM-LRC-000047.md`

### T0.4 — Register TORUS_rational_1/5 Finding as Auxiliary Result
**What:** The 000047 source file contains a structurally important secondary finding: TORUS_rational has bimodal boundary_hits (0 for 19/20 seeds, 79,999 for seed 10) with fragility at eps_star ≈ 6.37e-8 appearing on multiples-of-5 seeds. This is the real finding — rational speed periodicity causes fragile isolation.
**Action:** Create a new auxiliary note in `reports/notes/` documenting this as a candidate for a future claim: "Rational-periodic speed structures create fragile isolation events at eps ≈ 6.37e-8; irrational-periodic speeds do not."
**File:** `reports/notes/torus_rational_fragility_aux_note.md` (new)

---

## Tier 1 — Claim Reformulation (Cycle 004, highest impact)
*Required before re-adjudication of conflict_escalate claims. Blocks Tier 1.3.*

### T1.1 — Reformulate CLAIM-LRC-000041
**Current state:** Raw CSV excerpt. The claim text is a fragment showing arithmetic,6,2 rows only, omitting that the source file contains 4 families (arithmetic, geometric, perturbed, random) and that the random family has genuine failures at n=6.

**Proposed reformulation:**
> "For the arithmetic speed family with n=6 runners (φ(n)=2), complete isolation of all 6 runners is confirmed in 100/100 trials (horizon T=1000), with a universal average first isolation time of exactly 5/3 — a mathematical invariant independent of boundary_count (range 3601–6001). By contrast, random speed families at n=6 achieve isolation in only 98/100 trials, with 2 seeds producing 4/6 runners isolated despite exhaustive search (boundary_counts 18,186 and 20,428), constituting the only non-isolation events in the dataset across all tested n. The arithmetic invariant 5/3 = 10/n for n=6 is independently confirmed by CLAIM-LRC-000052."

**Why this matters:** The conflict escalation was correct — the original claim obscures the n=6 random-family failures, which are the most mathematically significant data point (potential near-counterexamples to LRC for n=6 with random speeds).

### T1.2 — Split and Reformulate CLAIM-LRC-000052 into Two Claims
**Current state:** A single claim over 7,287 rows mixing arithmetic (phi_match=100%, first_isolation=10/n) and non_arithmetic (phi_match=0%, no isolation detected) data.

**Proposed split:**

**000052-A (arithmetic):**
> "For arithmetic speed families across n=5 through n=15, the first isolation time follows the exact invariant: first_isolation = 10/n, holding across 3,300 baseline trials (300 per n) and confirmed by CLAIM-LRC-000041 for n=6. All 3,300 rows achieve phi_match=YES. The arithmetic_extended variant shows first_isolation = 1.1728 × (10/n), with the constant factor invariant across all n."

**000052-B (non-arithmetic methodology note):**
> "Non-arithmetic speed families (geometric, quadratic, perturbed; n=5–15) produce isolation_count=0 and phi_match=NO under the phi-match detection criterion. This reflects a methodology boundary: the phi_match criterion requires arithmetic phase structure and is inapplicable to non-arithmetic speeds. LRC validity for these speed families at proven cases (n≤5, n=7) is not in question; dedicated detection methodology is required (see Cycle 005 T3.4)."

**Why this matters:** ChatGPT's 0.82-confidence escalation was correct. Aggregating arithmetic (100% phi_match) with non-arithmetic (0% phi_match) into one claim creates a misleadingly heterogeneous claim.

### T1.3 — Register New Claim: first_isolation = 10/n
**Current state:** Not registered. Confirmed by two independent experiments (000041, 000052-A) across n=6 and n=5–15.
**Action:** Add to frontier_queue.csv with status "proposed_claim — awaiting mathematical explanation of the constant 10." The value 10 appears related to the speed normalization in the experiment setup (boundary_count = 30 for n=5 → first_isolation = 2.0 = 10/5; possible connection: 10 = 2 × boundary_count/n). Needs Writer/Compiler agent to formalize.
**Proposed ID:** CLAIM-LRC-000066 (next available)

### T1.4 — Re-run Quorum for 000041 and 000052 with Reformulated Text
**Dependency:** T1.1 and T1.2 must complete first.
**Action:** Generate new quorum task pack for 2 reformulated claims (000041 and 000052-A). Submit to both Claude and ChatGPT/Gemini lanes. With proper mathematical claim text, the conflict escalations should resolve to consensus_caveated or better.
**Expected outcome:** Both claims achieve external_quorum_complete=yes, conflict resolved → promote to A-Validated in Cycle 004.

---

## Tier 2 — Quorum Batch for 17 Pending B-Promising Claims
*Original P2 task. No new analysis required. All 17 have repro=match and numeric/measurement integrity.*

### T2.1 — Generate Quorum Task Pack for 17 Pending Claims
**Claims:** 000038, 000042–000044, 000048–000051, 000056–000060, 000062–000065
**Action:** Run `generate_quorum_task_pack.py` with these 17 claim IDs. Generate 2-model task pack (Claude + ChatGPT or Claude + Gemini).
**Note:** For 000062, the reformulated claim scope from T0.2 should be used in the quorum prompt — primary metric is l2_norm/max, not alt_sum_desc_abs.

### T2.2 — Execute Quorum Votes
**Action:** Run `run_two_model_quorum_pack_live.py`. If Codex CLI still unavailable, use manual quorum workflow (precedent from Cycle 003). All 17 claims have clean numeric/repro status so expect consensus_caveated or consensus_promote for most.
**Blocker:** Codex CLI not installed. Use manual packet workflow if needed (as per Cycle 003 precedent).

### T2.3 — Registry Promotion
**Action:** On consensus_caveated or better for each claim, promote to A-Validated via `update_registry_status.py`.
**Target:** 17 + 2 (from T1.4) = up to 19 new A-Validated claims after Cycle 004, bringing total to 27/27 A-Validated.

---

## Tier 3 — New Experiments (Cycle 005)
*Needed to fill the gaps identified by the deep-dive. These are new experiments, not re-analysis of existing data.*

### T3.1 — RANDU Timing Distribution Test
**What:** RANDU and PCG64 both produce ~793 boundary hits per run. Do the isolation events occur at the same *times*, or does RANDU's 15-plane lattice structure cluster events at specific time bins?
**Method:** Capture per-event witness times for all ~793 boundary hits per run, for RANDU and PCG64 (20 seeds each). Run Kolmogorov-Smirnov test on the distributions. If KS p > 0.05, the timing distributions are indistinguishable → RANDU's lattice defect does not affect isolation timing.
**Output:** KS statistic and p-value; histogram of witness times by generator.
**Why needed:** Current data only shows COUNT of boundary hits, not whether they occur at different times. The count equivalence could mask a timing bias.

### T3.2 — Speed-Space Proximity to LRC-Critical Values
**What:** Does RANDU's 15-plane structure cause generated speed values to fall near LRC-critical values (multiples of 1/n) more or less than a uniform random generator?
**Method:** Generate n=200,000 speed values from RANDU and PCG64. Compute minimum distance from each value to the nearest multiple of 1/6 (the n=6 threshold). Compare distributions. The 15-plane structure means RANDU triplets cluster on hyperplanes — check whether these hyperplanes intersect the isolation-threshold hyperplanes.
**Output:** Distribution of (min distance to 1/6 multiples) for RANDU vs PCG64; spatial density map of triplets near critical planes.
**Why needed:** This tests the actual hypothesis — RANDU's lattice structure could systematically bias speed selection toward or away from LRC-critical configurations.

### T3.3 — Adversarial Isolation-Boundary Experiment
**What:** Construct speed configurations specifically designed to sit just below the isolation threshold (within ε of failing to isolate) and verify that RANDU cannot generate these adversarial configurations due to its lattice structure.
**Method:** For n=6, generate 1,000 "near-failure" speed configurations: sets where the minimum runner separation approaches 1/6 from below (i.e., isolation criterion is just barely satisfied or just barely fails). Check whether RANDU can produce these configurations from its 15-plane lattice, versus what fraction of uniform-random configurations would be adversarial.
**Output:** Count of adversarial configurations reachable by RANDU vs. uniform random; characterization of the adversarial manifold in speed space.
**Why needed:** This directly tests whether RANDU's lattice defect is "safe" (lattice planes don't intersect the adversarial region) or "dangerous" (lattice planes overlap with near-failure configurations).

### T3.4 — Non-Arithmetic Speed Detection Experiment
**What:** The 000052 dataset shows geometric/quadratic/perturbed speeds have 0 phi_match events. This is because the phi_match criterion doesn't apply to non-arithmetic speeds. The LRC is proven for these speed families at n=5 and n=7, so the data is not counterevidence — it's a measurement gap.
**Method:** Design a detection criterion appropriate for non-arithmetic speeds:
- For geometric speeds (ratio r between consecutive speeds): isolation occurs when the geometric ratio produces separations ≥ 1/n. The detection criterion should use the geometric progression's natural periodicity (r^k) not the arithmetic periodicity (k/n).
- Run n=5, n=6, n=7 with geometric/quadratic/perturbed speeds using the new criterion.
- Expected result: isolation confirmed for n=5 and n=7 (known proven cases); n=6 may show partial failure under random geometric speeds.
**Output:** New isolation detection rates for non-arithmetic families; comparison with arithmetic family rates.
**Why needed:** Currently the corpus has zero valid measurements for non-arithmetic speeds. A publishable LRC paper cannot omit this.

### T3.5 — n=6 Random-Family Failure Investigation
**What:** Seeds 506060 and 506091 (random family, n=6) have 4/6 runners isolated after exhaustive search (boundary_counts 18,186 and 20,428). These are the most mathematically interesting data points in the corpus — potential near-counterexamples to the unproven n=6 LRC case.
**Method:**
1. Extract the exact speed values for these two seeds from the source file header/generation parameters
2. Verify: are these speeds valid LRC candidates (distinct, positive integers)?
3. Run with extended horizon T=10,000 and T=100,000 — do the 2 non-isolated runners eventually achieve isolation?
4. If they do: what is the isolation time? Does it follow a pattern (e.g., 10/n scaled by some factor)?
5. If they don't: characterize the speed configuration and determine whether this is a genuine LRC near-counterexample or a degenerate case (e.g., two runners with identical speeds)
**Output:** Full characterization of the 2 failure seeds; extended-horizon results; mathematical analysis of the speed structure.
**Why needed:** The n=6 LRC case is unproven. If these seeds represent configurations where isolation requires T >> 1000, documenting the required time horizon is mathematically valuable. If they represent a degenerate case, that should be documented.

---

## Tier 4 — Manuscript and Publication (Cycle 005–006)
*Original P3–P4 tasks, now with expanded scope from deep-dive findings.*

### T4.1 — Writer/Compiler Agent Pass: Formal Claim Reformulation
**Scope:** All 27 claims + 1 new proposed claim (T1.3). Convert raw CSV/text excerpts to proper mathematical propositions. For each claim:
- State the mathematical object being measured
- State the speed family and n value
- State the result as a quantitative statement with confidence bounds
- Distinguish empirical results from mathematical conjectures
**Dependencies:** T1.1, T1.2, T1.3 (provides correct reformulations for the 5 outlier claims)

### T4.2 — Dependency Graph Construction
**Scope:** Map which claims logically depend on or support other claims. Key dependencies identified:
- 000041 ← 000052 (cross-validates 10/n invariant)
- 000032 ← 000041/000052 (statistical backbone supports specific timing claims)
- 000047 ← 000052 (rational speed fragility is the mechanistic explanation for torus behavior)
- New Claim 000066 (10/n) ← 000041 + 000052

### T4.3 — Manuscript Sections B and G
- Section B (Mathematical Rigor): formal definitions, non-circular, proof steps or empirical status
- Section G (Writing/Transparency): proven facts vs conjectures vs heuristics; limitations; failure modes

**Key failure modes to document:**
1. Random speeds at n=6 fail isolation in 2% of trials (000041 — T3.5 investigation required)
2. Phi_match criterion inapplicable to non-arithmetic speeds (000052 — T3.4 fills this gap)
3. RANDU fragility test non-informative (000047 — T3.1–T3.3 fill this gap)
4. Strong-clustered speeds require 50× longer horizon (000032 — practical implication for all empirical work)
5. Coarse midpoint approximation introduces systematic early-detection bias of 0.84 ± 0.37 time units at n=10 (000062)

### T4.4 — Seed Policy and Re-Run Documentation (Section C)
**Action:** Document exact seed values and generation logic for all 27 claims. Identify claims where seed is fixed (e.g., arithmetic family, seed=0 always) vs. swept (random family, seeds 506060+ etc.).

### T4.5 — Final Publication Bar Pass (Cycle 006)
**Target:** All sections A–H PASS or NEAR PASS. Current blockers:
- A: 27/27 A-Validated (needs T2 + T1.4)
- B: Manuscript (needs T4.1, T4.2)
- C: Seed policy + re-run docs (needs T4.4)
- G: Manuscript written (needs T4.3)

---

## Execution Order (Dependency Graph)

```
T0.1 → T0.2 → T0.3 → T0.4   (parallel, no dependencies between them)
    ↓
T1.1 → T1.2 → T1.3            (sequential: reformulation before split before registration)
    ↓
T1.4                           (requires T1.1, T1.2)
    ↓
T2.1 → T2.2 → T2.3            (quorum batch, independent of Tier 1 except 000041 and 000052)

T3.1 → T3.2 → T3.3            (RANDU experiments, parallel with Tier 2)
T3.4                           (non-arithmetic detection, parallel)
T3.5                           (n=6 failure investigation, parallel)

T4.1 ← T1.1, T1.2, T1.3       (needs reformulations)
T4.2 ← T4.1
T4.3 ← T4.2, T3.1-T3.5        (needs all experiment results)
T4.4 ← T2.3
T4.5 ← T4.1, T4.2, T4.3, T4.4
```

---

## Cycle 004 Scope (This Cycle)

Execute: T0.1–T0.4 (all), T1.1–T1.4 (all), T2.1–T2.3 (all)
Defer: T3.1–T3.5, T4.1–T4.5 (Cycle 005–006)

**Expected Cycle 004 outcomes:**
- All 27 claims at A-Validated status (19 via quorum batch + 2 via reformulation + existing 8)
  - Actually: 17 (T2) + 2 (T1.4) + 8 (existing) = 27 total
- 3 dossier annotations corrected (T0.1–T0.3)
- 1 new proposed claim registered (T1.3)
- All conflict_escalate claims resolved
- Publication bar: Section A moves from NOT MET to PASS; B, C, G still require Cycle 005

---

## Outstanding Open Question

**Why is the constant in first_isolation = 10/n equal to 10?**

Hypothesis: The experiment setup uses boundary_count = 30 for n=5. The first isolation event occurs at the 10th boundary (out of 30), giving first_isolation = 10 × (1/boundary_density). The constant 10 may be an artifact of the specific arithmetic speed progression chosen (speeds {1, 2, ..., n-1} with n runners), where the first runner achieves isolation after exactly 10 "speed units" regardless of n. This needs mathematical verification by the Writer/Compiler agent.

Alternatively: 10/n = 2/φ(n) × (something) — the relationship to φ(n) may be the underlying mathematical structure. For n=5, φ(5)=4, 10/5=2; for n=6, φ(6)=2, 10/6=5/3; for n=7, φ(7)=6, 10/7... this doesn't simplify cleanly to φ(n). The constant 10 is genuinely mysterious and worth formal investigation.
