# PREREG — does the CM yield advantage reduce relation-collection COST? — v2 (rank of within-target differences, over ℤ/n)

**File:** `PREREG_semaev_relation_cost_v2.md`  **Date:** 2026-08-07
**Supersedes v1** after an isolated `experiment-designer` gate returned 3 blocking findings (§10). All three
were correct and are fixed; the redesign is sharper. **Status: PRE-RUN / DRAFT for a second gate.** No
confirmatory statistic computed.

**The three v1 defects and the redesign.**
- **B1 — the object is the WITHIN-TARGET-DIFFERENCE rank, not raw rows.** A single decomposition of a
  target `T` (unknown log `τ`) gives `Σc_i log P_i = −τ` — **no** constraint on the factor-base logs until a
  **second** decomposition of the *same* `T` lets the difference cancel `τ`: `Σ(c'−c)_i log P_i = 0`. So the
  cost-relevant object is the **homogeneous relation matrix `M_diff`** of within-target differences; its rank
  = the number of independent **factor-base** relations. v1's "rank over factor-base columns" overcounted
  every `quo=1` target. **This is also where the extra CM `quo` becomes relations — via the differences.**
- **B2 — over ℤ/n, not ℚ.** `rank_ℚ ≥ rank_{ℤ/n}`, so ℚ-rank OVERSTATES usable relations; and the
  automorphism redundancy under test (mult by `λ mod n`) is exactly the **ℚ-independent / ℤ/n-dependent**
  case. The cost statistic is **`rank_{ℤ/n}`** (`n=#E`); the **ℚ-vs-ℤ/n divergence is promoted to the
  redundancy detector**.
- **B3 — rate statistic, not fixed budget.** Reduced rank is capped at `|V|−1∈{3,5}`; a fixed large budget
  saturates both curves and compresses the gap below its floor. Primary = **`T*` = targets to reach
  `rank_{ℤ/n}(M_diff)=|V|−1`** (full dynamic range).

---

## §0 SCOPE BANNER
Enumerable model curves over the frozen wide schedule `p∈[523,8011]` (24 log-spaced, SHA 53d05e4b…, same
objects as the yield finding). `m=3`. **Object = CM (μ₆ j0) vs non-CM (μ₂)** — j0 only (the surviving robust
yield effect). **No transfer to `2²⁵⁶`; no ECDLP/extraction/security claim.** Any effect is a model-scale
statement about relation-collection rate; the subexponential-index question is out of scope. Both A1
(cost-reducing) and A2 (redundant-yield) are valid pre-committed outcomes — the test is built to go either way.

## §1 OBJECT — the within-target-difference relation matrix, over ℤ/n
Factor base `F={P_1,…,P_{|V|}}`, `|V|` points on `E`. Targets `T_1,T_2,…` = random points (fresh unknown
log `τ_j` each — the honest model; index calculus determines factor-base logs, not the target's).
- **Decompositions.** For `T_j`, enumerate all `m=3` net-coefficient vectors `c∈ℤ^{|V|}`, `Σ_i c_i P_i=−T_j`,
  by exact enumeration over `F∪(−F)` (`|c_i|≤m`). `quo(T_j)`=count (yield anchor; known CM-higher).
- **Difference relations.** For each `T_j` with `quo≥2`, add the `quo−1` homogeneous rows
  `d = c^{(l)}−c^{(1)}` (`Σ_i d_i log P_i = 0`) to the matrix `M_diff`. **`quo=1` targets contribute 0 rows**
  (B1). Targets processed in the frozen order until the stop rule (§3).
- **Cost statistic.** `rank_{ℤ/n}(M_diff)`, `n=#E` (via Smith normal form / rank mod each prime factor of
  `#E` — exact, small). Solvable threshold **`|V|−1`** (one global normalization d.o.f.). Also compute
  `rank_ℚ(M_diff)` (for the B2 divergence detector).
- **Exactness.** Point arithmetic exact `GF(p)`; `c,d` exact small `ℤ`; `rank_ℚ` and `rank_{ℤ/n}` exact
  (SNF / integer linear algebra); all permutation counts integer. No float on the signal path.

## §2 FORCED / ANCHOR FACTS (zero evidence)
- **A1 — CM `quo` > non-CM `quo`** ESTABLISHED (wide run); re-logged only for the `quo`-vs-rank contrast.
- **A2 — quo=1 ⇒ 0 factor-base relations** (B1); the difference construction encodes this.
- **A3 — `rank_ℚ ≥ rank_{ℤ/n}`** always; divergence `rank_ℚ > rank_{ℤ/n}` = ℤ/n-dependence among
  ℚ-independent differences = the redundancy signature.

## §3 HYPOTHESES & STATISTICS (frozen; matched-#E paired; sign pre-committed = CM cheaper)
Per wide prime: pair `j0` with nearest-`#E` non-CM (H1's rule). `|V|∈{4,6}`. Targets drawn from a frozen
seed list shared across the paired curves. Stop each curve at `rank_{ℤ/n}(M_diff)=|V|−1` (record `T*`) or a
cap `T_cap` (§6, censored).

| id | statistic (verdict-bearing) | matched null |
|---|---|---|
| **H1 (PRIMARY — cost rate)** | `TSTARGAP = T*_nonCM − T*_j0`, matched-#E paired, pooled; one-sided (`>0`, CM reaches solvable rank in FEWER targets ⇒ cheaper). Censored pairs handled by the log-rank/Gehan paired statistic (both may be uncensored at these `|V|`; §6). | within-pair (j0↔nonCM) label swap; ≥1e4; integer-rank one-sided p |
| **H2 (DECISIVE — is the extra yield independent or redundant?)** | For j0 pooled: `DIV = rank_ℚ(M_diff) − rank_{ℤ/n}(M_diff)` at a fixed target count. **`DIV≈0` ⇒ the CM differences are genuinely ℤ/n-independent (cost-reducing channel real); `DIV>0` (powered) ⇒ the extra CM relations are ℤ/n-REDUNDANT (ℚ-indep automorphism duplicates) — yield does NOT reduce cost.** | permute (ℚ vs ℤ/n) is not a null; use a matched **non-CM `DIV`** baseline — `DIV` should be ≈0 for μ₂; the test is j0-`DIV` vs nonCM-`DIV` paired |
| secondary | `quo`-rate vs ℤ/n-rank-rate (both curves): the raw contrast so redundancy is a number. | anchor, non-verdict |

**Verdicts (pre-committed).**
`COST-REDUCING` = **H1 fires** (`TSTARGAP>0`, powered) **∧** H2 `DIV≈0` (CM differences ℤ/n-independent):
the CM yield gives more independent factor-base relations per target ⇒ lowers relation-collection cost at
model scale.
`REDUNDANT-YIELD` = **H1 null** (powered) **∨** H2 `DIV>0` (powered): the extra CM decompositions do **not**
add ℤ/n-rank faster (either same `T*`, or the ℚ-gain is ℤ/n-redundant) ⇒ the real `quo` advantage does
**NOT** reduce cost. A backed negative — downgrades the candidate to a structural curiosity.
`NULL/UNDERPOWERED` = neither resolved at power (→ A3).

## §4 CONTROLS (all fire/hold; no verdict if any fails)
- **C1 — mechanism plants (validate the exact statistic).**
  (a) a batch of **all-`quo=1`** targets ⇒ `M_diff` empty ⇒ `rank=0` (validates the difference construction);
  (b) one target with **`quo=k` lifts that are ℤ/n-independent** ⇒ `rank_{ℤ/n}=k−1`;
  (c) one target with **ℚ-independent but ℤ/n-dependent** lifts (constructed via a `λ`-scaled integer combo,
      `det≡0 mod` a prime factor of `#E`) ⇒ `rank_ℚ>rank_{ℤ/n}` (validates the `DIV` detector — the whole H2).
  All three must be recovered, else no verdict.
- **C2 — enumeration vs Gröbner.** Direct `m=3` net-`c` decomposition count = `measure_system` `quo` on ≥3
  cells, **exact equality after dedup by net-`c`** (handles the ordered/multiplicity gap).
- **C3 — #E-match adequacy.** Median relative `#E` gap ≤ `2/√p` per pair (reuse H1's C2), sign-balanced.
- **C4 — non-CM vs non-CM null.** Two matched non-CM curves ⇒ `TSTARGAP≈0` and `DIV≈0` (in-band) — a nonzero
  result is a class effect, not a construction artifact.
- **C5 — budget adequacy.** `T_cap` large enough that **both** curves reach `rank=|V|−1` (uncensored) at
  `≥80%` of primes at the median (so `T*` is a rate, not a censoring artifact); reported pre-run as a number.

## §5 EXACTNESS
`rank_ℚ`, `rank_{ℤ/n}` (SNF / rank mod prime factors of `#E`) exact on integer matrices; `T*` integer;
permutation/sign-flip nulls integer. **No float decides a verdict** (`quo` `log` only in the non-verdict
anchor). `check_no_float.sh` on the statistic module.

## §6 SCOPE & SCHEDULE (frozen, SHA-256'd pre-run)
- **Primes:** the frozen wide set `[523…8011]` (reuse `_SCHEDULE_..._v3_wide` curves; same objects; SHA
  recorded). **`|V|∈{4,6}`**; `m=3`. **`T_cap`** set from a pre-run calibration so C5 holds (start 400; raise
  if C5 fails). Frozen target seed list shared across paired curves per prime.
- **Cost:** enumeration `(2|V|)^3≤1728` sums/target; SNF on `≤(quo·targets)×|V|` integer matrices — cheap
  (minutes–≈1h, no Gröbner).
- **`_SCHEDULE_relation_cost_v2`** (SHA'd pre-run): primes, curves+`#E`+prime-factorization of `#E`, `|V|`,
  `T_cap`, seeds.

## §7 POWER
- **H1 `TSTARGAP`.** 24 paired primes; if per-prime `T*` s.d. ≈ (mean `T*`)·0.5 and a true fractional gap
  ≥25%, the paired sign/rank test detects it one-sided α=0.01 at power ≈0.8 (re-estimate vs realized `T*`
  spread and censoring — `experiment-designer`). `[UNDERPOWERED]` boundary set from the realized spread,
  pre-registered as a number after the C5 calibration, before the confirmatory run.
- **H2 `DIV`.** Powered by the count of `quo≥2` targets (only those contribute differences); C5 ensures
  enough. Floor = the smallest `DIV` (in rank units) separable from the non-CM `DIV` baseline at 24 pairs.
- **A2 vs A3 (decidability, N1 fix):** upper one-sided CI on `TSTARGAP` **and** on `DIV` below the floor ⇒
  A2 (powered null); CI includes the floor ⇒ A3 (underpowered).

## §8 PRE-COMMITTED OUTCOME TABLE
| # | Outcome | Reported as |
|---|---|---|
| **A1** | H1 fires (`TSTARGAP>0`, powered) ∧ H2 `DIV≈0` (powered) | **COST-REDUCING:** CM (j0) reaches solvable factor-base rank in fewer targets, and its extra relations are ℤ/n-independent — the yield advantage lowers relation-collection cost at model scale. Report `TSTARGAP`, `DIV≈0`, per-`|V|`, and whether the gap grows with `|V|`. **Model-scale; no ECDLP/secp claim; subexponential-index out of scope.** |
| **A2** | H1 null (powered) ∨ H2 `DIV>0` (powered) | **REDUNDANT-YIELD:** the extra CM decompositions do not add ℤ/n-rank faster (same `T*`, or ℚ-gain is ℤ/n-redundant automorphism duplicates) — the real `quo` advantage does **NOT** reduce cost. Downgrades the candidate to a structural curiosity; report the `DIV`/`T*` numbers + the redundancy (automorphism) mechanism as next characterization. Backed null, not a closure of CM index-calculus structure. |
| **A3** | neither resolved at power (CI includes floor) | report `TSTARGAP`/`DIV` bounds + power; raise `T_cap`/primes. Not a verdict. |
| **A4** | any C1–C5 fails | that arm uninformative; no verdict. |

**Unprojected clause.** A null reports (i) `TSTARGAP`,`DIV` with power; (ii) raw `quo`/rank-rates so the
redundancy is a number; (iii) untested refinements (larger `|V|`, `T_cap`, other `m` if S₅ becomes feasible).
**CLOSURE LEDGER** (DESIGN_suppression_counter_v1) attached in the RESULT for any null.

## §9 Files
`semaev_relation_cost_v2.py` (reuses wide-schedule curves; direct `m=3` enumeration + within-target
differences + `rank_ℚ`/`rank_{ℤ/n}` via SNF); `_SCHEDULE_relation_cost_v2.*` (SHA'd); `..._v2.log`;
`RESULT_semaev_relation_cost_v2.md`; `PREREG_semaev_relation_cost_v2_DEVIATIONS.md`.

## §10 CHANGE LOG v1→v2
1. **B1:** object = within-target-difference matrix `M_diff` (reduced rank; `quo=1`→0 rows); raw-rows/"fresh
   unknown then rank over factor-base columns" removed. C1 gains target-level plants.
2. **B2:** primary field = **ℤ/n** (`n=#E`, SNF); ℚ-rank kept only as the `DIV=rank_ℚ−rank_{ℤ/n}` redundancy
   detector (H2); the backwards "ℚ lower-bounds ℤ/n" claim corrected. C1(c) validates `DIV`.
3. **B3:** primary = **`T*` rate** (targets to `rank=|V|−1`), not fixed-budget `RANKGAP`; C5 recast as
   uncensored-reachability; power re-derived for `T*`.
4. **N1–N4:** A2/A3 CI rule; C1 reduced-rank targets; C2 exact-equality-after-dedup; power floor set
   post-calibration against realized spread.
