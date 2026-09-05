# PREREG — does the CM yield advantage reduce relation-collection COST? (rank, not quo) — v1

**File:** `PREREG_semaev_relation_cost_v1.md`  **Date:** 2026-08-07
**Status: PRE-RUN / DRAFT for `experiment-designer`.** No confirmatory statistic computed.
**Follows** the confirmed A1 candidate of `RESULT_semaev_cm_relation_yield_v3_wide.md` /
`..._scaling.md`: CM (j0/μ₆) curves give **more Semaev decompositions per target** (`quo`) than
group-order-matched non-CM curves, growing with `|V|`, robust across `p∈[523,8011]`. **This spec asks the
consequential question that decides curiosity-vs-lever: does the higher `quo` translate into a real
relation-collection COST reduction — i.e. more *independent* relations per target — or is the extra `quo`
linearly REDUNDANT (automorphism-related duplicates that add no rank)?**

**The pivot from `quo` to rank.** Index calculus needs `≈|V|` **independent** relations (rank of the
factor-base relation matrix) to solve the factor-base logs. Extra decompositions of a target only lower
cost if they are **independent**. So the cost-relevant statistic is **rank of the accumulated relation
matrix per fixed target budget**, NOT `quo`. If CM has higher `quo` but the **same rank rate**, the yield
advantage is real but **inconsequential** — a structural curiosity, not a lever. Either outcome is a valid,
pre-committed answer.

---

## §0 SCOPE BANNER
Enumerable model curves `E:y²=x³+Ax+B` over small `F_p` (`p≡1 mod 3`, wide log-spaced schedule
`[523,8011]`, the frozen v3 wide set). `m=3`. **No transfer to `2²⁵⁶`; no ECDLP/extraction/security claim.**
Object = **CM (μ₆ j0) vs non-CM (μ₂)** — j0 only (the surviving robust effect; j1728/μ₄ faded and H2
weakened in the wide run, not re-tested here). Any effect is a **model-scale constant factor** on the
relation-collection rate; whether it changes the subexponential index is out of scope.

## §1 OBJECT — the relation matrix (exact, no Gröbner)
Factor base `F = {P_1,…,P_{|V|}}`, `|V|` points on `E` (same random construction / seed as the H1 test).
For a target point `T`, a **decomposition** is a net-coefficient vector `c ∈ ℤ^{|V|}` with
`Σ_i c_i P_i = −T`, obtained by exact enumeration of `m=3` ordered picks from `F ∪ (−F)` (each `±P_i`),
`|c_i| ≤ m`. Each decomposition is one **relation** (row) over the factor-base logs:
`Σ_i c_i·log(P_i) = −log(T) (mod n)`.

- **`quo(T)`** = number of distinct decompositions of `T` (the yield statistic — known higher for CM).
- **Relation matrix `M`** = the rows `c` accumulated over processed targets `T_1,…,T_j` (append the
  target column as `−T`'s coordinate is a fresh unknown per target, so rank is taken over the **factor-base
  columns only** — the standard reduced relation matrix). **`rank(M)`** over `ℚ` = independent relations.
- **Exactness:** all point arithmetic exact over `GF(p)`; `c` are exact small integers; `rank` is exact
  `ℚ`-rank of an integer matrix (Sage `matrix(QQ,…).rank()`), no float. Targets drawn from a frozen seed
  list **shared across curves** at each prime.

**Why `ℚ`-rank is the right proxy (and its scope).** A relation adds cost-reducing information iff it is
`ℤ/n`-independent of the collected ones. `ℚ`-rank lower-bounds `ℤ/n`-rank and is exact and
curve/`n`-agnostic; it captures "does this decomposition carry new linear information." (`ℤ/n`-rank
refinement — where `n=#E` differs per curve — is a §7 tertiary, not the primary; flagged for the gate.)

## §2 FORCED / ANCHOR FACTS (zero evidence)
- **A1 — CM `quo` > non-CM `quo`** is ESTABLISHED (wide run). Re-measuring `quo` here proves nothing new;
  it is logged only to compute the **`quo`-gap vs rank-gap** contrast (§3 H2).
- **A2 — trivial dependency.** The all-relations-share-`log G` normalization removes one d.o.f.; the
  solvable threshold is `rank = |V|−1`, pre-committed.
- **A3 — enumeration completeness.** `m=3` net-coefficient enumeration over `F∪(−F)` is exhaustive for
  `m=3` decompositions; asserted in code (cross-check vs `measure_system` `quo` on ≥3 cells: counts match).

## §3 HYPOTHESES & STATISTICS (frozen; matched-#E paired, sign pre-committed = CM cheaper/higher-rank)
Per wide prime `p`: pair `j0` with the nearest-`#E` non-CM curve (same rule as H1). Fixed target budget
`T_max` (§6). `|V|∈{4,6}` (the low and high Scaling ends).

| id | statistic (verdict-bearing) | matched null |
|---|---|---|
| **H1 (PRIMARY — independent relations per fixed budget)** | `RANKGAP = rank(M_j0 @ T_max) − rank(M_nonCM @ T_max)`, matched-#E paired, pooled over primes; one-sided (`>0`, CM more independent relations ⇒ fewer targets ⇒ cheaper). | within-pair (j0↔nonCM) label swap; ≥1e4; integer-rank one-sided p |
| **H2 (DECISIVE INTERPRETATION — is the yield advantage independent or redundant?)** | Contrast the paired `RANKGAP` against the paired `QUOGAP = log(Σquo_j0) − log(Σquo_nonCM)` (known `>0`). Pre-committed reading: **`RANKGAP>0` (powered) ⇒ yield IS cost-reducing; `QUOGAP>0 ∧ RANKGAP≈0` (powered) ⇒ extra `quo` is REDUNDANT, yield does NOT reduce cost.** | same swap null on `RANKGAP`; `QUOGAP` is anchor (A1), not re-tested |
| **secondary** | `T*` = targets to `rank=|V|−1`, CM vs non-CM (right-censored at `T_max`; report median + censoring); a cost readout, not the primary (censoring). | within-pair swap on uncensored pairs |

**Verdicts (pre-committed).**
`COST-REDUCING` = H1 fires (`RANKGAP>0`, powered): the CM yield advantage gives **more independent
relations per target** — the candidate lever is **consequential** at model scale.
`REDUNDANT-YIELD` = H1 null (powered) while `QUOGAP>0`: the extra CM decompositions are linearly
**dependent** — the yield advantage is real but **does NOT reduce relation-collection cost**. A valid,
important negative: it downgrades the candidate from "reduction lever" to "structural curiosity."
`NULL` = H1 null and the plant/controls leave it uninformative (→ A-controls).

## §4 CONTROLS (all must fire/hold; no verdict if any fails)
- **C1 — firing plant.** A factor base engineered so its decompositions are **known-independent** (relations
  = the |V| standard basis directions, by construction) must show `rank` climb to `|V|−1` fast; and a plant
  of **known-redundant** relations (all scalar multiples of one vector) must show `rank` stuck at 1. Both
  must be recovered — this proves the rank statistic **distinguishes independent from redundant** (the whole
  point). No fire ⇒ no verdict.
- **C2 — enumeration vs Gröbner.** On ≥3 cells, the direct-enumeration decomposition count equals
  `measure_system`'s `quo` (exactness cross-check).
- **C3 — #E-match adequacy.** Median relative `#E` gap ≤ `2/√p` per pair (reuse H1's C2), sign-balanced.
- **C4 — non-CM vs non-CM null.** Two matched non-CM curves give `RANKGAP ≈ 0` (in-band) — so a nonzero
  `RANKGAP` is a class effect, not a matching artifact.
- **C5 — target budget adequacy.** `T_max` large enough that `rank(M_nonCM)` reaches `≥ 0.8·(|V|−1)` at
  the median prime (so H1 is not measuring a floor effect); reported as a number pre-run.

## §5 EXACTNESS
All point arithmetic exact `GF(p)`; `c` exact `ℤ`; `rank` exact `ℚ`-rank of integer matrices; all
permutation/rank counts integer. `RANKGAP`/`QUOGAP` verdicts decided by the **integer permutation rank**,
never a float threshold. `check_no_float.sh` on the statistic module. (`QUOGAP` uses `log` only inside the
anchor readout, not a verdict.)

## §6 SCOPE & SCHEDULE (frozen, SHA-256'd pre-run)
- **Primes:** the frozen wide set `[523…8011]` (24, log-spaced) — reuse `_SCHEDULE_..._v3_wide` curves so
  the cost test is on the **same objects** as the yield finding (SHA recorded).
- **`|V| ∈ {4, 6}`**; `m=3`; **`T_max = 200`** targets per (curve, prime) (frozen; §7 power); frozen target
  seed list shared across the paired curves at each prime.
- **Cost:** direct enumeration is `(2|V|)^3 ≤ 1728` point-sums per target × 200 targets × ~3 curves × 24
  primes × 2 `|V|` ≈ cheap (minutes–≈1h; no Gröbner). Rank updates incremental.
- **`_SCHEDULE_relation_cost_v1`** (SHA'd pre-run): prime list, curves+`#E`, `|V|` set, `T_max`, seeds.

## §7 POWER
- **H1 `RANKGAP`.** 24 primes × (paired) ⇒ 24 paired diffs per `|V|`. If the per-prime `RANKGAP` s.d. ≈ 1.0
  (rank units) and a true mean gap ≥ 0.5, pooled SE ≈ `1/√24 = 0.20`, detectable one-sided α=0.01 at power
  ≈0.8 for a mean `RANKGAP ≥ 0.6`. `[UNDERPOWERED]` if `|RANKGAP| < 0.6`. (Re-estimate against realized
  s.d. — `experiment-designer`.)
- **C5 floor:** `T_max=200` must give `rank(M_nonCM) ≥ 0.8(|V|−1)` at the median prime, else raise `T_max`.
- Tertiary (`ℤ/n`-rank) power not pre-set (exploratory).

## §8 PRE-COMMITTED OUTCOME TABLE (no dismissal vocabulary)
| # | Outcome | Reported as |
|---|---|---|
| **A1** | H1 fires (`RANKGAP>0`, powered) | **COST-REDUCING:** CM (j0) yields more **independent** relations per target, `#E`-matched — the yield advantage lowers relation-collection cost at model scale. Report `RANKGAP` per `|V|`, the `T*` readout, and whether `RANKGAP` grows with `|V|` (parallels the yield growth). **Still model-scale; no ECDLP/secp claim; the subexponential-index question remains out of scope.** Next: does the rank advantage scale (its own prereg). |
| **A2** | H1 null (powered) ∧ `QUOGAP>0` (anchor) | **REDUNDANT-YIELD:** the extra CM decompositions are linearly **dependent** — the (real) `quo` advantage does **NOT** reduce relation-collection cost. Downgrades the candidate from "reduction lever" to a **structural curiosity** (yield without independence). Report `RANKGAP≈0` with its power, the `quo`/rank contrast, and the (likely automorphism-related) redundancy mechanism as the next characterization. A backed null, not a closure of "CM index-calculus structure." |
| **A3** | H1 `[UNDERPOWERED]` (`|RANKGAP|` below floor) | rank effect not resolved at `T_max`/24 primes; report the bound + power, raise `T_max`/primes. Not a verdict. |
| **A4** | any C1–C5 fails | that arm uninformative; no verdict. |

**Unprojected clause.** An H1 null must report (i) `RANKGAP` with power; (ii) the raw `quo`/rank rates so
the redundancy is a number; (iii) untested refinements (`ℤ/n`-rank, larger `T_max`, other `|V|`).

**Output type:** a characterization of relation-collection cost with power + §0 scope. Never ECDLP/secp/
security. The CLOSURE LEDGER (DESIGN_suppression_counter_v1) is attached in the RESULT for any null.

## §9 Files
`semaev_relation_cost_v1.py` (reuses `semaev_elimination_v1.py` curves + the wide schedule; direct m=3
enumeration + `ℚ`-rank); `_SCHEDULE_relation_cost_v1.*` (SHA'd); `..._v1.log`;
`RESULT_semaev_relation_cost_v1.md`; `PREREG_semaev_relation_cost_v1_DEVIATIONS.md`.
