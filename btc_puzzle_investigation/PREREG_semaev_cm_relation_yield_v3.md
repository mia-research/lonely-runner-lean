# PREREG — the R1 CM relation-yield test (v3): does CM raise Semaev decomposition count, group order MATCHED? (the automorphism factor does NOT live in single-target `quo` — corrected)

**File:** `PREREG_semaev_cm_relation_yield_v3.md`  **Date:** 2026-08-07
**Supersedes v2** after a second `experiment-designer` gate + a decidable check (`conservation_check.py`) that
**refuted** the v2 benchmark. **Status: PRE-RUN / DRAFT for a third `experiment-designer` pass.** No
confirmatory statistic computed. **Executes the owed follow-up of `RESULT_semaev_dsolv_statistic_power_v1.md` §4.**

**The three v1 defects and the redesign they force.**
- **B1 (benchmark).** `ρ_Aut` (the classical automorphism speedup) is derivable only for an **Aut-closed**
  factor base; on a **random** factor base the automorphism maps a decomposition of `t` to one of `ζt≠t`,
  so no |Aut| inflation acts. v1 benchmarked the random-V arm against `ρ_Aut` and conflated |Aut|=6,
  √|Aut| (runtime), and the x-coordinate order 3. **v2 splits the two arms:** H1 (random V) is an
  **unbenchmarked** magnitude; the automorphism benchmark moves to H2 (**Aut-closed vs random V**), where
  the correct factor is the **x-coordinate automorphism order** `κ` (**3** for j=0's μ₃, **2** for
  j=1728's x↦−x, **1** for non-CM) — *derived* below, not cited.
- **B2 (`#E` confound re-entry).** v1's `log #E` covariate mis-modeled A1's own `1/#E` law, and its
  class-label permutation randomized the class–`#E` association, letting a CM-trace-biased `#E` subset
  fake `β_CM`. **v2 replaces the covariate regression with a MATCHED-`#E` paired design** (each CM cell
  paired to its nearest-`#E` non-CM cell at the same prime) + a **within-pair** permutation null, so `#E`
  is controlled by matching, not by a parametric form, and the null preserves the class–`#E` association.
- **B3 (post-hoc power).** Every floor (H1, H2) is pinned as a number here (§7).

---

## §0 SCOPE BANNER (governs every number)

Enumerable model curves `E : y²=x³+Ax+B` over small `F_p` (`p ≡ 1 mod 3` so `j=0` and `j=1728` exist and
μ₃ is defined; `p ∈ [≈500, ≈8000]`). `p = 2²⁵⁶−2³²−977` is **not** enumerable; **nothing here transfers**.
**Ceiling — corrected in v3, and it is NOT an a-priori bound.** The classical automorphism speedup (`κ≤3`,
Wiener–Zuccherato 1998, Duquesne 2008) is a **target-orbit / factor-base-SIZE** effect (one target per
Aut-orbit) — it does **NOT** live in single-target `quo`: the automorphism sends `x_i↦ωx_i` *and* `t↦ωt`,
so it maps a decomposition of `t` to one of `ωt≠t` (does not inflate a fixed target's `quo`), and the total
`Σ_t quo(t)` is **curve-DEPENDENT** (`conservation_check.py`: secp 28 / nonCM 16 / j1728 12 at `p=43, m=2,
|V|=4` — a ~1.8× spread, refuting the `|V|^m·2^{m-1}` equality the v2 draft assumed). **There is therefore
no conservation bound on the CM relation-yield question; it is empirically open.** The more-than-constant
route is an effect that **grows with `m`/`|V|`** (tested §3, Scaling). Constant factors do not change the
subexponential asymptotics; but "constant" is NOT assumed here — it is one of the pre-committed outcomes.
Constant factors do not change the subexponential index-calculus asymptotics. **No secp break; no ECDLP/
extraction/security claim** is made or derivable. Per F2 (`RESULT_semaev_dsolv…`): the object is
**CM (μ₄,μ₆) vs non-CM (μ₂)**, NOT secp-vs-world (secp≈j1728 already reproduced).

---

## §1 OBJECT (reuses the FROZEN instrument `semaev_elimination_v1.py`)

Per curve `E/F_p`, `m` points per relation: `measure_system(F,A,B,m,tval,V,Dmax)` over `GF(p)` (exact):
```
quo    = dim_F F[x]/I  (I the decomposition ideal, dim 0) = # decompositions of target t over base V   [YIELD]
d_solv = min D s.t. the Macaulay quotient dim at degree D reaches quo                                   [COST proxy]
```
- **Consistent regime only.** Targets from `decomposable_target(F,A,B,m,extra,seed)` (a genuine sum of `m`
  base points ⇒ `dim I=0`, `quo≥1`). The inconsistent regime (F1, forced-blind) is excluded by
  construction; any `dim=−1` cell is dropped and logged.
- **`quo` = relation yield.** More decompositions per target ⇒ fewer targets for a full relation set ⇒ a
  relation-collection **search-space reduction** — the object. **Forced common-mode (stated):** every
  decomposable target carries its own planted decomposition and its `m!` orderings, a class-**independent**
  baseline that cancels in the class contrast; the differential (extra decompositions) is unforced.

**Curve classes.** `j0=(0,B0)` μ₆; `j1728=(A0,0)` μ₄; `nonCM=(A,B)` random `j∉{0,1728}`, μ₂. `μ` read from
`(A,B)`/`j`, never from `quo`.

---

## §2 FORCED / ANCHOR FACTS — ZERO evidence

- **A1 — `#E` drives `quo` as `≈1+(|V|^m/m!)/#E`** (rises with `|V|`, falls with `#E`). `#E` is the
  confound; v2 controls it by **matching** (§3), not modeling.
- **A2 — the automorphism order `κ` acts on the TARGET ORBIT / factor-base SIZE, NOT on single-target
  `quo` (corrected in v3).** The x-coordinate automorphism order is `κ = 3` (j0: `x↦ωx`), `2` (j1728:
  `x↦−x`), `1` (nonCM; negation fixes x). The classical speedup uses this to cover targets in
  Aut-**orbits** (one target per orbit ⇒ ≤`κ` fewer distinct DLPs) — a **target-side / base-size** effect.
  It does **NOT** inflate a fixed target's `quo`: the automorphism sends `x_i↦ωx_i` AND `t↦ωt`, so the `κ`
  x-images of a decomposition of `t` decompose `ωt≠t`; and `Σ_t quo(t)` is curve-dependent, not the
  x-closure-invariant constant v2 assumed (`conservation_check.py`, §0). **Consequently `κ` is NOT a `quo`
  benchmark** — neither H1 (random V) nor H2 (x-closed V) has a `κ` prediction on single-target `quo`; both
  are unbenchmarked. (The v1/v2 error, now removed: benchmarking a `quo` ratio against `κ`, a size/orbit
  quantity living in a different observable.)
- **A3 — `deg(Sx)` curve-independent `[PROVED]`** ⇒ any `d_solv` *difference* is lower-order; `d_solv`
  read only jointly with `quo`, non-verdict.

---

## §3 HYPOTHESES & STATISTICS (frozen; sign pre-committed = CM higher, from F3)

Schedule §6. Per prime `p`: `j0`, `j1728`, and **≥5** non-CM curves (frozen), `|V|` **equal across all
classes** (`|V|=m+extra`, frozen), `K` decomposable targets per cell (frozen seed list), `m=3` primary,
`m=4` secondary where `Dmax` resolves. Cell value `Q = mean_K quo` (full K-vector logged).

| id | hypothesis / statistic (verdict-bearing) | matched null |
|---|---|---|
| **H1 (PRIMARY — is there a CM `quo` effect on a RANDOM base, `#E` MATCHED?)** | **Matched-`#E` paired design.** At each prime, pair `j0` with the **same-prime non-CM curve of nearest `#E`**, and `j1728` likewise (nearest **remaining** non-CM). Paired difference `Δ = logQ_CM − logQ_nonCM(matched)`. Statistic `T1 = mean over all pairs of Δ`, one-sided (CM higher). Run `j0` and `j1728` as **separate** CM levels (each its own pooled `T1`). **Unbenchmarked magnitude** — a positive `T1` on random V is a CM relation-yield effect that is **NOT** the factor-base-closure mechanism (A2). | **within-pair label swap**: for each matched pair independently flip the (CM↔nonCM) label, recompute `T1`; ≥1e4 draws; integer-rank one-sided p. Preserves each pair's `#E` bracket and the class–`#E` association. |
| **H2 (MECHANISM — does x-closing the base change single-target `quo` at ALL? Unbenchmarked.)** | `mu3_lever_test` on `j0`: `quo` for an **x-closed (β-invariant) `V`** vs a **random `V` of the same size**, same decomposable target. Statistic `R2 = quo_βinv / quo_rand`, paired across primes; **two-sided `R2 ≠ 1`** (reported as a signed magnitude). **No `κ` benchmark** (A2, corrected): the moving-target argument predicts `R2 ≈ 1`, so a deviation is a *novel* x-closure effect on single-target `quo`; `R2≈1` locates the known automorphism effect entirely in the target-orbit/size observable (untested here, known bounded ≤`κ`). | permute (βinv↔rand) label per prime; integer-rank p, **null centered at `R2=1`** |
| **Scaling (SECONDARY, feeds the verdict — the only route to more-than-constant)** | Does `T1` (H1) grow with `|V|`∈{m+1,m+2} and with `m`∈{3,4}? Slope of `T1` vs `|V|` and vs `m`, sign test. A **constant** `T1` ⇒ bounded; a **growing** `T1` ⇒ the candidate lever. | permutation of the (|V| ↔ T1) / (m ↔ T1) labels |
| secondary | consistent-regime `d_solv`, CM vs matched non-CM (A3: partly forced), reported not verdict. | within-pair swap |

**Verdicts (conjunctions; no post-hoc subset).**
- `CM-YIELD-EFFECT` = **H1 fires** (`T1>0`, powered): CM raises relation yield on a random base, `#E`
  matched — a real, `#E`-controlled effect not explained by factor-base closure. Then Scaling decides:
  `+ Scaling flat` ⇒ **bounded constant**; `+ Scaling grows` ⇒ **candidate lever, next probe named**.
- `X-CLOSURE-EFFECT` = H1 null (powered) ∧ H2 fires (`R2≠1`, powered): x-closing the base changes
  single-target `quo` (a novel effect — the moving-target argument predicts `R2≈1`); report the signed
  magnitude. Random bases show no CM effect, so any yield structure is x-closure-specific.
- `X-CLOSURE-NULL` = H2 `R2≈1` (powered): x-closure does not change single-target `quo` — the known
  automorphism effect lives entirely in the target-orbit / factor-base-size observable (bounded ≤`κ`,
  known, not measured here). A clean location result, not a closure of the H1 question.
- `NULL` = H1 null (powered) ∧ H2(a) null: no CM relation-yield effect survives `#E` matching and no
  x-closed shrink — F3 **was** the `#E` confound. Scoped null, not a closure.

---

## §4 CONTROLS (all must fire/hold; no verdict if any fails)

- **C1 — firing control (consistent regime).** A **planted** decomposable system whose factor base is
  seeded with several x-closed point-orbits summing to the target must show `quo` far above baseline, and
  the H1 matched-pair statistic must recover the planted excess. Fires in the consistent regime (§4d). No fire ⇒ no verdict.
- **C2 — `#E`-match adequacy (replaces v1's slope-significance C2).** For every matched pair, log
  `|#E_CM − #E_nonCM| / #E`; require the **median relative `#E` gap ≤ 2/√p** (i.e. within the same prime's
  Hasse-scale) and assert the paired `#E`-gap distribution is **sign-balanced** (CM not systematically
  higher/lower `#E` than its match) — so residual `#E` cannot masquerade as the CM effect. Pairs failing the
  gap cap are dropped and logged; if <70% of pairs survive, the schedule is regrown before freezing.
- **C3 — `|V|` equality asserted** across classes at every prime (code assert).
- **C4 — `#E`-stratified negation-only null (strengthened).** Split the non-CM curves at each prime into
  **high-`#E`** and **low-`#E`** halves and run the H1 statistic **non-CM(high) vs non-CM(low)**: must give
  `T1=0` within the null band. This is a real firing control for B2 — it fails iff the matched design still
  leaks `#E` (a nonzero non-CM/non-CM contrast would expose residual `#E` sensitivity). Fires by landing in-band.
- **C5 — group-law construction** (`verify_group_law`: ok>0, bad=0) for each `S_{m+1}`; each decomposable
  target's own decomposition is a system root (`quo≥1`).

**Pre-run `#E` common-support check (before the first solve, on the frozen schedule):** assert the CM `#E`
values lie inside the pooled non-CM `#E` support with ≥2 non-CM below and ≥2 above each CM `#E` at its
prime (regrow the non-CM sample, and **randomize the CM twist** — draw `B0`/`A0` over all valid residues,
not "smallest" — if the CM traces cluster to one side). Tautology guard: `quo` and `μ`/`#E` disjointly
constructed; nulls hold `quo` fixed and move only labels.

---

## §5 EXACTNESS (project no-float rule)

- **Exact int / GF(p):** curve arithmetic, `#E`, `quo` (`vector_space_dimension`), `d_solv` (Macaulay
  ranks), all permutation/rank counts and p-values, and the `#E`-nearest **matching** (integer `|#E−#E'|`
  comparison — no float decides a pair).
- **Sanctioned analytic-only float:** `log Q` and the ratio `R2` enter **only** as monotone statistics
  ranked against permutation nulls (integer-count p-values). **H1's `T1` and H2's `R2≠1` verdicts are
  decided by the integer permutation rank, never a float threshold**: the βinv↔rand swap centers the null
  at `R2=1`, so `#{permuted |log R2| ≥ observed}` is the exact two-sided count (no `κ`-centered null — the
  v2 §5/§7 conflict is removed). `check_no_float.sh` on the statistic module.

---

## §6 SCOPE & SCHEDULE (frozen pre-run, SHA-256'd)

- **Primes:** the first `P = 24` primes `p ≡ 1 mod 3` above a frozen anchor set spanning `[≈500, ≈8000]`
  (deterministic rule frozen here). At each: `j0=(0,B0)`, `j1728=(A0,0)`, and **≥5** non-CM curves (frozen
  seed, `j∉{0,1728}`, admitting a decomposable target and satisfying the §4 common-support/bracket rule;
  regrow to bracket both CM `#E`).
- **`K = 25`** decomposable targets per (curve, prime) — **frozen** (fixes the v1 unspecified-`K`), a frozen
  seed list shared across classes at each prime (target-luck matched). `m=3` primary; `|V|=m+extra`,
  `extra∈{1,2}` (`|V|∈{4,5}`, both run for Scaling). `m=4` secondary where `Dmax` resolves `quo` in the
  time box (else logged `unresolved`, dropped — not data).
- **Cost.** `m=3,|V|≤5` cells are seconds; `24 primes × ~7 curves × 25 targets × {|V|=4,5}` ≈ hours. `m=4`
  gated on `S₅` build (time-boxed; `S₆` intractable per 08-05).
- **`_SCHEDULE.txt`** (SHA-256'd with this spec **before the first `quo`**): prime list; every curve's
  `(A,B)`, `#E`, `μ`, `κ`; the matched-pair assignment; the `K=25` seed list; `extra`. Post-run audit
  verifies the SHA precedes any confirmatory `quo`.

---

## §7 POWER (pinned as numbers)

- **H1 (matched pairs).** `24 primes × 2 CM levels = 48` matched pairs; per-pair `logQ` scatter ≈ 0.2
  (Finding-3-consistent) ⇒ pooled SE ≈ `0.2/√48 ≈ 0.029`. At permutation **α=0.01 one-sided** (`z_α=2.326`),
  the minimum detectable mean paired difference is **`T1 = 0.105`** at power ≈ 0.9 and **`T1 = 0.092`** at
  power ≈ 0.8 (v2 quoted 0.10/0.07 with an α≈0.05 critical value — corrected). **`[UNDERPOWERED]` boundary:
  a null H1 with `|T1| < 0.092` → `[UNDERPOWERED below T1≈0.092]`, not a refutation.** (F3's raw effect, if
  `log 1.3–3`, is far above — H1 firing is expected if F3 survives `#E` matching; the informative content
  is the *magnitude* and Scaling.)
- **H2 (unbenchmarked `R2≠1`).** 24 paired primes; per-prime `log R2` scatter ≈ 0.25 ⇒ SE ≈ 0.051.
  **Two-sided α=0.01** (`z=2.576`), power ≈ 0.8 detects `|log R2| ≥ 0.174` (a ×1.19 / ÷1.19 `quo` ratio).
  **`[UNDERPOWERED]`: a null H2 with `|log R2| < 0.174` → underpowered, not "x-closure has no effect".**
  (No `κ` benchmark — the moving-target argument predicts `R2≈1`; the test is whether x-closure moves
  single-target `quo` at all.)
- **Scaling.** Slope of `T1` over `|V|∈{4,5}` and `m∈{3,4}`: 2 `|V|`-points × 48 pairs and 2 `m`-points;
  a per-step `ΔT1 ≥ 0.10` is detectable; a flat result within ±0.05 is reported "bounded (constant) at this
  range," an increase ≥0.10/step is "growing — candidate lever."
- The powered claim is the named conjunction (§3); each arm carries its own floor.

---

## §8 PRE-COMMITTED OUTCOME TABLE (no dismissal vocabulary; every row a positive result)

| # | Outcome | Reported as |
|---|---|---|
| **A1** | H1 fires (`T1≥0.092`, powered) ∧ Scaling **grows** | **Candidate lever: CM raises Semaev relation yield on a random factor base, `#E` matched, and the effect GROWS with `m`/`|V|`** — not the bounded factor-base-closure shrink. Report `T1` per CM level, the growth slope, `d_solv`. Next probe (own prereg): does it keep growing to a super-constant / does it lower relation-collection cost. **Still model-scale; no secp/ECDLP claim.** |
| **A2** | H1 fires ∧ Scaling **flat** | **Bounded CM relation-yield effect on random V** (`T1≈const`, `#E` matched) — real and not the closure mechanism, but a bounded constant at the tested range. Report `T1`, the flat slope, scope. |
| **A3** | H1 fires ∧ Scaling `[UNDERPOWERED]` | CM `quo` effect present and `#E`-matched; growth not resolved. Report H1; Scaling needs more `|V|`/`m`. NOT graded a lever. |
| **A4** | H1 null (powered) ∧ H2 fires (`|log R2|≥0.174`, powered) | **X-CLOSURE-EFFECT:** x-closing the base moves single-target `quo` (novel — the moving-target argument predicts `R2≈1`); report the signed magnitude. Random bases show no CM effect (H1 null), so any yield structure is x-closure-specific. NOT the classical target-orbit shrink (that lives in base size, not `quo`). |
| **A5** | H1 null (powered) ∧ H2 `R2≈1` (powered) | **NULL:** no CM relation-yield effect survives `#E` matching on random V, and x-closure does not move single-target `quo`. The known automorphism effect is target-orbit / factor-base-size only (bounded ≤`κ`, not measured here). Scoped null (method+sample+floor); `d_solv`/asymptotics untested; not a closure of "CM index-calculus structure." Report the raw un-matched ratio (F3's confounded size) per the unprojected-covariate clause. |
| **A6** | H1 or H2 `[UNDERPOWERED]` (floor not met) | report the bounded result with its power floor; route to A5 only when both floors are met. NOT a refutation. |
| **A7** | any C1–C5 or the common-support check fails | that arm "control did not fire; uninformative"; no verdict. |

**Unprojected-covariate clause.** An H1 null must NOT be read "no structure": report (i) the matched-pair
`Δ` distribution + power floor; (ii) the **raw un-matched** CM/non-CM `quo` ratio, so F3's confounded effect
size is a number; (iii) untested extensions (`m≥4`, x-closed base at scale, `d_solv` asymptotics) as next
candidates, not absences.

**Output type:** a characterization of relation yield with power + §0 scope. Never ECDLP/extraction/
security; the automorphism factor is an explicitly-derived bounded constant `κ≤3`; any effect is a constant
unless Scaling shows growth.

---

## §9 Files this run will produce
- `semaev_cm_relation_yield_v2.sage` (reuses `semaev_elimination_v1.py`: `measure_system`,
  `decomposable_target`, `mu3_lever_test`; adds the frozen schedule, `#E`-nearest matching, within-pair
  permutation nulls, the Scaling sweep, the plant C1, the `#E`-stratified C4).
- `_SCHEDULE.txt` (SHA-256'd) · `..._v3.log` · `..._results.jsonl` · `RESULT_semaev_cm_relation_yield_v3.md`
  · `PREREG_semaev_cm_relation_yield_v3_DEVIATIONS.md`. Instrument: `semaev_cm_relation_yield_v3.sage`.

---

## §10 CHANGE LOG

**v2→v3 (this revision) — the second gate's remaining B1 + a decidable refutation.** v2 re-attached the
automorphism factor `κ` to H2 as a **single-target `quo` inflation**; that is invalid (the automorphism
sends `t↦ωt`, moving the target), and `conservation_check.py` **refuted** the stronger "total `Σ_t quo`
curve-independent" claim (secp 28 / nonCM 16 / j1728 12 at p=43 — curve-DEPENDENT). Fixes: (i) A2 corrected —
`κ` is a target-orbit / factor-base-SIZE effect, **not** a `quo` benchmark; (ii) H2 reframed unbenchmarked
(`R2≠1`, moving-target predicts ≈1); (iii) §0 ceiling corrected — **no a-priori bound**, the CM
relation-yield question is empirically open; (iv) verdicts / A4–A6 rewritten off `κ`; (v) §5/§7 `κ`-null
conflict removed; (vi) H1 α/MDE arithmetic fixed (0.092 at power 0.8, α=0.01). H1 (matched-`#E`) + Scaling —
the primary result path — were gate-cleared and are unchanged. **The lever is preserved and centered, not
caveated away.**

## §10a CHANGE LOG v1→v2 (all 3 blocking + the non-blocking items)
1. **B1 (benchmark):** `ρ_Aut` removed from the random-V arm; H1/H2 reframed — H1 unbenchmarked magnitude
   on random V, the automorphism factor moved to H2 (x-closed vs random V) with the **derived** x-coordinate
   order `κ` (3/2/1), replacing the |Aut|/√|Aut| conflation (A2). Citation demoted to non-load-bearing context.
2. **B2 (`#E` confound):** covariate regression + class-label permutation replaced by a **matched-`#E`
   paired design** with a **within-pair** permutation null (preserves class–`#E` association); C2 recast as
   an `#E`-match-adequacy + sign-balance check; a pre-run `#E` common-support/bracket check added; CM twist
   randomized to symmetrize traces.
3. **B3 (power):** H1, H2, Scaling floors pinned as numbers (§7); `[UNDERPOWERED]` boundaries pre-set.
4. **Non-blocking:** `K=25` frozen; C4 → `#E`-stratified non-CM(high) vs non-CM(low); no-float-verdict
   extended to `R2>κ` (integer permutation count); `quo` forced common-mode (`m!`) stated as class-cancelling;
   `m`/`|V|` Scaling made an explicit arm (the more-than-constant route). Verified-good & unchanged:
   consistent-regime discipline, F2 handling (CM-vs-nonCM, j0/j1728 separate levels), tautology guard,
   exact core path, scope banner + unprojected-covariate clause, C1/C3/C5.
