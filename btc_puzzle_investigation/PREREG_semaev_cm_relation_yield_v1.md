# PREREG — the R1 CM relation-yield test: does CM structure raise Semaev decomposition count BEYOND the automorphism factor, group order controlled? (v1)

**File:** `PREREG_semaev_cm_relation_yield_v1.md`  **Date:** 2026-08-07
**Status: PRE-RUN / DRAFT for `experiment-designer`.** No confirmatory statistic in §3 computed.
**Executes the owed follow-up of `RESULT_semaev_dsolv_statistic_power_v1.md` §4** — the "real B": a
pre-registered, matched **consistent-regime** comparison that (a) controls for group order, (b) uses
`quo` (relation yield) and consistent-regime `d_solv`, (c) tests the Finding-3 CM decomposition-count
effect, (d) carries a firing control that fires in the consistent regime.

**What the prior work established (grounding, not re-litigated).**
- **F1 `[PROVED-mechanical]`:** the *inconsistent*-regime `d_solv` is forced curve-independent
  (`= deg(Sx)+m(|V|−1)`, the isobaric leading form is curve-free) ⇒ **zero power**. This run uses the
  **consistent** regime only.
- **F2 `[EMPIRICAL, reproduced]`:** secp is **not** special vs the other CM curve — over K=15 draws
  j1728 (μ₄) matches or exceeds secp (μ₆). So the object is **not "secp vs the world"**; it is
  **CM (μ₄,μ₆) vs non-CM (μ₂)**.
- **F3 `[EMPIRICAL, suggestive, CONFOUNDED]`:** both CM curves carry a right-tail of higher `quo` than
  non-CM, growing with `|V|` — but **confounded by group order** (the three curves have different `#E`
  at fixed `p`) and un-pre-registered. This run de-confounds it.

---

## §0 SCOPE BANNER (governs every number)

Enumerable model curves `E : y²=x³+Ax+B` over small `F_p` (`p ≡ 1 mod 3` so `j=0` and `j=1728` both
exist and μ₃ is defined; a few hundred to a few thousand). `p = 2²⁵⁶−2³²−977` is **not** enumerable;
**nothing here transfers to it** — the Semaev system and its Gröbner solve are built over the full small
field. **The automorphism relation-yield effect is, at most, the classically-known `√|Aut|` speedup**
(negation √2 for every curve; the extra μ₃ of `j=0` gives √6 total — Wiener–Zuccherato 1998,
Duquesne 2008; `[CITED — to verify]`). A **confirmed |Aut|-factor effect re-measures a known bounded
constant, NOT a new lever**; the only novel outcome is **excess beyond |Aut|**. Either way it is a
constant factor, does not change the subexponential index-calculus asymptotics, and is **no secp break**.
No ECDLP/extraction/security claim is made or derivable.

---

## §1 OBJECT (reuses the FROZEN instrument `semaev_elimination_v1.py`)

For a curve `E/F_p` and `m` (points per relation), the Semaev summation polynomial `S_{m+1}` plus the
factor-base field equations `∏_{r∈V}(x_i−r)` form the **decomposition system** an index-calculus
attacker solves per target `t`. Exact over `GF(p)` (no float). From `measure_system(F,A,B,m,tval,V,Dmax)`:

```
quo    = dim_{F} F[x]/I   (I = decomposition ideal, dim 0)  = # decompositions of t over V  [RELATION YIELD]
d_solv = min D s.t. the Macaulay quotient dim at degree D reaches `quo`      [SOLVING-DEGREE cost proxy]
d_ff   = first-fall degree;  d_gb = max Gröbner-basis degree                 [secondary]
```

- **Consistent regime only.** Targets come from `decomposable_target(F,A,B,m,extra,seed)` — a genuine
  sum of `m` factor-base points, so the variety is nonempty (`dim I = 0`, `quo ≥ 1`). The inconsistent
  regime (F1) is **excluded by construction**; any cell returning `dim = −1` is dropped and logged.
- **`quo` is the attack-relevant statistic.** More decompositions per target ⇒ fewer targets to collect
  a full relation set ⇒ a relation-collection **search-space reduction** — this is the object.

**Curve classes (per prime).**
| class | `(A,B)` recipe | `|Aut|` | `μ` |
|---|---|---|---|
| `j0` (secp form) | `(0, B)`, `B` a fixed nonzero residue | 6 | μ₆ |
| `j1728` | `(A, 0)`, `A` a fixed nonzero residue | 4 | μ₄ |
| `nonCM` (baseline, **≥3 per prime**) | random `(A,B)`, `j∉{0,1728}`, `4A³+27B²≠0` | 2 | μ₂ |

The **≥3 non-CM curves per prime** give a within-prime non-CM `quo`-vs-`#E` baseline, so `#E` varies
*within* the non-CM class too (needed for the §3 regression to separate `#E` from CM-class).

---

## §2 FORCED / ANCHOR FACTS — contribute ZERO evidence

- **A1 — `#E` drives `quo` (the confound to remove).** For a random decomposable target from a size-`|V|`
  base, `E[quo] ≈ 1 + (|V|^m/m!)/#E`-scale: `quo` rises with `|V|` and falls with `#E`. **`#E` is a
  covariate, not the effect.** The run logs `#E` per curve and regresses it out (§3). A "CM has higher
  quo" claim that does not hold `#E` fixed is F3's confound and is barred.
- **A2 — the negation automorphism is universal.** Every curve has `±1` (√2). The **differential** CM
  effect is μ₃ (`j=0`, ×3 over μ₂) or the extra μ₂ (`j=1728`, ×2). The pre-committed "known-effect"
  benchmark is the `|Aut|`-ratio `ρ_Aut = |Aut|_CM/|Aut|_nonCM` (= 3 for `j0`, 2 for `j1728`).
- **A3 — `deg(Sx)` curve-independent `[PROVED]`.** The leading form is isobaric/curve-free, so any
  `d_solv` **difference** lives entirely in the lower-order (curve-dependent) terms; a `d_solv` *equality*
  across curves is partly forced and is read only jointly with `quo`.

---

## §3 HYPOTHESES & STATISTICS (frozen; sign pre-committed from F3 = CM higher)

Design: `P ≥ 24` primes `p ≡ 1 mod 3` (schedule frozen §6); per prime, the `j0` + `j1728` curves and
`≥3` random non-CM curves; per (curve, prime), `K` decomposable targets (matched seed list), `m=3`
(primary) and `m=4` where `Dmax` resolves (secondary). Cell statistic `Q = mean_K quo` (and its
distribution), with `#E` and `|V|` logged. `|V|` **held equal across the three classes at each prime**
(`|V| = m + extra`, `extra` frozen) so the only cross-class variables are `#E` and `μ`.

| id | hypothesis / statistic (verdict-bearing) | null |
|---|---|---|
| **H1 (PRIMARY — is there a CM `quo` effect at all, `#E` controlled?)** | Regress `log Q` on `log #E` (covariate) + `CM` indicator (1 for `j0`,`j1728`; 0 for non-CM) across all cells; test the **CM coefficient `β_CM > 0`**, one-sided. | permute the `CM`/`nonCM` **class labels** across cells (holds `#E`, `|V|`, the `Q` multiset fixed); ≥1e4 shuffles; integer-rank p-value |
| **H2 (DECISIVE — is it MORE than the automorphism factor?)** | Is `β_CM` **greater than `log ρ_Aut`** (the known-effect benchmark, `ρ_Aut`=3 for `j0`, 2 for `j1728`; run `j0` and `j1728` as separate CM levels so each carries its own `ρ_Aut`)? Statistic: the `#E`-adjusted ratio `R = Q_CM / (ρ_Aut · Q_nonCM^{pred})` where `Q_nonCM^{pred}` is the regression's non-CM prediction at the CM curve's `#E`; test `R > 1` one-sided, per CM level, pooled by Stouffer. | bootstrap the regression residuals; `R`'s null centered at 1 under "effect = exactly `ρ_Aut`" |
| **H3 (MECHANISM — does the effect need an `Aut`-closed factor base?)** | `mu3_lever_test`-style: on `j0`, compare `quo` for a **β-invariant `V`** (μ₃-closed) vs a **random `V`** of the **same size**, same decomposable target. Statistic: `quo_βinv − quo_rand`, paired across primes, one-sided. | permute the (βinv ↔ rand) label per prime |
| secondary | consistent-regime `d_solv`: CM vs non-CM, `#E`-adjusted, reported not verdict (A3: partly forced). | class-label permutation |

**Verdicts (conjunctions, no post-hoc subset).**
`KNOWN-FACTOR` = H1 fires ∧ H2 null (`β_CM ≈ log ρ_Aut`): the CM relation-yield advantage is (within
power) the classically-known `√|Aut|` speedup — **re-measured, in the index-calculus/Semaev setting for
the first time; a bounded constant, not a lever.**
`EXCESS` = H1 fires ∧ H2 fires (`β_CM > log ρ_Aut`): CM raises relation yield **beyond** the automorphism
factor — the novel result; next probe named (§9), still a constant unless it grows with `m`/`p`.
`NULL` = H1 null (`#E`-adjusted, adequately powered §7): no CM `quo` effect survives the group-order
control — F3 **was** the confound. A scoped null, not a closure.

---

## §4 CONTROLS (all must fire / hold; no verdict if any fails)

- **C1 — firing control (consistent regime, the §4d requirement).** A **planted** decomposable system
  with a deliberately inflated decomposition count (a factor base seeded with several `Aut`-orbit-closed
  point sets summing to the target) must show `quo` far above the class baseline, and the H1 regression
  must recover a positive planted `β`. If C1 does not fire, **no verdict**.
- **C2 — `#E`-covariate sufficiency.** Within the **non-CM class alone** (all μ₂), regress `log Q` on
  `log #E`: the slope must be significantly negative (A1) and CM-indicator-free by construction — this
  confirms `#E` is captured before it is used to adjust the CM comparison. If the non-CM `#E` slope is
  flat/ill-fit, the covariate control is void and H2 is not run.
- **C3 — `|V|` equality asserted.** `|V|` identical across the three classes at every prime (code
  assert). A per-class `|V|` drift would reintroduce A1's scaling as a fake CM effect.
- **C4 — negation-only sanity.** A μ₂ curve compared to another μ₂ curve (two non-CM) must give
  `β = 0` within the null band (the class contrast is null when both are non-CM). Fires by landing in-band.
- **C5 — group-law construction check.** `verify_group_law` (harness) passes for each `S_{m+1}` used
  (ok>0, bad=0); a decomposable target's own decomposition is a root of the system (`quo ≥ 1`).

**Tautology guard.** `quo` (a solution count of the decomposition ideal) and `#E`/`μ` (curve invariants)
are disjointly constructed; the class-label permutation null holds `quo` fixed and shuffles only the
label, so a firing is "yield ranks with CM class," never a definitional identity. `μ` is read from
`(A,B)` (`j`-invariant), never from `quo`.

---

## §5 EXACTNESS (project no-float rule)

- **Exact int / GF(p):** all curve arithmetic, `#E`, the Semaev system, `I.vector_space_dimension()`
  (`quo`), the Macaulay ranks (`d_solv`), all permutation/rank counts and p-values (integer counts).
- **Sanctioned analytic-only float:** the regression `log Q ~ log #E` is a **ranked** statistic — the
  verdict is the **permutation p-value of `β_CM`** (integer-count), never a float threshold on `β`
  itself; `log` is a monotone transform inside a permutation-nulled statistic (allowed per directory
  rule). No key/scalar/`quo`/`#E` bit is on a float path. `check_no_float.sh` on the statistic module.

---

## §6 SCOPE & SCHEDULE (frozen pre-run, SHA-256'd)

- **Primes:** the first `P ≥ 24` primes `p ≡ 1 mod 3` above a frozen anchor set spanning `[≈500, ≈8000]`
  (deterministic rule frozen here so the set cannot be chosen to help). At each, `j0=(0,B0)`,
  `j1728=(A0,0)` with `B0,A0` the smallest residues giving a valid curve, and the **first ≥3** random
  non-CM curves (frozen PRNG seed per prime, `j∉{0,1728}`) that admit a decomposable target.
- **Targets:** `K` decomposable targets per (curve, prime), a **frozen seed list** shared across classes
  at each prime (so target-draw luck is matched); `m=3` primary, `|V| = m + extra` with `extra` frozen
  (start `extra=1`→`|V|=4`, add `extra=2` if compute allows). `m=4` secondary where `Dmax` resolves
  `quo` (else logged `unresolved`, dropped — not counted as data).
- **Cost.** Each cell = a 0-dim Gröbner/vector-space-dim over `GF(p)` for a size-`|V|`, `m`-variable
  system; `m=3,|V|≤5` is seconds. `24 primes × ~5 curves × K targets × {m=3}` ≈ hours. `m=4` gated on
  the `S₅` build time (the 08-05 note: `S₆` intractable; `S₅` may be heavy — time-boxed, logged).
- **`_SCHEDULE.txt`** (SHA-256'd with this spec before the first solve): the prime list, the `(A,B)` of
  every curve with its `#E`, `μ`, the `K` seed list, `extra`. A post-run audit verifies the SHA precedes
  any confirmatory `quo`.

---

## §7 POWER

- **H1 (regression `β_CM`).** With `P≥24` primes × (2 CM + ≥3 nonCM) ≈ **120 cells**, a class-mean
  `log Q` separation of `0.3` (a ×1.35 `quo` ratio) at the observed cell scatter is detected one-sided
  at the permutation α=0.01 with power ≈0.8 (to be recomputed by `experiment-designer` against the
  realized cell count and residual scatter). The known-`ρ_Aut` effect (`log 3 ≈ 1.1`, `log 2 ≈ 0.69`) is
  **large** relative to this floor, so H1 is expected to fire if F3 is real; the informative test is H2.
- **H2 (excess over `ρ_Aut`).** Powered by the residual scatter of `R` about 1; report the minimum
  detectable excess (e.g. `R = 1.3`) at the realized cell count. A null H2 with `|R−1|` below that floor
  is `[UNDERPOWERED-excess]`, **not** "exactly the automorphism factor."
- **H3 (Aut-closed FB).** Paired across `P` primes; power from the paired-difference scatter.
- The powered claim is **H1 ∧ (H2 fires ⇒ EXCESS | H2 null ⇒ KNOWN-FACTOR)**; each with its floor.

---

## §8 PRE-COMMITTED OUTCOME TABLE (no dismissal vocabulary; every row a positive result)

| # | Outcome | Reported as |
|---|---|---|
| **A1** | H1 fires ∧ H2 fires (`β_CM > log ρ_Aut`, powered) | **EXCESS: CM structure raises Semaev relation yield beyond the `√|Aut|` automorphism factor**, `#E` controlled, on model primes. Report `β_CM`, `R` per CM level, the `d_solv` reading, and whether the excess grows with `m`/`|V|` (the only route to more-than-constant). Next probe: does the excess scale, or is it a bounded constant? — its own prereg. **No secp/ECDLP claim.** |
| **A2** | H1 fires ∧ H2 null `[powered]` | **KNOWN-FACTOR: the CM relation-yield advantage is (within power) the classically-known `√|Aut|` speedup**, now measured in the Semaev/index-calculus setting, `#E` controlled. A bounded constant (√6 for `j=0`), not a new lever — but a clean confirmation that secp's `j=0` carries the known factor here too. Report `β_CM ≈ log ρ_Aut`. |
| **A3** | H1 fires ∧ H2 `[UNDERPOWERED-excess]` | CM `quo` effect present and `#E`-controlled; excess-over-`ρ_Aut` not resolved at this cell count. Report H1; H2 needs more primes/targets. NOT graded EXCESS. |
| **A4** | H1 null `[powered]` | **NULL: no CM relation-yield effect survives the group-order control** — F3 was the `#E` confound. Scoped null bound to method+sample+floor; the automorphism factor may still act on `d_solv`/asymptotics untested here; not a closure of "CM index-calculus structure." |
| **A5** | H3 fires (Aut-closed `V` >> random `V`) | the relation-yield effect **requires an `Aut`-closed factor base** — a known index-calculus design choice (factor-base compression by automorphisms), reported as the mechanism, with its own `|V|/|Aut|`-shrink baseline separated. |
| **A6** | any of C1–C5 fails | that arm reports "control did not fire; uninformative"; no verdict. |

**Unprojected-covariate clause.** If H1 is null, do NOT report "no structure": report (i) the `#E`-slope
and residual scatter with the power floor; (ii) the raw (un-adjusted) CM/non-CM `quo` ratio so the F3
confounded effect size is a number; (iii) untested extensions (`m≥4`, `Aut`-closed FB at scale, `d_solv`
asymptotics) as next candidates, not absences.

**Output type:** a characterization of relation yield with its power and §0 scope. Never ECDLP/
extraction/security; the automorphism factor is explicitly a **known bounded constant**, and any
"EXCESS" is a constant unless shown to grow.

---

## Files this run will produce
- `semaev_cm_relation_yield_v1.sage` (reuses `semaev_elimination_v1.py`: `measure_system`,
  `decomposable_target`, `mu3_lever_test`; adds the multi-prime schedule, the `#E` regression, the
  permutation nulls, the plant C1).
- `_SCHEDULE.txt` (frozen prime/curve/#E/seed list, SHA-256'd) · `..._v1.log` · `..._results.jsonl`.
- `RESULT_semaev_cm_relation_yield_v1.md` (characterization + bounds).
- `PREREG_semaev_cm_relation_yield_v1_DEVIATIONS.md`.
