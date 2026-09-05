# DEVIATIONS — `PREREG_semaev_cm_relation_yield_v3.md` run (2026-08-07)

Run: `semaev_cm_relation_yield_v3.py` → `semaev_cm_relation_yield_v3.log`. Recorded against the frozen spec.

| # | Pre-committed (spec) | Actual | Handling / impact |
|---|---|---|---|
| **D1** | §6: "first `P=24` primes `p ≡ 1 mod 3` above a frozen anchor set **spanning `[≈500, ≈8000]`**". | `primes_1mod3(500, 24, cap=8000)` returned the **first 24** primes `≡1 mod 3` above 500 = **[523 … 823]** — it did NOT log-space to 8000. | **Material scope deviation.** Deterministic (no cherry-picking; rule-fixed), so pre-registration integrity holds, but the between-prime `#E` range is narrow (~523–823). The within-prime matched-pair H1 statistic is unaffected (each pair is at one prime); the "toward scale" reach is untested. **Recorded as the #1 next probe (wider-range rerun).** Fix: `primes_1mod3` → log-spaced next-prime rule. |
| **D2** | §6: `m=3` primary, `m=4` secondary "where `Dmax` resolves". Scaling arm tests growth with `|V|` AND `m`. | Only **`m=3`** run (`|V|∈{4,5}`). `m=4` (S₅) not attempted (time-box). | The Scaling "grows" verdict rests on the **`|V|` axis, 2 points**. The `m` axis is unrun. Owed; noted in RESULT §3/§4. Does not affect H1's firing (H1 is `m=3`). |
| **D3** | §4 C4: "split the non-CM curves into high-/low-`#E` halves … must give `T1≈0`". | Implemented as the **nearest-`#E` non-CM/non-CM matched pair** (the two non-CM curves not used as CM matches), `Δ = logQ − logQ`. | Equivalent negative-control intent (matched non-CM contrast ⇒ ≈0 when no class effect); the v2 gate read C4 this way. Result behaved (mean ≈0.01–0.03, in-band). The literal high-vs-low split is a stronger `#E`-sensitivity probe, owed to the wider-range rerun. |
| **D4** | §4 C1: plant "seeded with several x-closed point-orbits". | Plant seeded with **`n_decomps=3` genuine decompositions**, factor base **capped at `|V|=7`** for field-equation tractability (an uncapped plant hit degree-24 field equations and hung). | Firing intent met (`quo=18` ≫ baseline). The "x-closed orbits" wording is a stronger plant; the capped-decomposition plant is a valid firing control (detects inflated `quo`). |
| **D5** | §6: `K=25`, `≥5` non-CM per prime, `|V|=m+extra`. | `K=25`, exactly **5** non-CM per prime, `|V|∈{4,5}`. As specified. | Not a deviation. |

**Not deviations (as specified):** consistent-regime targets only (`decomposable_target`, `dim=0`);
exact GF(p) `quo`/`d_solv`; within-pair sign-flip permutation null (20 000 draws); schedule frozen +
SHA-256 (`f92cb4bb…`) before the first `quo`; `#E`-nearest integer matching.
