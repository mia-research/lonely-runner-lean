> **⚠ RETRACTED (2026-07-21) — the "b=0 axis LOCALIZATION" claimed below is a WRONG-NULL ARTIFACT.**
> The random-unit-phase null omits the character's forced Hermitian symmetry `g(n−d)=conj(g(d))`; that
> mismatch is concentrated on the ±-symmetric pure-y axis and manufactured the −10..−13% "localization."
> Under a symmetry-matched null the on-axis deficit collapses to −0.1..−3.8% (`_axis_null_check_v1.py`).
> The AGGREGATE ~−0.1% sub-Rayleigh deficit DOES survive the matched null (`_aggregate_null_check_v1.py`,
> z≈−2..−5) but is **DIFFUSE — there is NO b=0 locus**. Prior memory `btc_puzzle_INDEX.md:210` had already
> flagged this ("wrong-null hypothesis" on the b=0,c≠0 pure-y rows). The plant/floor/replication controls
> all fired but shared the same wrong null, so they never validated it. Content retained for the record;
> **do not cite the localization claim.**

# RESULT — the sub-Rayleigh deficit is a LOCUS: the b=0 (pure-y) axis

**Date 2026-07-21.** Executes `PREREG_harmonic_deficit_locus_v1.md` (frozen pre-run).
Artifacts: `harmonic_deficit_locus_v2.py` / `.log`; direction follow-up `_axis_direction_check_v1.py`;
deviations in `PREREG_harmonic_deficit_locus_v1_DEVIATIONS.md`.
**Scope, up front:** enumerable model curves `E : y²=x³+7` over `F_p`, `a₀=1` slice, 7 primes
`163 … 2089`. `p = 2²⁵⁶−2³²−977` is not enumerable and **nothing here transfers to it**. This is a
characterization of *where* a magnitude deficit sits; **no ECDLP / extraction / security claim** is made.

---

## 0. What was tested

Input (from `RESULT_harmonic_support_pattern_v1.md` §2, not re-scored): a `mean|U|` sub-Rayleigh
deficit exists (`D(b,c)=|U(1,b,c)| − E_r|U_rand(b,c)|`, `Σ D<0`, `−13.9σ` at `p=2089`). This run tests
the §5 open question: does `D` concentrate on a **publicly-computable locus**, against a replication
gate. Seven pre-committed frequency partitions, each `part(b,c,p)` (tautology guard asserted).

---

## 1. The finding `[EMPIRICAL, 7 primes, replicated across a disjoint split]`

**Exactly one partition survived the gate: `P6_baxis` — the b=0 axis** (pure-y harmonics
`U(1,0,c) = Σ_d e_n(d) e_p(c·y_d)`). Locus-permutation perm-p:

| partition | discovery {163,211,349} | replication {433,577,991,2089} | gate |
|---|---|---|---|
| **P6_baxis (b=0)** | **0.002, 0.006, 0.001** | **0.001, 0.001, 0.001, 0.001** | **LOCUS** |
| P6_caxis (c=0) | 0.732, 0.564, 0.557 | 0.931, 0.577, 0.545, 0.546 | uniform |
| P1_chi3b | 0.001, 0.089, 0.042 | 0.029, 0.087, 0.241, 0.367 | uniform (chance) |
| P5_bband | 0.645, 0.678, 0.008 | 0.002, 0.590, 0.001, 1.000 | uniform |
| P2/P3/P4/P7 | — all in-band or scattered — | | uniform |

The b=0 axis is extreme (perm-p ≤ 0.006) at **all 7 primes**, across the disjoint discovery/replication
split, at both `p≡1` (349) and `p≡3 mod 4`. The **c=0 axis is not** — a clean x/y asymmetry.

**Direction and magnitude `[EMPIRICAL, 3 primes]`** (`_axis_direction_check_v1.py`): the axis deficit
is **negative (sub-Rayleigh)** and large:

| p | axis (b=0) deficit | off-axis deficit | ratio | `mean|U|` char vs rand on axis |
|---|---|---|---|---|
| 433 | **−10.32%** | −0.105% | 97.8× | 15.75 vs 17.56 |
| 577 | **−12.78%** | −0.074% | 172.5× | 19.11 vs 21.91 |
| 991 | **−10.13%** | −0.107% | 94.3× | 25.27 vs 28.12 |

The character's pure-y harmonics are ~10–13% smaller than random targets'; off-axis the deficit is
~0.1%. **The deficit is not one thing but two:** a large concentrated suppression on the ~`p`-harmonic
y-axis, plus a diffuse ~0.1% uniform suppression off-axis (which no partition localized — the "uniform"
rows). The aggregate `−0.06..−0.10%` is dominated by the off-axis diffuse part (the axis is only ~`1/p`
of the harmonics).

---

## 2. Controls — all fired

- **C0** `Σ D < 0` at all 7 primes. **C1** equivariance `|U(1,βb,c)|=|U(λ⁻¹,b,c)|` to `≤1.6e-11` (β,λ from coordinates, `x_{λd}=βx_d` err 0).
- **C2 PLANT** (inject `−0.5` into a χ₃ class, all primes): P1 perm-p ≤ 0.005 → gate flags LOCUS. Detector fires.
- **C3 negative control:** the χ₃@p=163 chance spike (perm-p 0.001) is correctly classed **uniform** — it does not replicate (0.089, 0.042, then 0.029–0.367). The gate filtered exactly the pattern the quick check flagged.
- **C4 FLOOR:** a held-out random target's deficit gives P1 perm-p 0.152 (in-band) — the null does not manufacture a locus.

---

## 3. The load-bearing open question (symmetric-rigor caveat on a positive)

The b=0 axis is the **least-surprising possible locus**: it is the y-channel, and a y-channel
suppression is already on record — the **χ₂(y) 0.470 → ½ saturation** (master M3/N1), whose mechanism
N1 is recorded **OPEN**. This run measures an *additive-harmonic magnitude* deficit; M3 measured a
*multiplicative-character* saturation. They are the same channel by different statistics.

**Not yet resolved, and it decides what this is:** whether the b=0 axis deficit is the χ₂(y)
half-saturation re-expressed, or a distinct additive-y phenomenon. Treating it as a new object before
that check would be the "narrative overreach" failure. It is graded here only as: *a replicated,
control-passing, publicly-computable locus for the deficit, coincident with the known y-channel.*

---

## 4. What this is, at grade

- `[EMPIRICAL, 7 primes, replicated]`: in the `a₀=1` frequency slice, the sub-Rayleigh `mean|U|`
  deficit concentrates on the b=0 (pure-y) axis (−10..−13%, ≥94×), not the c=0 axis; the off-axis
  remainder is a diffuse ~0.1% uniform suppression with no sub-locus.
- The locus is `d`-**free and publicly computable** ("b=0"), so it is a cheap descriptor of *where*
  the character's magnitude departs from Gaussian — **not** a `d`-readout. Whether it carries `d` is
  untested and is the next probe.
- **Scope/power:** model primes 163–2089, `a₀=1`, this partition list, `K=1000`. The `4099` extension
  did not resolve a prime-order curve in its window. Nulls are conditional on method+sample+floor+list.
  No transfer to `2²⁵⁶`.

---

## 5. Next probes (named now, each needs its own prereg)

1. **Resolve §3:** compute the χ₂(y) saturation and the b=0-axis additive deficit on the same curves;
   test whether one is a deterministic function of the other. If yes, this is the known y-suppression
   located; if no, a distinct object.
2. **Is the locus `d`-predictive?** The b=0 axis is `d`-free, but the *pattern of D along it* (over `c`)
   is a length-`p` signal — test whether it correlates with any hardcore predicate of `d` against the
   strong automorphism null (tautology-guarded). This is the only probe that would bear on extraction,
   and it is expected to be null by the ECDLP-scramble prior; it is run to bound, not to hope.
