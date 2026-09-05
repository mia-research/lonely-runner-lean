# PREREG v2 — is the sub-Rayleigh deficit's prime-to-prime scatter an ARITHMETIC function of the curve?

**File:** `PREREG_subrayleigh_deficit_arithmetic_scatter_v2.md`  **Date:** 2026-08-06
**Supersedes v1** after TWO isolated `experiment-designer` gates: the first returned REVISE with six
defects (three code-verified); a second, independent pass confirmed those fixes and caught one more
(the H2 power/α mismatch). This version fixes all seven. Change log at the end (§10).
**Status: PRE-RUN.** No confirmatory statistic in §3 has been computed. The 30-prime table of
`RESULT_subrayleigh_deficit_scaling_v1.md` is used **only** to fix the hypothesis sign (§2), frozen as
TRAINING; it may not appear in any confirmation number.

**The audit's load-bearing correction (drives this whole rewrite).** At a FIXED prime, the Frobenius
trace `a_p = p+1−n` is an exact affine function of the group order `n`, and `n` is not an external
label — it is a **construction parameter of `δ`** (the weight-vector length, the character modulus in
`e_n(d)`, and the Parseval energy scale `mean|U|²≈n−1`). So within a fixed p, "δ vs `a_p`" and "δ vs
`n`" are the **same one-parameter sweep**, and a monotone result cannot by itself be attributed to
*curve geometry* rather than to a generic *finite-size* dependence of the deficit on the group
order/character modulus. v1's §1 claim that the two are "disjointly constructed" was **false for the
within-p test**. v2 keeps the disjointness only where it holds (between-p, §2 H2) and adds a
matched-`(p,n)` control (§4 B) to separate finite-size from curve-specific, with the conclusions
(§9) re-scoped accordingly.

---

## §0 SCOPE BANNER (inherited by every number)

Enumerable model curves over `F_p`, `p ≡ 1 (mod 3)`, full group enumeration, cyclic part only.
`p = 2²⁵⁶−2³²−977` is **not** enumerable; **nothing here transfers to it** — every object is a full
group sum. No ECDLP, extraction, key-recovery, or security claim is made or derivable. This studies the
structure of a spectral statistic of a curve, nothing downstream.

---

## §1 OBJECT (with the v1 cancellation claim now VERIFIED, and the fixed-p identity stated)

Reusing the FROZEN instrument `subrayleigh_deficit_scaling_v1.py` (`run_prime`): for cyclic `E/F_p` of
order `n`, generator `G`, `P_d=d·G`, coordinates `(x_d,y_d)` (exact int EC arithmetic):

```
U(b,c) = Σ_d e_n(d)·e_p(b x_d + c y_d),   S=(b,c)≠(0,0)
M_char = mean_S|U|;   mu = E_null[mean_S|U|] (K Hermitian-matched null draws);
δ      = (mu − M_char)/mu   [run_prime D];   SE_δ = sdM/(mu√K)   [run_prime SE_D]
```

- **δ is DETERMINISTIC given the curve** (`M_char` has no sampling noise); only `mu` is estimated,
  with error `SE_δ ≤ 8e−5` throughout the training range. Between-curve variation of δ above `SE_δ` is
  real curve structure, not measurement noise.
- **VERIFIED (audit check 1):** the leading `√(n−1)` energy scale CANCELS in δ. `mu/√(n−1)=√(π/4)=
  0.8862` to 0.03% across a 92× range in n; `M_char/mu∈[0.9983,0.9997]`. So δ is a pure L1/L2 *shape*
  ratio, NOT a trivial `√n` image of `a_p`. The crude tautology is excluded.
- **NOT excluded by that (DEFECT 1):** a *shape* ratio can still depend smoothly on `n` (finite-size).
  At fixed p, `n = p+1−a_p`, so the six twists sweep `n` over a width-`4√p` window around p and
  `δ(a_p) ≡ δ(n)`. Separating "finite-size δ(n)" from "curve-specific geometry" is the job of §4 B.

**Candidate compact invariant.** `a_p = p+1−#E` (exact integer), `t = a_p/(2√p) ∈ [−1,1]`.
Between-p (H2), `a_p`/`t` is genuinely disjoint from δ (different curves, `n≈p` fixed-ish, the sweep
is over p). Within-p (H1), it is the group-order sweep (above).

---

## §2 HYPOTHESES — sign fixed from TRAINING only; conclusions re-scoped

Training shows δ largest at `t≈+1`, smallest at `t≈−1` (p=2671 t=+0.997 D=1.11e−3; p=4177 t=−0.967
D=0.88e−3). **Pre-committed sign: δ increases with signed `a_p` (equiv. decreases with `n`).**

- **H1 (PRIMARY — within-p, p held exactly constant).** Across the cyclic sextic twists at fixed p,
  δ is positively monotone in `a_p` (≡ negatively monotone in `n`). This isolates the group-order axis
  with p, the CM field, and |S| identical. **A fired H1 establishes "δ tracks the group order
  `n=p+1−a_p`" — NOT, by itself, "curve geometry."** The curve-specific claim requires §4 B.
- **H1-B (CURVE-SPECIFICITY gate on H1).** The within-p twist slope `dδ/da_p` **exceeds in magnitude**
  the finite-size baseline slope `β_fs(p)` measured from the matched-`(p,n)` control (§4 B) by the
  pre-committed margin. Only H1 ∧ H1-B licenses a *curve-geometry* reading.
- **H2 (SUPPORTING — between-p, out-of-sample, genuinely disjoint).** On NEW base curves `y²=x³+7` at
  primes not in training, δ rank-correlates positively with `t`, one-sided.
- **H0 (NULL — a valid pre-committed positive).** δ does not compress to `a_p`: H1 null (adequately
  powered per §7) and/or H2 null at the committed sign. Scoped null; not a closure of "arithmetic
  structure," not a mechanism claim.

**Verdicts (conjunctions, no post-hoc subset):**
`CONFIRMED-geometry` = H1 ∧ H1-B ∧ H2. `CONFIRMED-finite-size` = H1 ∧ ¬H1-B (∧ H2). `H0` = ¬H1 ∧ ¬H2,
both adequately powered. See §9.

---

## §3 STATISTICS — one primary; small-n handled exactly (DEFECT 3, 4)

| id | statistic | null / combination |
|---|---|---|
| **H1** | per twist-prime p: **exact permutation one-sided p-value** `π_p` of the δ-vs-`a_p` rank slope over the `m_p` resolved cyclic twists (Spearman; all `m_p!` orderings enumerated). Combine across the `P_tw` primes by **Fisher**: `X = −2Σ_p ln π_p`. | Threshold from the **EXACT combined null** of `X` (convolve the discrete per-prime `π_p` supports), NOT χ²/N(0,1). The discrete small-`m` support makes N(0,1)/χ² miscalibrated by ~10× (audit check 4). |
| **H1-B** | the twist slope `dδ/da_p` vs the baseline `β_fs(p)` (§4 B): sign test + magnitude ratio across primes, one-sided (twist steeper). | permutation of (twist-object ↔ baseline-object) labels at matched (p,n) |
| **H2** | **Spearman ρ(δ,t)** over the OOS between-p schedule, one-sided positive. | exact permutation of (p↔t) labels; integer-count p-value |
| tertiary | each secondary invariant (§9 A7): exact permutation rank-corr with δ, **Holm FWER 0.05**, reported only if H1 fires, non-verdict. | permutation of (p↔invariant) |

The v1 form `z(ρ_p)=ρ√(m−1)` is **removed** (invalid at `m=4`: best one-sided `π_p=1/24`, `z_max=1.73`).
Per-prime evidence enters only as the exact `π_p`; the combination is Fisher on those exact p-values.
Reported-not-verdict: isotonic δ-vs-t shape; per-twist δ table with exact `a_p`; leave-one-prime-out.

---

## §4 CONTROLS

- **B — matched-`(p,n)` finite-size baseline (NEW, the DEFECT-1 fix).** For each twist-prime p and each
  tested twist order `n`, construct a **second object with the same (p,n) but without the CM/curve
  geometry**, and measure its deficit `δ_B`. Two admissible constructions, both pre-committed; use the
  first that yields ≥3 matched n per prime:
  - **B1 (preferred):** a non-CM elliptic curve `E'/F_p` with `#E' = n` (search random `y²=x³+ax+b`,
    `j≠0`, count points, match the twist's `n`). Same (p,n), different geometry ⇒ `δ_twist − δ_B1` is
    the curve-specific part at fixed group order.
  - **B2 (fallback if B1's order-matching is infeasible at some n):** a synthetic point set of `n−1`
    points placed on the `p×p` torus by a non-curve rule (arithmetic-progression or PRNG-with-recorded-
    seed), same weight `e_n(d)`. Captures the pure "count + character-modulus" finite-size level.
  `β_fs(p)` = slope of `δ_B` vs `n` over the matched orders. **H1-B fires iff the twist slope exceeds
  `β_fs` (magnitude, committed sign).** Constructing B uses **no real-twist δ**, so it may be built now
  without contaminating H1.
- **Tautology guard (local, DEFECT 1).** Beyond v1's global perfect-fit flag: assert the within-p twist
  `dδ/da_p` is compared against `β_fs` at the **local slope** granularity, not just checked for a global
  affine identity. Log `M_char, mu, #E` per object; if `δ_twist` equals `δ_B` within noise, the effect
  is finite-size (A-fs), not geometry.
- **Disjoint construction (between-p only).** For H2 the (p↔t) permutation holds both computations
  fixed; a_p (point count) and δ (spectral shape) are different functionals over the p-sweep.
- **Scatter ≫ estimation (state; passes).** At p=12043, `SE_δ=2.6e−6`, δ≈1e−3 ⇒ ratio ~400. Asserted
  in code, not assumed.

---

## §5 PLANTED / NEGATIVE CONTROLS — all must behave before any verdict

| id | plant | in | pass |
|---|---|---|---|
| **P1** | inject `δ'=c·a_p+base` (c>0) onto real twist/`a_p` labels | H1,H2 | recovered one-sided p<0.01 |
| **P2** | shuffle (curve↔`a_p`) on same δ (negative — must be SILENT) | H1,H2 | null at nominal rate |
| **P3** | `#E` (⇒`a_p`) by two independent exact methods at 2 twist-primes | invariant | integer-identical; six `a_p` sum to 0 (**verified in audit**) |
| **P4** | re-measure δ at 3 training primes, independent null seeds | instrument | stable to ≤2·SE_δ |
| **P5 (NEW)** | the baseline instrument B must itself resolve a *planted* `dδ_B/dn` slope | H1-B | recovered ⇒ `β_fs` is calibrated, not a floor artifact |

Any failure ⇒ that arm reports "control did not fire; uninformative," no verdict.

---

## §6 SCOPE & SCHEDULE (DEFECT 2 — cheap cyclicity screen, realized-yield logging)

- **Training (direction only, FROZEN):** the 30 primes of `RESULT_subrayleigh_deficit_scaling_v1`.
- **Cyclicity screen is CHEAP (integer point-count / point-order, NO FFT).** Screen ~**160** candidate
  primes `p≡1 mod 3` disjoint from training; compute all six twists' `#E` and cyclicity by exact
  integer arithmetic. **Verified realized yield ≈ 27–29% have ≥4 cyclic twists** (audit checks 2/2b:
  distribution `{1:1,2:1,3:6,4:3}` / `{1:1,2:2,3:7,4:4}`, mode 3). Run the EXPENSIVE FFT δ-measurement
  ONLY on retained primes (≥4 cyclic twists) — expected ~**44 retained**, sized for §7 power.
- **H1 twist schedule (PRIMARY):** retained primes, restricted to `p ∈ [~3000, ~12000]` so
  `SE_δ ≪` the within-p δ-spread (DEFECT 5 resolvability, §8). Target `P_tw ≥ 44`. `g` = smallest
  sextic non-residue; twist included only if `E_k` cyclic (selection on `a_p`, not on δ ⇒ permutation
  null valid — audit confirmed no `a_p`-bias, mean `|a_p|_cyc−|a_p|_non=−17.5`, not one-signed).
- **H2 OOS schedule (SUPPORTING):** **≥48** NEW base curves `y²=x³+7` (net cyclic; §7 power), disjoint
  from training and H1, chosen by a frozen deterministic rule (next qualifying primes above a frozen set
  of ≥48 log-spaced anchors in `[1500, 19000]`; a non-cyclic base rolls to the next qualifying prime,
  logged).
- **`_SCHEDULE.txt` (binding, SHA-256'd with this spec) records BEFORE the Fisher combine:** exact H1/H2
  prime lists, `g` per prime, per-prime realized cyclic count, and which primes were dropped and why.
  No prime enters a combine unless it is in the frozen list.
- **Cost.** Screen: integer-only, minutes. FFT: one `p×p` complex128 (~1.8 GB at p≈12000) per
  (object,K-draw); ~44 primes × ~4 twists + ~30 OOS + baselines — hours, feasible. complex128 only.

---

## §7 POWER — H1 recomputed EXACTLY at small m (DEFECT 3, 6)

**H2 (between-p), Fisher-z, one-sided α=0.01 (`z_α=2.326`), committed `N ≥ 48` net-cyclic OOS primes
⇒ SE = `1/√45 = 0.149` (DEFECT 7 fix — a second independent gate found v1/earlier-v2's H2 power was
quoted at α=0.05 while the test is α=0.01):**

| true ρ | 0.50 | 0.45 | 0.40 | 0.35 |
|---|---|---|---|---|
| power | 0.91 | **0.82** | 0.70 | 0.55 |

Training Spearman (direction-fixing only) ρ≈+0.45 ⇒ powered ≈0.82 at N=48. The earlier "≈0.9 / ≈0.7"
were the **α=0.05** values (at α=0.05, N=30: ρ=0.5→0.89, ρ=0.4→0.71); at the actual α=0.01 they drop to
0.70 / 0.45 at N=30, so **N is raised 30→48** to restore power at the training effect size.
**`[UNDERPOWERED]` boundary at ρ<0.40:** a null H2 with observed `|ρ| < 0.40` is reported
`[UNDERPOWERED below ρ≈0.40]` (power ≤0.70 there), not a refutation.

**H1 (within-p) — EXACT small-`m` power (audit check5, `Z_within>3`-equivalent via Fisher), retained
configs are `m=4` in ± pairs:**

| P_tw retained | ρ_p=0.5 | ρ_p=0.7 | ρ_p=0.9 |
|---|---|---|---|
| 12 | **0.14** | 0.82 | 1.00 |
| 20 | 0.42 | 0.99 | 1.00 |
| 44 | **0.89** | 1.00 | 1.00 |

The v1 claim "ρ_p≈0.5 over 12 primes clears the bar" was FALSE (that used the invalid large-`m`
z). 80% power at ρ_p≈0.5 needs **~44 retained** ⇒ ~160 screened at 29% yield (§6).

**H1 adequacy floor (DEFECT 6, makes A4 vs [UNDERPOWERED] deterministic):** H1 is "adequately powered"
ONLY if the realized `P_tw` and per-prime `m_p` give **≥0.80 power at ρ_p=0.5** by the check5 curve.
A null H1 with realized power <0.80 routes to `[UNDERPOWERED]`, NOT to H0/A4.

---

## §8 EXACTNESS (DEFECT 5 — δ-rank resolvability pre-committed)

- **Exact int:** all EC arithmetic, `#E`, `a_p=p+1−#E`, twist `g^k`, six-`a_p`-sum-zero check, all
  permutation/rank counts and p-values, and the `a_p`-rank by **integer cross-multiplication**
  (`a/√p ≷ a'/√p'` ⇔ sign-tracked `a²p' ≷ a'²p`) — no float decides an `a_p` comparison.
- **δ-rank resolvability (NEW).** Verdicts rank δ values each carrying `SE_δ`. At fixed p the twists'
  `a_p` differ by O(√p), so within-p δ-gaps are small. **Pre-commit:** (i) restrict H1 to `p≥3000`
  where `SE_δ≤~5e−6` and the expected within-p δ-spread (~1e−4 from the training between-p variation)
  gives gap/SE ≳ 20; (ii) size per-prime `K` so `SE_δ(p) ≤ (min expected within-p δ-gap)/5`; (iii)
  count a twist pair as **resolved** only if `|δ_i−δ_j| > 5·SE_δ`; a prime with `<3` resolved pairs is
  dropped for H1 and logged. This filter is on gap **magnitude**, not sign ⇒ it does not bias the rank
  direction (stated).
- **Sanctioned float carve-out (analytic magnitude only):** the `p×p` FFT `|U|`, the factor `e_n(·)`;
  error ≤1e−12 ≪ δ≈1e−3, common-mode-cancelling. complex128 only.
- `check_no_float.sh` must pass on the invariant/statistic module before any verdict.

---

## §9 PRE-COMMITTED OUTCOME TABLE (A1 re-scoped; A-fs added)

No row licenses ECDLP/extraction/security, a mechanism claim (row-budget thread), or *generic/benign/
no structure*.

| # | Outcome | Conclusion |
|---|---|---|
| **A1 (geometry)** | H1 ∧ **H1-B** ∧ H2 | **The scatter is a curve-specific function of the Frobenius trace `a_p`, beyond finite-size:** the within-p twist slope EXCEEDS the matched-(p,n) baseline `β_fs`, and it reproduces OOS between-p. Report Fisher `X`, twist-vs-baseline slopes, OOS ρ, isotonic shape; name the residual-after-`t` as the next object. Re-frames scaling-run level-2: `D(p)` is scattered in p because it is structured in `a_p`, which is arithmetically scattered in p. |
| **A-fs (finite-size)** | H1 ∧ **¬H1-B** (∧ H2) | **The scatter is δ's dependence on the group order `n=p+1−a_p`, at the generic finite-size level** (twist slope ≈ baseline `β_fs`). Still a real, scoped characterization of the scatter: the Frobenius enters *through the group order/character modulus*, not through curve geometry. Report both slopes; do NOT claim "curve geometry." |
| **A2** | H1 ∧ H2 `[UNDERPOWERED]` | within-p evidence δ tracks `a_p`/`n`; not yet OOS-corroborated. Not CONFIRMED. |
| **A3** | ¬H1 ∧ H2 | between-p corr with `t` NOT reproduced p-controlled ⇒ a **p-covariate** co-varying with `a_p`, not `a_p` itself. Name the candidate (log-p residual, |S|); `a_p`-driver NOT supported. |
| **A4 (H0)** | ¬H1 ∧ ¬H2, **both adequately powered (§7 floors)** | **H0: the scatter does not compress to `a_p` at this scope.** Report power floors and the isotonic residual. Scoped null; scatter remains real and unexplained by `a_p`; mechanism + tertiary invariants open. |
| **A5** | tautology guard fails (δ≈image of `a_p` to ≤SE_δ with a definitional link found) | report the link (a readout artifact); "correlation" is bookkeeping. |
| **A6** | any P1–P5 misbehaves | that arm uninformative; no verdict. |
| **A7** | tertiary invariant survives Holm after A1 | additional exploratory handle, its own prereg; never folded into A1. |

**Unprojected-covariate clause (mandatory).** If H1 and H2 both null: report (i) the confirmed real
spread (≥10·SE_δ) with scope; (ii) the isotonic-`t` residual as a number; (iii) the explicit list of
untested invariants (`M` from `4p=L²+27M²`, twist-class of 7, `a_p mod ℓ`, higher Frobenius data) as
next candidates, not absences.

**Output type:** a characterization + power + §0 scope. Never ECDLP/extraction/security; never a
mechanism claim.

---

## §10 CHANGE LOG v1→v2 (audit defects, all six)
1. **D1 (frame/§1,§9):** within-p disjointness claim corrected; `a_p≡n` construction-parameter identity
   stated; matched-(p,n) baseline **B** added (§4); A1 re-scoped to "group order," new **A-fs** row for
   finite-size, curve-geometry gated on **H1-B**.
2. **D2 (§6):** cheap integer cyclicity screen; realized ~29% ≥4-cyclic yield logged; ~160 screened →
   ~44 retained; FFT only on retained.
3. **D3 (§7):** H1 power replaced with the exact small-`m` curve (0.14 at ρ=0.5/P_tw=12; ~44 for 0.80).
4. **D4 (§3):** H1 combine = **Fisher on exact per-prime permutation p-values**, threshold from the
   exact combined null; invalid `z(ρ)=ρ√(m−1)` removed.
5. **D5 (§8):** δ-rank resolvability pre-committed (p≥3000; K sized to SE_δ≤gap/5; resolved-pair def).
6. **D6 (§7,§9):** explicit H1 adequacy floor routes a null H1 to A4 vs `[UNDERPOWERED]` deterministically.

7. **D7 (§6,§7 — added after a SECOND independent `experiment-designer` gate):** H2 power was quoted at
   α=0.05 while the test runs at α=0.01 (0.9/0.7 → the true α=0.01 values are 0.70/0.45 at N=30). Fixed by
   recomputing the power table at α=0.01 and raising the OOS schedule 30→48 net-cyclic primes (power ≈0.82
   at the training ρ≈0.45); `[UNDERPOWERED]` boundary moved to ρ<0.40.

Verified-good and unchanged: `√(n−1)` cancellation; `a_p` integer-rank exactness; P3 twist structure;
direction-fixing cleanliness; the matched-(p,n) finite-size baseline (B) + H1-B geometry gate; Fisher
exact-combined H1 null; δ-rank resolvability; null-side outcome frame.
