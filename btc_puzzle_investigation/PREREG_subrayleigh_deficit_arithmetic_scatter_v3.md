# PREREG v3 — is the sub-Rayleigh deficit's prime-to-prime scatter arithmetic BEYOND the smooth δ(p,n) surface?

**File:** `PREREG_subrayleigh_deficit_arithmetic_scatter_v3.md`  **Date:** 2026-08-06
**Supersedes v2** after a second isolated `experiment-designer` re-audit. v2's fixes for D2–D6 are
carried forward (they PASSED). v2's D1 remedy (control B + a finite-size-vs-Frobenius split) is
**discarded** as ill-posed; v3 replaces the whole primary with a surface-residual design. Change log §10.
**Status: PRE-RUN.** No confirmatory statistic computed. The 30-prime table of
`RESULT_subrayleigh_deficit_scaling_v1.md` is TRAINING (fixes signs/priors only); it may not enter a
confirmation number.

**The obstruction that forced this rewrite (audit-confirmed, code `checkB.py`).** At a FIXED prime the
group order `n` and the Frobenius trace `a_p = p+1−n` are **affinely locked — the same axis** — so
"finite-size in `n`" vs "arithmetic in `a_p`" has no within-p separation, and no fixed-`(p,n)` control
can make one: any curve `E'/F_p` with `#E'=n` has trace `a=p+1−n`, hence Frobenius in the **same field**
`Q(√(a²−4p))`; for the j=0 sextic twists `a²−4p=−3M²`, and `M=1` twists admit **only** j=0 curves of
that order (verified: 0 j≠0 curves in 4000 tries at p=6007, n=5853). v2's control B therefore silently
answered a different question and mislabeled outcomes. v3 stops trying to separate the unseparable and
asks the question that IS well-posed (below).

---

## §0 SCOPE BANNER (inherited by every number)

Enumerable model curves over `F_p`, `p ≡ 1 (mod 3)`, full group enumeration, cyclic part only.
`p = 2²⁵⁶−2³²−977` is **not** enumerable; **nothing here transfers to it**. No ECDLP, extraction,
key-recovery, or security claim is made or derivable. This studies the structure of a spectral
statistic of a curve.

---

## §1 OBJECT AND THE WELL-POSED QUESTION

Frozen instrument `subrayleigh_deficit_scaling_v1.py` (`run_prime`): for cyclic `E/F_p` order `n`,
`δ = (mu − M_char)/mu`, `SE_δ = sdM/(mu√K)`; δ deterministic given the curve; the `√(n−1)` energy scale
cancels (audit-verified: `mu/√(n−1)=√(π/4)` to 0.03%), so δ is a pure L1/L2 **shape** ratio.

**δ is a function of two independent variables `(p, n)`** (plus finer curve data), NOT of a separate
`a_p` channel — `a_p=p+1−n` is their affine combination. The scaling run measured δ along ONE curve,
the base-curve trajectory `p ↦ (p, n₀(p))`, `n₀(p)=#E(y²=x³+7 / F_p)`, and found it scattered far beyond
any smooth model of `p` alone (`χ²_red=204`). Because `n₀(p)` jumps arithmetically as `p` increases
smoothly, that scatter is (at least partly) δ's **`n`-dependence** sampled along an arithmetically
jumping `n₀(p)`. The well-posed successor question is therefore:

> **After removing the smooth `δ(p,n)` surface, does the base-curve trajectory's residual carry
> arithmetic structure — or is the scatter fully accounted for by δ tracking `n` on a smooth surface?**

The sextic twists provide the **off-trajectory `(p,n,δ)` samples** needed to map the surface without
fitting it to the trajectory being tested.

---

## §2 HYPOTHESES (signs/priors from TRAINING only)

- **H1 (PRIMARY — trajectory residual).** Let `f̂(p,n)` be the smooth surface fit to the OFF-trajectory
  twist samples (sister twists `k≠0`, all screened primes; §6). For each trajectory prime, the residual
  `r(p) = δ₀(p) − f̂(p, n₀(p))`. **H1: `r(p)` is structured** — it has nonzero lag-1 rank
  autocorrelation OR correlates with a finer arithmetic invariant of the base curve (candidate set frozen
  in §3, Holm-corrected). `H1-null`: `r(p)` is consistent with unstructured scatter about the surface.
- **H2 (ENABLING / SUPPORTING — the local `n`-slope, the correctly-scoped within-p result).** The local
  slope `f₁(p) = ∂δ/∂n|_p`, measured from the twists at each prime, is nonzero with a **consistent sign
  across primes** (training prior: δ increases with `a_p` ⇒ decreases with `n` ⇒ `f₁<0`). This establishes
  "**δ depends on the group order `n` at fixed p**" — stated with NO finite-size-vs-geometry claim (that
  split is ill-posed, §1). It also validates that the surface `f̂` has real `n`-structure to remove.
- **H3 (SECONDARY, optional, `M>1` twists only — B1 relabeled).** At fixed `(p,n,a_p)`, does δ depend on
  the j-invariant / endomorphism conductor? Compare δ of the twist vs a non-CM `E'` with `#E'=n`
  (feasible only where `M=√((4p−a²)/3) > 1`; audit NEW-1). This decides **"δ is a function of the trace
  alone (trace-universal) vs specific to the j=0 CM family"** — NOT finite-size vs Frobenius.
- **H0 (a valid pre-committed positive).** `H1-null ∧ H2 fires`: the scatter is **fully** δ's smooth
  dependence on the group order `n` (which scatters via `a_p`); no arithmetic structure beyond the
  surface at this scope. A real, scoped characterization — not a closure, not a mechanism claim.

---

## §3 STATISTICS

**Surface fit `f̂(p,n)` (pre-committed form; fit from `k≠0` twists only).** In the sampled band
`n ≈ p` (|a_p|≤2√p), a local model: `f̂(p,n) = g₀(p) + g₁(p)·u`, `u = (n − p − 1)/√p = −t` (normalized
`n`-deviation), with `g₀,g₁` low-order in `ln p` (degree ≤2, frozen). Fit by exact rational weighted LS
(weights `1/SE_δ²`). **The base-curve `k=0` points are HELD OUT of the fit** (tested, not fitted).

| id | statistic (verdict-bearing) | null |
|---|---|---|
| **H1** | (a) lag-1 **rank autocorrelation** of `r(p)` ordered by `p`; (b) exact permutation **rank-correlation** of `r(p)` with each frozen invariant. Primary = a **single Holm-FWER-0.05** decision over {autocorr, and the frozen invariant list}. | exact permutation of the `r(p)` labels (integer-count p-values) |
| **H2** | per prime: exact permutation one-sided p-value `π_p` of the δ-vs-`n` rank slope over the `m_p` resolved cyclic twists; combine by **Fisher** `X=−2Σ ln π_p`; threshold from the **EXACT combined null** (convolve discrete `π_p` supports), not χ²/N(0,1). | discrete exact combined null |
| **H3** | at each `M>1` matched `(p,n)`: `δ_twist − δ_{B1}`, ensemble over ≥K_B independent B1 curves; sign test + magnitude vs the B1-ensemble scatter (audit NEW-3: compare to the ensemble, not one realization). | B1-curve ensemble at matched `(p,n)` |

**Frozen finer-invariant list for H1(b)** (the only invariants that may be tested; Holm over exactly
these + autocorr): `M` from `4p=L²+27M²`; the **sextic residue class of 7** mod p (which twist-slot the
base curve occupies, ∈ Z/6); `a_p mod 3` and `a_p mod 4`. No invariant outside this list may be added
post hoc. **Direction/priors** for each are fixed here from TRAINING before any confirmation number.

---

## §4 CONTROLS

- **Off-trajectory fit (the D1 fix).** `f̂` is fit from `k≠0` twists only; the tested `k=0` residuals are
  out-of-fit, so a small residual cannot be an artifact of fitting the trajectory to itself.
- **Surface-adequacy firing control (must PASS before H1).** `f̂` must actually capture the twist
  `n`-structure: its off-trajectory cross-validated `R²` (leave-one-prime-out on the `k≠0` fit) must
  exceed a frozen floor; if `f̂` is a bad fit even off-trajectory, H1's residual is meaningless and the
  run reports "surface underdetermined; H1 uninformative." (This is also where H2's `f₁≠0` is confirmed —
  a flat surface `g₁≈0` means δ has no `n`-structure, so the scatter is NOT `n`, routing to §9 A5.)
- **H3 ensemble (audit NEW-3).** B1 uses the **average over many** independent order-`n` curves, and H3
  fires only if the twist deviates beyond the B1 **ensemble scatter** — no single-realization floor.
- **Invariant disjointness / multiplicity (audit's fishing guard).** The finer-invariant list is frozen
  (§3) and Holm-corrected; `M`, sextic-class, `a_p mod ℓ` are exact integers computed from the curve,
  disjoint from the spectral δ. Between-trajectory-primes the (r ↔ invariant) pairing is genuinely
  disjoint (different curves).
- **Scatter ≫ estimation (state; passes).** trajectory δ-spread ≥ 10·SE_δ at large p (ratio ~400 at
  p=12043), asserted in code.

---

## §5 PLANTED / NEGATIVE CONTROLS — all must behave

| id | plant | in | pass |
|---|---|---|---|
| **P1** | inject `r'(p)=c·M(p)+noise` onto real trajectory labels | H1 | recovered Holm-significant |
| **P2** | shuffle (curve↔invariant) on same `r` (negative — SILENT) | H1 | null at nominal rate |
| **P3** | inject a known `f₁` slope into synthetic twist δ | H2 | recovered; exact combined-null threshold calibrated |
| **P4** | `#E`/`a_p`/`M` by two independent exact methods; six `a_p` sum to 0 | invariants | integer-identical (**audit-verified** structure) |
| **P5** | re-measure δ at 3 training primes, independent seeds | instrument | stable ≤2·SE_δ |
| **P6** | surface-adequacy: fit `f̂` to a synthetic δ with a KNOWN smooth `f` + zero residual | H1 | recovered `r≈0`, no false structure (guards against the fit manufacturing residual structure) |

Any misbehavior ⇒ that arm uninformative; no verdict.

---

## §6 SCOPE & SCHEDULE

- **Training (FROZEN, direction/priors only):** the 30 primes of `RESULT_subrayleigh_deficit_scaling_v1`.
- **Cheap integer cyclicity screen (no FFT):** ~**160** candidate primes `p≡1 mod 3`, `p∈[3000,12000]`
  (large-p for δ-resolvability, §8), disjoint from training. Compute all six twists' `#E`, cyclicity,
  and `M` per twist by exact integer arithmetic.
- **FFT δ-measurement schedule (the cost increase v3 incurs):** ALL cyclic twists at a frozen subset of
  **`P_surf ≥ 50`** screened primes (mode ~3 cyclic/prime ⇒ ~150 measurements) — these fit `f̂` and give
  H2. The **base curve (`k=0`)** at each of ≥30 **trajectory primes** (its own frozen list, disjoint or
  overlapping-by-p with `P_surf` but always held out of the fit) gives the H1 residual sequence.
- **H3 (optional):** `M>1` matched-`(p,n)` B1 ensembles at a frozen subset of ~10 primes.
- **`_SCHEDULE.txt` (SHA-256'd with this spec, binding):** exact prime lists (surface / trajectory / H3),
  `g` per prime, per-prime cyclic count and per-twist `M`, dropped primes + reason. No prime enters a fit
  or combine unless frozen here.
- **Cost.** Screen: minutes. FFT: one `p×p` complex128 (~1.8 GB at p≈12000) per (object,K-draw);
  ~150 surface + ~30 trajectory + H3 ensembles — hours to ~a day. complex128 only.

---

## §7 POWER

- **H2 (within-p `n`-slope):** exact small-`m` power (audit check5): `P_surf=50` retained primes with
  `m_p≈3–4` gives ≥0.8 power at `f₁`-equivalent `ρ_p≈0.5`. Adequacy floor: H2 "adequately powered" only
  if realized `P_surf, m_p` give ≥0.80 at `ρ_p=0.5`; else `[UNDERPOWERED]`, not H0.
- **H1 (residual structure):** with ~30 trajectory residuals, the Holm-over-{autocorr + 4 invariants}
  decision detects a per-invariant Spearman `|ρ|≈0.55` at FWER 0.05 with power ≈0.8; `|ρ|≈0.45` ≈0.6.
  **Pre-committed floor:** a null H1 is `[UNDERPOWERED below |ρ|≈0.45]` unless the trajectory set is
  extended. (Training hint used ONLY to set this expectation, not to test.)
- **H3:** powered by the B1 ensemble size `K_B`; `K_B` sized so the ensemble SE ≤ (target j-effect)/3.
- Verdicts state their individual floors; A1 (deeper arithmetic) requires H1 to fire at the Holm level.

---

## §8 EXACTNESS

- **Exact int:** EC arithmetic, `#E`, `a_p`, `M` (via `4p=L²+27M²`, integer solve), sextic-class of 7
  (exact power-residue test), `a_p mod ℓ`, twist `g^k`, six-`a_p`-sum-zero, all rank/permutation counts
  and p-values, the surface-fit weighted LS in **exact rationals** (`Fraction`), invariant ranks by
  integer cross-multiplication.
- **δ-rank resolvability (carried from v2 D5):** `p≥3000`; per-prime `K` sized so `SE_δ ≤ gap/5`;
  resolved-pair `|δ_i−δ_j|>5·SE_δ`; drop `<3` resolved pairs (magnitude filter, sign-neutral).
- **Sanctioned float carve-out (analytic magnitude only):** the `p×p` FFT `|U|`, `e_n(·)`; error
  `≤1e−12 ≪ δ`. complex128 only. No verdict decided by float precision.
- `check_no_float.sh` passes on the invariant/statistic module before any verdict.

---

## §9 PRE-COMMITTED OUTCOME TABLE (MECE over {H1, H2, H3}, audit NEW-4)

Enumerated so every (H1∈{fire, underpowered, null}, H2∈{fire, underpowered, null}, H3∈{fire,null,not-run})
combination maps to exactly one row. No row licenses ECDLP/extraction/security, a mechanism claim, or
*generic/benign/no structure*.

| # | Condition | Conclusion |
|---|---|---|
| **A1** | H1 fires (Holm) ∧ H2 fires | **Arithmetic structure BEYOND the smooth δ(p,n) surface:** name the surviving invariant(s) / autocorrelation; the base-curve trajectory's deficit is not fully explained by δ tracking `n`. Report `f̂`, its off-trajectory CV-R², the residual `r(p)`, and the surviving-invariant p-values. The deepest positive; next probe = the mechanism behind that invariant, its own prereg. |
| **A2** | H1-null (powered) ∧ H2 fires | **H0: the scatter is δ's smooth dependence on the group order `n` (which scatters via `a_p`); NO arithmetic structure beyond the surface at this scope.** The correctly-derived "the Frobenius enters through `n`" answer — stated WITHOUT the ill-posed finite-size/geometry label. Report the surface, CV-R², and the flat residual with its power floor. |
| **A3** | H1 fires ∧ H2 underpowered/null | residual structure without a confirmed surface `n`-slope ⇒ the "surface" is underdetermined; report H1 as **provisional**, requiring a powered H2 (more twist primes) before A1. |
| **A4** | H1-null (powered) ∧ H2-null (powered) | δ has **no** resolved `n`-dependence AND no residual structure ⇒ the scatter is NOT the group order and NOT the frozen invariants ⇒ it lives in finer curve data (beyond `(p,n)` and the §3 list). Report the untested-invariant list (§9 clause) as next candidates; scoped null. |
| **A5** | H2-null with surface `g₁≈0` (flat) but trajectory scatter real | δ does not depend on `n` in the sampled band ⇒ the χ²_red=204 scatter is NOT group-order; re-open the source (finer curve data or a p-direct effect). Positive: excludes the leading hypothesis. |
| **A6** | H1 or H2 `[UNDERPOWERED]` (realized power < floor) | report the bounded result with its power floor; route to A2/A4 only when the §7 floor is met. NOT a refutation. |
| **A7** | H3 fires (independent of H1/H2) | δ depends on `j` beyond the trace (j=0-family-specific); report as an additional handle with its own follow-up. H3-null ⇒ "trace-universal at this scope." Never folded into A1. |
| **A8** | any P1–P6 misbehaves | that arm uninformative; no verdict. |

**Unprojected-covariate clause (mandatory).** If H1 and H2 both null (A4): report (i) the confirmed real
trajectory spread (≥10·SE_δ) with scope; (ii) the surface CV-R² and residual variance as numbers; (iii)
the explicit untested list (higher-order surface terms, `a_p mod ℓ` for ℓ∉{3,4}, class/conductor data,
2-adic `v₂(n)`), as next candidates — not absences.

**Output type:** a characterization + power + §0 scope. Never ECDLP/extraction/security; never a
mechanism claim.

---

## §10 CHANGE LOG v2→v3
- **Discarded** v2's control B and the finite-size-vs-Frobenius split (audit: ill-posed at fixed p; B1
  shares the trace / infeasible at `M=1` / B2 floor uncontrolled — NEW-1/2/3).
- **New primary H1:** trajectory residual from an OFF-trajectory-fit smooth surface `f̂(p,n)` — the
  well-posed "arithmetic beyond the surface" question.
- **Relabeled H2:** the within-p `n`-slope now states "δ depends on group order `n`" only, no
  finite-size/geometry claim; exact small-`m` Fisher stats retained (v2 D3/D4).
- **Relabeled H3:** old B1, now "trace-universal vs j=0-family-specific," `M>1` only, ensemble-compared
  (NEW-1/3).
- **MECE outcome table** over {H1,H2,H3} with an explicit row per cell (NEW-4).
- **Carried from v2 (PASSED):** cheap cyclicity screen + realized-yield logging (D2), exact small-`m`
  power + adequacy floors (D3/D6), Fisher/exact-combined-null (D4), δ-resolvability (D5), direction-fixing
  cleanliness, `√(n−1)` cancellation, `a_p`/`M` integer exactness, frozen SHA'd schedule.
