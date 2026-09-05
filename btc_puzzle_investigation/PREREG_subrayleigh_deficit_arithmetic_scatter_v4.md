# PREREG v4 — is the sub-Rayleigh deficit's scatter arithmetic BEYOND the smooth δ(p,n) surface?

**File:** `PREREG_subrayleigh_deficit_arithmetic_scatter_v4.md`  **Date:** 2026-08-06
**Supersedes v3** after a THIRD isolated `experiment-designer` audit: obstruction handling PASSED and the
surface-residual primary was judged well-posed, with three specification defects on its controls and two
refinements. v4 fixes all five. Change log §10.
**Status: PRE-RUN.** No confirmatory statistic computed. The 30-prime table of
`RESULT_subrayleigh_deficit_scaling_v1.md` is TRAINING (fixes signs/priors only); it may not enter a
confirmation number.

**Lineage of the design (why this is v4, not v1).** v1→v2: six mechanical/power defects. v2→v3: a
*conceptual* obstruction — at fixed p, group order `n` and Frobenius trace `a_p=p+1−n` are the **same
axis**, so no within-p control separates "finite-size" from "arithmetic" (v2's control B was ill-posed;
`M=1` twists admit only j=0 curves — verified). v3→v4: the surface-residual reframing is well-posed; the
remaining fixes are to its firing controls, verified below.

**The number that drives v4's control fixes (independently verified).** A weighted deg-2-in-`ln p` fit of
the trajectory `D(p)` has **R² = 0.0048** — the smooth-in-`p` surface explains essentially NONE of the
scatter (consistent with the scaling run's `χ²_red=204`). So the surface's only real content is its
**within-prime `n`-slope** `g₁(p)`; the residual `r(p) ≈ Δ(p) − g₁(p)·u₀` is the prime-specific spectral
anomaly minus a linear-`u` correction. The controls must gate the `u`-slope, not an overall R², and must
guard against **out-of-class** smooth misspecification (a true `u²` term leaking into `r`).

---

## §0 SCOPE BANNER (inherited by every number)

Enumerable model curves over `F_p`, `p ≡ 1 (mod 3)`, full group enumeration, cyclic part only.
`p = 2²⁵⁶−2³²−977` is **not** enumerable; **nothing here transfers to it**. No ECDLP, extraction,
key-recovery, or security claim is made or derivable. This studies the structure of a spectral statistic.

---

## §1 OBJECT AND THE WELL-POSED QUESTION

Frozen instrument `subrayleigh_deficit_scaling_v1.py` (`run_prime`): for cyclic `E/F_p` order `n`,
`δ=(mu−M_char)/mu`, `SE_δ=sdM/(mu√K)`; δ deterministic; `√(n−1)` scale cancels (audit-verified,
`mu/√(n−1)=√(π/4)` to 0.03%), so δ is a pure L1/L2 **shape** ratio.

**δ is a function of two independent variables `(p,n)`; `a_p=p+1−n` is their affine combination, not a
third channel.** The scaling run measured δ along the base-curve trajectory `p↦(p, n₀(p))`,
`n₀(p)=#E(y²=x³+7/F_p)`, and found scatter far beyond any smooth `p`-model (`R²_smooth=0.0048`,
verified). The well-posed successor question:

> **After removing the smooth `δ(p,n)` surface, does the base-curve trajectory's residual carry
> arithmetic structure — specifically, does it depend on an arithmetic RESIDUE invariant of the curve
> that a smooth surface cannot mimic — or is the scatter fully accounted for by δ's `n`-dependence?**

The sextic twists supply the off-trajectory `(p,n,δ)` samples to fix the surface `n`-slope.

---

## §2 HYPOTHESES (signs/priors from TRAINING only)

Normalized `n`-deviation `u = (n−p−1)/√p = −a_p/√p` (`|u|≤2` on the twist band). Surface
`f̂(p,n)=g₀(p)+g₁(p)·u` (§3), fit from OFF-trajectory `k≠0` twists; base `k=0` HELD OUT. Residual
`r(p)=δ₀(p)−f̂(p,n₀(p))`.

- **H1 (PRIMARY — trajectory residual carries arithmetic structure).** Split by protection class
  (audit refinement a):
  - **H1a (PRIMARY channel — arithmetic-residue invariants, misspecification-protected).** `r(p)`
    correlates with an invariant from the frozen RESIDUE set `{a_p mod 3, a_p mod 4, sextic-residue
    class of 7 mod p ∈ Z/6}`. A residue is orthogonal to any smooth `u`-polynomial, so a hit here
    **cannot** be a surface-underfit artifact. This is the load-bearing primary.
  - **H1b (SECONDARY channel — smooth-confoundable, reported not verdict-primary).** `r(p)` vs `M`
    (`4p=L²+27M²`) or lag-1 rank autocorrelation of `r(p)` ordered by p. These confound with
    out-of-class smooth misspecification (M is a smooth magnitude; autocorr ↔ under-fit-in-p), so they
    may only support A1 **if** H1a fires AND the smooth-misspecification control (§4 SM) is clean.
  - Decision: Holm-FWER-0.05 over the RESIDUE set for the H1a verdict; H1b invariants reported under a
    separate Holm slot, non-primary.
- **H2 (ENABLING — the within-p `n`-slope, correctly scoped).** `g₁(p)=∂δ/∂n|_p` is nonzero with a
  consistent sign across primes (training prior `g₁<0`, i.e. δ increases with `a_p`). Establishes "**δ
  depends on the group order `n` at fixed p**" — NO finite-size-vs-geometry claim. **H2 is also the
  surface-adequacy gate for H1** (§4).
- **H3 (SECONDARY, `M>1` only — trace-universality).** At fixed `(p,n,a_p)`, does δ depend on the
  j-invariant beyond the trace? Ensemble-compared vs non-CM `E'` with `#E'=n` (audit NEW-1/3).
- **H0 (a valid pre-committed positive).** `H1a-null (powered) ∧ H2 fires`: the scatter is **fully** δ's
  smooth dependence on group order `n` (which scatters via `a_p`); no arithmetic-residue structure beyond
  the surface at this scope. Scoped characterization, not a closure, not a mechanism claim.

---

## §3 STATISTICS

**Surface fit `f̂(p,n)=g₀(p)+g₁(p)·u`**, `g₀,g₁` degree ≤2 in `ln p` (frozen), fit from `k≠0` twists
only by exact-rational weighted LS (weights `1/SE_δ²`). Base `k=0` points held out.

| id | statistic (verdict-bearing) | null |
|---|---|---|
| **H1a** | exact permutation rank-association of `r(p)` with each RESIDUE invariant: for the Z/6 sextic class, a **Kruskal–Wallis** exact permutation stat; for binary `a_p mod 3`, `a_p mod 4`, a **rank-biserial / Mann–Whitney** exact permutation stat (audit refinement c: these are 2-group splits, NOT continuous Spearman). Primary = **Holm-FWER-0.05** over the three. | exact permutation of `r(p)` labels (integer counts) |
| **H1b** | `r(p)` vs `M`: one-sided Spearman; lag-1 rank autocorr of `r(p)`. Separate Holm slot; **gated on H1a ∧ clean §4 SM**. | exact permutation of `r(p)` labels |
| **H2** | per prime: exact permutation one-sided p-value `π_p` of δ-vs-`n` rank slope over `m_p` resolved cyclic twists (all `m_p!` orderings); Fisher `X=−2Σln π_p`; threshold from the **EXACT combined null** (convolve discrete `π_p` supports), not χ²/N(0,1). | discrete exact combined null |
| **H3** | at each `M>1` matched `(p,n)`: `δ_twist − δ_{B1}` vs the **B1 ensemble scatter** over ≥K_B curves (audit NEW-3). | B1 ensemble |

**Frozen invariant lists (the ONLY invariants testable; no post-hoc additions):** RESIDUE
`{a_p mod 3, a_p mod 4, sextic-class(7)}` (H1a); SMOOTH-CONFOUNDABLE `{M, lag-1 autocorr}` (H1b).
Directions fixed here from TRAINING. Note (audit c): sextic-class(7) and `a_p mod 3` both carry the
cubic/sextic character ⇒ mutually dependent, effective multiplicity < 3 — Holm stays valid, flagged.

---

## §4 CONTROLS

- **Off-trajectory fit (D1 lineage).** `f̂` from `k≠0` only; tested `k=0` residuals out-of-fit.
- **Surface-adequacy gate — RESPECIFIED (audit DEFECT, was mis-targeted).** The gate is NOT overall
  CV-R² (which is ~`R²_smooth=0.0048`, so an overall floor gates nothing or blocks always). It is the
  **within-prime partial-R² of the `u`-term**, equivalently **H2's Fisher significance**. Pre-committed
  numeric floor: H1 proceeds only if H2 fires (exact combined-null p < 0.01) AND the pooled within-prime
  partial-R²(u) ≥ **0.25**. If `g₁·u` does not capture the twist spread, the surface has no `n`-content
  to remove and H1 is "surface underdetermined; uninformative" (routes to §9 A5).
- **SM — smooth-misspecification negative control (NEW, audit refinement a).** `r(p)` vs `u₀² = a_p²/p`
  (a purely smooth function of the trajectory) **must be null**. A nonzero `r`-vs-`u₀²` means the linear
  surface under-fits a `u²` term that has leaked into `r`; then H1b is void and any H1a-survivor must
  additionally **survive a refit with a richer `u`-basis** (add `u²`, higher `ln p`). H1a's residue
  invariants are orthogonal to `u²` by construction, so SM protects H1b and stress-tests H1a.
- **H3 ensemble (audit NEW-3).** compare to the B1 **ensemble scatter**, never a single realization.
- **Multiplicity/disjointness.** Frozen lists (§3), Holm-corrected; residue invariants are exact integer
  point-count residues, disjoint from spectral δ; the (r↔invariant) pairing is across different curves.
- **Scatter ≫ estimation.** trajectory δ-spread ≥10·SE_δ (ratio ~400 at p=12043), asserted in code.

---

## §5 PLANTED / NEGATIVE CONTROLS — all must behave

| id | plant | in | pass |
|---|---|---|---|
| **P1** | inject `r'(p)=c·[a_p mod 3]+noise` onto real labels | H1a | recovered Holm-significant |
| **P2** | shuffle (curve↔invariant) on same `r` (negative — SILENT) | H1a,H1b | null at nominal rate |
| **P3** | inject a known `g₁` slope into synthetic twist δ | H2 | recovered; exact combined-null threshold calibrated |
| **P4** | `#E`/`a_p`/`M`/sextic-class by two independent exact methods; six `a_p` sum to 0 | invariants | integer-identical (**audit-verified** structure) |
| **P5** | re-measure δ at 3 training primes, independent seeds | instrument | stable ≤2·SE_δ |
| **P6 (STRENGTHENED, audit DEFECT).** | plant an **OUT-of-model-class** smooth surface (`u²`, `u³`, and/or higher `ln p`) with **zero arithmetic residual**, fit the in-class linear `f̂`, and confirm the leaked residual does **NOT** produce a false H1a/H1b hit or false autocorr; ALSO the old in-class zero-residual plant (must give `r≈0`) | H1, §4 SM | H1a/H1b silent on the misspecified-but-arithmetically-null input; SM control **fires** (catches the `u²` leak) |

Any misbehavior ⇒ that arm uninformative; no verdict.

---

## §6 SCOPE & SCHEDULE

- **Training (FROZEN, direction/priors only):** the 30 primes of `RESULT_subrayleigh_deficit_scaling_v1`.
- **Cheap integer cyclicity screen (no FFT):** ~160 candidate primes `p≡1 mod 3`, `p∈[3000,12000]`
  (large-p for δ-resolvability, §8), disjoint from training; compute all six twists' `#E`, cyclicity, `M`,
  sextic-class exactly.
- **FFT δ-measurement schedule:** ALL cyclic twists at a frozen `P_surf ≥ 50` screened primes (~150
  measurements; fit `f̂`, give H2); base curve `k=0` at ≥30 frozen **trajectory primes** (held out of the
  fit) for the H1 residual sequence; `M>1` matched-`(p,n)` B1 ensembles at ~10 primes (H3).
- **`_SCHEDULE.txt` (SHA-256'd with this spec, binding):** exact prime lists (surface / trajectory / H3),
  `g` per prime, per-prime cyclic count, per-twist `M` and sextic-class, dropped primes + reason. Nothing
  enters a fit or combine unless frozen here.
- **Cost.** Screen: minutes. FFT: one `p×p` complex128 (~1.8 GB at p≈12000) per (object,K-draw);
  ~150 surface + ~30 trajectory + H3 — hours to ~a day. complex128 only.

---

## §7 POWER

- **H1a (residue channel):** the Z/6 sextic-class KW test detects a moderate between-class δ-shift at 30
  primes with power ≈0.8 for a class-separation ≥ ~1·(residual sd); **the binary `a_p mod 3`/`a_p mod 4`
  splits are 2-group, imbalanced (19:11, 14:16 — verified), so their achievable rank-biserial is
  ceilinged and §7's continuous-ρ power does NOT apply** — their floor is stated as the Mann–Whitney
  detectable shift at that imbalance (≈0.9·sd for 0.8 power). A null H1a is `[UNDERPOWERED]` below these.
- **H2 (`n`-slope):** exact small-`m` power (audit check5): `P_surf≈50`, `m_p≈3–4` ⇒ ≥0.8 at
  `ρ_p≈0.5`. Adequacy floor as in §4.
- **H3:** `K_B` sized so ensemble SE ≤ (target j-effect)/3.
- Verdicts state individual floors; A1 requires H1a at Holm level with the §4 SM control clean.

---

## §8 EXACTNESS

- **Exact int:** EC arithmetic, `#E`, `a_p`, `M` (integer solve of `4p=L²+27M²`), sextic-class(7) (exact
  power-residue), `a_p mod ℓ`, twist `g^k`, six-`a_p`-sum-zero, all rank/permutation counts & p-values,
  the surface-fit weighted LS in exact `Fraction`, invariant ranks by integer cross-multiplication.
- **δ-rank resolvability (v2 D5):** `p≥3000`; per-prime `K` sized so `SE_δ≤gap/5`; resolved-pair
  `|δ_i−δ_j|>5·SE_δ`; drop `<3` resolved pairs (sign-neutral magnitude filter).
- **Sanctioned float carve-out (analytic magnitude only):** the `p×p` FFT `|U|`, `e_n(·)`; error
  `≤1e−12≪δ`. complex128 only. No verdict decided by float precision.
- `check_no_float.sh` passes on the invariant/statistic module before any verdict.

---

## §9 PRE-COMMITTED OUTCOME TABLE — MECE over {H1a, H2∈(fire, underpowered, null-flat), H3} (audit DEFECT)

H2 now has a THREE-state axis; flatness (`g₁≈0`, resolved) is a resolved H2 state, not a cross-cutting
condition — this removes the A5/A3/A4 overlap. Every (H1a, H2) cell maps to exactly one row.

| # | Condition | Conclusion |
|---|---|---|
| **A1** | H1a fires (Holm) ∧ H2 fires ∧ §4 SM clean | **Arithmetic-residue structure BEYOND the smooth δ(p,n) surface.** Name the surviving residue invariant(s); the trajectory deficit is not fully explained by δ tracking `n`. Report `f̂`, within-`u` partial-R², `r(p)`, surviving p-values, and any H1b support. Deepest positive; next probe = the mechanism, its own prereg. |
| **A2** | H1a-null (powered) ∧ H2 fires | **H0: the scatter is δ's smooth dependence on group order `n` (which scatters via `a_p`); no residue structure beyond the surface.** The correctly-derived answer, stated WITHOUT the ill-posed finite-size/geometry label. Report surface, within-`u` partial-R², flat residual, power floor. |
| **A3** | H1a fires ∧ H2 underpowered | residual residue-structure without a powered surface slope ⇒ `f̂` underdetermined; report H1a **provisional**, requiring powered H2 (more twist primes) before A1. |
| **A4** | H1a-null (powered) ∧ H2 underpowered | inconclusive on both; report bounds + the §7/§4 floors; extend the twist schedule. NOT a refutation. |
| **A5** | H2 null-flat (`g₁≈0` resolved, powered) — ANY H1a state | **δ has no resolved `n`-dependence in the sampled band ⇒ the scatter is NOT the group order.** Positive: excludes the leading hypothesis; re-open the source (finer curve data or a p-direct effect). If H1a nonetheless fires, report the residue structure as the new object (it is not `n`-mediated). |
| **A6** | H1a or H2 `[UNDERPOWERED]` below §7 floor | bounded result + floor; route to A2/A4 only when the floor is met. NOT a refutation. |
| **A7** | H3 fires (independent) | δ depends on `j` beyond the trace (j=0-family-specific); its own follow-up. H3-null ⇒ "trace-universal at this scope." Never folded into A1. |
| **A8** | any P1–P6 misbehaves, OR §4 SM control dirty (leak into `r`) | affected arm uninformative; H1b void on a dirty SM; no verdict. |

**Unprojected-covariate clause (mandatory).** If H1a null and H2 fires/flat: report (i) the confirmed
real trajectory spread (≥10·SE_δ); (ii) within-`u` partial-R² and residual variance as numbers; (iii) the
explicit untested list (higher-order surface terms, `a_p mod ℓ` for ℓ∉{3,4}, class/conductor data,
`v₂(n)`), as next candidates — not absences.

**Output type:** a characterization + power + §0 scope. Never ECDLP/extraction/security; never a
mechanism claim.

---

## §10 CHANGE LOG v3→v4 (three defects + two refinements)
1. **Surface-adequacy gate respecified** (§4): within-prime partial-R²(u) ≥0.25 + H2 Fisher p<0.01,
   replacing the mis-targeted overall-R² floor (proven trivial by `R²_smooth=0.0048`, verified).
2. **P6 strengthened** (§5): plants an OUT-of-model-class smooth surface (`u²`+) with zero arithmetic
   residual and confirms no false H1 hit + that the SM control fires — the actual misspecification mode.
3. **MECE table fixed** (§9): H2 is a three-state axis (fire / underpowered / null-flat); flatness folded
   in as A5; `g₁≈0` removed from A3/A4 scope — every cell maps to one row.
4. **Refinement a:** H1 split into H1a (residue invariants, misspecification-protected, PRIMARY) and H1b
   (M/autocorr, smooth-confoundable, secondary, gated); added the SM negative control (`r` vs `u₀²`).
5. **Refinement c:** `a_p mod 3`/`a_p mod 4` treated as binary 2-group tests (Mann–Whitney, not
   continuous Spearman) with imbalance-aware power; sextic-class↔`a_p mod 3` dependence flagged (effective
   multiplicity <3, Holm still valid).
- **Carried from v3 (PASSED):** obstruction retirement, off-trajectory fit, exact small-`m` Fisher/H2,
  δ-resolvability, cheap cyclicity screen + realized-yield logging, direction-fixing cleanliness, frozen
  SHA'd schedule, `√(n−1)` cancellation, invariant integer exactness.
