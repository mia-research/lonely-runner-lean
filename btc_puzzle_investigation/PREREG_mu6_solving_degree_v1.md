# PRE-REGISTRATION — does the μ₆/ω-symmetry of the j=0 Semaev system LOWER its solving degree vs a #E-matched non-CM system?

**Status: FROZEN 2026-08-13, BEFORE any data.** No computation run; no data seen. This file is the
spec. A run is judged against it (post-run audit mode). Any change after the first datum is a
DEVIATION and must be disclosed.

**Probe id:** P2 (the solving-degree lever probe named in `ANALYSIS_semaev_cm_yield_mechanism_v1.md §4`
and `CORRECTION_semaev_cm_yield_mechanism_literature_v1.md §4`). This is the SOLVING-DEGREE invariant,
NOT R1's yield/`quo` invariant.

**Instruments to reuse (frozen):** `semaev_elimination_v1.py` (`_build_summation`, `summation_poly`,
`decomposition_system`, `measure_system`, `macaulay_stats`, `decomposable_target`, `mu3_lever_test`);
`semaev_cm_relation_yield_v4.py` (`match_nearest`, `build_curves`). One HARNESS EXTENSION is required
(see §2, `d_LF`) — that extension must be frozen and the firing plant re-run on the extended harness
before any cell is measured.

---

## 0. Ordering guard (why this spec exists)

Three ordering traps are pre-closed here, each traceable to a prior failure on this project:

- **Trap A — the forced statistic (tautology).** `RESULT_semaev_dsolv_statistic_power_v1.md` Finding 1
  proved the *matched-inconsistent* `d_solv` equals `deg(Sx)+m(|V|−1)` EXACTLY, identical across curves,
  because the Semaev leading form is isobaric hence curve-independent. That statistic has **zero power**;
  "identical across curves" there is FORCED, not measured. **First-fall degree `d_ff` inherits the same
  defect** (it is a leading-form invariant → curve-independent → forced). Both are EXCLUDED as the
  primary statistic by pre-commitment (§2). Using either would be a rationalization with a p-value.
- **Trap B — yield/degree entanglement.** R1 established j0 has HIGHER decomposition count `quo`
  (~log|V|). The quo-saturation degree `d_solv` is *defined by hitting the quo target*, so a raw
  cross-curve `d_solv` difference re-expresses the already-known yield difference — a tautology dressed
  as a new invariant. The primary statistic is therefore the **last-fall degree `d_LF`** (a regularity
  invariant) measured on **quo-MATCHED pairs** (§2, §3). Disentanglement is built into the pairing, not
  applied post hoc.
- **Trap C — closure by declaration.** Per `CORRECTION_..._literature_v1.md`: a null here is a scoped
  COMPONENT result (solving degree is one factor of total IC cost = relations × (1/yield) ×
  cost/solve + linear algebra), NEVER a closure of the CM/Semaev avenue. Pre-committed in §9.

---

## 1. OBJECT

**What is measured:** the *last-fall degree* `d_LF` (equivalently the degree of regularity read from the
Macaulay rank profile) of the **consistent** point-decomposition ideal
`I = ⟨ S_{m+1}(x₁,…,x_m, t) ⟩ + ⟨ g_i(x_i) = Π_{r∈V}(x_i − r) : i=1..m ⟩` over `GF(p)`, where `t = x`-coord
of a real decomposable target `T = P₁+…+P_m`, `P_i` points whose x-coords lie in the factor base `V`.
This is the binding-cost invariant of Semaev index calculus (Caminata–Gorla: solving degree ≥ last-fall
degree — CITATION OWED, §h).

**The object, not a proxy.** `d_LF` is the highest degree at which a genuine reduction-to-lower-degree
occurs in the exact Macaulay computation; it is the standard object the "solving degree" is compared to,
and it is an emergent computational property of `I`, not a quantity defined to differ between curves.

**Tautology check (stated before the run).** The j=0 system's ω-covariance
`S_{m+1}(βx₁,…,βx_m,βx_T) = β^κ S_{m+1}` (β³≡1, an EXACT algebraic symmetry) is present **by
construction** (A=0). That is the feature. The target is `d_LF`, an emergent Gröbner/Macaulay quantity —
disjoint in construction from the covariance, so measuring one against the other is NOT a tautology.
The ONE genuine entanglement is with `quo` (Trap B): `quo` and `d_LF` are both computed from the same
ideal, and the yield difference is already known. That entanglement is removed by quo-matching (§3), and
`d_solv` (the quo-saturation degree, entangled by definition) is DEMOTED to a disclosed secondary
read-out, never the primary.

**Subspace caveat (mandatory, per project law).** `d_LF` is a scalar. If the ω-symmetry's effect on the
Gröbner computation lives NOT in the scalar last-fall degree but in the *shape* of the resolution — the
μ₃-graded pieces of the staircase, which variables resolve first, the syzygy-module degrees — a scalar
null does NOT close it. A scalar null is scoped to the scalar; the pre-committed non-closure follow-up
(§9) is the μ₃-graded staircase / syzygy structure.

---

## 2. STATISTIC (exactly one, named now)

**Primary statistic:** `d_LF` = the **last-fall degree**, defined operationally as

```
d_LF(I) := max { D ∈ [1, Dmax] : macaulay_stats(F, gens(I), xs, Dmax)[D]['fall'] > 0 }
```

read from the EXACT Macaulay rank profile `macaulay_stats` in `semaev_elimination_v1.py` over `GF(p)`
(the field `fall = inter − prev_rank`; a fall > 0 at degree D marks a genuine new lower-degree element).
`macaulay_stats` already computes `fall` per degree; the harness currently returns only the FIRST fall
(`d_ff`). **Harness extension (frozen before any cell):** add `d_LF = max{D : fall(D)>0}` to
`first_fall_and_solving`. This is a read-out change only; `macaulay_stats` (the exact linear algebra) is
unchanged. The extended harness is frozen (SHA-256 recorded) and the firing plant (§4) is re-run on it.

**Distribution under the null.** Under H0 (ω-symmetry does not lower the last-fall degree), the paired
per-prime difference `Δ = d_LF(j0) − d_LF(nonCM_matched)` is symmetric about 0 → a sign-flip permutation
null: `Σ ε_i Δ_i`, `ε_i∈{±1}`, pooled over primes (targeted, pooled statistic — NOT a max-over-cells).

**Excluded statistics (pre-committed, with reason):**
- `d_ff` (first-fall degree): FORCED curve-independent (leading-form invariant, isobaric) — zero power.
- matched-INCONSISTENT `d_solv`: FORCED `= deg(Sx)+m(|V|−1)` (Finding 1) — zero power.
- raw cross-curve `d_solv` (quo-saturation): entangled with `quo` by definition (Trap B) — retained
  ONLY as a disclosed secondary read-out, never the headline.

**Secondary read-outs (reported, never the verdict):** `d_solv`, `d_gb` (max reduced-GB generator
degree from `I.groebner_basis()`), and the Caminata–Gorla consistency check `d_gb ≥ d_LF` /
`solving_degree ≥ d_LF`. Divergence between `d_LF` and `d_gb` is disclosed, not hidden.

**Validity gate on every cell (Dmax-stability, per Finding 1's method):** `Dmax` must be large enough
that `quo` fully resolves AND that raising `Dmax` by +8 leaves `d_LF` unchanged. A cell whose `d_LF` is
censored by `Dmax` (moves when `Dmax` is raised) is marked UNRESOLVED and excluded from the pooled
statistic (its exclusion is recorded — no silent filtering).

---

## 3. MATCHED CONTROL

The consistent regime FORBIDS an identical-V control (each curve needs its own decomposition points, so
V differs per curve — the identical-V control is exactly the forced inconsistent regime of Trap A).
The matched control is therefore **#E-matching + a null band**, with quo-matching layered on to kill
Trap B.

**Primary matched control (isolates μ₆/CM from #E and from yield):**
- Per model prime, build j0 (`y²=x³+B`, μ₆) and `n_nonCM ≥ 5` **ORDINARY** non-CM curves
  (`j∉{0,1728}`, `4A³+27B²≠0`), via `build_curves`.
- Pair j0 to the NEAREST-#E non-CM (`match_nearest`), C2-capped: accept only if relative #E gap
  `< 2/√p` (else the prime is dropped from the pooled test — recorded).
- **quo-matching (removes the yield confound):** for the paired (j0, nonCM) cell, resample
  decomposable targets (`decomposable_target`, distinct seeds) until a j0 target and a nonCM target with
  **equal `quo`** are found (bounded attempt budget B_match; if unmet at a prime, that prime is recorded
  as quo-unmatched and enters ONLY the stratified fallback, not the primary paired test).
- Statistic per prime: `Δ = d_LF(j0, quo=q) − d_LF(nonCM_matched, quo=q)`.

**What the control PRESERVES:** p; #E (±2/√p); m; |V|; the Semaev generator degree profile (isobaric →
IDENTICAL leading forms across curves — proven, `semaev_elimination_v1.py` `isobaric_check` /
`leading_form_independence`); consistent regime (real decompositions); `quo` (matched). **What it
DESTROYS:** the j=0 ω-covariance of `S_{m+1}` and the curve arithmetic. Because leading forms are
identical (Finding 1), any surviving `Δ` lives strictly in the LOWER-order structure — which is exactly
where an ω-syzygy effect would live, and (after quo-matching) is NOT the yield channel.

**Disclosed residual confound.** The cross-curve arm still varies "which specific decompositions exist"
(curve arithmetic). This is absorbed by the null band over `n_nonCM` curves and by the within-j0 arm
below; it is stated, not hidden.

**Secondary matched control — the SHARP ω-isolation (mechanism tie, §e):** within the SAME j0 curve,
`mu3_lever_test` compares a **β-invariant** factor base `V` (μ₃-orbit-closed, so `g_i ∈ F[x³]`, the whole
ideal ω-equivariant) vs a **random** `V` of identical size, both containing the SAME decomposition
x-coords. This toggles ONLY the factor-base μ₃-symmetry (identical p, #E, curve, `S_{m+1}`, m, |V|,
target). Statistic: `Δ_β = d_LF(betaInvV) − d_LF(randomV)`, quo-matched, sign-flip null over primes.
A `Δ<0` in the cross-curve arm is credited to the ω-action ONLY if `Δ_β<0` corroborates.

**Secondary discriminating arm (j0-specific vs generic-CM):** j1728 (μ₄), ORDINARY (require p≡1 mod 12),
#E-matched, same statistic — to separate a μ₆-specific drop from a generic-CM drop (Finding 3's open
question). Not part of the primary verdict.

---

## 4. PLANTED CONTROL (must fire) + NEGATIVE CONTROL

**Firing plant (independent of the hypothesis — a KNOWN last-fall-degree gap of KNOWN size).** Build a
matched pair of ideals over `GF(p)` with IDENTICAL generator-degree profile
`(deg S = 2^{m−1}·m or the actual deg(Sx), |V|, …, |V|)` and IDENTICAL solution count (matched quo):
- `I_low` — a system carrying a planted syzygy that forces an EARLY last fall: e.g. top forms sharing a
  common factor / an injected linear syzygy among the leading forms, whose last-fall degree `d_low` is
  known a priori from the construction.
- `I_high` — a generic dense system of the same degree profile with no such syzygy, last-fall degree
  `d_high ≈` the Macaulay/complete-intersection bound `Σ(deg_i − 1) + 1`, `d_high > d_low`.
- **MUST FIRE:** `d_LF(I_low) < d_LF(I_high)`, i.e. the instrument reads the KNOWN drop. Record both
  integers and `d_low`, `d_high`. *(The §2 note that planted early-resolving systems give `d_solv=1`
  in `RESULT_semaev_dsolv_statistic_power_v1.md` is prior evidence the machinery can read a real drop;
  it must be re-confirmed for `d_LF` on the extended harness.)*
- **This plant is NOT the hypothesis.** It is a generic algebraic syzygy of known size, not the ω-action
  — so its firing certifies the instrument WITHOUT presupposing the μ₆ answer. (The β-invariant-V arm of
  §3 is the mechanism tie, deliberately kept SEPARATE from the firing plant to avoid circularity.)

**Negative control (must NOT fire):** two INDEPENDENT generic dense systems of the same degree profile
and matched quo → `Δ = d_LF(gen1) − d_LF(gen2)` centered at 0, sign-flip p not significant. If the
negative control fires, the null band is mis-calibrated → run VOID.

**Rule (project law):** if the firing plant does NOT fire, the null is uninformative — **full stop**,
outcome is VOID (§9), NOT a reported null.

---

## 5. POWER

- `d_LF` is a small INTEGER (for m=3, |V|∈{4..8}, the Macaulay bound is `deg(Sx)+Σ(|V|−1)`, so `d_LF`
  sits in a bounded low range). The MINIMUM detectable per-pair effect is therefore **one full integer
  degree**; a sub-integer trend is BELOW power and cannot be claimed.
- **Detection model:** if the true effect is "j0 lower by ≥1 degree in a fraction `q` of #E-matched,
  quo-matched pairs", a one-sided sign test on `N` pooled pairs detects `q` bounded above 0.5. With
  `N=24` primes (the frozen v4 band, or comparable): 18/24 negative `Δ` → p ≈ 0.011; 17/24 → p ≈ 0.032.
  So the design has power to detect an effect **present in ≳70% of pairs**; an effect present in **<65%**
  of pairs at N=24 is BELOW power — a null then means "no ≥1-degree drop in ≳70% of pairs", not "no
  effect".
- **Shape power (decisive for a scale claim):** stratify pooled `Δ` by |V| (and by m where tractable).
  Power to distinguish a CONSTANT (O(1)) drop from a GROWING drop requires the per-|V| pooled `Δ` to be
  monotone across ≥3 |V|-levels with consistent sign — the same AICc/flat-vs-linear-vs-log machinery R1
  used, ranked against a permutation bootstrap (size-only float, §8). At N=24 per level and integer `Δ`,
  a growth of <0.3 degree per |V|-step is below resolution.
- **Cross-prime stability (scale-free requirement):** a scale-free CLAIM needs the SIGN of `Δ` stable
  across the prime band AND corroborated by `Δ_β` (within-j0), NOT an extrapolation of a fitted number.

---

## 6. SCOPE

- **Model primes only.** `p ≡ 1 mod 3` (⟹ p≡1 mod 6, so μ₆ rational on j0 and the cube root β exists).
  Primary band: the FROZEN v4 set (24 primes, p∈[523,823]) or a comparable small band where m=3/4 is
  tractable. j1728 secondary arm restricts to `p ≡ 1 mod 12` (μ₄ ordinary). Every number the run emits
  carries `(p-band, m, |V|, quo, n_nonCM)`.
- **m grid:** m=3 (S₄) PRIMARY; m=4 (S₅) SECONDARY under a per-cell time box (e.g. 120s) — Finding 2 used
  m=4 successfully. m=5 (S₆): see §f (VOID — build intractable).
- **|V| grid:** m=3 → |V|∈{4,5,6,7,8} (v4's tractable range); m=4 → |V|∈{2,3,4} if the last-fall /
  Gröbner computation completes in the time box.
- **secp-scale (2²⁵⁶) is INFEASIBLE and is not attempted:** the exact Macaulay matrix over `GF(p)` with
  `p≈2²⁵⁶`, and the point enumeration `decomposable_target` needs, are astronomically infeasible; more
  fundamentally the deliverable is a MECHANISM claim (ω-action is scale-free), decided by cross-prime
  stability + the exact symmetry, NOT by extrapolating a model-scale number.
- **Every `d_LF` is a per-`(p,m,|V|,quo)` integer.** No number is stated without this scope tag.

---

## 7. FALSIFICATION (written before the run)

- **Instrument invalid → VOID (not a null):** firing plant does not fire, OR negative control fires, OR
  the primary cells are Dmax-censored (UNRESOLVED) at the |V| where μ₆ would matter.
- **H (μ₆ lowers `d_LF`) is FALSIFIED at this scope if:** with the plant firing and cells resolved, the
  quo-matched pooled sign-test on `Δ` has p > 0.05 (two-sided), AND the within-j0 `Δ_β` arm shows no
  drop (p > 0.05), AND `Δ` is not systematically negative in any |V|-stratum. → scoped COMPONENT NULL
  (§9), explicitly NOT an avenue closure.
- **A model-scale positive is DOWNGRADED to "structural curiosity, not a lever component" if:** the drop
  is a CONSTANT (O(1)) additive shift that does NOT grow with m or |V| (a bounded reduction does not
  change the exponential regime), OR it is NOT corroborated by `Δ_β` (so it is curve-arithmetic, not the
  ω-action), OR it appears equally on j1728 with no μ₆-specific component AND does not grow.

---

## 8. EXACTNESS

- **Signal path exact.** Macaulay ranks and Gröbner bases are over `GF(p)` (exact integer/modular linear
  algebra). `d_LF`, `d_ff`, `d_solv`, `d_gb`, `quo`, `dim` are INTEGERS read from ranks / GB generator
  degrees — no float threshold decides any degree. Curve construction, targets, factor bases: `int`/
  `GF(p)`. No key or key-derived value enters (this is model-prime arithmetic, no puzzle key).
- **Float carve-out (size-only, no key in path):** the permutation-test bookkeeping is integer counts/
  ratios (exact); the AICc/flat-vs-linear-vs-log SHAPE fit uses float LS but is ranked against a
  permutation bootstrap and reports a size, never a threshold verdict on the data — identical carve-out
  to the graded v4 harness.
- `check_no_float.sh` must pass on any new/extended signal-path code before the run.

---

## 9. PRE-COMMITMENT (filled BEFORE the run — one row per outcome)

| # | Outcome (plant fires unless stated) | Conclusion (pre-committed) | Grade |
|---|---|---|---|
| A | quo-matched pooled `Δ<0`, p<0.05, stable across primes, GROWS with m/|V|, corroborated by `Δ_β<0` | The ω-symmetry lowers the last-fall degree of the j0 Semaev system at model scale, tied to the exact ω-action, in a growing (not-merely-constant) way — a real structural finding and the **necessary-not-sufficient COMPONENT** that motivates the full IC-cost probe (yield × solves × cost/solve + linear algebra). NOT a lever claim on its own. | EMPIRICAL (DERIVED if the drop is analytically tied to the β-covariance syzygy count) |
| B | `Δ<0`, p<0.05, but CONSTANT (O(1), no growth) OR not corroborated by `Δ_β` | Bounded/curve-arithmetic degree offset; a structural curiosity, NOT a lever component (a constant shift does not touch the exponential; uncorroborated ⇒ not the ω-action). Report with the bound and scope. | EMPIRICAL — bounded, scoped |
| C | plant fires, cells resolved, `Δ` sign-test p>0.05 AND `Δ_β` p>0.05 | **Scoped COMPONENT NULL:** at p∈[band], m∈{3,(4)}, |V|∈{…}, quo-matched, the ω-symmetry does NOT lower the last-fall degree beyond the yield-matched baseline, with power to detect a ≥1-degree drop present in ≳70% of pairs. **Explicitly NOT a closure of the CM/Semaev avenue** — solving degree is ONE component of total cost; the μ₃-graded staircase / syzygy structure is the un-projected subspace and remains open (§1 subspace caveat). | EMPIRICAL — scoped component null (NOT avenue closure) |
| D | plant does NOT fire, or negative control fires, or primary cells UNRESOLVED at the |V| where μ₆ matters | **VOID** — instrument uninformative. State the tractability boundary (largest resolved `(m,|V|,p)`). No null reported. | VOID |
| E | m=4/5 (or large |V|) intractable in the time box where the ω-effect would be strongest | **VOID-intractable** with the tractability boundary stated; the probe's reach is scoped to the resolved `(m,|V|)`; a null at m=3 does NOT extend to the un-reached m. | VOID-intractable |

**No grade in this table moves UP until the owed citation-verifier passes (§h).** A run under an
unavailable gate is `[PROVISIONAL — citation-verifier owed]` in the grade slot and produces evidence
only, never a promotion (CLAUDE.md §2a).

---

## Deliverable cross-map (task letters → sections)

- **(a) operational degree statistic:** §2 — `d_LF = max{D: fall(D)>0}` from the exact `macaulay_stats`
  rank profile over GF(p); `d_ff`/inconsistent-`d_solv` excluded as forced; `d_solv`/`d_gb` secondary.
- **(b) exact system + grid + why:** §1 (`I = ⟨S_{m+1}(x,·,t)⟩ + ⟨Π(x_i−r)⟩`, degrevlex, consistent
  regime = attack-relevant), §6 (m∈{3,4}, |V| grids, p≡1 mod 3 band). Consistent regime is the right
  object because the inconsistent regime is forced (Trap A).
- **(c) matched #E control + null band:** §3 — `match_nearest` (C2-capped) + null band over n_nonCM,
  with quo-matching to remove the yield confound.
- **(d) firing + negative controls:** §4 — planted known-syzygy low-`d_LF` ideal (must fire) vs generic
  (must not); kept SEPARATE from the ω-mechanism to avoid circularity.
- **(e) μ₆ tie:** §3 secondary arm (`mu3_lever_test` β-invariant V vs random V, exact ω-action) +
  cross-prime stability (§5) — a positive is credited to ω only if `Δ_β` corroborates and the sign is
  prime-stable, so it is not a one-prime fluke.
- **(f) tractability boundary:** §6 + §9 row E — m=5 (S₆) build intractable (>240s,
  `RESULT_semaev_dsolv_statistic_power_v1.md`) → VOID; m=4 secondary under time box; |V|≤~8 at m=3.
- **(g) grade slots incl. component-null + VOID-intractable:** §9 rows C, D, E.
- **(h) falsification + scope + owed citation-verifier:** §7, §6, and below.

## Owed citation-verifier (BEFORE any grade moves up)

1. **Caminata–Gorla** (solving degree ≥ last-fall degree; eprint 2021/1611) — before `d_LF` is
   interpreted as a solving-degree LOWER bound.
2. **"No competitive prime-field summation-poly index calculus is known"** (Semaev; Petit et al.;
   Amadori–Pintore–Sala 2017, eprint 2017/609) — before any grade leans on it; and per
   `CORRECTION_..._literature_v1.md`, the extension-field LFD "stays exponential" literature
   (Huang–Kosters–Yang–Yeo; Semaev–Tenti) must NOT be cited as a prime-field secp bound (category
   error). Both are `[CITED]` and BLOCK grade promotion until cleared.

**Meta:** a null here is a component result, not a verdict on μ₆; a positive here is a component that
motivates the full-cost probe, not a lever. Neither closes the CM/Semaev avenue.
