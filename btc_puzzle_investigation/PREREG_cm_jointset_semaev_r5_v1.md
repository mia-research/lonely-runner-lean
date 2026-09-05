# PREREG — S5 (r=5 Semaev): CM-specific joint-set synergy of the FIFTH summation polynomial

**File:** `PREREG_cm_jointset_semaev_r5_v1.md`  **Status: SPEC ONLY — no runner has executed.**
**Splits out of (does not supersede):** `PREREG_cm_jointset_higherorder_v1.md` §2, which explicitly
deferred "`r=5` Semaev (`S₅`)" as a materially different primitive: *"requires the 5th summation
polynomial (a resultant chain with an extraneous-factor problem) and its own exactness + citation gate;
it does NOT share the v3/HO harness as a drop-in → SPLIT to its own prereg."* This is that prereg.
**Chain of custody:** `PREREG_cm_jointset_excess_v3.md` (A-joint base, `[VERIFIED-scope — scoped null]`,
r=3/m=3/μ₃) → `PREREG_cm_jointset_higherorder_v1.md` (A-joint-HO: r=4 Semaev + m=4/m=5 combos + GLV +
μ₂ + coord-pair + finer-interval, `RESULT_cm_jointset_higherorder_v1.md` = full scoped null across
discovery+OOS+ladder) → **this file (S5, the m=5 PURE-Semaev arm).**
**Runner (suggested):** `cm_jointset_semaev_r5_v1.py` (imports `model_curve_infra_v1.py` + one new exact
primitive `semaev_s5`; reuses v3/HO MI machinery, within-stratum permutation, plant harness).
**Curve schedule REUSED UNCHANGED:** `schedules_v1/schedule_A_joint_v1.json` (SHA
`c533f66952118e621b05dae8f9fbf0b0762ec8a8a25917653c642e0c5b151406`, confirmed on disk).

**Distinctness (non-negotiable).** This is the `m=5` INDEPENDENT-SET line on ENUMERABLE MODEL CURVES,
feature = the FIFTH Semaev summation polynomial `S₅` (a single symmetric 5-point relation). It is
**complementary to HO's S-C5**, which was the m=5 *pairwise-COMBO* arm (`Σ_{i<j} χ₃(x(P_i+P_j))`), NOT
the Semaev relation. It is NOT the single-key N15 readout test
(`PREREG_n15_joint_readout_confinement_v1.md`). It reuses v3's object (synergy `E`), matched
within-stratum null, paired CM/non-CM contrast, exact arithmetic, and firing-control discipline; only
the feature (`S₅`), set size (`m=5`), and the conditioning-stratum ESTIMABILITY DECISION (§2) change.

**Freeze protocol (inherited from v3/HO).** The runner prints this file's SHA-256 into the RESULT and
opens `PREREG_cm_jointset_semaev_r5_v1_DEVIATIONS.md`; every post-freeze change is a disclosed deviation
appended there. A run that did not complete is a run that did not happen (not a run that passed).

---

## 0. SCOPE BANNER

Enumerable model curves `E:y²=x³+B` (CM, `j=0`) and `E:y²=x³+Ax+B` (matched non-CM) over small primes
`F_q`, `q≡1 mod 3`, PRIME order `N`, `q≲2¹⁶` (possibly one ladder rung further only if power permits,
§5/§6). **`q=2²⁵⁶−2³²−977` is NOT enumerable; nothing here transfers to secp256k1; this carries ZERO
power against the real curve.** It measures a MECHANISM — does the `r=5` Semaev relation on CM structure
produce joint-set synergy at model scale — NEVER the real object. **No ECDLP / extraction / security
claim.**

Two matched arms per `q`, both from `schedule_A_joint_v1.json`: **CM** (`j=0`, `y²=x³+B`, `Z[ω]`) and
**non-CM** (ordinary, `j∉{0,1728}`, `|t²−4q|≥⌊√q⌋`), **both excluding anomalous (trace-1, `N=q`) curves**
(D4 — Smart-attackable curves must not enter the contrast from either side). `S₅` is defined for any
elliptic curve with `char q≠2,3`, so — UNLIKE the GLV arm P3 — the non-CM arm HAS a matched `S₅` feature,
and this arm produces a real `Δ = Î(CM) − Î(non-CM)`. The object is a JOINT property of a SET, never a
per-point marginal. **A null on any arm is a BOUNDED MAGNITUDE with stated power and scope — never a
closure.** (Burden-of-proof, project CLAUDE.md: a dismissal clears the same bar as a PROVED claim —
object + class-of-observable + power + scope, or it is an overclaim. No dismissal vocabulary in any
scoped-null verdict.)

## 1. OBJECT

Hypothesis (S5): for a SET of `m=5` targets `d_i` drawn INDEPENDENTLY uniform in a known interval
`I=[2^{b−1},2^b)`, the FIFTH Semaev summation feature `Ψ₅ = χ₃(S₅(x₁,…,x₅))` carries SYNERGISTIC
information about a joint label `J = (Σd_i) mod 3` EXCEEDING what per-point readouts carry, and this
excess is CM-specific (present on CM, absent on matched non-CM).

**Synergy `E` (v3 definition, re-used exactly).** Because the `d_i` are INDEPENDENT, per-point-only
features give `MI = Σ_i MI(Φ_i^pt ; T_i)` EXACTLY. Therefore, for the cross-feature `Ψ₅` and label `J`
conditioned on the per-point stratum `Φ^pt`, `E = Î(Ψ₅ ; J | Φ^pt)` is precisely the EXCESS `Ψ₅` adds
over the per-point marginals — **provided `Φ^pt` conditions on all per-point information `Ψ₅` can carry
marginally** (the load-bearing anti-tautology requirement, re-checked in §2R for the coarsened stratum
this arm is forced to use).

**The `S₅` primitive (construction + vanishing property).** Semaev's recursion (Semaev 2004 Thm 1;
Kosters–Yeo 2015 Prop 2.1) `f_n = Res_X(f_{n−k}(X_1..X_{n−k−1},X), f_{k+2}(X_{n−k}..X_n,X))` at `n=5`
(the split that pairs `f₄` with `f₃`):
`S₅(x₁,x₂,x₃,x₄,x₅) = Res_X( S₄(x₁,x₂,x₃,X), S₃(x₄,x₅,X) )`, where `S₄(x₁,x₂,x₃,·)` is degree
`2^{4−2}=4` in its free variable and `S₃(x₄,x₅,·)` is degree `2^{3−2}=2`; the resultant is a **6×6
Sylvester determinant** (deg-4 ⊕ deg-2), NOT the 2-quadratic closed form used for `semaev_s4`. `S₅` has
degree `2^{5−2}=8` in each `x_i`, is absolutely irreducible (Semaev Thm 1), and
`S₅=0 ⇔ ∃ signs ε_i and points P_i with x(P_i)=x_i and Σ ε_i P_i = O` (the 5-point relation;
Kosters–Yeo Prop 2.1 for r=5). Whether `f₅ = Res(…)` EXACTLY or carries an extraneous factor at r=5 is
**citation-verifier OWED (§10)** and gated by a mechanical KAT (§8) before any `Δ` promotes.

**Disjointness / forcedness ruling (re-checked for `S₅` in §2R).** `Ψ₅` is a field-side `F_q` symmetric
function of the five x-coordinates; `J` is a scalar-ring function of the `d_i`; the only bridge is the
DLP (`d_i ↦ [d_i]G ↦ x_i ↦ S₅ ↦ χ₃`). `Ψ₅` is NOT a difference/component sharing construction with `J`
(not the `r=v−w` artifact, not the linear-relation check). The one construction artifact `S₅` DOES admit
— a curve-INDEPENDENT trivial relation from a repeated x-coordinate — is removed by the coincident-x
guard (§2R/§8).

## 2. STATISTIC (one PRIMARY; the estimability decision; matched null stratum)

Estimator: v3's `Î(F ; T | Φ^pt)` (Miller–Madow corrected bits), ranked by the exact integer
within-stratum permutation count of §3. The float `log₂` inside MI is a monotone scalar ranked against
the exact integer null (carve-out, §8). Every `Î,Δ,p` carries scope
`(arm,q,N_CM,N_non,t_non,|I|,m=5,r=5,ℓ=3,N,N_eff,s,stratum-mode,MI_min)`.

**The estimability wall (stated honestly).** Full per-point conditioning `Φ^pt(5)=(χ₃x_i)_{i≤5}∈{0,1,2}⁵`
is `3⁵=243` strata; `Ψ₅∈{0,1,2} × J∈{0,1,2}` = 9 cells/stratum ⇒ **2187 cells**, ~9/cell at N=20000 —
the SAME wall HO's S-C5 hit (FRONTIER, VOID-gated). v3's lesson is binding: an unestimable table returns
an identically-0 / noise permutation statistic (v2's 27×27|27 omnibus was `mi=0.0000,p=1.0`). Therefore
the PRIMARY here is registered on a **coarsened, estimable stratum**, with the full ordered stratum kept
as a VOID-gated frontier co-arm.

**PRIMARY — S5-multiset (estimable).**
`Ψ₅ = χ₃(S₅(x₁,…,x₅)) ∈ {0,1,2}`; `J = (Σd_i) mod 3 ∈ {0,1,2}`; condition on the **symmetric multiset
stratum** `Φ^pt_ms = (n₀,n₁,n₂)` = the counts of the five per-point readouts `χ₃(x_i)` by value, with
`n₀+n₁+n₂=5`. Strata = `C(5+3−1, 3−1)=C(7,2)=21` (fewer if `χ₃=0`, i.e. `x_i=0`, is absent — reported).
`Î_S5 = Î(Ψ₅ ; J | Φ^pt_ms)`. **Verdict:** `Δ = Î_S5(CM) − Î_S5(non-CM)`; significance from the per-arm
within-stratum null (§3); direction from the paired CM/non-CM sign across the frozen schedule.

**Why the coarsening is not a power compromise — it recovers the SAME population synergy.** `Ψ₅`
(Semaev-symmetric) and `J` (a sum) are BOTH invariant under simultaneous relabeling of the five points,
and the `(x_i,d_i)` pairs are i.i.d./exchangeable. Given the multiset `(n₀,n₁,n₂)`, the extra information
in the ordered tuple `(χ₃x_1,…,χ₃x_5)` is exactly the position-labeling, to which both `Ψ₅` and `J` are
invariant. Hence, in the true distribution, `Î(Ψ₅;J | Φ^pt_ordered) = Î(Ψ₅;J | Φ^pt_ms)` EXACTLY — the
multiset is the order statistic, a sufficient statistic under exchangeability for any pair of symmetric
functions. The coarsening changes only the ESTIMATOR (from an unestimable 243-stratum table to an
estimable 21-stratum table), not the estimand. (This is a population identity; §2R gives the
anti-tautology consequence and §4 registers the placebo control that verifies the marginal-removal
empirically.)

**FRONTIER CO-ARM — S5-ordered (VOID-gated, robustness only).** `Î_S5^ord = Î(Ψ₅ ; J | Φ^pt(5))`,
`Φ^pt(5)=(χ₃x_i)_{i≤5}`, 243 strata, N=20000. Run ONLY as a robustness check of the multiset primary; a
firing here that the multiset misses names the ordered stratum as a next probe, never the headline; if
its plant (PC-S5-ord, §4) cannot fire at N=20000 the co-arm is VOID (no null banked at ordered
resolution — abstaining, not closing).

## 2R. ANTI-TAUTOLOGY (re-derived for `S₅` and for the coarsened stratum)

- **`S₅` is a genuine symmetric 5-point field function, not a per-point readout.**
  `S₅=0 ⇔ ∃ signs ±P₁±P₂±P₃±P₄±P₅=O` — a real 5-point group relation, a symmetric CROSS function of
  all five x-coordinates, not a function of any single `x_i`. Feature→label is the DLP; no shared
  construction with `J=Σd mod 3` beyond `(E,q,the set)`. **RULE IN.**
- **The coincident-x construction artifact (the load-bearing hygiene point, extended from the S4
  verdict).** A tuple with a REPEATED x-coordinate forces `S₅=0` as a curve-INDEPENDENT trivial relation
  (`+P−P+…=O`), i.e. `Ψ₅=χ₃(0)=0` for reasons unrelated to CM structure. Because `draw_sets` draws each
  `d_i` by INDEPENDENT `randrange` over `[2^{b−1},2^b)`, two `d_i` can coincide as SCALARS (⇒ identical
  points ⇒ identical x); at the smallest discovery prime this rate is ~`C(5,2)/2^{b−1}≈15%` (q=541,
  b=7, span=64), falling with `q`. (Distinct scalars in the interval give distinct x: `x([d_i]G)=x([d_j]G)
  ⇔ d_i≡±d_j mod L`, impossible for distinct `d_i,d_j∈[2^{b−1},2^b)` since `d_i+d_j<2^{b+1}<L` and
  `d_i≠d_j`.) **GUARD (registered, in the feature path, not merely a KAT):** skip any tuple with
  `len(set(x_i)) < 5`. Applied IDENTICALLY to CM and non-CM arms, inside `measure` AND inside every
  plant, BEFORE any statistic — a matched removal of a confound, not a post-hoc label-dependent filter.
  The runner reports `N_eff` (retained) per arm/prime. **RULE IN under the guard.**
- **Does the coarsened (multiset) stratum reintroduce a per-point marginal?** No — and this is provable,
  not merely argued. Any per-point-only feature that is a symmetric aggregate of the per-point readouts
  `χ₃(x_i)` (e.g. `Σ_i χ₃(x_i) mod 3`, or any counts-based functional) is a DETERMINISTIC function of
  `(n₀,n₁,n₂)`, hence `Î(such feature ; J | Φ^pt_ms) = 0` identically. Thus the multiset stratum removes
  the per-point `χ₃`-marginal channel COMPLETELY — the same channel the ordered `χ₃` stratum removes.
  The ONLY per-point channels NOT removed (per-point `χ₂(x_i)`, interval position) are exactly those the
  ordered `χ₃` stratum of v3/HO also does not remove — so the coarsening introduces NO NEW marginal leak.
  Registered as an explicit placebo control (PC-PLACEBO, §4: `Σ_i χ₃(x_i) mod 3` must return within-null).
  **RULE IN.**

## 3. MATCHED CONTROL (within-stratum permutation)

Both the primary and the frontier co-arm **permute the feature `Ψ₅` WITHIN each conditioning stratum**,
holding the stratum and the labels fixed — preserving `p(Ψ₅ | stratum)` in every stratum and destroying
ONLY the within-stratum `Ψ₅↔J` coupling (the exact matched null for conditional MI; NOT a global
permutation, which would break the symmetry `Ψ₅` and `J` have by definition — the invalid-null failure
mode this project has hit).

| arm | stratum permuted within | why this stratum removes all per-point info `Ψ₅` can carry |
|---|---|---|
| S5-multiset (PRIMARY) | `Φ^pt_ms=(n₀,n₁,n₂)` of `(χ₃x_i)` | any symmetric aggregate of per-point `χ₃x_i` is a fn of `(n₀,n₁,n₂)`; `Ψ₅,J` symmetric ⇒ ordered adds nothing (§2R) |
| S5-ordered (FRONTIER) | `Φ^pt(5)=(χ₃x_i)_{i≤5}` | per-point x-readout is `χ₃x_i`; robustness at finer resolution |

`≥10⁴` restricted permutations; exact integer count p-value `p=(ge+1)/(R+1)` (Fraction). `Δ`: each arm
vs its OWN within-stratum null; paired CM/non-CM sign across the frozen schedule. The permutation p is
exact and VALID even where corner strata are sparse (sparsity costs power, not validity — §5).

## 4. PLANTED / FIRING CONTROL (must fire; monotone; VOID rule)

All plants inject ONLY into the conditioned-in cross channel, mirror v3/HO's PC-SEM/PC-COMBO/PC-C5
(mixture plant using a REAL INDEPENDENT resampled 5th point, never a degenerate linear collapse), respect
the coincident-x guard, and are required to fire `p<0.01` at `ρ=0.30`, monotone across
`ρ∈{0,0.15,0.30,0.60}`, with a non-degeneracy guard. **If a required plant does not fire at `(q,N)`,
that arm is VOID at that scale (no null claimed); a tripped non-degeneracy guard ⇒ STOP-fix (mis-built
plant), distinct from VOID.**

- **PC-S5 (PRIMARY, must fire).** Resample `d₅` (REAL independent `P₅`) until `Ψ₅ == J`, subject to
  `len(set(x_i))=5`. Because both `Ψ₅` and `J` are 3-valued, the plant exercises ≥2 label values (avoids
  the HO P4_μ₂ 3-vs-2 degeneracy). Guard: `#distinct(Ψ₅_planted) ≥ 2`; `S₅≠0` on ≥99% planted (after the
  guard); coincident-x guard active. VOID if unfired at `(q,N)`.
- **PC-S5-ord (FRONTIER co-arm, must fire for the ordered co-arm to bank anything).** Same plant,
  evaluated under `Φ^pt(5)` at N=20000. If it does not fire ⇒ ordered co-arm VOID (frontier-limited);
  the multiset primary is unaffected.
- **PC-PLACEBO (must NOT fire — marginal-removal control).** Feature `Ψ_pp = (Σ_i χ₃(x_i)) mod 3`
  conditioned on `Φ^pt_ms`; algebraically a within-stratum constant ⇒ `Î` must be within null (`p` not
  `<0.01`, `mi≈0`). A firing here would prove the multiset stratum FAILS to remove the per-point
  `χ₃`-marginal ⇒ STOP-fix the stratum (the anti-tautology invariant is broken), and NO `Δ` may be read.
- **PC-GRADE (resolution floor).** `Ψ₅_plant = J` w.p. `mix`, else uniform; monotone firing; the
  `MI_min` rung (§5) must fire ≥80%. Calibrates that the estimator resolves an effect of size `MI_min`
  at the arm's `(N, table)`.
- **PC-nonCM (CM-specificity control).** The matched non-CM arm is the control for CM-specificity of the
  `Δ`. (S₅ is curve-generic, so this arm is a real computed feature, not a placebo.)

## 5. POWER + ESTIMABILITY

**Model (v3/HO, unchanged form).** For an `(a×b | s)` conditional table, `df=(a−1)(b−1)·s` and
`MI_min(df,N)=λ₈₀(df)/(2 N ln2)` bits, where `λ₈₀(df)` is the noncentral-χ² noncentrality for 80% power
at `α=0.05`. The runner recomputes `λ₈₀(df)` exactly at the frozen config; the table below uses the HO
LINEAR planning scaling `λ₈₀(df)≈54.9·df/108` (anchor `λ₈₀(108)=54.9`), which OVERSTATES `λ₈₀` for large
`df` (true growth ~`df+c√df`) and therefore reports a CONSERVATIVE `MI_min` — true power is at least this
good.

| arm | a×b | s (strata) | df | N | MI_min (bits, conservative) | estimability (~count/cell) |
|---|---|---|---|---|---|---|
| **S5-multiset (PRIMARY)** | 3×3 | ~21 | ~84 | 5000 | ~6.2×10⁻³ | ~26/cell mean (189 cells) |
| **S5-multiset (PRIMARY)** | 3×3 | ~21 | ~84 | 20000 | ~1.5×10⁻³ | ~106/cell mean |
| S5-ordered (FRONTIER) | 3×3 | 243 | 972 | 20000 | ~1.8×10⁻² | ~9/cell — VOID-gated |

Corner multiset strata (`(5,0,0)`-type, multiplicity 1) carry ~`N/243` samples over 9 cells (~9/cell at
N=20000); the dominant strata (`(2,2,1)`-type, multiplicity 30) carry ~30× that. The exact within-stratum
permutation p is valid regardless; sparsity in the corners costs power, not validity. `Ψ₅=χ₃(0)=0` after
the coincident-x guard is generic-rare, so the feature is effectively `{0,1,2}`-valued as in v3.

**Weil-type multiplicative-character floor.** The relevant single-character floor is a Weil/Deligne
MULTIPLICATIVE-character bound `∼ (deg f)·√q / N_ord`, NOT the KS-2000 additive `e_p(rational f)` theorem
(D3). `Ψ₅=χ₃(S₅)`, `deg S₅ = 2^{5−2}=8` in each variable — HIGHER than `S₄` (deg 4) — so the floor is
correspondingly coarser; the runner logs `deg f=8`, `√q/N_ord`, and the resulting floor per prime. **HO
finding (carried):** the CM arm was FLOOR-LIMITED — raw `Î` shrank with `N` toward the null mean (plug-in
bias absorbed by the matched null, not signal); the same diagnostic (`Î` shrinking with `N`) is reported.

**Estimability limit named.** Full ordered `m=5` conditioning (243 strata) is unestimable at feasible `N`
(the wall). The multiset coarsening is what makes `m=5` pure-Semaev estimable at all; it is
information-equivalent for the true synergy (§2). A run that finds PC-S5 unable to fire at the planned
`(q,N)` returns VOID for the primary and reports the `N` that would be needed.

## 6. SCOPE / PARAMETERS

- **Curve schedule REUSED UNCHANGED:** `schedules_v1/schedule_A_joint_v1.json` (SHA `c533f669…`):
  discovery `{541,571,577}`; confirmation/OOS `{2029,2053,2089}`; ladder `{1033,4111,16417,65539}`.
  CM = `j=0` B-witness prime order, `q≡1 mod 3`, `trace≠1`; non-CM = ordinary `j∉{0,1728}`,
  `|t²−4q|≥⌊√q⌋`, `t≠1`, minimize `|N_non−N_CM|` (ladder uses the D-LADDER bounded-random matcher, exact
  order match, `seed=q`). Generator = the order-`L` point of smallest x, smaller y.
- **Arm parameters (FROZEN):** `m=5`, `r=5`, `ℓ=3`; feature `Ψ₅=χ₃(S₅)`; label `J=(Σd) mod 3`; PRIMARY
  stratum = multiset `(n₀,n₁,n₂)` of `(χ₃x_i)`; FRONTIER co-arm stratum = ordered `Φ^pt(5)`.
- `b=⌊log₂ q⌋−2` (interval `I=[2^{b−1},2^b)`; assert `2^b < L`). `N`: discovery 5,000; confirmation/OOS
  20,000; ladder 5,000; the FRONTIER co-arm runs at N=20,000 only. `N_eff` (post coincident-x guard)
  reported per arm/prime. `seed = 20260821`; `#perm ≥ 10⁴`. Anomalous curves excluded BOTH arms.
- One ladder rung beyond `2¹⁶` MAY be added ONLY if PC-S5 fires and per-prime cost (dominated by the 6×6
  `S₅` Sylvester determinant × `N` × `R`) stays tractable; adding it is a disclosed deviation.

## 7. FALSIFICATION (pre-committed)

For the PRIMARY arm S5-multiset:
- **RETAINED ⇔** PC-S5 + PC-GRADE fired AND PC-PLACEBO did NOT fire; CM within-stratum `p≤0.01`
  REPRODUCIBLY (≥ half of discovery+confirmation primes AND holds OOS); `Δ>0` beyond the paired null
  across the schedule.
- **SCOPED NULL ⇔** PC-S5 + PC-GRADE fired, PC-PLACEBO did not fire; CM `p` within the null across the
  whole schedule; `Δ≤0` ⇒ `|Δ|<MI_min(N)` reported WITH object + class-of-observable + power + scope +
  untested-channel list. Never "no structure"; a magnitude is a size, not an absence (Weil floor
  uncrossed).
- **OFF-TARGET ⇔** the multiset primary is null but the FRONTIER co-arm S5-ordered fires `p≤0.01`
  (reproducibly, with PC-S5-ord fired) ⇒ name the ordered-`m=5` stratum as the next probe; not the
  headline.
- **VOID ⇔** PC-S5 did not fire at `(q,N)` ⇒ instrument dead at scale; bank NO null; report the power
  ceiling and the `N` needed.
- **STOP-FIX ⇔** PC-PLACEBO fires (multiset stratum fails to remove the per-point `χ₃`-marginal) OR a
  non-degeneracy guard trips ⇒ mis-built stratum/plant; fix before any read; distinct from VOID.

**Arm-abandonment (this prereg):** if S5-multiset returns SCOPED NULL with all required plants fired,
PC-PLACEBO silent, and flat `Δ` across the schedule, conclude: no CM-specific joint-set synergy in the
`r=5` PURE-Semaev channel at `q≲2¹⁶`, `m=5`, at the tabulated power — a BOUNDED MAGNITUDE, NOT a closure;
the ordered-resolution stratum (if VOID), the joint-`μ₆` label, and `r≥6` remain untested.

## 8. EXACTNESS (no-float compliance)

Signal path is int/GF(q) throughout: curve arithmetic, x-coords, `χ₃`, `S₃`, `S₄`, the `S₅` Sylvester
determinant, the multiset counts `(n₀,n₁,n₂)`, all labels, and every permutation COUNT (Fraction). Banned
ops (`/`, `float()`, `**0.5`, `round(ratio)`, `math.*/np.*` on curve/point/feature values) do not appear
in the signal path. Ratio comparisons use integer cross-product.

- **`S₅` exactness (the new mechanical gate the runner owes).** `S₅(x₁,x₂,x₃,x₄,x₅) =
  Res_X(S₄(x₁,x₂,x₃,X), S₃(x₄,x₅,X))`. Two exact routes, both float-free over GF(q): (a) obtain the
  degree-4-in-X coefficient vector of `S₄(x₁,x₂,x₃,X)` by exact Lagrange interpolation of the existing
  `semaev_s4` evaluated at 5 distinct nodes mod `q` (interpolation via integer arithmetic + modular
  inverse `pow(·,q−2,q)`, no float), then (b) the **6×6 Sylvester determinant** of the deg-4 ⊕ deg-2
  system by division-free cofactor/Laplace expansion mod `q` (only `+,−,×,mod`). The resultant may carry
  an EXTRANEOUS FACTOR at r=5; the runner divides it out per Kosters–Yeo and asserts the vanishing
  identity on a **KAT** (mechanical, self-auditable WITH the artifact per CLAUDE.md §2b):
  (i) `S₅=0` on constructed true 5-relations `P₅=−(P₁+P₂+P₃+P₄)` (100% vanish);
  (ii) generic-nonzero on random 5-tuples AFTER the coincident-x guard (`<10%` spurious zeros);
  (iii) `S₅=0` on planted coincident-x tuples is CORRECTLY excluded by the guard (confirms the guard is
  the reason, not an extraneous factor).
- **Coincident-x guard in the signal path.** `len(set(x_i)) < 5 ⇒ skip` in `measure` and in every plant,
  identically across arms, before any statistic; `N_eff` reported.
- **Float carve-out (unchanged from v3).** Float appears ONLY as the `log₂` inside the MI estimator, used
  as a monotone quantity RANKED against the exact integer within-stratum permutation count; the verdict
  p-value is an exact Fraction of integer counts. Statistic lines carry `# noqa: float`.
- **`check_no_float.sh` MUST exit 0** on `cm_jointset_semaev_r5_v1.py` and the new `semaev_s5` primitive
  before any arm is run or any result reported.

## 9. PRE-COMMITMENT TABLE

| arm (channel) | outcome | trigger | conclusion | grade |
|---|---|---|---|---|
| **S5-multiset** (r=5 pure Semaev) | CM synergy | PC-S5+PC-GRADE fired, PC-PLACEBO silent; CM `p≤0.01` reproducible; `Δ>0` beyond paired null | CM produces `S₅`-`μ₃` joint-set synergy absent on non-CM. NEXT: which multiset stratum drives it; ordered-`m=5` co-arm; joint-`μ₆`; `r≥6`. | EMPIRICAL (mechanism, model-scale) |
| S5-multiset | scoped null | PCs fired, PC-PLACEBO silent; CM within null; `Δ≤0` across schedule | `|Δ|<MI_min` (~1.5×10⁻³ @20k / ~6.2×10⁻³ @5k): no CM-specific `S₅`-`μ₃` joint synergy at `q≲2¹⁶`, `m=5`. Bounded magnitude + power + scope; untested: ordered-`m=5` (if VOID), joint-`μ₆`, `r≥6`. | VERIFIED-scope (scoped null) |
| S5-multiset | void | PC-S5 did not fire | instrument dead at scale; report `N` needed; bank NO null. | VOID |
| S5-multiset | stop-fix | PC-PLACEBO fired OR guard tripped | multiset stratum/plant mis-built (per-point marginal not removed); fix before any read. | STOP-fix |
| generic (either arm) | CM-independent | `Î` fires BOTH arms; `Δ≈0` | `S₅` synergy generic to `d↦point`, not CM-specific. | EMPIRICAL (generic) |
| **S5-ordered** (frontier) | lead / null / void | own ledger, N=20k, PC-S5-ord gate | ordered-`m=5` stratum named as probe / bounded frontier null (~1.8×10⁻²) / VOID if PC-S5-ord unfired. | EMPIRICAL (exploratory) / VERIFIED-scope (frontier) / VOID |

Every scoped-null row carries the symmetric burden (object / class-of-observable / power / scope). No
dismissal vocabulary anywhere. Abstaining on the frontier co-arm (VOID) is NOT closing that channel.

## 10. OWED GATES

- **`semaev_s5` exactness KAT (mechanical — runner owes, self-auditable WITH the artifact per §2b):** the
  three-part KAT of §8 (true 5-relations vanish; generic-nonzero after the guard; guard, not an
  extraneous factor, explains coincident-x zeros) MUST pass before any `Δ` is read. Mechanical layer —
  the artifact (KAT log) discharges it; isolation not required.
- **`citation-verifier` OWED (FRAME/citation — external, before any S5 `Δ` promotes):** the r=5-specific
  question — does `f₅ = Res_X(S₄(x₁,x₂,x₃,X), S₃(x₄,x₅,X))` hold EXACTLY, or with an extraneous factor,
  and is the K-Y Prop 2.1 vanishing identity `S₅=0 ⇔ ±P₁±…±P₅=O` correctly stated at r=5 (plus the
  Prop 2.2 degenerate-tuple treatment the HO S4 gate left owed)? (Semaev 2004 Thm 1 / Kosters–Yeo 2015
  Prop 2.1–2.2.) Also: the higher-degree (`deg f=8`) Weil/Deligne multiplicative-character floor cited in
  §5.
- **Second independent `experiment-designer` read of THIS prereg: OWED (FRAME layer)** before any `Δ`
  promotes — object/disjointness for `S₅`, adequacy of the MULTISET matched null (the coarsening is the
  novel frame element and cannot be self-audited from inside this context), scope, falsification,
  pre-commitment.
- **`compile-diff` OWED** if this prereg or its result is folded into a master/handover.
- **Provisional-run rule (CLAUDE.md §2a):** if a gate is UNAVAILABLE, tag every output
  `[PROVISIONAL — <gate> unavailable]` in the grade slot, attach a self-audit naming its uncovered FRAME
  sections (for this arm: the multiset matched-null adequacy is the highest-risk FRAME item), record the
  gate as owed with date/reason; NO grade promotion until it clears. A run that did not complete did not
  happen.

---

**Provenance.** Pre-registered via the `experiment-designer` gate (context-isolated: baseline v3 +
HO prereg/result + the `S₅` construction + the estimability-wall statement + criteria only; no session
narrative, no expected answer), 2026-08-25. Splits the `r=5` Semaev channel out of
`PREREG_cm_jointset_higherorder_v1.md` §2. Reuses `model_curve_infra_v1.py`, the v3/HO MI machinery and
within-stratum permutation harness, and `schedules_v1/schedule_A_joint_v1.json` (SHA
`c533f669…`, on-disk-confirmed). Load-bearing facts checked against the code before writing: `chi3`
range `{0,1,2}` with `chi3(0)=0` (`model_curve_infra_v1.py`); `draw_sets` uses independent `randrange`
(so repeated SCALARS — hence coincident x — occur at ~15% at q=541, motivating the guard); `S₄` degree-4
/ `S₃` degree-2 ⇒ 6×6 Sylvester (matches Semaev degree `2^{r−2}`). The exchangeability/sufficient-statistic
justification for the multiset coarsening (population identity `Î(·|ordered)=Î(·|multiset)` for symmetric
`Ψ₅`,`J`) is derived in §2. The multiset matched-null adequacy is the highest-risk FRAME item and is the
owed second experiment-designer read's first target. This is SPEC ONLY — no runner has executed.
