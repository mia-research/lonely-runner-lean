# DEVIATIONS — PREREG_cm_jointset_excess_v1.md (A-joint)

Deviations from the frozen spec, disclosed per the prereg's freeze protocol. Each entry
is dated, states the change, the reason, and the impact on statistic/null/power/scope.

---

## D1 (2026-08-21) — exclude anomalous (trace-1) model curves from the j=0 selection

**Change.** The §6 selection rule "B-witness: smallest `B>0` s.t. `y²=x³+B` over `F_q` has
PRIME order" is amended to "…PRIME order **AND trace `t = q+1-N ≠ 1`** (i.e. `N ≠ q`)."
Implemented as `select_j0_prime_order(q, exclude_anomalous=True)` and
`schedule_A_joint(exclude_anomalous=True)` (default ON) in `model_curve_infra_v1.py`.

**Reason (a confound, found at staging, before any confirmatory run).** The bare B-witness
rule is biased toward **anomalous** curves (`N = q`, trace 1) because `N = q` is automatically
prime, so an anomalous sextic twist, when it exists, is often the smallest-`B` prime-order hit.
An anomalous curve admits **Smart's formal-group / p-adic-log attack**: the discrete log `d` is
recoverable **per point** in linear time. On such an arm every per-point label is effectively
readable, so the joint-synergy object `E = Î(Ψ;J|Φ^pt)` would be dominated by a per-point
anomalous leak rather than by CM joint structure — a direct confound of the CM-vs-non-CM
contrast `Δ`, and specifically a violation of the prereg's own §0 premise that per-point
readouts are (heuristically) redundant with the point. Excluding anomalous curves removes the
confound; it does not touch the object, the statistic, the null, or the power model.

**Impact.**
- Statistic / null / power / falsification: **unchanged.** This is a selection filter only.
- Schedule (`schedules_v1/schedule_A_joint_v1.json`): regenerated.
  - discovery `{541, 547, 571}` → **`{541, 571, 577}`** (q=547 had only the anomalous prime-order
    twist among its sextic twists; dropped; 577 backfills as the next qualifying `q>500`).
  - confirmation `{2029, 2053, 2089}` and ladder `{1033, 4111, 16417, 65539}`: unchanged (none
    was anomalous).
  - All emitted arms now carry `trace` and satisfy `trace ≠ 1`.
  - SHA-256 changed `a03f7217…f087c9` → **`c533f669…b151406`** (sidecar `.sha256` regenerated).
- Scope: the exclusion is A-joint-only. C-center (`PREREG_monodromy_center_glv_ratio_v1.md`)
  keeps anomalous primes in its band (its statistic is on the twisted sheaf `L_{χ₂(y)}⊗χ_a`
  eigenvalues, not the curve's own trace); its runner reports `Δ₃` with and without the
  anomalous primes {37, 61} per STAGING_NOTES, rather than excluding them.

**Grade of this note.** Selection-filter deviation, pre-run, no data seen. Does not move any
result grade.

---

## D2 (2026-08-21) — Semaev S₃ vanishing-iff: field-of-definition caveat (citation gate discharged)

**Gate.** The §-owed-gates `citation-verifier` on the Semaev S₃ definition ran 2026-08-21
(primary: Semaev, ePrint 2004/031, §2 Thm 1; corroboration: Kosters–Yeo, arXiv:1503.08001, Prop 2.1;
plus an explicit hand-expansion).

**Finding.**
- **Polynomial: SUPPORTS (exact).** `semaev_s3` coefficients match Semaev Thm 1 term-for-term
  (`x₃²`, `x₃¹`, `x₃⁰` all MATCH), cross-verified against the Kosters–Yeo symmetric form specialized to
  `(a₁..a₃,a₄,a₆)=(0,0,0,A,B)`. **No coefficient error.** (This is the slot the standing rule
  `feedback_verify_root_system_against_defining_polynomial` flags as historically mis-"corrected" from
  memory — the on-disk formula is correct; do NOT "fix" it.)
- **Vanishing-iff: SUPPORTS-WITH-CAVEAT.** Semaev's iff is over the ALGEBRAIC CLOSURE (`y_i∈K̄`, sum in
  `E(K̄)`). The infra comment previously wrote `(x_i,y_i)∈E(F_q)`, a narrowing that is sound *as A-joint
  applies it* (inputs are x-coords of genuine `E(F_q)` points ⇒ `y_i∈F_q`; PC-SEM builds `P₃` as a real
  curve point; 2-torsion `y_i=0` needs no special case) but overstates the field of definition in
  general.

**Fix applied.** `model_curve_infra_v1.py` §3 comment corrected to state `y_i∈K̄` (with the `F_q`
restatement noted as exact for genuine `E(F_q)` x-coords) and to add the hypothesis `char q ≠ 2,3`
(satisfied: `q>500` prime). No code / coefficient change. Statistic, null, power: unchanged.

## D3 (2026-08-21) — KS floor (§5): re-attribute to a Weil-type bound (citation gate discharged)

**Gate.** The §-owed-gates `citation-verifier` on the Kohel–Shparlinski single-character floor ran
2026-08-21 (primary on-disk `kohel_shparlinski_ants4_2000.pdf`, SHA-256 `645d9022…d8d2a`, re-verified).

**Finding: SUPPORTS-WITH-CAVEAT (attribution).**
- The `O(√q/N_ord)` magnitude and the "uniform, polylog-free" character are a faithful rendering of KS
  2000 eq. (3) / Cor 1 (`|S| ≤ 2·deg(f)·√q`; single-pole `(1+deg f)√q`); the `(1+log p)` belongs to
  KS Thm 2 (interval distribution), NOT the raw sum. Both confirm the earlier `AUDIT_ks_backstop` read.
- **But KS Thm 1's hypotheses are NOT satisfied by A-joint's features.** KS bounds `ω(P)·ψ(f(P))` with
  `ω` a POINT-GROUP character and `ψ` an ADDITIVE character composed with a rational `f` (proof via an
  Artin–Schreier cover). A-joint's `χ₃(x(P))` is a MULTIPLICATIVE (Kummer) character; `Ψ=χ₃(S₃(x₁,x₂,x₃))`
  is a 3-VARIABLE multiplicative sum. Their √q cancellation holds via the GENERAL Weil / Deligne bound
  for multiplicative (and multivariate) character sums — the same RH-for-function-fields machinery KS
  invoke, but NOT their stated single-character elliptic Theorem 1.

**Fix (to apply wherever §5's floor is cited / at any promotion).** State the benchmark as "a **Weil-type**
single-character floor of order `√q/N_ord`"; if KS is kept by name, restrict its citation to additive
`e_p(rational f)` readouts and attribute the `χ₃` / `χ₃(S₃)` features to the general Weil bound instead.
**Scope/power unchanged** — §5 invokes the floor only as a conservative lower benchmark the test cannot
reach ("detects only GROSS synergy," "floor uncrossed"), never as a closure, so the null's scope and
power are unaffected. The A-joint prereg body (frozen) is not rewritten; this deviation records the
narrowing to carry into the runner and any grade.

**Citation gate status: DISCHARGED** for both S₃ (SUPPORTS) and the floor (SUPPORTS-WITH-CAVEAT, Weil
re-attribution). No grade is licensed to move on KS "single-character elliptic theorem" strength for the
χ₃ features; the Weil bound is the correct authority.

---

## Second-read gate (2026-08-21): VERDICT = NOT RUNNABLE AS FROZEN — 4 defects

An independent `experiment-designer` second read (the owed gate) audited v1 + this DEVIATIONS + the
infra, verifying mechanical claims in code at q=541 (and 571/577/613). Items 1 (object-level), 2
(disjointness/tautology), 6 (exactness), 7 (falsification/scope) PASS. Four defects, each with a local
fix (none touches the object, the disjointness ruling, or the choice of statistic):

- **[BLOCKER, item 4] PC-SEM cannot fire.** Forcing `±P₁±P₂±P₃=O` makes `S₃≡0` ⇒ `Ψ=χ₃(0)=0` constant
  ⇒ `Î(Ψ;J|Φ)=0` (verified 2000/2000 plant sets, and `J` also constant since `d₁+d₂<N` never wraps). The
  VOID rule names "PC-LIN **or PC-SEM**", so a dead PC-SEM **spuriously VOIDs every arm before any data.**
  Also: `S₃=0 ⟺ ±d₁±d₂±d₃≡0 mod N` is *linear in the scalars* — PC-SEM's distinctiveness is the feature
  path `χ₃(S₃)`, not scalar nonlinearity. **Fix (v2):** PC-SEM = MIXTURE — inject the Semaev relation into
  a fraction `ρ` of sets, leave the rest generic, label tracks membership (so `Ψ=0` flags planted sets
  and correlates with `J`); or force `S₃` to a nonzero cubic class tracking `J`.
- **[item 3] Matched null is global, must be within-stratum.** For `Î(Ψ;J|Φ^pt)` the exact matched null
  permutes `Ψ` **within each `Φ^pt` stratum**; the v1 global permutation additionally destroys `Ψ↔Φ^pt`,
  testing `Ψ⊥(Φ,J)` not `Ψ⊥J|Φ`. Measured `I(Ψ;Φ^pt)=0.0083` bits > 0 at q=541 ⇒ the nulls provably
  differ, and the gap can be CM-arm-larger so it is NOT netted by the paired Δ (the "shuffle breaks a
  forced symmetry" class). **Fix (v2):** restricted within-`Φ^pt`-stratum permutation of `Ψ` (and the
  `L`-block for the omnibus).
- **[item 5] Power df wrong.** `Î_prim` conditions on `Φ^pt`, so `df = 4·s`, `s = #non-empty strata` (=27
  at m=3, N=5k), not 4. Correct `MI_min ≈ 7.9×10⁻³` @5k / `2.0×10⁻³` @20k — v1 understated ~3.3×.
  Permutation p-values unaffected; the scoped-null floor in §7/§9 is overstated. **Fix (v2):** recompute
  `MI_min` with `df = 4·s` (s exact per q).
- **[item 8 — FIXED HERE as D4, below] D1 anomalous-exclusion was CM-arm-only.**

## D4 (2026-08-21) — extend anomalous exclusion to the non-CM matching arm (item 8)

**Change.** D1 threaded `exclude_anomalous` through the j=0 selection only; the non-CM matcher
`select_jgen` did not exclude trace-1 curves. Ordinary anomalous curves (`N=q`) exist at schedule
primes (verified 541, 571, 577, 613) and are equally Smart-attackable, so the same per-point-recovery
confound can enter `Δ` from the non-CM side (e.g. where `N_CM ≈ q` and the anomalous non-CM curve wins
the order-match). **Fix applied:** `select_jgen(..., exclude_anomalous=True)` now skips `t==1`; the
A-joint runner passes `exclude_anomalous=True` on BOTH arms, and logs `trace` on the non-CM arm.
Selection-filter only; statistic/null/power untouched.

**Runner status: BLOCKED pending v2.** Items 3, 4, 5 are prereg-spec fixes (null definition, firing
control, power model) and require `PREREG_cm_jointset_excess_v2.md`, re-frozen and re-second-read before
any A-joint run. D4 (code) is applied; D2/D3 (citations) recorded. Nothing runs until v2 clears.
