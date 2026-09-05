# PREREG — A-joint-HO v1: higher-order / endomorphism-mixed / finer-label CM joint-set synergy

**File:** `PREREG_cm_jointset_higherorder_v1.md`  **Status: SPEC ONLY.**
**Extends (does not supersede):** `PREREG_cm_jointset_excess_v3.md` (A-joint, `[VERIFIED-scope — scoped
null]`, `RESULT_cm_jointset_excess_v3.md`). This document pre-registers the SIX channels the v3 RESULT
named verbatim under "What is NOT settled": `r≥4` Semaev; `m≥4`; other label moduli; GLV-mixed
`x([λ]P_i+[λ²]P_j)`; a coordinate-pair `(x,y)` statistic; a finer interval-position label.
**Runner (suggested):** `cm_jointset_ho_v1.py` (imports `model_curve_infra_v1.py` + one new exact
primitive `semaev_s4` — see §8). **Curve schedule REUSED UNCHANGED:** `schedules_v1/schedule_A_joint_v1.json`
(SHA `c533f669…`); the arm-parameter table is frozen in §6 and mirrored to
`schedules_v1/schedule_B_joint_v1.json` (SHA printed by the runner at freeze).

**Distinctness (non-negotiable).** This is the `m≥2` INDEPENDENT-SET line on ENUMERABLE MODEL CURVES.
It is NOT the separately-preregistered single-key N15 readout test
(`PREREG_n15_joint_readout_confinement_v1.md`); do not conflate. Every arm here reuses v3's object
(synergy `E`), matched within-stratum null, paired CM/non-CM contrast, exact arithmetic, and
firing-control discipline. Only the feature, label, conditioning stratum, and set size change per arm.

**Freeze protocol (inherited from v3).** The runner prints this file's SHA-256 into the RESULT and opens
`PREREG_cm_jointset_higherorder_v1_DEVIATIONS.md`; every post-freeze change is a disclosed deviation
appended there. A run that did not complete is a run that did not happen (not a run that passed).

---

## 0. SCOPE BANNER

Enumerable model curves `E:y²=x³+Ax+B` over small primes `F_q`, `q≡1 mod 3`, PRIME order `N`, `q≲2¹⁶`
(possibly one ladder rung further only if power permits, §5/§6). **`q=2²⁵⁶−2³²−977` is NOT enumerable;
nothing here transfers to secp256k1; this carries ZERO power against the real curve.** It measures a
MECHANISM — does HIGHER-ORDER (`r≥4`), LARGER-SET (`m≥4`), ENDOMORPHISM-MIXED (GLV), COORDINATE-PAIR,
OTHER-CHARACTER (`ℓ=2`, `μ₆`), or FINER-LABEL CM structure produce joint-set synergy at model scale —
NEVER the real object. **No ECDLP / extraction / security claim.**

Two matched arms per `q`, both from `schedule_A_joint_v1.json`: **CM** (`j=0`, `y²=x³+B`, `Z[ω]`) and
**non-CM** (ordinary, `j∉{0,1728}`, `|t²−4q|≥⌊√q⌋`), **both excluding anomalous (trace-1, `N=q`)
curves** (D4 — Smart-attackable curves must not enter the contrast from either side). The object is a
JOINT property of a SET, never a per-point marginal. **A null on any arm is a BOUNDED MAGNITUDE with
stated power and scope — never a closure.** (Burden-of-proof rule, project CLAUDE.md: a dismissal clears
the same bar as a PROVED claim: object + class-of-observable + power + scope, or it is an overclaim. No
dismissal vocabulary in any scoped-null verdict.)

## 1. OBJECT (per channel)

Hypothesis (A-joint-HO): for a SET of `m` targets `d_i` drawn INDEPENDENTLY uniform in known intervals
`I_i=[2^{b−1},2^b)`, a HIGHER-ORDER / ENDOMORPHISM-MIXED / FINER cross-target public function carries
SYNERGISTIC information about a joint label EXCEEDING what per-point readouts carry, and this excess is
CM-specific (present on CM, absent on matched non-CM).

**Synergy `E` (v3 definition, re-used exactly).** Because the `d_i` are INDEPENDENT, per-point-only
features give `MI = Σ_i MI(Φ_i^pt ; T_i)` EXACTLY. Therefore, for any cross-feature `F` and label `T`
conditioned on the per-point stratum `Φ^pt`, `E = Î(F ; T | Φ^pt)` is precisely the EXCESS the cross
feature adds over the per-point marginals. This holds channel-by-channel provided `Φ^pt` conditions on
**all** per-point information the feature `F` can carry marginally — see the per-arm stratum in §2/§3;
this is the load-bearing anti-tautology requirement re-checked per arm in §2R.

**Disjointness / forcedness ruling (v3, re-checked per new feature in §2R).** Features are field-side
`F_q` functions; labels are scalar-ring functions of the `d_i`; the only bridge is the DLP; no feature
is a difference/component sharing construction with the target (not the `r=v−w` artifact, not the
linear-relation check). `χ₃(βx)=1+χ₃(x)` and its analogues are conditioned out by `Φ^pt`.

## 2. STATISTIC (one PRIMARY per arm; conditional-MI synergy; Miller–Madow)

All arms use v3's estimator: `Î(F ; T | Φ^pt)` (Miller–Madow corrected bits), ranked by the exact
integer within-stratum permutation count of §3. The float `log₂` inside MI is a monotone scalar ranked
against the exact integer null (carve-out, §8). Every `Î,Δ,p` carries scope `(arm,q,N_CM,N_non,t_non,
|I|,m,r,ℓ,k,N,s,MI_min)`.

**PRIMARY FAMILY (4 arms, Holm-controlled at family `α=0.05`, §5) — the CM-mechanism headline.**

- **P1 — S4 (`r=4` Semaev; `m=4`).** `Ψ₄ = χ₃(S₄(x₁,x₂,x₃,x₄))`; `J = (Σd_i) mod 3`;
  condition `Φ^pt = (χ₃(x₁),…,χ₃(x₄)) ∈ {0,1,2}⁴` (81 strata). `Î_P1 = Î(Ψ₄ ; J | Φ^pt)`.
- **P2 — C4 (`m=4` additive combo).** `L_sum = (Σ_{i<j} χ₃(x(P_i+P_j))) mod 3` over the 6 pairs;
  `J = (Σd_i) mod 3`; same `Φ^pt` (81 strata). The `m=4` analogue of v3's omnibus guard.
- **P3 — GLV-mixed (`m=3`).** `G = (Σ_{i<j}[χ₃(x([λ]P_i+[λ²]P_j)) + χ₃(x([λ]P_j+[λ²]P_i))]) mod 3`;
  `J = (Σd_i) mod 3`; condition `Φ^pt = (χ₃(x₁),χ₃(x₂),χ₃(x₃))` (27 strata). Uses the schedule's
  `beta,lam`. `[λ]P=(β·x,y)`, `[λ²]P=(β²·x,y)` exactly.
- **P4 — μ₂ Semaev (other label modulus `ℓ=2`; `m=3`).** `Ψ₂ = χ₂(S₃(x₁,x₂,x₃))` (Legendre);
  `J₂ = (Σd_i) mod 2`; condition `Φ₂^pt = (χ₂(x₁),χ₂(x₂),χ₂(x₃)) ∈ {−1,0,1}³` (≤8 strata).
  `Î_P4 = Î(Ψ₂ ; J₂ | Φ₂^pt)`. This is the complementary CM character (`μ₆ = μ₂×μ₃`; `μ₃` = v3).

**SECONDARY / GUARD ARMS (own ledger each, NOT in the Holm family; mirror v3's omnibus+interval
treatment).** Reported with their own null and own power; a firing names a next probe, never the
headline.

- **S-INT — finer interval label (`m=3`).** Divide `I_i` into `2^k` equal blocks; `pos_k(d_i)∈{0..2^k−1}`;
  `J'_k = (Σ pos_k(d_i)) mod 2^k`. `Ψ = χ₃(S₃)`; condition `Φ^pt(3)` (27 strata). PRIMARY-of-arm at
  `k=2` (N=5k); EXPLORATORY at `k=3` (N=20k).
- **S-XY — coordinate-pair `(x,y)` (`m=3`, EXPLORATORY, estimability frontier).**
  `M = ((Σ_{i<j} χ₃(x(P_i+P_j))) mod 3 , (Σ_{i<j} χ₂(y(P_i+P_j))) mod 2) ∈ Z₃×Z₂` (6 symbols);
  `J = (Σd_i) mod 3`; condition on the FULL per-point `(x,y)` symbol
  `Φ^pt_{xy} = ((χ₃(x_i),χ₂(y_i)))_i ∈ (Z₃×{−1,0,1})³` (≤216 strata). N=20k. See §5 for why the full
  `(x,y)` stratum is required (partial conditioning would admit a per-point `y`-marginal as spurious
  synergy). A separate per-point diagnostic `Î(χ₂(y_i) ; d_i mod 2)` is reported to SURFACE (not bury)
  any per-point `y`-leak.
- **S-C5 — `m=5` combo (EXPLORATORY, estimability frontier).** `L_sum` over the 10 pairs mod 3 vs
  `J = (Σd_i) mod 3`; condition `Φ^pt(5)` (243 strata). N=20k.

**Estimability sizing (the v3 finding drives this: v2's 27×27|27 omnibus was IDENTICALLY 0 at feasible
N because every joint cell had count ≤1).** Each table is sized so mean count/cell ≥ ~5:

| arm | conditioning strata | feat×label cells/stratum | N | ~count/cell | status |
|---|---|---|---|---|---|
| v3 primary (anchor) | 3³=27 | 3×3=9 | 5k | ~20 | baseline OK |
| P1 S4 (m=4) | 3⁴=81 | 9 | 20k | ~27 | OK |
| P2 C4 (m=4) | 81 | 9 | 20k | ~27 | OK |
| P3 GLV (m=3) | 27 | 9 | 5k / 20k | ~20 / ~82 | OK |
| P4 μ₂ (m=3) | 2³=8 | 3×2=6 | 5k | ~104 | OK |
| S-INT k=2 (m=3) | 27 | 3×4=12 | 5k | ~15 | OK |
| S-INT k=3 (m=3) | 27 | 3×8=24 | 20k | ~30 | OK (needs 20k) |
| S-XY (m=3) | 6³=216 | 6×3=18 | 20k | ~5 | FRONTIER (VOID-gated) |
| S-C5 (m=5) | 3⁵=243 | 9 | 20k | ~9 | FRONTIER (VOID-gated) |

**Explicitly out of scope of this prereg (SPLIT, materially different instrument):**
- **`r=5` Semaev (`S₅`)** — requires the 5th summation polynomial (a resultant chain with an
  extraneous-factor problem) and its own exactness + citation gate; it does NOT share the v3 harness
  as a drop-in. → **SPLIT to its own prereg.** (`m=5` is covered here only via the combo channel S-C5.)
- **Joint `μ₆` label** (`(χ₃(S₃),χ₂(S₃))` vs `Σd mod 6`) — its correct matched null conditions on the
  216-stratum `μ₆` per-point symbol, same estimability wall as S-XY; deferred as EXPLORATORY only if
  S-XY's frontier proves runnable; otherwise SPLIT.

## 2R. ANTI-TAUTOLOGY (re-derived per NEW feature; GLV and coordinate-pair explicitly)

- **P1/P2 (`m=4` Semaev/combo).** `S₄=0 ⇔ ∃ signs ±P₁±P₂±P₃±P₄=O` — a genuine 4-point relation, a
  CROSS function of four x-coords, not a per-point function. `L_sum` over 6 pairs is not forced by
  `Φ^pt` (v3 verified the `m=3` analogue: `Ψ==L_sum` on only 33.9%, `L_sum` varies in 27/27 strata;
  holds a fortiori for `m=4`). **RULE IN.**
- **P3 (GLV-mixed) — the at-risk case, ruled explicitly.** `[λ]` acts as `(x,y)↦(βx,y)`, so the
  PER-POINT twisted readout `χ₃(x([λ]P_i)) = χ₃(β)+χ₃(x_i)` is FORCED by `Φ^pt` (a constant shift of the
  stratum) — **it is EXCLUDED** (per-point, zero synergy by construction). The registered feature is the
  CROSS form only. Identity: `[λ]P_i+[λ²]P_j = [λ](P_i+[λ]P_j)`, so
  `χ₃(x([λ]P_i+[λ²]P_j)) = χ₃(β) + χ₃(x(P_i+[λ]P_j)) (mod 3)`. `P_i+[λ]P_j` is a genuinely NEW group
  element (≠ `P_i+P_j`, ≠ any per-point image); no character identity links `χ₃(x(P_i+[λ]P_j))` to
  `χ₃(x(P_i+P_j))` or to `Φ^pt`. Bridge remains the DLP (`d_i ↦ [d_i]G ↦ [λd_i+λ²d_j]G ↦ x ↦ χ₃`), no
  shared construction beyond `(E,q,set)`. **RULE IN** as a distinct channel. Non-degeneracy guard:
  twisted sum ≠ O on ≥99% (§4).
- **S-XY (coordinate-pair) — the second at-risk case, ruled explicitly.** `y(P_i+P_j)` and its Legendre
  `χ₂` are CROSS functions (via the addition formula), not per-point. The risk is not shared
  construction but a per-point `y`-marginal masquerading as synergy: if `χ₂(y_i)` correlated with `d_i`,
  a null conditioning only on `χ₃(x_i)` would pass that through as false "synergy." **Mitigation
  (registered):** condition on the FULL per-point `(χ₃(x_i),χ₂(y_i))` symbol (216 strata), which removes
  every per-point `(x,y)` marginal; AND report the standalone per-point diagnostic
  `Î(χ₂(y_i);d_i mod 2)` so any real per-point `y`-leak is SURFACED as its own (per-point) finding, not
  absorbed. **RULE IN** as EXPLORATORY under full `(x,y)` conditioning.
- **P4 (μ₂), S-INT (finer interval).** `χ₂(S₃)` is a field-side character of the same object as `χ₃(S₃)`;
  `J₂,J'_k` are scalar-side functions of the `d_i`; bridge = DLP; no shared construction. **RULE IN.**

## 3. MATCHED CONTROL (within-stratum permutation, per v3; stratum named per arm)

Each arm's null **permutes the feature `F` WITHIN each conditioning stratum**, holding the stratum and
the labels fixed — preserving `p(F | stratum)` in every stratum and destroying ONLY the within-stratum
`F↔label` coupling (the exact matched null for conditional MI; NOT a global permutation). The
conditioning stratum per arm:

| arm | stratum permuted within | why this stratum (removes all per-point info `F` can carry) |
|---|---|---|
| P1 S4 | `Φ^pt(4)=(χ₃x_i)_{i≤4}` | `S₄` is a fn of the four x-coords; `χ₃x_i` is the per-point x-readout |
| P2 C4 | `Φ^pt(4)` | combos are x-coord cross fns; per-point x-readout is `χ₃x_i` |
| P3 GLV | `Φ^pt(3)=(χ₃x_i)` | per-point GLV readout `= χ₃(β)+χ₃x_i`, a fn of `Φ^pt(3)` (see §2R) |
| P4 μ₂ | `Φ₂^pt(3)=(χ₂x_i)` | `μ₂` feature/label ⇒ `μ₂` per-point x-readout |
| S-INT | `Φ^pt(3)` | feature is `χ₃(S₃)`; per-point x-readout is `χ₃x_i` |
| S-XY | `Φ^pt_{xy}(3)=((χ₃x_i,χ₂y_i))` | feature carries per-point `(x,y)` info; MUST condition on both |
| S-C5 | `Φ^pt(5)` | combos over 5 points; per-point x-readout `χ₃x_i` |

`≥10⁴` restricted permutations; exact integer count p-value `p = (ge+1)/(R+1)` (Fraction). `Δ`: each
arm vs its OWN within-stratum null; paired CM/non-CM sign across the frozen schedule. The permutation
p is exact and VALID even where cells are sparse (sparsity costs power, not validity — §5).

## 4. PLANTED / FIRING CONTROL (one plant per arm that MUST fire; monotone; VOID rule)

All plants inject ONLY into the conditioned-in cross channel, mirror v3's PC-SEM/PC-COMBO (mixture
plant using a REAL INDEPENDENT resampled point, never a degenerate linear collapse), and are required
to fire `p<0.01` at `ρ=0.30`, monotone across `ρ∈{0,0.15,0.30,0.60}`, with a non-degeneracy guard.
**If an arm's required plant does not fire at `(q,N)`, that arm is VOID at that scale (no null
claimed); a tripped non-degeneracy guard ⇒ STOP-fix (mis-built plant), distinct from VOID.**

- **PC-S4 (P1).** Resample `d₄` until `χ₃(S₄)==(Σd) mod 3`, REAL independent `P₄`. Guard:
  `#distinct(Ψ₄_planted)≥2`, `S₄≠0` on ≥99% planted.
- **PC-C4 (P2).** Resample `d₄` until `L_sum==(Σd) mod 3`, REAL independent `P₄` (NOT
  `−(P₁+P₂+P₃)`, which would collapse combos into `Φ^pt`). Guard: `#distinct(L_sum_planted)≥2`.
- **PC-GLV (P3).** Resample `d₃` until `G==(Σd) mod 3`, REAL independent `P₃`. Guard:
  `#distinct(G_planted)≥2`; twisted sums `[λ]P_i+[λ²]P_j ≠ O` on ≥99% planted.
- **PC-L2 (P4).** Resample `d₃` until `χ₂(S₃)==(Σd) mod 2`. Guard: `#distinct(Ψ₂_planted)≥2`,
  `S₃≠0` on ≥99% planted.
- **PC-INT (S-INT).** Resample `d₃`'s block position until `(Σ pos_k)==J'_k`. Guard:
  `#distinct(J'_k over planted)≥2`.
- **PC-XY (S-XY).** Resample `d₃` until `M==(J , 0)` (target the `Z₃×Z₂` symbol). Guard:
  `#distinct(M_planted)≥2`; if it does not fire at N=20k the arm is VOID (frontier-limited).
- **PC-C5 (S-C5).** Resample `d₅` until `L_sum==(Σd) mod 3`, REAL independent `P₅`. Guard:
  `#distinct(L_sum_planted)≥2`; VOID if unfired at N=20k.
- **PC-GRADE (resolution floor — per arm, unchanged from v3).** `F_plant = label` w.p. `mix`, else
  uniform; monotone firing; the `MI_min` rung must fire ≥80%. Calibrates that the estimator resolves an
  effect of size `MI_min` at the arm's `(N, table)`.
- **PC-nonCM (CM-specificity control).** The matched non-CM arm is the control for CM-specificity of
  every `Δ`.

## 5. POWER

**Model (v3, extended).** For a `(a×b | s)` conditional table, `df = (a−1)(b−1)·s` and
`MI_min(df,N) = λ₈₀(df) / (2 N ln2)` bits, where `λ₈₀(df)` is the noncentral-χ² noncentrality for 80%
power at `α=0.05` — the SAME routine v3 used (anchor: `λ₈₀(108)=54.9 ⇒ MI_min=7.9×10⁻³` @5k,
`2.0×10⁻³` @20k). The runner recomputes `λ₈₀(df)` exactly at the frozen config; the table below uses a
LINEAR planning scaling `λ₈₀(df)≈54.9·df/108`, which OVERSTATES `λ₈₀` for large `df` (true growth is
sub-linear ~`df + c√df`) and therefore reports a CONSERVATIVE (pessimistic) `MI_min` — true power is at
least this good.

| arm | df | N | MI_min (bits, conservative) | notes |
|---|---|---|---|---|
| P1 S4 | 4·81=324 | 20k | ~5.9×10⁻³ | detects gross synergy only |
| P2 C4 | 324 | 20k | ~5.9×10⁻³ | guard, m=4 |
| P3 GLV | 108 | 5k / 20k | 7.9×10⁻³ / 2.0×10⁻³ | same floor form as v3 |
| P4 μ₂ | 2·8=16 | 5k | ~1.2×10⁻³ | highest power of the family |
| S-INT k=2 | 6·27=162 | 5k | ~1.2×10⁻² | |
| S-INT k=3 | 14·27=378 | 20k | ~6.9×10⁻³ | |
| S-XY | 10·216=2160 | 20k | ~4.0×10⁻² | POWER+ESTIMABILITY frontier ⇒ EXPLORATORY |
| S-C5 | 4·243=972 | 20k | ~1.8×10⁻² | frontier ⇒ EXPLORATORY |

**Weil-type multiplicative-character floor.** The relevant single-character floor is a **Weil/Deligne
multiplicative-character bound** `∼ (deg f)·√q / N_ord`, NOT the KS-2000 additive `e_p(rational f)`
theorem (D3). For `r≥4` the feature is `χ_ℓ` of a HIGHER-DEGREE polynomial (`S₄`; the pair-combo of
`x(P_i+P_j)`), so `deg f` grows with `r`; the runner logs `deg f`, `√q/N_ord`, and the resulting floor
per arm. **v3 finding (carried):** the CM arm was FLOOR-LIMITED — raw `Î` shrank with `N`
(0.033→0.0075), the fingerprint of plug-in bias absorbed by the matched null, not signal; the same
diagnostic (`Î` shrinking with `N` toward the null mean) is reported per arm here.

**Estimability limits (how far `m`, `r`, `k`, `ℓ` reach at feasible `N`).** The wall is the `3^m`
(or `6^m` for `(x,y)`) conditioning-stratum count, not the feature. Full per-point conditioning is
comfortable to `m=4` at N=20k (81 strata, ~27/cell) and BORDERLINE at `m=5` (243 strata, ~9/cell —
EXPLORATORY, VOID-gated). The coordinate-pair / joint-`μ₆` symbol hits `6^m` and is a frontier already
at `m=3` (216 strata, ~5/cell at N=20k). `k` (interval resolution) reaches `k=2` at N=5k, `k=3` at
N=20k; `k≥4` is unestimable at feasible `N`. A run that finds a plant unable to fire (PC-…) at the
planned `(q,N)` returns VOID for that arm and reports the `N` that would be needed.

## 6. SCOPE / PARAMETERS

- **Curve schedule REUSED UNCHANGED:** `schedules_v1/schedule_A_joint_v1.json` (SHA `c533f669…`):
  discovery `{541,571,577}`; confirmation/OOS `{2029,2053,2089}`; ladder `{1033,4111,16417,65539}`.
  CM = `j=0` B-witness prime order, `q≡1 mod 3`, `trace≠1`; non-CM = ordinary `j∉{0,1728}`,
  `|t²−4q|≥⌊√q⌋`, `t≠1`, minimize `|N_non−N_CM|` (ladder uses the D-LADDER bounded-random matcher, exact
  order match, `seed=q`). Generator = the order-`L` point of smallest x, smaller y. `beta,lam` for the
  GLV arm are taken from the schedule (verified `[λ]G=(β·Gx,Gy)` in infra selftest).
- **Arm-parameter table (FROZEN here; mirrored to `schedules_v1/schedule_B_joint_v1.json`, SHA printed
  by the runner at freeze):** P1 `m=4,r=4,ℓ=3`; P2 `m=4,ℓ=3`; P3 `m=3,ℓ=3` (GLV); P4 `m=3,ℓ=2`;
  S-INT `m=3,ℓ=3,k∈{2,3}`; S-XY `m=3`; S-C5 `m=5,ℓ=3`.
- `b = ⌊log₂ q⌋ − 2` (interval `I_i=[2^{b−1},2^b)`; assert `2^b < L`). `N` (sample size): discovery
  5,000; confirmation/OOS 20,000; frontier arms (S-XY, S-C5, S-INT k=3) 20,000. `seed = 20260821`;
  `#perm ≥ 10⁴`. Anomalous curves excluded BOTH arms.
- One ladder rung beyond `2¹⁶` MAY be added ONLY if the frontier arms' plants fire and per-prime cost
  stays tractable; adding it is a disclosed deviation, not a silent extension.

## 7. FALSIFICATION (per-arm, pre-committed)

For each PRIMARY arm `X ∈ {P1,P2,P3,P4}`:
- **RETAINED ⇔** its plant(s) + PC-GRADE fired; CM within-stratum `p≤0.01` REPRODUCIBLY (≥ half of
  discovery+confirmation primes AND holds OOS); `Δ_X>0` beyond the paired null across the schedule; AND
  the arm's Fisher-combined-across-primes p survives Holm–Bonferroni at family `α=0.05` across the 4
  primary arms.
- **SCOPED NULL ⇔** all its plants fired; CM `p` within the null across the whole schedule; `Δ_X≤0` ⇒
  `|Δ_X|<MI_min(N)` reported WITH object + class-of-observable + power + scope + untested-channel list.
  Never "no structure"; a magnitude is a size, not an absence (Weil floor uncrossed).
- **OFF-TARGET ⇔** the CM primary is null but a SECONDARY/GUARD arm fires `p≤0.01` (reproducibly) ⇒
  name the channel (combo / interval / coordinate-pair) as the next probe; not the headline.
- **VOID ⇔** the arm's required plant did not fire at `(q,N)` ⇒ instrument dead at scale; bank NO null;
  report the power ceiling and the `N` needed.

For SECONDARY/GUARD arms `{S-INT, S-XY, S-C5}`: same four outcomes on their OWN ledger; a firing is a
NAMED next probe, never the CM headline; a null is a bounded magnitude with its own (possibly weak,
frontier) power number stated.

**Family-abandonment (whole prereg):** if EVERY primary arm returns SCOPED NULL with all plants fired
and flat `Δ` across the schedule, conclude: no CM-specific joint-set synergy in the
`{S₄-μ₃, m=4-combo, GLV-mixed-μ₃, μ₂-Semaev}` channels at `q≲2¹⁶`, at the tabulated power — a bounded
magnitude, NOT a closure; the SPLIT channels (`r=5`, joint-`μ₆`) and the frontier arms remain untested.

## 8. EXACTNESS (no-float compliance)

Signal path is int/GF(q) throughout: curve arithmetic, x- and y-coords, `χ₂` (Legendre), `χ₃`, `S₃`,
`S₄`, the GLV twisted points `[λ]P=(β·x,y)`, all combos, all labels, and every permutation COUNT
(Fraction). Banned ops (`/`, `float()`, `**0.5`, `round(ratio)`, `math.*/np.*` on curve/point/feature
values) do not appear in the signal path. Ratio comparisons use integer cross-product.

- **`S₄` exactness.** `S₄` is built by exact GF(q) resultant of two `S₃` quadratics-in-`X`
  (`S₄(x₁,x₂,x₃,x₄) = Res_X(S₃(x₁,x₂,X), S₃(x₃,x₄,X))`); the resultant may carry an EXTRANEOUS FACTOR —
  the runner divides it out per Kosters–Yeo and asserts `S₄=0 ⇔ ∃ signs ±P₁±P₂±P₃±P₄=O` on a KAT (true
  4-point relations vanish; random 4-tuples are generic-nonzero), mirroring the infra `S₃` selftest.
  This new primitive + its identity is **citation-verifier owed** (§10) before any P1 `Δ` promotes.
- **Float carve-out (unchanged from v3).** Float appears ONLY as the `log₂` inside the MI estimator,
  used as a monotone quantity RANKED against the exact integer within-stratum permutation count; the
  verdict p-value is an exact Fraction of integer counts. Statistic lines carry `# noqa: float`.
- **`check_no_float.sh` MUST exit 0** on every new/changed signal-path file (`cm_jointset_ho_v1.py`
  and any new `semaev_s4` primitive) before any arm is run or any result reported.

## 9. PRE-COMMITMENT TABLE (one row per arm per branch)

| arm (channel) | outcome | trigger | conclusion | grade |
|---|---|---|---|---|
| **P1 S4** (r=4) | CM synergy | PCs fired; CM `p≤0.01` reproducible; `Δ>0`; survives Holm | CM produces `S₄`-`μ₃` joint synergy absent on non-CM. NEXT: which stratum; `r=5` (SPLIT). | EMPIRICAL (mechanism, model-scale) |
| P1 S4 | scoped null | PCs fired; within null; `Δ≤0` across schedule | `|Δ|<MI_min` (~5.9e-3 @20k): no CM-specific `S₄`-`μ₃` synergy at `q≲2¹⁶`, `m=4`. Bounded magnitude + power + scope; untested: `r=5`, joint-`μ₆`. | VERIFIED-scope (scoped null) |
| P1 S4 | void | PC-S4 did not fire | instrument dead at scale; report `N` needed. | VOID |
| **P2 C4** (m=4 combo) | fires / null / void | as P1 with `L_sum(6 pairs)` | m=4 additive-combo channel named as probe / bounded null / void. | EMPIRICAL / VERIFIED-scope / VOID |
| **P3 GLV** | CM synergy | PCs fired; CM `p≤0.01` reproducible; `Δ>0`; Holm | endomorphism-mixed CM structure adds joint synergy absent on non-CM. NEXT: twisted-label variant. | EMPIRICAL (mechanism) |
| P3 GLV | scoped null | PCs fired; within null; `Δ≤0` | `|Δ|<MI_min` (7.9e-3 @5k): no CM-specific GLV-mixed synergy, `q≲2¹⁶`, `m=3`. Bounded + power + scope. | VERIFIED-scope |
| P3 GLV | void | PC-GLV did not fire / guard tripped | dead at scale / STOP-fix. | VOID / STOP-fix |
| **P4 μ₂** (ℓ=2) | CM synergy / null / void | as P3 with `χ₂(S₃)`, `J₂` | `μ₂` (complementary CM char) synergy / bounded null (~1.2e-3 @5k) / void. | EMPIRICAL / VERIFIED-scope / VOID |
| generic (any primary) | CM-independent | `Î` fires BOTH arms; `Δ≈0` | generic to `d↦point`, not CM-specific. | EMPIRICAL (generic) |
| **S-INT** (finer interval) | off-target / null / void | own ledger, k=2 then k=3 | interval channel named as probe / bounded null / void. | EMPIRICAL (off-target) / VERIFIED-scope / VOID |
| **S-XY** (coord-pair) | lead / null / void | own ledger, N=20k, full `(x,y)` cond; per-point `y`-diagnostic reported | coordinate-pair lead named / bounded frontier null (~4.0e-2) / VOID if PC-XY unfired. | EMPIRICAL (exploratory) / VERIFIED-scope (frontier) / VOID |
| **S-C5** (m=5 combo) | lead / null / void | own ledger, N=20k | m=5 combo lead / bounded frontier null (~1.8e-2) / VOID. | EMPIRICAL (exploratory) / VERIFIED-scope (frontier) / VOID |

Every scoped-null row carries the symmetric burden (object / class-of-observable / power / scope). No
dismissal vocabulary anywhere. Abstaining on a frontier arm (VOID) is NOT closing that channel.

## 10. OWED GATES

- **Second independent `experiment-designer` read of THIS prereg: OWED** before any `Δ` promotes
  (isolation is load-bearing on the FRAME layers — object/disjointness, matched-control adequacy for
  the new strata, scope, falsification, pre-commitment; a same-context self-audit cannot discharge
  these).
- **`citation-verifier` OWED** for: (a) the `S₄` summation-polynomial construction + extraneous-factor
  handling + the `S₄=0 ⇔ ±P₁±P₂±P₃±P₄=O` identity (Semaev 2004 / Kosters–Yeo), before any P1 `Δ`
  promotes; (b) any specific higher-degree Weil/Deligne multiplicative-character floor cited in §5.
- **`compile-diff` OWED** if this prereg or its result is folded into a master/handover.
- Provisional-run rule (CLAUDE.md §2a): if a gate is UNAVAILABLE, tag every output
  `[PROVISIONAL — <gate> unavailable]` in the grade slot, attach a self-audit naming its uncovered
  FRAME sections, record the gate as owed; NO grade promotion until it clears.

---

**Provenance.** Pre-registered via the `experiment-designer` gate (context-isolated; baseline v3 spec +
result + the named untested-channel list + criteria only, no session narrative, no expected answer),
2026-08-25. Extends `PREREG_cm_jointset_excess_v3.md`; reuses `model_curve_infra_v1.py`,
`cm_jointset_excess_v3.py`, `schedules_v1/schedule_A_joint_v1.json`. GLV cross-feature algebra
(`[λ]P_i+[λ²]P_j=[λ](P_i+[λ]P_j)`) and the sublinear-λ₈₀ (conservative power) claim independently
re-derived in the main session before persistence. This is SPEC ONLY — no runner has executed.
