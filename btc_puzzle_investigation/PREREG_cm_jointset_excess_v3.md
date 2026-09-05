# PREREG — A-joint v3: CM-structured JOINT-SET synergy excess (estimable omnibus)

**File:** `PREREG_cm_jointset_excess_v3.md`  **Date frozen:** 2026-08-22
**Supersedes:** `PREREG_cm_jointset_excess_v2.md` (its second-read passed on paper, but the RUN found
its omnibus ill-posed). v3 changes ONLY the omnibus guard and its firing control; the object,
disjointness ruling, primary statistic `Î_prim`, matched null, PC-SEM/PC-GRADE, power, exactness, and
selection are UNCHANGED from v2 (all passed the v2 second-read and the run). **Status: SPEC ONLY.**
Runner: `cm_jointset_excess_v3.py` (imports `model_curve_infra_v1.py`).

**Change log v2→v3 (traced to the v2 RUN finding, `log_ajoint_v2_*`):**
- **[RUN] §2 omnibus:** v2's `Î_omni = Î((L₁₂,L₁₃,L₂₃);(T₁,T₂,T₃)|Φ^pt)` is a 27×27 table over 27
  strata (19,683 cells); at feasible N every joint cell has count ≤1, so the permutation statistic is
  identically 0 (`mi=0.0000, p=1.0` at N=5,000, R=10⁴ — verified). Replaced by the **estimable 3×3
  guard** `Î_omni = Î(L_sum ; J | Φ^pt)`, `L_sum = (L₁₂+L₁₃+L₂₃) mod 3`, `L_{ij}=χ₃(x(P_i+P_j))`,
  `J=(d₁+d₂+d₃) mod 3` — 243 cells, ~20/cell at N=5,000.
- **[RUN] §4 PC-LIN → PC-COMBO:** v2's PC-LIN (`d₃=−(d₁+d₂)`) is DEGENERATE for the combo channel too:
  it forces `P₃=−(P₁+P₂)`, so every `x(P_i+P_j)` collapses to a per-point coordinate and `L_sum`
  becomes a function of `Φ^pt` ⇒ `Î(L_sum;J|Φ^pt)=0`. Replaced by **PC-COMBO**, a non-degenerate mixture
  plant (resample `d₃` until `L_sum==J`, using a REAL INDEPENDENT `P₃`), which fires the coarsened
  omnibus (verified: p=0.0020 at ρ≥0.3, monotone, `distinct_lsum=3`).
- **[RUN] §7 VOID rule:** "PC-LIN or PC-SEM" → "**PC-COMBO or PC-SEM**".

**Freeze protocol:** runner prints this file's SHA-256 into the RESULT and opens
`PREREG_cm_jointset_excess_v3_DEVIATIONS.md`; post-freeze changes are disclosed deviations.

---

## 0. SCOPE BANNER (unchanged from v2)

Enumerable model curves `E:y²=x³+Ax+B` over small prime `F_q`, `q≡1 mod 3`, PRIME order `N`.
`q=2²⁵⁶−2³²−977` is NOT enumerable; nothing transfers to secp256k1; `q≲2¹⁶` carries zero power against
the real curve. Measures a MECHANISM (does CM structure produce joint-set synergy at model scale), never
the real object. No ECDLP/extraction/security claim. Two matched arms per `q`: CM (`j=0`, `y²=x³+B`,
`Z[ω]`) and non-CM (ordinary, `j∉{0,1728}`, `|D|≥⌊√q⌋`), **both excluding anomalous (trace-1) curves**
(D4). The object is a JOINT property of a SET, never a per-point marginal.

## 1. OBJECT (unchanged from v2 — passed)

Hypothesis (A-joint): for a SET of `m=3` targets `d_i` drawn INDEPENDENTLY uniform in known intervals
`I_i=[2^{b−1},2^b)`, the CROSS-target public functions carry SYNERGISTIC information about a joint
label EXCEEDING what per-point readouts carry, and this excess is CM-specific (present on CM, absent on
matched non-CM). Object = synergy `E`: because the `d_i` are independent, per-point-only features give
`MI = Σ_i MI(Φ_i^pt;T_i)` exactly, so `E` is the excess the cross features add.
Disjointness/tautology ruling and forcedness ruling: unchanged from v2 (features are field-side `F_q`
functions; labels are scalar-ring; bridge = DLP; not the `r=v−w` artifact; not the linear-relation
check; `χ₃(βx)=1+χ₃(x)` conditioned out).

## 2. STATISTIC

**Primary (unchanged from v2).** `Φ^pt=(χ₃(x₁),χ₃(x₂),χ₃(x₃))∈{0,1,2}³` (27 strata);
`Ψ=χ₃(S₃(x₁,x₂,x₃))∈{0,1,2}`; `J=(d₁+d₂+d₃) mod 3`.
`Î_prim(arm) = Î(Ψ;J|Φ^pt)` (Miller–Madow), the chain-rule synergy excess.
**Verdict:** `Δ = Î_prim(CM) − Î_prim(non-CM)`; significance from the per-arm within-stratum null (§3),
direction from the paired CM/non-CM sign across the frozen schedule.

**CO-PRIMARY OMNIBUS (COARSENED — v3).** `Î_omni(arm) = Î(L_sum ; J | Φ^pt)`,
`L_sum = (L₁₂+L₁₃+L₂₃) mod 3`, `L_{ij}=χ₃(x(P_i+P_j))`. A 3×3 table conditioned on `Φ^pt` (243 cells,
estimable). It is a co-primary GUARD, never the headline: a primary null is reported as "no synergy in
the *Semaev-μ₃* channel," and an omnibus-only firing names the *additive combo* channel as the next
probe. (v2's full-tuple omnibus was unestimable at feasible N; this coarsening restores a working guard.)

**SECONDARY LABEL (unchanged).** interval-position `J'=(Σ block(d_i)) mod 2`; own null, own ledger.

Float `log₂` inside MI is a monotone scalar ranked against the §3 exact integer within-stratum
permutation count.

## 2R. ANTI-TAUTOLOGY (unchanged from v2 — passed)

Prediction and measurement paths share no intermediate beyond `(E,q,the set)`; feature→label is the DLP;
no feature is a difference/component sharing construction with the target.

## 3. MATCHED CONTROL (unchanged from v2 — within-stratum permutation)

Primary/omnibus/secondary nulls each **permute the feature WITHIN each `Φ^pt` stratum**, holding `Φ^pt`
and the labels fixed — preserving `p(feature|Φ^pt=u)` in every stratum and destroying only the
within-stratum feature↔label coupling (the exact matched null for conditional MI; NOT a global
permutation). `≥10⁴` restricted permutations; exact integer count p-value. `Δ`: each arm vs its own
within-stratum null; paired CM/non-CM sign across the schedule.

## 4. PLANTED CONTROL (PC-COMBO replaces PC-LIN)

All plants inject into the conditioned-in cross channel. **ALL required plants must fire or the arm is
VOID.**

- **PC-SEM (Semaev-feature plant — MUST fire; unchanged from v2).** Planted fraction `ρ=0.30`: resample
  `d₃` until `χ₃(S₃)==(d₁+d₂+d₃) mod 3`, REAL point `P₃` (S₃ generically ≠0, ~3 draws). Require `Î_prim`
  fires exact perm `p<0.01` at ρ=0.30, monotone across `ρ∈{0,0.15,0.30,0.60}`. Non-degeneracy guard:
  `#distinct(Ψ_planted)≥2`, `S₃≠0` on ≥99% planted; a tripped guard ⇒ STOP-fix (not VOID).
  (Verified in the v2 run: fires p=1e-4, monotone 0.058→0.155→0.524, non-degenerate.)
- **PC-COMBO (omnibus firing control — MUST fire; NEW in v3).** Planted fraction `ρ`: resample `d₃`
  until `L_sum==J`, using a REAL INDEPENDENT `P₃` (NOT `−(P₁+P₂)`, which would collapse the combos into
  `Φ^pt`). Require `Î_omni` fires exact perm `p<0.01` at ρ=0.30, monotone across
  `ρ∈{0,0.15,0.30,0.60}`. Non-degeneracy guard: `#distinct(L_sum_planted)≥2`; a tripped guard ⇒
  STOP-fix. (Verified in smoke: fires p=0.0020 at ρ≥0.3, `distinct_lsum=3`, ~3 draws.)
- **PC-GRADE (resolution floor — unchanged).** `Ψ_plant=J` with prob `mix`, else uniform; monotone
  firing; `MI_min` rung ≥80%. (Verified: fires.)
- **PC-nonCM (arm control).** the matched non-CM arm is the control for CM-specificity of `Δ`.

**VOID rule.** If **PC-COMBO or PC-SEM** does not fire at `(q,N)`, the instrument is dead at that scale
⇒ the arm is VOID; no null claimed. A tripped non-degeneracy guard ⇒ STOP-fix (mis-built plant),
distinct from VOID.

## 5. POWER (unchanged from v2)

Primary `Î_prim`: `df=4·s`, `s=#non-empty Φ^pt strata` (=27 at m=3), `λ₈₀(108)=54.9` ⇒
`MI_min≈7.9×10⁻³` @N=5k, `2.0×10⁻³` @N=20k. The exact within-stratum permutation p is the verdict.
Omnibus `Î_omni`: 3×3|27 = `df=4·s`, same floor form, now estimable. The relevant single-character floor
is a **Weil-type** bound `√q/N_ord` (general Weil/Deligne multiplicative-character bound; KS 2000's
additive `e_p(rational f)` theorem is not the authority — D3). Detects only GROSS synergy.

## 6. SCOPE / PARAMETERS (unchanged from v2)

Schedule frozen in `schedules_v1/schedule_A_joint_v1.json` (SHA `c533f669…`): j=0 B-witness prime order,
`q≡1 mod 3`, `trace≠1`. Discovery {541,571,577}; confirmation (OOS) {2029,2053,2089}; ladder
{1033,4111,16417,65539}. Non-CM matching: ordinary `j∉{0,1728}`, `|t²−4q|≥⌊√q⌋`, `t≠1`, minimize
`|N_non−N_CM|`. Generator = the order-`L` (largest prime factor) point of smallest x, smaller y.
`m=3`; `b=⌊log₂ q⌋−2`; `ℓ=3`. `N`: 5,000 (discovery), 20,000 (confirmation); seed `20260821`;
`#perm≥10⁴`. Every `Î,Δ,p` carries `(arm,q,N_CM,N_non,t_non,|I|,m,N,s,MI_min)`.

## 7. FALSIFICATION (VOID clause updated)

- **A-joint RETAINED ⇔** CM `Î_prim` fires (within-stratum `p≤0.01`) AND `Δ>0` beyond the paired null
  across the schedule, with PC-SEM, PC-COMBO, PC-GRADE having fired.
- **A-joint ABANDONED at this scope ⇔** `Δ≤0` within the null across the whole schedule, all positive
  controls fired ⇒ scoped magnitude bound `|Δ|<MI_min(N)` with power+scope+untested-channel list,
  never "no structure."
- **VOID ⇔** PC-COMBO or PC-SEM did not fire at `(q,N)` (mis-built plant ⇒ STOP-fix, distinct).

## 8. EXACTNESS (unchanged from v2)

Signal path int/GF(q): curve arithmetic, x-coords, `χ₃`, `S₃`, `L_{ij}`, labels, permutation counts.
Semaev S₃ (citation-verified D2): `S₃=0` iff `∃ y_i∈K̄` with `(x_i,y_i)∈E` and `±P₁±P₂±P₃=O`; exact over
`F_q` for genuine `E(F_q)` x-coords; `char q≠2,3`. Float ONLY as the `log₂` inside MI, ranked against the
exact integer within-stratum permutation count (`# noqa: float` marks the statistic lines).
`check_no_float.sh` exits 0.

## 9. PRE-COMMITMENT (MI_min at corrected floor; omnibus now a real guard)

| Outcome | Trigger | Conclusion | Grade |
|---|---|---|---|
| CM-specific joint synergy | PC-SEM+PC-COMBO+PC-GRADE fired; `Î_prim(CM)` p≤0.01; `Δ>0` beyond paired null | CM structure produces Semaev-μ₃ joint-set synergy absent on the non-CM arm. Report `Δ`, scope, ladder trend. NEXT: which stratum; higher `r`; `m=4`; other `ℓ`. | EMPIRICAL (mechanism, model-scale) |
| CM-independent synergy | `Î_prim` fires both arms; `Δ≈0` | Generic to `d↦(x,y)`, not CM-specific. | EMPIRICAL (generic) |
| Off-target channel | `Î_prim(CM)` null but `Î_omni(CM)` or interval arm fires p≤0.01 | Effect lives in the additive-combo/interval channel, not Semaev-μ₃; NAMED next probe. | EMPIRICAL (off-target) |
| Scoped null | all PCs fired; `Î_prim` AND `Î_omni` AND interval within null; `Δ≤0` across schedule | `|Δ|<MI_min` (≈7.9×10⁻³ @5k): no CM-specific joint synergy in the {Semaev-μ₃, additive-combo, interval} channels at `q≲2¹⁶`, `m=3`. BOUNDED MAGNITUDE with power+scope, NOT a closure — Weil floor uncrossed. Untested next: `r≥4`; `m≥4`; other `ℓ`; GLV-mixed; coord-pair; finer interval. | VERIFIED-scope (scoped null) |
| Void | PC-COMBO or PC-SEM did not fire | Instrument dead at scale; bank NO null; report power ceiling and the `N` needed. | VOID |

Scoped-null row carries the symmetric burden (object/class/power/scope). No dismissal vocabulary.

## Owed gates
- `citation-verifier` (S₃ + floor): DISCHARGED 2026-08-21 (D2/D3).
- **Second independent `experiment-designer` read of THIS v3: OWED** before any Δ promotes.
- `compile-diff` if folded into a master/handover.
