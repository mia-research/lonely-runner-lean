# PREREG — Does χ_k(x([d]G)) leak the additive residue d mod k? (gated, both key-sets) — v2

**File:** `PREREG_chik_dmodk_leakage_v2.md`  **Date:** 2026-07-27  **Supersedes:** `_v1` (folds in
`experiment-designer` tightenings #1–#4; no verdict logic changed).
**Status:** PRE-RUN on UNSEEN data (constructed known-MT set + fresh random-d / orbit). The real-82
section-G readout is ALREADY SEEN (§5) and is in-sample here.
**`experiment-designer` SIGNED OFF 2026-07-27** (conditional on #1–#4, now folded in; re-audit of this
v2 requested before the freeze SHA is taken). Model / known-generator data only; **no ECDLP /
extraction / secp-scale claim.**

**What this decides.** `masked_structure_harness` section G (the "closure-blind corner": `‖χ_k‖_A ~ √p`,
so the closure theorem does not bound it) has been run ad hoc and never pre-registered. During an audit
run it produced `chi_3` pooled perm-p `0.043` on the 82 real keys. This prereg closes that loose end
PROPERLY: it freezes the test on unseen data, with the `kfold_gate` both-folds mechanism, a firing
positive control, and a matched null — before any "signal / no signal" language is used.

---

## 0. PRIOR EXPECTATION (base rate; not a futility verdict)

`χ_k(x([d]G))` vs `d mod k` is a **per-point readout**: one public point → one character value, the
scalar → one residue. By the `d ↔ (X,Y)` bijection (CLAUDE.md) this is a **distribution marginal —
Farey-generic, EXPECTED NULL**; a per-point readout that recovered `d mod k` beyond chance and
replicated would *be* an ECDLP break, which is not anticipated. Running it (i) closes the loose end I
created, (ii) exercises the gate workflow end-to-end, (iii) bounds the channel with a stated power
ceiling. A null here is a **scoped bound, not a closure**; the avenue is not thereby declared dead.

---

## 1. OBJECT

`E: y²=x³+7`, base point `G`, group order `n`. `k ∈ {2,3,6}` (`k | p−1` at secp; `χ_k` = exact k-th
power-residue character via `make_chik`, value in `{0..k−1}`; `χ_k(0)=None` mapped to label `0`, see §6).

- **Feature** `f_k(d) = χ_k(x([d]G))`.  **Target** `t_k(d) = d mod k`.
- **Datasets** — each a frozen list of `(x_d, d)`; ALL generation seeds pinned here (tighten #1):
  - `D_known` — constructed **known-MT** set: **MT19937 seeded `SEED_MT = S0`** → select-bitlen → curve
    (the pipeline of `[[feedback_test_on_both_sets_2026_07_12]]`); take the **first `N_known = 10000`** in
    generation order. **UNSEEN for section G.** The full-power known-generator set.
  - `D_rand` — fresh random-`d` curve points, `d = Random(SEED_RAND).randrange(1,n)`, **`SEED_RAND = S0+1`**,
    `N_rand = 10000`, **unseen**.
  - `D_orbit` — generator orbit `{x([i]G)}`, `d=i`, `N_orbit = 40000` (deterministic; structured `d`).
  - `D_real82` — the 82 solved keys. **SEEN (§5); reported for continuity, NOT scored.**
- **Fold content-key (tighten #4):** `fold_of(x_d, seed=S0, K=2)` hashes the **integer x-coordinate
  `x_d`** (disjoint from the target `d mod k`; SHA-256 is uncorrelated with `d mod k`).

---

## 2. FORCED FACTS — zero evidence

- **F1** `x([d]G)` is a deterministic bijection of `d`; `f_k` is per-point ⇒ any `f_k ↔ t_k` association
  is a marginal (§0). The one structural coupling is `x([d]G)=x([n−d]G)` (χ_k invariant under `d→n−d`);
  the negation partner `n−d ≈ 2²⁵⁶` lies outside every sampled range (`d ≤ 4·10⁴`, or ≤160-bit), so it
  neither collapses the target nor lets the graded control inject an unreachable shape.
- **F2** three characters `k∈{2,3,6}` ⇒ **multiple comparison**: family-wise, the seen `chi_3 = 0.043`
  is `≈1−(1−0.043)³ ≈ 0.12` — unremarkable. The verdict tests all three k (does not narrow to k=3).
- **F3** `D_real82` is a fixed finite set already run in full ⇒ **no out-of-sample remains on the real
  keys**. The frozen verdict lives on `D_known` / `D_rand` / `D_orbit` only.

---

## 3. STATISTIC (frozen)

Per dataset, per `k`: single-shot `MI = mi_bits(f_k, t_k)` (bits), and its exact integer **permutation
p-value** `p_perm(k)` = fraction of `B=4000` target-shuffles with `MI ≥` observed (**ties → hit**,
conservative). Permutation RNG **pinned** (tighten #1): `np.random.default_rng(S0 + 7919·k + 31·fold +
dataset_id)`, `dataset_id ∈ {known:0, rand:1, orbit:2}`.

**Gated verdict.** `KFoldGate(alpha="0.01", K=2, seed=S0)`, `S0 = 20260727` (the calendar date, fixed
pre-run on data that does not yet exist — unfishable). EMIT for `(dataset,k)` iff BOTH hash-folds'
`p_perm ≤ 0.01`. **No re-seeding:** `S0`, `SEED_MT`, `SEED_RAND`, and the permutation RNG scheme above
are the ONLY seeds used; no alternative seed is tried (drill rule 1, `[[feedback_anomaly_drill_protocol_2026_07_17]]`).

**Pre-run power estimate (tighten #2, sizing only — the verdict rides the exact permutation null).**
Analytic detection floor `MI_thresh ≈ χ²_{(k−1)²,0.99} / (2·n_f·ln2)` at `n_f ≈ 5000` points/fold:
**≈ 0.0010 / 0.0019 / 0.0064 bits for k = 2 / 3 / 6.** `N=10⁴` is amply powered for C1 (a perfect-copy
leak gives `MI = H(d mod k) ≈ 1–2.6 bits`, dwarfing these floors).

**Positive control C1 (MUST fire).** Planted-leak feature `f_k^+(d) = t_k(d)` on `D_known` → `MI` maximal,
gate must EMIT at `N_known`. If C1 does NOT fire, the instrument is underpowered at that `N` → **no
verdict; report the power ceiling** (§4c). Graded `f_k^{ε}` (fraction `ε` of rows overwritten by `t_k`)
locates the smallest detectable `ε` = the extraction ceiling (the run-time power number).

**Negative control C2 (must be flat).** The permutation null gates-null; a fresh independent unseen
subset of `D_rand` gates-null; self-MI `mi_bits(f_k,f_k) > 0` confirms the estimator is live.

---

## 4. DETERMINATION CRITERION (pre-committed)

Require the SAME `k` to agree across the two independent random-style sets (`D_known`, `D_rand`) —
stronger than within-set both-folds, and it absorbs the `k∈{2,3,6}` multiplicity (per-k both-sets
both-folds ≈ `0.01⁴`; family-wise ~`3×10⁻⁸`).

- **(a) LEAKAGE — surprising, escalate.** Gate EMITs for some `k` on BOTH `D_known` AND `D_rand`, with
  C1 firing and C2 flat. Contradicts the §0 marginal-null expectation ⇒ candidate structural break;
  **do not narrate it as a break here** — freeze witnesses, open a dedicated replication prereg.
- **(b) NULL — expected, scoped bound.** Gate SUPPRESSES on the unseen random-style sets (C1 having
  fired, so power existed). `[EMPIRICAL — SCOPED]`: no `d mod k` leakage at `N≤10⁴`, `k∈{2,3,6}`, gate
  α=0.01. **Bound, not closure** — report the ε-ceiling from C1's graded control. Higher-order / joint /
  set-level readouts are NOT tested; named as separate objects.
  **Single-set hit (tighten #3):** EMIT on exactly ONE of `D_known`/`D_rand` is recorded HERE under (b)
  as a **non-replicating single-set hit** — witnesses noted, **NOT scored as leakage** (mirrors the
  gate's own "a single-fold hit is not a claim").
- **(c) ABSTENTION — underpowered.** C1 fails to fire at `N` ⇒ **bank no null**; report only the power
  ceiling and the `N` needed (`[[feedback_prereg_abstention_is_the_finding_2026_07_19]]`).

`D_orbit` is reported alongside but does NOT by itself trigger (a) — structured `d` can create/destroy
an association for reasons unrelated to leakage; agreement with the random sets is required.

---

## 5. SEEN-DATA DISCLOSURE (binding)

`D_real82` section G was run this session during an audit, WITHOUT prereg: `chi_2` pooled perm-p `0.525`,
**`chi_3` pooled `0.043`**, `chi_6` `0.638`; all **gated-null** (`chi_3` fold0 `0.022`, fold1 `0.750` at
the default seed). These are IN-SAMPLE / EXPLORATORY, cannot be un-seen, and are **excluded from the §4
verdict**. The `chi_3` `0.043` is the motivation, not evidence; the verdict tests all three k so the seen
result does not privilege k=3.

---

## 6. TAUTOLOGY / FLOAT / SCOPE

- Feature `χ_k(x_d)` and target `d mod k` are **disjoint constructions** (character of the x-coordinate,
  reached through the ECDLP-hard scalar mult, vs a residue of `d`) — no residue-vs-component tautology
  (`[[feedback_residue_vs_component_tautology_2026_07_14]]`); the fold split is content-hashed on `x_d`,
  not a `d`-derived circular selector.
- Feature `χ_k` and target `d mod k` are exact `int`. `mi_bits`' internal `log2` on exact integer
  contingency counts is a monotone statistic ranked against the matched shuffle null (CLAUDE.md
  allowance); `p_perm` is an **exact integer count**; the gate verdict is the integer cross-product
  `hits·αden ≤ αnum·trials`. **No float threshold decides.** `check_no_float.py` must pass on the run
  script before execution. **Convention (tighten #4):** `χ_k(0)=None → label 0` (`make_chik`/harness);
  `x_d=0` is a ~`2⁻²⁵⁶` event, immaterial, named for reproducibility.
- Scope (tighten #4): **scored verdict at `N≤10⁴` (`D_known`, `D_rand`)**; `D_orbit` observed at
  `N=4·10⁴` as **non-scoring** context. `k∈{2,3,6}`, model/known-generator data. **Nothing transfers to
  `2²⁵⁶`.** A null is a per-point marginal bound; **no security claim**, no PRNG/generation-side reading
  (`[[feedback_no_prng_generation_side_2026_07_14]]` — this is a curve-arithmetic readout of `x([d]G)`).

---

## 7. OUTCOME → ACTION

- (a) leakage → freeze witnesses, open a dedicated replication prereg; report nothing as a break yet.
- (b) null → `[EMPIRICAL — SCOPED]` bound + ε-ceiling; the gate workflow is validated as the standing
  out-of-sample mechanism for section-G-class readouts; note untested higher-order objects.
- (c) abstention → power ceiling only; raise `N`, re-run under this same prereg.

## Files (to be created on sign-off)
- `chik_dmodk_leakage_v1.py` / `.log`; `RESULT_chik_dmodk_leakage_v1.md`; `_DEVIATIONS.md` if any.
- Reuses `kfold_gate_v1.py` (frozen seed `S0=20260727`), `make_chik` / `mi_bits` from the harness.

## Sign-off (mandated before any run)
- [x] `experiment-designer` sign-off 2026-07-27 (conditional on #1–#4, folded into this v2).
- [ ] `experiment-designer` re-audit confirms #1–#4 correctly folded in (requested before freeze).
- [ ] freeze SHA-256 of THIS FILE recorded in the run log.
- [ ] `check_no_float.py` green on `chik_dmodk_leakage_v1.py`.
