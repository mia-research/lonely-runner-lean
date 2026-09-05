# PREREG — Does χ_k(x([d]G)) leak the additive residue d mod k? (gated, both key-sets)

**File:** `PREREG_chik_dmodk_leakage_v1.md`  **Date:** 2026-07-27
**Status:** PRE-RUN on UNSEEN data (constructed known-MT set + fresh random-d / orbit).
The real-82 section-G readout is ALREADY SEEN (disclosed §7) and is in-sample here.
**DRAFT — pending `experiment-designer` sign-off (mandated, CLAUDE.md §2) + freeze SHA before any run.**
Model / known-generator data only; **no ECDLP / extraction / secp-scale claim.**

**What this decides.** `masked_structure_harness` section G (the "closure-blind corner":
`‖χ_k‖_A ~ √p`, so the closure theorem does not bound it) has been run ad hoc and never
pre-registered. During an audit run it produced `chi_3` pooled perm-p `0.043` on the 82 real
keys. This prereg closes that loose end PROPERLY: it freezes the test on unseen data, with the
`kfold_gate` both-folds mechanism, a firing positive control, and a matched null — before any
"signal / no signal" language is used.

---

## 0. PRIOR EXPECTATION (states the base rate; not a futility verdict)

`χ_k(x([d]G))` vs `d mod k` is a **per-point readout**: one public point → one character value,
the scalar → one residue. By the `d ↔ (X,Y)` bijection (CLAUDE.md) this is a **distribution
marginal — Farey-generic, EXPECTED NULL**; a per-point readout that recovered `d mod k` beyond
chance and replicated would *be* an ECDLP break, which is not anticipated. The value of running
it is (i) to close the loose end I created, (ii) to exercise the gate workflow end-to-end, and
(iii) to bound the channel with a stated power ceiling. A null here is a **scoped bound, not a
closure**; the avenue is not thereby declared dead (project stance).

---

## 1. OBJECT

`E: y²=x³+7`, base point `G`, group order `n`. `k ∈ {2,3,6}` (so `k | p−1` at secp; `χ_k` =
exact k-th power-residue character via `make_chik`, value in `{0..k−1}`, undefined at `x=0`).

- **Feature** `f_k(d) = χ_k(x([d]G))`.
- **Target** `t_k(d) = d mod k`.
- **Datasets** (each a frozen list of `(x_d, d)`):
  - `D_known` — the constructed **known-MT** set: MT19937 → select-bitlen → curve, the SAME
    pipeline as the real keys (`feedback_test_on_both_sets`); the full-power known-generator set.
    **UNSEEN for section G.** Frozen sample size `N_known = 10000`.
  - `D_rand` — fresh random-`d` curve points, `N_rand = 10000`, **unseen**, independent seed.
  - `D_orbit` — the generator orbit `{x([i]G)}`, `d=i`, `N_orbit = 40000` (structured `d`; a
    second, non-random `d`-law — informative if it and the random streams disagree).
  - `D_real82` — the 82 solved keys. **SEEN (§7); reported for continuity, NOT scored as a verdict.**

---

## 2. FORCED FACTS — zero evidence

- **F1** `x([d]G)` is a deterministic bijection of `d`; `f_k` is a per-point function ⇒ any
  `f_k ↔ t_k` association is a marginal (§0). Zero evidence either way until measured.
- **F2** three characters `k∈{2,3,6}` ⇒ **multiple comparison**: family-wise, the seen
  `chi_3 = 0.043` is `≈1−(1−0.043)^3 ≈ 0.12` — unremarkable on its own.
- **F3** `D_real82` is a fixed finite set already run in full ⇒ **no out-of-sample remains on the
  real keys**. The frozen verdict lives on `D_known` / `D_rand` / `D_orbit` only.

---

## 3. STATISTIC (frozen)

Per dataset, per `k`: single-shot `MI = mi_bits(f_k, t_k)` (bits), and its exact integer
**permutation p-value** `p_perm(k)` = fraction of `B=4000` target-shuffles with `MI ≥` observed.

**Gated verdict (the new instrument).** Split each dataset by `kfold_gate.fold_of(item, seed=S0,
K=2)` with `S0` FROZEN here to **`S0 = 20260727`** (declared before any run; no re-seeding — drill
rule 1 / `[[feedback_anomaly_drill_protocol_2026_07_17]]`). `KFoldGate(alpha="0.01", K=2, seed=S0)`
EMITs for `(dataset,k)` iff BOTH hash-folds' `p_perm ≤ 0.01`.

**Positive control C1 (MUST fire).** A planted-leak feature `f_k^+(d) = t_k(d)` (the residue
itself) on `D_known`: MI is maximal and the gate must EMIT at `N_known`. If C1 does NOT fire, the
instrument is underpowered at that `N` → **no verdict; report the power ceiling** (§4c). A softer
graded control `f_k^{ε}` = `f_k` with a fraction `ε` of rows overwritten by `t_k` locates the
smallest detectable `ε` (the extraction ceiling).

**Negative control C2 (must be flat).** The permutation null itself (shuffled `t_k`) gates-null;
a fresh independent unseen subset of `D_rand` gates-null. Self-MI `mi_bits(f_k,f_k) > 0` confirms
the estimator is live (not returning 0 by construction).

---

## 4. DETERMINATION CRITERION (pre-committed)

Require the SAME `k` to agree across the two independent random-style sets (`D_known`, `D_rand`) —
stronger than the gate's within-set both-folds, and it absorbs the `k∈{2,3,6}` multiplicity.

- **(a) LEAKAGE — surprising, escalate.** Gate EMITs for some `k` on BOTH `D_known` and `D_rand`,
  with C1 firing and C2 flat. This contradicts the §0 marginal-null expectation ⇒ treat as a
  candidate structural break; **do not narrate it as a break here** — freeze the witnesses and open
  a dedicated follow-up prereg (adversarial replication, larger `N`, both sets again).
- **(b) NULL — expected, scoped bound.** Gate SUPPRESSES on the unseen sets (with C1 having fired,
  so power existed). Report as `[EMPIRICAL — SCOPED]`: the per-point χ_k channel shows no `d mod k`
  leakage at `N≤10^4`, `k∈{2,3,6}`, gate α=0.01. **Bound, not closure** — state the ε-ceiling from
  C1's graded control (smallest `ε` the run could have caught). Higher-order / joint / set-level
  readouts are NOT tested and are named as separate objects.
- **(c) ABSTENTION — underpowered.** C1 fails to fire at `N` ⇒ the run had no power; **bank no
  null**, report only the power ceiling and the `N` that would be needed. (`[[feedback_prereg_abstention_is_the_finding_2026_07_19]]`.)

`D_orbit` is reported alongside but does not by itself trigger (a) — structured `d` can create or
destroy an association for reasons unrelated to leakage; agreement with the random sets is required.

---

## 5. SEEN-DATA DISCLOSURE (binding)

`D_real82` section G was run this session during an audit, WITHOUT prereg:
`chi_2` pooled perm-p `0.525`, **`chi_3` pooled `0.043`**, `chi_6` `0.638`; all **gated-null**
(`chi_3` fold0 `0.022`, fold1 `0.750` at the default seed). These are IN-SAMPLE / EXPLORATORY,
cannot be un-seen, and are **excluded from the §4 verdict**. The `chi_3` pooled `0.043` is the
motivation, not evidence.

---

## 6. TAUTOLOGY / FLOAT / SCOPE

- Feature `χ_k` and target `d mod k` are exact `int`. MI's internal `log` and the permutation
  p-value are a monotone statistic ranked against a matched shuffle null (CLAUDE.md allowance); the
  p-value is an **exact integer count**; the gate verdict is the integer cross-product
  `hits·αden ≤ αnum·trials`. **No float threshold decides.** `check_no_float.py` must pass on the
  run script before execution.
- Feature and target are disjoint constructions (character of `x` vs residue of `d`) — no residue-
  vs-component tautology (`[[feedback_residue_vs_component_tautology_2026_07_14]]`); the fold split is
  content-hashed, not a `d`-derived circular selector.
- Scope: `N ≤ 10^4`, `k∈{2,3,6}`, model/known-generator data. **Nothing transfers to `2²⁵⁶`.** A
  null is a per-point marginal bound; **no security claim**, and no PRNG/generation-side reading
  (`[[feedback_no_prng_generation_side_2026_07_14]]` — this is a curve-arithmetic readout of `x([d]G)`).

---

## 7. OUTCOME → ACTION

- (a) leakage → freeze witnesses, open a dedicated replication prereg; report nothing as a break yet.
- (b) null → `[EMPIRICAL — SCOPED]` bound with the ε-ceiling; the gate workflow is validated as the
  standing out-of-sample mechanism for section-G-class readouts; note untested higher-order objects.
- (c) abstention → power ceiling only; raise `N` and re-run under this same prereg.

## Files (to be created on sign-off)
- `chik_dmodk_leakage_v1.py` / `.log`; `RESULT_chik_dmodk_leakage_v1.md`; `_DEVIATIONS.md` if any.
- Reuses `kfold_gate_v1.py` (frozen seed `S0=20260727`), `make_chik` / `mi_bits` from the harness.

## Sign-off (mandated before any run)
- [ ] `experiment-designer` sign-off (blocked by session cap at draft time; resets 20:00 Brisbane).
- [ ] freeze SHA-256 of this file recorded in the run log.
- [ ] `check_no_float.py` green on `chik_dmodk_leakage_v1.py`.
