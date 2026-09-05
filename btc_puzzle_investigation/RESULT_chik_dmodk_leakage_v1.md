# RESULT — χ_k(x([d]G)) vs d mod k: NULL, gated, both key-sets `[EMPIRICAL — SCOPED]`

**File:** `RESULT_chik_dmodk_leakage_v1.md`  **Date:** 2026-07-27
**Prereg:** `PREREG_chik_dmodk_leakage_v3.md`, freeze **SHA-256
`feda18a2cd9fbc1c6200c6302465011d4aec1178df04f9e3acf18501a32c7220`** (confirmed intact post-run).
**Run:** `chik_dmodk_leakage_v1.py` / `.log`; `check_no_float.py` green.
**Status:** CONFIRMATORY (user-authorised) — the channel was already adjudicated null; this run is an
end-to-end demonstration of the `kfold_gate` out-of-sample workflow on UNSEEN data. **No ECDLP /
extraction / secp-scale claim.**

---

## Verdict (§4b, pre-committed)

**(b) NULL.** The gate SUPPRESSES χ_k(x_d)-vs-(d mod k) on BOTH unseen random-style sets (`D_known`,
`D_rand`) for every `k∈{2,3,6}`, with the positive control C1 firing (so power existed).
**`[EMPIRICAL — SCOPED]`: no `d mod k` leakage at `N≤10⁴`, `k∈{2,3,6}`, gate α=0.01.** A per-point
marginal BOUND — **not a closure**; higher-order / joint / set-level readouts are untested (named below).

## Controls (both fired as required)

| control | result |
|---|---|
| **C1 positive** (feature = the residue) | EMIT at k=2,3,6 — MI 1.00 / 1.58 / 2.58 b, `0/4000`, both folds ✓. Instrument has power. |
| **graded extraction ceiling** (k=3, D_known) | ε=1/50 suppresses (`133/68` per fold); **ε=1/20 emits** (`0/4000`). Ceiling ≈ **1/20** — the run could catch ≈5% of rows carrying the residue. |
| **C2 negative** (permutation null) | flat by construction; every scored fold's `hits/4000` sits mid-bulk (see below), self-MI>0. |

## Scored verdict (unseen sets; both folds must clear α=0.01, i.e. hits ≤ 40)

| dataset | k=2 | k=3 | k=6 | gate |
|---|---|---|---|---|
| `D_known` | MI 0.0002, folds 329/2866 | 0.0003, 347/2036 | 0.0017, 750/2520 | **suppress** |
| `D_rand`  | 0.0000, 2787/1930 | 0.0002, 3197/2246 | 0.0014, 3323/190 | **suppress** |
| `D_orbit` (non-scoring) | 0.0000, 3253/2729 | 0.0001, 3205/2682 | 0.0004, 2107/2274 | suppress |

Every observed MI is below the pre-run detection floor (`≈0.0010 / 0.0019 / 0.0064 b` for k=2/3/6);
no fold approaches the `≤40/4000` bar. `D_orbit` emits ∅.

## Relation to prior work + the loose end this closes

- The channel was already null in the record: `leak_test_exact.py:154` tests `d%3` (and `d%2`) vs
  coordinate-character features (exact MI, Westfall–Young min-p, matched perm null, both sets);
  `key_cubic_char_v2.py` records the cubic/sextic lean `~p=0.10` as **intrinsic to the short-interval
  character sum, not creator signal**. This run REPRODUCES that null with the added `kfold_gate`
  out-of-sample control, on freshly-generated unseen sets.
- **Loose end closed:** the ad-hoc `chi_3` pooled `0.043` on the real 82 (this session's audit,
  quarantined in prereg §5) was small-N noise — on the unseen `N=10⁴` sets `chi_3` flattens to pooled
  `p ≈ 0.39` (`D_known`) / `0.65` (`D_rand`). Not a signal.

## What this does NOT touch (named, per §4b)

Per-point marginals only. Untested and NOT bounded by this run: higher-order / **joint** readouts
(additive×multiplicative cross, short-scalar), **set-level** structural objects (where the project
stance says any surviving signal must live), larger `N`, and `2²⁵⁶` scale. The `kfold_gate` workflow is
now validated end-to-end (controls + verdict) as the standing out-of-sample mechanism for section-G-class
readouts.

## Deviations
See `PREREG_chik_dmodk_leakage_v3_DEVIATIONS.md` — one (D1): the D_known select-bitlen schedule (left
underspecified by the frozen spec) was pinned in the run script; immaterial for a marginal test.
