# DEVIATIONS — PREREG_chik_dmodk_leakage_v3.md run

**Run:** `chik_dmodk_leakage_v1.py` (2026-07-27). Freeze SHA-256 of the prereg
`feda18a2cd9fbc1c6200c6302465011d4aec1178df04f9e3acf18501a32c7220` (confirmed intact post-run).

## D1 — D_known select-bitlen schedule pinned at run time (spec underspecified)

- **Spec (v3 §1):** `D_known` = "MT19937 seeded `SEED_MT = S0` → select-bitlen → curve … first
  `N_known = 10000` in generation order. (Bitlengths ≤160.)" — the bitlen *schedule* was not pinned.
- **As run:** a single `random.Random(S0)` (MT19937) stream; bitlen `b = 16 + (i mod 145)` cycling
  `[16,160]`; `d = (1<<(b-1)) + rng.randrange(1<<(b-1))`; `x = scalar_mul(d)[0]`; first 10000 valid
  points in generation order. This is the canonical b-bit draw of
  `angular_interference_scaling_v1.gen_keys` / `evaluate_dsig_residue_claim_v1`.
- **Impact: none on the verdict.** The scored statistic is the per-point marginal `χ_k(x_d)` vs
  `d mod k`; `d mod k` is ~uniform for any bitlength `b ≥ 3`, so the null does not depend on the bitlen
  distribution. Bitlengths `[16,160]` avoid degenerate tiny-`b` cells (`b=1` gives a single value).
  The verdict is NULL and would be NULL for any faithful known-MT select-bitlen schedule.
- **Why not the canonical `constructed_keys_1to160_100k` file:** that set is SEEN for χ_k-class tests
  (`leak_test_exact.py`, `key_cubic_char_v2.py`, `phi_n_residue_XY_battery_v1.py` all load it), so it
  cannot serve as the unseen out-of-sample set. A fresh `S0` stream is required and used.

## Notes (not deviations from the frozen spec)

- The **pooled** perm-p (spec §4: context only, not the verdict) uses `fold=9` as a sentinel offset in
  the permutation-seed formula `S0 + 7919·k + 31·fold + dataset_id`, giving it a distinct RNG stream
  from the two scored folds (`fold∈{0,1}`). It is reported for context and does not enter the §4 gate
  verdict, which uses only the two hash-folds.
- Fold content-key = the integer x-coordinate `x_d` (§1), via `fold_of(x_d, S0, 2)`, as specified.
