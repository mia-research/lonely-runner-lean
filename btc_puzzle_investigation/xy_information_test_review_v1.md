# Critical review of the (X,Y)→key leakage test (v1) + corrected rerun (v2)

Self-audit of `xy_information_test_v1.py` and the Y-parity→n-parity finding, then
the corrections folded into `xy_information_test_v2.py`.

## What was checked, and what held

**The synthetic null is valid — PASS.** The whole "map property vs selection"
split depends on `constructed_keys_1to160_100k.csv` being uniform-random d with
real curve arithmetic. Verified from the generator (`scripts/session_2026-07/
generate_dataset.py`) and independently:
- d is drawn `lo + rand(2^{N-1})` per band → genuinely uniform in `[2^{N-1},2^N)`.
- X,Y confirmed `= d·G` on sampled rows with an independent library (`ecdsa`), not
  the generator's own arithmetic.
- n,k are an honest `nmax=256` convergent search, deterministic from d.

**Real vs synthetic is apples-to-apples — PASS.** Both compute n,k with the same
`nmax=256`, and the CSV columns reproduce a canonical recompute (real 75/75,
synth 300/300). Exact-rational u agrees with the generator's float u, so the
float truncation of low bits (for N>53) introduced no artifact here.

## The flaws that changed the answer

**F1 — the n-parity target carried an unpriced researcher degree of freedom
(`nmax`).** v1 tested `nmax=256` only. Scanning nmax shows the Y-parity↔n-parity
association is significant only for `nmax∈[~180,300]` (min Fisher p≈0.0008 near
234) and null below 180 / above ~300; 12.2% of all nmax cross p<0.05 vs 5%
expected. The canonical 256 sits inside that band by luck of the upstream choice.
Pricing the nmax search into the null (matched min-p over the nmax grid) moves the
real-key significance from the naive **0.0026 → 0.007**. Pricing the *feature*
choice as well (v2 n/k channel, max over feature×nmax) moves it to **≈0.057**.
The effect erodes monotonically as the degrees of freedom actually used are
accounted for. It is not an artifact I can dismiss (it survives the nmax-only
correction), but v1's headline number was overconfident by ignoring the search.

**F2 — multiplicity was under-counted.** v1 corrected only over the 42 features,
per target. The real exposure was ~20 targets × 42 features × the nmax DOF, plus a
post-hoc zoom onto the winning (Y-parity, n-parity, nmax=256) cell. v2 corrects
family-wise and prices nmax.

**F3 — no negative control.** v1 proved the detector *can* fire (planted positive)
but never measured how often it fires on pure noise. v2 pushes 8 random binary
targets through the identical pipeline to read the family-wise false-positive rate.

**F4 — the cleaner null for the specific 2×2 is exact-conditional.** v1's
subsample-of-synthetic null mixes in the real/synthetic marginal differences
(real P(n even)=0.45 vs synth 0.35). Permuting the label within the dataset
(preserving marginals) is exact for these binary targets; v2 uses it.

**F5 — bug found in v2's own parameter-free target (caught by this review).** The
first CF convergent denominator `q1` came out ≡1 for all keys — a degenerate
target whose "null" was fake. Cause: the Euclid loop started on `den/num` and then
also dropped `a[1:]`, discarding a1. Fixed; verified against known convergents
(2/7→[3,7], 16/113→[7,113]); q1 now spans 11 values on the real keys.

## v2 corrections (all in `xy_information_test_v2.py`)

- Targets recomputed canonically from d (exact rational), not read from CSV.
- Parameter-free "n-shadow": CF convergent denominators q1,q2 (no nmax cap).
- n/k channel statistic = max standardized-MI over feature×nmax, matched
  max-over-(feature×nmax) permutation null → prices both searches.
- Positive (graded) + negative (random-binary) controls.
- Family-wise correction across the target grid.

## Results (full power)

Controls, real keys: positive fires (z≈28); **negative 0/8 fired** (pipeline not
trigger-happy); weak positives don't fire at 75 keys (known low power).

| channel | real (75 keys) | synthetic (high power) |
|---|---|---|
| parameter-free (d mod p, bits, position, CF q1/q2) | all null | all null |
| n/k channel, nmax priced in | **p ≈ 0.057 (n/k), pending full-power** | pending |

Significance of the Y-parity→n-parity effect by how much search is priced:
naive Fisher (nothing priced) 0.0026 → nmax priced 0.007 → feature×nmax priced
0.057. **Corrected honest read: at the 75-key sample it does not clear 0.05 once
the degrees of freedom are paid for.** It is a watch-item to re-test as more
puzzles are solved, not a handle. (Final numbers filled from
`xy_test_v2_real.txt` / `xy_test_v2_synth.txt`.)
