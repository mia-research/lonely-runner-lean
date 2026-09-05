# WP7 — Bucket-A feature-family battery  (ATTACK-VALID · each idea tested individually)

**Farm to:** Sonnet subagent.  **Runtime budget:** ~60–120 min.  **Priority: run
after WP1/WP6, but MUST be run** — do not skip on the basis of any prior 20k result.

## The correction this WP embodies
The prior record claims pure-`(X,Y)→n` is flat (20k MI≈0.0005). **We do not trust
that number to stand in for these tests.** We do not know those runs used the right
features, parameters, or interpretation. Each idea below is its OWN feature
representation, and "does (X,Y) leak n" depends on representation — a
byte-slice classifier can be blind to a signal a spectral or compression feature
would catch. So: **run each family separately, fresh, at 100k, with its own
control and its own conditional reading.** Do NOT merge them into one matrix and
report a single number (that merge was the earlier mistake; WP2 is the *joint*
member — this WP is the per-family complement).

## Families (each PUBLIC-only: features from X, Y, N; `L.assert_attack_valid`)
Test every one; report each independently:
1. **Spectral** — FFT and DCT of the 256-bit strings of X and of Y (source 5.1,
   8.1-recast, 8.2 structure factor, 9.12 autocorrelation). Peak locations/heights.
2. **Compression / Kolmogorov** — gzip, bz2, lzma ratio of X, Y, X‖Y bytes
   (5.4, 9.3). Mean ratio vs n and vs n-class.
3. **k-mer / motif** — enrichment of 8/12/16-bit substrings of X,Y per n (5.6, 8.4).
4. **Continued fraction** — CF of `X/p`, `Y/p`, `X·Y⁻¹ mod p /p`; do early
   denominators hit the true n? (5.5, 9.9).
5. **Bit autocorrelation** — ACF of X,Y bitstrings at lags 1..256 vs n (9.12).
6. **GF(2) rank** — per-n bit matrices of X,Y; rank deficiency vs random (9.21).
7. **Unsupervised cluster purity** — kmeans / (UMAP if installed, else PCA) on
   coordinate features, ARI vs n labels (5.2, 9.23, 9.20).
8. **Coordinate statistics** — Hamming weight, byte-entropy profile, run-length /
   longest-1-run (percolation, 8.14), min(X,p−X) size bias.
9. **Address/hash** — first 3 bytes of the P2PKH address, Base58 char freqs vs n
   (3.3, 9.13, 5.5-hash).

## Protocol (identical for every family)
- Extract the family features from public data only.
- Readout A: `MI(feature; n)` and `MI(feature; n-class)` (sklearn mutual_info).
- Readout B: grouped-CV (by bits) accuracy of a classifier on THIS family alone
  vs baseline, and the *delta* when this family is added to a byte-slice base.
- **Control (MANDATORY, per family):** `C.plant_leak` swept in strength; report the
  min detectable strength `s*` at this family's dimensionality. A family's null is
  only meaningful relative to its own `s*`.
- Matched-null (`C.matched_null`) comparison for any family that shows a lift.

## Report → `../RESULTS/WP7_feature_families.json`
Dict keyed by family: `{mi_n, mi_nclass, cv_acc, cv_delta, control_s_star,
matched_null_acc, reading}`. Each `reading` is a conditional negative/positive
bound to that family + n=100k + its `s*`. **No family omitted, none merged.**

**Done-check:** all 9 families present with a fired control and a bounded verdict
each; any family beating its `s*` floor is flagged for WPZ with its matched-null.
