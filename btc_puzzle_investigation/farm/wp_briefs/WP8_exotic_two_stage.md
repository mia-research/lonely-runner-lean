# WP8 — Exotic / cross-domain ideas, two-stage  (§8 + physics ideas — TESTED, not dismissed)

**Farm to:** Sonnet subagent.  **Runtime budget:** ~60–120 min.  **Priority: medium.**

## The correction this WP embodies
These (§8 seismic/crystallography/fluid/DNA/topology/RMT/Hough/side-channel/…,
plus §5.7, §7, the pairing ideas) were dropped as "need the bits of d / the
double-and-add trace, which the real puzzle doesn't expose." **That skipped the
work.** Two things make them testable:

- On the **dataset we HAVE d**, so we can test whether the exotic quantity even
  correlates with n *with full access* (a necessary condition). If it is flat even
  with the whole trace, the channel is empirically dead — that is a RESULT, earned,
  not asserted. If it correlates, it is worth pushing to stage 2.
- Most recast onto the **public (X,Y)** directly. Do that and test with a control.

## Stage 1 — necessary-condition probe (uses d/trace; STRUCTURE PROBE, attack_valid=false)
For each idea, compute its quantity on the trace/bits and measure `MI(quantity; n)`
and `MI(quantity; L=ord_n(2))` with a `C.matched_null` baseline:
- Seismic/crystallographic power spectrum & Bragg peaks of the double-and-add
  intermediate x-coords (8.1, 8.2); peak ratio at harmonics of `1/L`.
- Side-channel "power" `Σ HW(x_j)+HW(y_j)` and "timing" (add count = HW(d)) (8.9).
- Persistent homology / point-cloud shape of the intermediate cloud (8.5, 9.6) —
  use `ripser` if importable, else 0-dim persistence via single-linkage; note which.
- Turbulence spectral exponent, RMT eigenvalue spacing, spin-glass magnetization,
  percolation cluster (8.3, 8.13, 8.15, 8.14).
Report, per idea, whether the trace quantity carries ANY n-information at all.

## Stage 2 — public recast (ATTACK-VALID; only for ideas that survive stage 1, but
run the obvious public recasts regardless)
Recast the extractor onto public `(X,Y)` and test `MI(·;n)` + grouped-CV with a
`C.plant_leak` control:
- FFT/structure-factor of the **public X,Y bitstrings** (already partly in WP7 —
  here add the crystallographic Bragg-peak-at-1/n' **candidate sweep**: is
  `|S_curve(m/n')|` larger at the true n'? attack-valid, ties to WP6).
- Persistent homology / Hough transform / RMT eigenvalue spacing of the **public
  point cloud** `{(X_i mod M, Y_i mod M)}` binned by candidate n' (8.5, 8.18, 8.13).
- Compression / k-mer already in WP7 — cross-reference, don't duplicate.

## Sub-task — verify the "dead" pairing ideas numerically (do the work)
Weil/Tate pairing (8.16, 9.8): rather than assert `e(P,G)=1`, **compute** it on a
sample and report the value; compute the **embedding degree** obstruction (smallest
`k` with `N_ord | p^k − 1`) and report the actual number that makes a pairing
attack infeasible. Turn the assertion into a measured fact.

## Report → `../RESULTS/WP8_exotic.json`
`{stage1: {idea: {mi_n, mi_L, vs_matched_null, carries_info: bool}},
stage2: {idea: {mi_n_public, cv_acc, control_s_star, candidate_sweep_result}},
pairing: {e_PG_value, embedding_degree_k, note}, reading}`. Mark stage-1 entries
`attack_valid:false` (probe), stage-2 `attack_valid:true`.

**Done-check:** every §8 idea has a stage-1 empirical verdict (with matched null);
public recasts run with fired controls; pairing triviality + embedding degree are
NUMBERS, not claims. Nothing marked "dismissed."
