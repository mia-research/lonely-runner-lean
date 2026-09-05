# CT.1 Selection Proof Attempt v1

Date: 2026-04-12
Status: proof-track note / candidate replacement for the raw `min-e` story

## 1. What changed

The earlier note [ct1_selection_rule_min_e_2026-04-12.md](/Users/trentpalelei/Desktop/Math%20Ex/reports/ct1_selection_rule_min_e_2026-04-12.md)
identified a strong empirical rule:

> choose the multiplicity-`1` residue whose sole-cover runner has smallest actual speed.

That rule was an excellent first clue, but it is **not** globally correct in the currently tested range.

Explicit counterexample:

- `n = 11`
- `E = (1,7,74,88,106,151,152,156,157,210)`

At the fully covered base fibre `b_0=L/11`, the thin residues are

- `(r,e,pos) = (5,106,low)`,
- `(7,152,high)`,
- `(4,156,low)`,
- `(9,156,high)`.

The raw `min-e` rule chooses `(5,106,low)`, but that start has depth `1` with a genuine
companion re-add before the first safe fibre. Meanwhile the high starts `(7,152)` and `(9,156)`
are both depth `0`.

So the selection phenomenon survives, but the selection rule must include more arithmetic than just “smallest runner.”

## 2. Corrected structural clue

For a unit runner `e = nq + rho` at the base fibre `b_0 = L/n`, the two blocked residues are

- `a_low(e) = -q rho^{-1} mod n`,
- `a_high(e) = -(q+1) rho^{-1} mod n`.

These behave differently dynamically:

- the **LOW** residue is dropped at the first reset of `e`,
- the **HIGH** residue survives the first reset and is dropped only at the second reset.

So the natural holding windows are:

- `Delta_low(e) = L((q+1)/e - 1/n) = L(n-rho)/(n e)`,
- `Delta_high(e) = L((q+2)/e - 1/n) = L(2n-rho)/(n e)`.

This is exactly the old lower-zone / upper-zone arrival split from
[lrc_lemma_br_minimax_proof_v1.md](/Users/trentpalelei/Desktop/Math%20Ex/reports/proofs/lrc_proof_pack_2026-03-01/lrc_lemma_br_minimax_proof_v1.md),
reinterpreted in the present base-fibre language.

So the real privilege seems to be:

> choose a thin residue with the **largest protected holding window**, and in practice that means choosing a **HIGH** thin residue.

## 3. Refined selection candidates

Two concrete candidate rules now look much better than raw `min-e`.

### Rule S1: `high-min-e`

Choose a HIGH thin residue if one exists, and among HIGH thin residues choose the one with smallest actual speed.
If no HIGH thin residue exists, fall back to `min-e`.

### Rule S2: `high-max-hold`

Choose a HIGH thin residue maximizing the holding window

`Delta_high(e) = L(2n-rho)/(n e)`,

equivalently minimizing `e / (2n-rho)`.
If no HIGH thin residue exists, fall back to `min-e`.

`S2` is the more arithmetic rule.
`S1` is the simpler rule.

## 4. Current computational support

The updated scanner is:

- [ct1_prime_selection_rule_scan.py](/Users/trentpalelei/Desktop/Math%20Ex/tools/ct1_prime_selection_rule_scan.py)

### Support for `high-min-e`

Tested results:

- exhaustive:
  - `n=5`, speeds `<= 15`: `147/147`
  - `n=7`, speeds `<= 14`: `420/420`
- targeted full-cover random samples:
  - `n=11`, max speed `220`: `500/500`
  - `n=13`, max speed `260`: `250/250`
  - `n=17`, max speed `340`: `150/150`
  - `n=19`, max speed `380`: `100/100`

Depth profile in these tests:

- all tested `n>=11` full-cover samples were depth `0` under `high-min-e`,
- the only depth `1` cases currently known remain the four exhaustive `n=7` prototypes.

### Support for `high-max-hold`

Direct checks on the same style of data also produced zero failures in the tested ranges.
So `S2` is at least as plausible as `S1`, and probably closer to the eventual analytic statement.

## 5. Why this is promising

The new rule matches a much cleaner mechanism than the raw `min-e` story.

If we select a HIGH thin residue:

- its owner does **not** drop it at the first reset,
- so the residue remains protected through an initial interval where other runners may already force a safe fibre,
- and if no safe fibre appears in that interval, we reach a more rigid second-reset geometry.

This explains why HIGH starts are so much more stable in the scans.

It also explains the old `n=7` hard family:

- the selected start is always the HIGH thin residue `(r^*, e^*) = (1, 6)`,
- it survives the first reset of `6`,
- and only later enters the single-transfer depth-`1` mechanism already understood from the prototype trace.

## 6. Candidate lemma chain

The current proof-track should therefore be:

### Lemma S-A (existence of a good HIGH thin start)

In the prime dropped-unit full-cover regime, either:

- there exists a HIGH thin residue, or
- the rare no-HIGH fallback family has a separate direct argument.

### Lemma S-B (holding-window privilege)

Let `r^* = a_high(e^*)` be the selected HIGH thin residue.
Then `r^*` persists until the second reset of `e^*`, so any obstruction to a safe fibre must survive the whole interval of length

`Delta_high(e^*) = L(2n-rho_{e^*})/(n e^*)`.

### Lemma S-C (failure before release)

If no safe fibre appears before the release time of the selected HIGH thin residue, the coverage schedule in that interval forces either:

- a direct gap earlier, or
- the known one-transfer prototype geometry.

This is where the four `n=7` hard tuples should be used as the model family.

## 7. Bridge to older work

This is not a brand-new object. It appears to be the corrected version of several older themes:

- the upper-zone arrival formulas in
  [lrc_lemma_br_minimax_proof_v1.md](/Users/trentpalelei/Desktop/Math%20Ex/reports/proofs/lrc_proof_pack_2026-03-01/lrc_lemma_br_minimax_proof_v1.md),
- the ownership / single-owner transition framing in
  [lrc_owner_set_harness_v2.py](/Users/trentpalelei/Desktop/Math%20Ex/reports/proofs/lrc_proof_pack_2026-03-01/lrc_owner_set_harness_v2.py),
- and the desynchronization viewpoint in
  [lrc_coverage_desync_master_v1.md](/Users/trentpalelei/Desktop/Math%20Ex/reports/proofs/lrc_proof_pack_2026-03-01/lrc_coverage_desync_master_v1.md).

So the current proof direction is not a fresh branch explosion. It is a convergence:

> the selected HIGH thin residue is the modern base-fibre version of the old protected witness / upper-zone owner.

## 8. Current best theorem target

The strongest candidate statement I would currently try to prove is:

> **CT.1-SH (selected HIGH-thin theorem, candidate).**
> In the prime dropped-unit branch with fully covered base fibre, choose a HIGH multiplicity-`1` residue maximizing the protected holding window `Delta_high`, with fallback to `min-e` only if no HIGH thin residue exists. Then the associated chain reaches a safe fibre before any sustaining repair chain can form.

This is still a conjectural theorem target, not a proved lemma.
But it is currently the cleanest analytically meaningful replacement for the raw `CT.1` and for the now-falsified universal `min-e` guess.
