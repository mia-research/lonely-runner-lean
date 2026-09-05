# PRE-REGISTRATION v4 — amendment to v3 (R-CONTIG null correction)

**Status: `[FROZEN on SHA below]`. Amendment to `PREREG_shortscalar_sum_object_v3.md`**
(frame layers §1/§6/§7 inherited unchanged from v3, SHA
`f3d26cc8f13792f4cdc39edcae8ae08279a88f5f45801a3ff6cdf492ca446bb0`; the experiment-designer gate
cleared that frame). This amendment overrides **§2 (screen), §3 (null), §5 (bound), §9 (freeze)** for
the **R-CONTIG** object only, driven by an empirical finding. R-BAND is unchanged.

**Driver:** `RESULT_shortscalar_sum_stageA_v1.md`. The iid random-point null is **invalid** for the
deterministic-interval R-CONTIG: `|Σχ|²` under a with-replacement bootstrap acquires an `L²·δ²` mean
from the pool's finite-sample class imbalance `δ~1/√pool`, swamping the O(L) variance at large L; and a
deterministic orbit has lower discrepancy than iid. Both drove Stage A's arms into a spurious low tail.
The gate had already named the fix in principle (a structure-matched null); this promotes it.

## §3′ (override) — R-CONTIG primary gating null
- **PRIMARY gate = random-location interval:** a real interval `{[s]G : s∈[s₀,s₀+L)}` at `s₀` uniform
  in `[2, n)`, same L, same statistic. It **shares the arm's forced structure** (equidistribution, the
  true class distribution) and differs from the band arm ONLY in `s₀`'s location — so it isolates
  bit-length/location effects, which is the leakage question. This is a **like-to-like** null, immune
  to the pool-imbalance and equidistribution artifacts (both sides are real intervals).
- **The iid random-point null is WITHDRAWN for R-CONTIG** (kept only as a reported reference, and only
  for R-BAND where sampling is genuinely iid-like). **Forbidden** `F_p`-integer null unchanged.
- **C-NEG (calibration):** extra random-location intervals must rank ≈uniform vs the null (they ARE
  null draws → exchangeable → uniform by construction; confirms no implementation bug), tail within the
  two-sided binomial band.

## §2′ (override) — two-sided screen
Against a like-to-like interval null a band effect can push `|Σχ|²` **either way** (extra
cancellation-breaking → high; extra cancellation → low; Stage A showed the low direction is live). So:
- **SCREEN (two-sided):** a cell screens iff its rank p ≤ 0.005 **or** ≥ 0.995 (99th two-sided).
- **GATE = OOS:** a screened (k, readout) cell is a candidate only if it screens in the **same tail on
  ≥5 independent fresh seeds** (band `s₀` and the null both re-drawn). All per-cell p **uncorrected**;
  Holm reported secondary only.

## §5′ (override) — the bound, empirically calibrated
`ε*` (smallest coherent single-class cubic bias detectable) is fixed **empirically** by a C-PLANT power
scan against THIS null: inject `δ ∈ {0.5%, 1%, 2%, 4%}` into a random-location interval and report the
smallest `δ` that reaches the null's 99th. **Report `ε*` as that measured firing threshold** ("excludes
a coherent cubic bias ≥ ε* at this L; BLIND below") — not the crude `2√V₉₉/L` estimate (which used the
inflated iid null and is withdrawn as a number).

## §9′ (override) — freeze
Frozen: R-CONTIG primary null = random-location interval; two-sided 99th screen + same-tail 5-seed OOS;
`ε*` from the C-PLANT power scan; C-GLV forced-zero + C-NEG uniform-rank + C-PLANT scan controls;
L (this run 5000, deeper L a logged follow-up); R_null ≥ 300; seeds recorded. Executing script:
`shortscalar_sum_stageA_v2.py`. **Open, not tested by this null** (recorded honestly): a
**location-INDEPENDENT** interval effect common to all `s₀` is invisible to a random-location null; its
leading candidate (lower-than-iid discrepancy) is a generic/near-artifactual property, but a genuine
location-independent secp effect would require a different instrument and is NOT closed here.
