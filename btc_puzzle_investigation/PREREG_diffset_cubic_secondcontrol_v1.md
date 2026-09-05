# PREREG — Cubic `E3` second-control reproduction (v1)

**Status:** rule + interpretation FROZEN before the new null is built. Reproduction of the fired
cell in [RESULT_diffset_cubic_v1.md]. Date: 2026-07-27. Inline pre-registration (statistic and
real value already frozen/public — this fixes only the new-null decision rule + interpretation).

> **CORRECTION (2026-07-27):** the pre-committed interpretation below used the phrases *"ceiling
> (unliftable by any control)"* and *"generic curve points"*. "Unliftable by any control" is an
> unproved overclaim and is **RETRACTED** — a reject *may* reflect the d-distribution, but that is a
> possibility, not a proven fact, and the interpretation is **open**. "Generic curve points" = uniform
> random valid curve points. See [RESULT_diffset_cubic_secondcontrol_v1.md] for corrected wording.

---

## Fixed inputs (already frozen; not re-opened)
- Statistic `E3` and real value **E3(real) = 13125** (public in RESULT v1). Not recomputed for the
  decision; recomputed once only as an integrity check.
- Original result: REJECT-HIGH vs the MT19937 matched control (98.4th pct, p≈0.033).

## New object: a generator-agnostic control
**Control-2 = uniform random valid secp curve x-coordinates** (`x` with `x³+7` a QR mod P), drawn
with an integer RNG (null model only — not on the signal path). No private key, no PRNG-of-d, no
bit-length structure. This is the population that *any* uniform-`d` generator's pubkey x-coords are
drawn from; it shares the "valid curve x" structure with the MT control and removes only the
bit-length matching. Null = 10,000 resamples of 82 distinct valid x, E3 each. Integer-exact path.

## Frozen decision rule (before seeing where 13125 lands vs Control-2)
Two-sided empirical α=0.05 region from the Control-2 null: reject-HIGH iff E3(real) > its 97.5% order
statistic, reject-LOW iff < 2.5%. Report percentile + rank-p.

## Validity gate on Control-2 (must pass or the control is void)
Control-2's E3 null must reproduce the MT null's shape — Exp(mean ≈ 3321), 97.5% ≈ 11997±noise. If
it does, bit-length is confirmed irrelevant to the E3 null (pubkey-x pseudorandom in d) and Control-2
is a valid, stronger-independence null. If Control-2's null differs materially from MT's, that
mismatch is itself the finding (bit-length affects the cubic-difference null) and is analyzed
separately.

## Pre-committed interpretation
1. **Reject vs Control-2 AND Control-2 null ≈ MT null** → the reject is not MT-specific and not a
   bit-length artifact. It reflects a real pubkey-set property vs generic curve points. **Ceiling
   (unliftable by any control):** the pubkey set is a deterministic image of the d set, so this most
   naturally reflects the real key **generation / d-distribution** — off-limits for curve/ECDLP
   conclusions per `feedback_no_prng_generation_side`. Remaining statistical caveat: 1 of ~7 tests,
   p≈0.03, not MC-corrected; n=82 fixed, no independent real replication.
2. **No reject vs Control-2** → the MT reject was tied to the bit-length-matched MT construction;
   downgrade the cell — not a robust property.
3. **Control-2 null ≠ MT null** → bit-length affects the E3 null; a separate curve-structural
   observation, analyzed on its own.

## Grade impact
This reproduction does **not** upgrade the `[EMPIRICAL — p≈0.033, not MC-corrected]` grade. Its only
job is to close the "MT-specific" escape route and state the generation-side ceiling.
