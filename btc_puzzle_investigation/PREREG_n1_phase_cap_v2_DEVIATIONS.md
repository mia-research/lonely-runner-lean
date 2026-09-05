# DEVIATIONS — `PREREG_n1_phase_cap_v2.md`

*2026-07-24. Six. Filed with `RESULT_n1_phase_cap_v3.md`, not after a challenge.*

## D1 — ⚠ MY parity bug in N-PERM; caught by a forced check I had registered

`h(λd) = h(d)` holds in **both** strata, but `h(−d) = χ₂(−1)h(d)`, so `h` is **odd** at
`p ≡ 3 mod 4` (ODD) and **even** at `p ≡ 1 mod 4` (EVEN). The first run applied the **odd**
orbit-sign convention to both, so for all 60 EVEN primes the null did **not** carry the symmetry the
readout has by definition — the exact defect already on this record ("a null must carry the object's
own symmetry").

**Caught by `C-ORBIT`**, which came back `60/60` ODD and **`0/60` EVEN**. Confirmed directly:
at `p=32497`, `h(−d) = +h(d)` TRUE and `h(−d) = −h(d)` FALSE. **`S_y` is unaffected** — it is computed
from `h` directly and never touches the orbit structure, so `Nviol = 0` and every `S` value stand.
Rebuilt with per-stratum parity (`n1_phase_cap_v2_nullfix.py`): **`C-ORBIT` now 120/120**, purity
`≤6.4e−16`, Parseval `≤1.3e−15`. This is the registered forced check doing its job.

## D2 — N-PERM reads `4.24`, F7 predicted `≈4.65` (~9% low)

Not a halt (the halt condition is `S ≤ 2`; observed min `3.341`, `0/120` at or below 2), but the
derived prediction over-shoots the measurement by ~9% in both strata. Recorded so the F7 model is not
treated as exact.

## D3 — `ε*_pred` is wrong by ~20×, and `ε*` is bracketed from above only

The spec's derived fragility prediction `ε*_pred = (1−ρ*)/2` gives `0.45–0.50` at these primes.
**Measured `ε* ≤ 0.02` at 20/20** — the derived model is off by more than an order of magnitude.
Since the pre-committed reading keys on `ε* ≤ 0.10` (fragile) vs `≥ 0.25` (near-vacuous), the
measurement lands far inside "fragile" and the model error does not change the branch — but the model
must not be reused. **Also: `0.02` was the smallest level swept, so `ε*` is bounded above, not
located.** A finer grid would be needed to state it.

## D4 — seed scheme differs from the spec's

The spec fixes `SHA-256("n1phasecap-v2" | p | stratum | arm | level | replicate)`. The run used
`SHA-256("nperm"|p)` / `default_rng(p)`. Deterministic and reproducible, but not the specified stream.

## D5 — one N-PERM draw per prime, not a per-prime replicate distribution

`R = 1` null draw per prime. The null is therefore used as a **scale and halt check** (pooled over 120
primes), not as a per-prime verdict null. No per-prime `z` against N-PERM is computed or claimed.

## D6 — ARM-3 not run; the phase language remains a proxy

The weight-1 premise stays `[VERIFIED at p = 13, 43 only — six unforced cells]`. ARM-3 (extending it
to `p ≤ 100`) was not run, so every phase-language sentence in the result carries the spec's mandatory
proxy tag: `S_y ≤ 2` is object-level for `max|V| ≤ 2√p`, **not** for `|sin θ₁+sin θ₂| ≤ 1`.
