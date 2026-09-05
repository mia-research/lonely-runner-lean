# RESULT — "alignment-key leakage" thesis, audited against ground truth

Serious test of the graded-leakage claim: `(j,s)` 100% leaked; carry `c` shadowed by a
±0.58 trace correlation; boundary `ε` perfectly leaked inside the `3/16` Eisenstein
inradius; therefore cost collapses to searching the constrained `c` distribution.

Same ground-truth GLV curve (`y²=x³+2 / F_100003`, `n=99667`, `λ=30642`; every dlog known).
GLV short basis via Gauss reduction: `v1=(13,−309)`, `v2=(−322,−13)` (`|v|≈√n≈316`),
so the balanced decomposition `d=d₁+d₂λ (mod n)` and the λ-carry `c=d₂` are exact.
Harness: `align_key.sage`. Positive controls fired (`MI(d%3;d%3)=1.585`, `corr(c,c)=1.0`);
every elevated MI checked against a **shuffle baseline**.

**The through-line question for all three components:** is the localizing quantity
estimable **from the public point `P`**, or only from `d`? A shadow you can see only by
already holding `d` casts nothing.

## Component 1 — `(j,s)` orbit phase: leaked, but vacuous
Computable from `P` via `F=χ₃(x)y`: **yes**. Bits it pins about the secret:

| `MI((j,s) ; ·)` | value | floor |
|---|---|---|
| `d mod 3` | 0.00008 | ~0.0005 |
| half-plane `[d<n/2]` | 0.00005 | ~0.0005 |
| carry `c` (mod 16) | 0.00052 | ~0.0005 |

"100% leaked" is **true and vacuous**: `(j,s)` labels the orbit *presentation*, and
constrains `d` by ≈ 0 bits (consistent with the banked "orbit readout ≠ secret" trap).

## Component 2 — the ±0.58 trace↔carry correlation: not found, and not observable
| pair | corr / MI |
|---|---|
| B1 hidden↔hidden: `corr(d₁, c)` | 0.0014 |
| B1 hidden↔hidden: `corr(d mod3, c)` | 0.0000 |
| B2 **observable**↔hidden: `corr(χ₂(y), c)` | −0.0050 |
| B2 **observable**↔hidden: `corr(χ₃(x), c)` | 0.0000 |
| B2 `MI(all observables ; c mod16)` | 0.132 → **shuffle 0.135 = pure bias**; chars-only 0.0011 |

No ±0.58 in any pair — hidden-vs-hidden or observable-vs-hidden. The single elevated MI
was estimator bias (97-bin feature), killed by the shuffle control. There is **no
observable channel to the carry**; the "massive statistical shadow" is absent at this
scale under the natural definitions.

## Component 3 — `ε` "perfectly leaked inside the `3/16` inradius": refuted twice over
- Fraction with lift-norm `s_lift<3/16`: **0.68** (normalization-dependent — see caveat).
- **You cannot select the inside-disk keys from `P`:** `MI(observables ; [s<3/16]) =
  0.0099 → shuffle 0.0089 = bias floor`. The gate condition is not observable.
- **`ε` is not leaked even inside the disk:** there `H(ε)=0.994 bit`, `mean 0.547`,
  `MI(observables ; ε)=0.00016`. `ε` is ≈ a full random bit and ≈ independent of `P`.

So even granting the geometry, the leak is unusable: its enabling condition is invisible
from public data, and the bit it would leak stays hidden anyway.

## Verdict (scoped, ground truth, `n≈10^5`)
The thesis needs the localizing quantity (`c` / `ε`) to be estimable from the public
point. Measured: it is not — for the carry (Comp 2), for the boundary indicator, and for
the inradius gate (Comp 3); and the freely-leaked part (`(j,s)`, Comp 1) constrains `d`
by ≈ 0 bits. Every "shadow" here is a relation among `d`-derived quantities, computable
only by someone who already holds `d`. **No sub-cryptographic cost reduction is exhibited.**
This refutes the mechanism at this scale; it does not prove secp secure in general (ECDLP
assumed-not-proven).

## Caveats / owed (stated, not buried)
- **Definitions.** "Isotypic trace `ℓ(d)=dlog_W(Q_W(P))`" and "reciprocal-floor carry"
  are underspecified in the source; I used `c=d₂` (balanced GLV λ-carry) and natural
  observable traces. If a *different, genuinely point-computable* trace is meant, Comp 2
  should be re-run with it — but note any trace defined via `dlog_W` is itself a discrete
  log (hard), so "measuring the trace" cannot be `O(1)`. Flag, like the prior T2.
- **Inradius normalization / scale.** `3/16` threshold and the 0.68 inside-fraction depend
  on the norm normalization, and the "dispersed 256-bit" regime is not reached at
  `n≈10^5`. The decisive results (gate not observable; `ε` not observable inside) are
  robust to normalization.
- experiment-designer pre-registration audit not run this turn — [PROVISIONAL] on graded
  slots; the observability nulls stand on their shuffle controls + positive controls.

Reproduce: `btc_puzzle_investigation/align_key.sage`.
