# Findings v18 — the thermodynamic lens: secp is a critical, single-well chaotic system

**Date:** 2026-07-16. Lens (per the programme's substrate view): equidistribution = maximum
entropy; `T(a,b)=Σ_d e_p(bx_d)e_n(ad)` = partition function; the leak = available work behind a
second-law (DLP) barrier. Scripts: inline Porter–Thomas test; `conservation_spectrum_v1.py`.
The lens is scaffolding, not claimed physics — but it made 3 predictions and all 3 resolved.

## [PROVED] The curve sits exactly at criticality
Weil's theorem (RH for curves / finite fields) puts Frobenius `π_p,π̄_p` on `|π|=√p` — the
critical circle. So secp is *at* a phase transition, not near one. Consequences: no bulk order
(no extensive leak) but scale-free, slowly-decaying correlations — which retroactively explains
the aligned-leak's `~1/√log p` decay (log-corrections = the marginal/critical signature).

## [EMPIRICAL, p≤2089] Magnitude spectrum is Porter–Thomas — thermal, and RIGID
`|T(a,b)|²/mean` intensities vs the exponential (Porter–Thomas / quantum-chaotic) law:

| p | E[I²] (2) | E[I³] (6) | E[I⁴] (24) | P(I>5) (.0067) | maxI |
|---|---|---|---|---|---|
| 433 | 1.98 | 5.93 | 23.1 | .0083 | 8.5 |
| 1051 | 2.00 | 5.92 | 22.2 | .0068 | 8.1 |
| 2089 | 2.00 | 5.97 | 22.7 | .0071 | 8.1 |

Matches Porter–Thomas across 3 moments; the tail is if anything **lighter** than thermal
(bounded max ≈ 8×, sub-exponential) = spectral rigidity, the GUE/critical signature. **No scar,
no condensed mode, no localized weakness in the magnitude spectrum** ⇒ hunting magnitude
structure is closed. (Likely follows from Katz equidistribution for these families — `[CITED, verify]`.)

## [EMPIRICAL, p≤2503] No metastable soft mode / no approximate conservation law beyond μ₆
Coarse-grained transfer (Koopman) operator of a computable label under `P→P+G`; eigenvalue near
the unit circle = (approximate) conservation = slow phase-coherence = a metastable soft spot.

- **μ₆-covariant label:** `|λ₂|` = 0.39→0.25→0.15 (p=433→1051→2503), ~1.8× the shuffle floor but
  **decaying at the thermal `1/√n` rate** — the μ₆ conserved charge gives a bounded short-range
  correlation that itself thermalizes normally. No persistent mode.
- **μ₆-invariant label (beyond μ₆):** real/shuffle → **0.89, 0.96** at p≥1051 (at the thermal
  floor; the 3.9 at p=433 was small-p noise). **Nothing beyond μ₆.**

⇒ The transfer spectrum is fully mixing beyond the one conserved symmetry (μ₆); **no metastable
basin.**

## Synthesis (the arc, in the lens)
**secp is a critical, maximally-scrambled chaotic system that is thermal in magnitude
(Porter–Thomas, rigid) and CUE-random in phase beyond its single conserved charge μ₆.** Its
security is not a wall but a thermodynamic cost: the ordered microstate (the key) exists and is
extractable *in principle* (v14: the aligned readout leaks 28×, `H(d|P)=0`), but reading it is
irreversible work — the DLP. **The free-energy landscape is a single well: equilibrium (generic)
→ ground state (aligned = key), with no metastable trap between**, so there is no cheap
partial-extraction. This *closes the cheap-partial-shadow lead* — empirically, scoped to p≤2503 —
in the way the lens predicted.

## Grades
Weil-criticality `[PROVED]`. Porter–Thomas fit + no-soft-mode `[EMPIRICAL, matched null +
1/√n scaling, p≤~2500]` — not proven at secp; the synthesis is a *framing* of proved+empirical
pieces, not a theorem. The lens is a heuristic that generated the tests; the tests carry the grades.

## ★ REVIEW CORRECTION (self-audit) — the v18 closure was assumed, then earned
The Porter–Thomas and conservation-spectrum tests above were computed on **x-only** objects
(`|T(a,b)|²` uses `e_p(bx_d)`, no y; the transfer labels were built from `eis(x_d)`, no y). But
the v16 shadow — the one positive of the arc — lives in the **(x,y) joint** channel (the *odd
half* x cannot see). So "closes the cheap-partial-shadow lead" was a **premature dismissal: I
closed a joint-channel question with x-marginal tests.** Re-run on the correct channel:
- **Joint magnitude** `|U(a,b,c)|²`, `c≠0`: E[I²]=1.995/1.998, E[I⁴]=23.5/23.9 — Porter–Thomas,
  thermal, same as x-only (higher `maxI≈12` explained by ~14× more samples). **No scar.**
- **Joint transfer** label `(x-cell × y-parity)`: `real/shuffle` = **1.09–1.15** (vs 1.8–2.3 for
  x-cell) — *more* thermal; y adds a fast-mixing coordinate, no soft mode.

⇒ The closure **holds on the correct channel** — but it is now *earned*, not assumed.
**SCOPE (do not re-dismiss):** the joint soft-mode test used **y-parity only**, not a general
y-readout; and the x-cell `~1.8×` prefactor was *attributed* to μ₆ **without checking the
eigenvector** (consistent with μ₆, and `|λ₂|` decays thermally `1/√n`, but the mode identity is
unverified). Both are un-shut at the finer level.

## What remains genuinely open (unchanged by this)
The v14 leak (aligned readout) still exists and is real; only its *cheap partial* version is now
(empirically) closed. Untouched: secp's actual p; the `T_y` odd-half max-bound; `S₄⁺` Gröbner;
non-homomorphic amicable. And whether the `~1/√log p` critical decay is exactly log — the one
quantitative critical-exponent claim, still `[HEURISTIC/PARTIAL]`.
