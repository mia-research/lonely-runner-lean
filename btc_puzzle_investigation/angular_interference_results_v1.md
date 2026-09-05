# Angular / Interference Shadow — Results v1 (2026-07-13)

**Hypothesis (user).** The public point looks random, but a curve-native ANGLE
(the CM / μ₆ sextic phase of the coordinates) might hold a coherent shadow of the
scalar `d` that only reveals itself when accumulated across many keys — an
interference pattern kept ~180°/near-random by the twist geometry.

**Instrument.** `angular_interference_scaling_v1.py`. Exact arithmetic
(CLAUDE.md); μ₆/μ₃/μ₂ characters via `x^((p-1)/k) mod p`; phase sums as EXACT
Eisenstein integers in ℤ[ω] with exact norm `N(a+bω)=a²−ab+b²`. Angles tested:
χ₆(X), χ₆(Y), χ₃(X), χ₂(Y) (the quadratic "180°" phase). Sets: **gen256**
(uniform d, non-degenerate GLV — the regime the ≤160-bit 100k never reached),
**gen130** (puzzle frontier), **real82** (creator selection), **d100k**
(known-MT through the same pipeline). M up to 40 000.

## ARM A — coherence / accumulation (does the shadow build up?)
Statistic `ratio = N(ΣᵢuΘᵢ)/M`: ~1 under a uniform phase marginal (incoherent
random walk); grows ~M under a coherent shadow. Rank p vs uniform-random baseline.

**Result: NULL on every angle, every set.** All verdicts "uniform"; smallest
rank_p = 0.07 (gen256 χ₃X) — never < 0.01. Ratio bounces in [0.1, 2.9] with no
monotone growth from M/10 to M (e.g. gen256 χ₆X 0.65→2.18 but χ₆Y 1.23→0.18).
The phase sum is a random walk: the μ₆/CM phase marginal is uniform, so it does
not accumulate. **The "interference shadow" does not build up for these
curve-native angles.**

## ARM B — conditional d-leak (does the angle decode d?)
Bias-corrected MI `I_c` + permutation z between angle and targets
`d mod {2,3,5,6,7}` and mid-bit, with the power-scaling classifier
(plateau + z~√M ⇒ signal; 1/M decay ⇒ noise).

**Result: NULL.** All I_c ≤ ~1e-4 bits. The classifier's z>3 gate fired twice
(gen130 χ₂Y–d%2 z=3.66; d100k χ₆Y–bit_mid z=3.06) out of 96 tests — both
**confirmed noise** by the audit (`_ang_audit.py`): across 3–5 independent seeds
the z wanders in sign and never grows with M (the b256 bit_mid "peak" z=4.52 at
M=20k *falls* to 1.10 at M=40k; a real plateau rises with √M). Neither reproduces
on the clean gen256 set. Multiple-comparison false positives.

## Verdict (scoped, conditional)
Under the CM/μ₆/μ₃/quadratic phase functionals of (X,Y), tested for
marginal-coherence accumulation and for MI with d mod {2,3,5,6,7}/mid-bit, at
M ≤ 40 000, floor ~1e-5 bits, with firing controls (uniform baseline gives
ratio~1; power_scaling classifier fires on planted 2–5% leaks): **no coherent
angular shadow and no decodable d-leak** — on generated-256 (non-degenerate GLV),
generated-130, real-82, and 100k-MT alike. Consistent with the standing result
that per-point readouts of (X,Y) are Farey/curve-generic; extends it to the
accumulation/interference framing and to the non-degenerate 256-bit regime the
prior 100k battery could not reach.

## Not covered by this run (the one clean remaining variant)
The **Eisenstein 2-D LIFT angle** — the canonical 2-D ℤ[ω] representative
("section") of a point, distinct from the affine χ₆(X) — is the object where the
prior "sectors 4,10 ≈3×" non-uniformity was recorded (secp arithmetic study). If
non-uniform, Arm A would be COHERENT there — but that is **curve-fixed CM
geometry** (identical for every key, present for uniform-random d), so it cannot
recover d; only a real-vs-generated difference or a conditional MI would be a
key/selection signal, and Arm B already bounds the latter null over the raw
coordinate characters. Buildable as a follow-up; low recovery prior.
