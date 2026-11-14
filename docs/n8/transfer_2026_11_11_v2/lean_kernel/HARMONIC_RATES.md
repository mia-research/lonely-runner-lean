The entry points are `Fresh.Harmonic.five_rates` and
`Fresh.Harmonic.six_rates` in `Fresh/HarmonicRates.lean`. They cover
mixed primitive harmonic profiles through 10 for five fast readings and
through 5 for six fast readings. The fast rates have the form
`p[i] * frequency + b[i]`, with `|b[i]| ≤ B`. Five fast readings
allow slow readings `1, a` and either pinned window when
`frequency ≥ max (40*a) (100*B)`. Six fast readings allow the slow
reading `1` and the first pinned window when
`frequency ≥ max 20 (100*B)`.

Run `./check_kernel.sh` after building or
fetching Mathlib. The optional argument is the Lean search path for a
compatible Mathlib build. The script builds the kernel extract and prints the axiom dependencies. The soundness and lifting lemmas use the
standard Lean axioms. Each final rate theorem also uses the
`native_decide` axiom for its finite replay. The four short relations
reduction and the global cascade cutoff are separate obligations.

The [harmonic cutoff note](../N8_HARMONIC_CUTOFF.md) gives a paper proof of a
finite reduction for the buffered fast sectors and specifies the
remaining line and plane cases.
