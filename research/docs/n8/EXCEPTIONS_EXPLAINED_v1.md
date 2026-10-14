# The two exceptional sets: what is happening, and why

`AP_GENERALISATION_v1` reported two claims failing on small fractions and left the exceptions
unexamined. Examined here. **They are two different phenomena, and one is fully explained by a
theorem.**

First, the figures, since they were misread once: the successes were `97.01%` and `98.4%`, so the
exceptional sets are **2.99%** and **1.61%** — not 12%. (An earlier "distinct moduli" count also
conflated the two questions by accepting any witness with two tight constraints; redone cleanly, the
sets are `A = 595` and `B = 321` of 19,880, overlapping in 205.)

## Set A — no witness on both patterns (2.99%)

**Explained.** The clear residues at modulus `b` form `I(b) = [⌈(b−1)/8⌉, ⌊(7b−1)/8⌋]`. At `b = 2`
this collapses to a **single residue**, `L(2) = U(2) = 1`, and computation shows **`b = 2` is the
only modulus with `L(b) = U(b)`** for `2 ≤ b < 500`.

So a profile containing modulus 2 has *every* witness on both patterns automatically — the
coincidence is degenerate rather than arithmetic.

> **`Degenerate2.two_degenerate` / `two_both_patterns` / `contains_two_coincides`** (Lean,
> axiom-clean; the first depends on no axioms at all): at `b = 2`, being clear, being on the `+1`
> pattern, and being on the `−1` pattern are the **same condition**.

**Measured consequence, exactly as predicted: 0 of the 595 A-profiles contain modulus 2.** Further,
`min(bᵢ) ≥ 3` in **100%** of A against 59.3% elsewhere, and `min(bᵢ) ≥ 4` in 80.5% against 36.1%.

**A is not about scarcity.** A-profiles carry **12 to 20 witnesses** each. The supply is ample; what
fails is that the `L`-witnesses and the `U`-witnesses never land on the same point. Removing the
degenerate modulus removes the free coincidence, and nothing forces one in its place.

## Set B — no doubly-tight witness (1.61%)

**A different cause: scarcity.** B-profiles are witness-poor — the witness-count distribution starts
at `2, 4, 6, 8` where A's starts at `12`. With two or four witnesses there is simply little room for
one of them to be tight twice. And 36.1% of B *does* contain modulus 2, so the A mechanism does not
apply: modulus 2 hands them one tight constraint for free, and there is no second.

## Why the distinction matters

The two exceptional sets are nearly opposite:

| | A (2.99%) | B (1.61%) |
|---|---|---|
| contains modulus 2 | **0%** | 36.1% |
| witness count | 12–20 | 2–12 |
| cause | no degenerate modulus, no forced coincidence | too few witnesses |

An argument that repaired A — say by supplying a coincidence — would leave B untouched, and an
argument that produced more witnesses would leave A untouched. **They must be handled separately.**
That is worth knowing before attempting either, and it is the kind of thing that stays hidden when a
complement is recorded as a percentage rather than examined.

## Status

`Degenerate2` is proved and axiom-clean (3 declarations; witness file now 51). The characterisation
of A as "no modulus 2" is a **sufficient** condition for non-membership, verified exactly; it is not
a full characterisation of A, since 95% of profiles with `min(bᵢ) ≥ 3` are *not* in A. B's scarcity
explanation is `[VERIFIED]` only. Existence at order 8 is unchanged.
