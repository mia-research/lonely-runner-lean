# The method applied to what is open: interior witness normalisation

The ceiling sentence was: *every tool built so far locates extremal objects, and the remaining cases
admit only interior ones.* The method's instruction for that is not to invent a tool but to
**measure the interior witnesses exactly and ask why they sit where they do**. That had never been
done — only their non-extremality had been established.

## The measurement

For every witness `q` and every modulus `b`, record where `q mod b` sits inside `I(b) = [L,U]`,
normalised to `[0,1]`. Over 9,461 interior-only profiles, 255,953 witnesses, 1,453,739 residue
samples:

```
   [0.0,0.1)  17.63%  ##########
   [0.1,0.2)   8.21%  ####
   [0.2,0.3)   6.73%  ####
   [0.3,0.4)   8.99%  #####
   [0.4,0.5)   5.98%  ###
   [0.5,0.6)  10.16%  ######
   [0.6,0.7)   9.78%  #####
   [0.7,0.8)   6.54%  ###
   [0.8,0.9)   7.99%  ####
   [0.9,1.0)  17.98%  ##########
```

**U-shaped, and symmetric** (17.63 against 17.98 — the reflection). The "interior" witnesses are not
interior within their intervals at all: they **hug the edges**. Middle 40% of the interval holds
35.13% of the mass against 40% uniform.

## The family that measurement names

Call `q` an **edge witness** if `q mod b ∈ {L(b), U(b)}` for some modulus `b`.

> **Every profile that has a witness has an edge witness.**

| arm | profiles | no edge witness |
|---|---|---|
| divisor-closed, exhaustive `m < 320` | 51,295 | **0** |
| divisor-closed, exhaustive `m < 500` | 185,729 | **0** |
| divisor-closed, sampled `500 ≤ m < 4000` | 772 | **0** |
| **arbitrary moduli** (b need not divide m) | 4,000 | **0** |

The last row matters: the family is **not** specific to divisor-closed.

Structure of the supply: a minimum of **2** supplying `(b, end)` pairs, never 1; `L` and `U` split
**49.8% / 50.2%** — the reflection pairing `(b,L) ↔ (b,U)`. No single modulus always works (rank
spread 23.7% down to 8.0%; the smallest works 99.97%, not 100%).

## Why this is the right shape

`q ≡ L(b) (mod b)` means `8q+1` is the **smallest admissible value ≥ b** — the nearest lattice point
to the boundary of `b`'s bad interval, not the boundary itself.

- `ReachRule.witness_normalised` says the witness sits **at** a boundary.
- Integrality says it **cannot**: `q = m·x/8` is an integer only when `8 ∣ m` or `8 ∣ b`, which caps
  that family at 38.83%.
- The measurement says it sits at the **nearest admissible lattice point to** a boundary — and that
  always suffices.

So this is normalisation adapted to integrality, which is exactly what the ceiling demanded. It
covers 100% where the extremal family covers 38.83%.

## Status, and what it does not do

**`[VERIFIED]`, not proved** — roughly 242,000 profiles across four arms, 0 counterexamples.

It is a **normalisation**, not an existence proof: it is conditional on a witness existing and says
*where* to look, exactly as `witness_normalised` does. It does not by itself close any frontier.

What it changes: the remaining cases now have a named candidate family that contains a witness,
rather than only a proof that the previous family does not. Any existence argument for those cases
can be posed on 12 residue classes — `6` moduli × `2` ends — instead of on `ℤ/m`.

## One artefact caught

A first pass reported the supplying modulus was *always* the smallest and *always* the `L` end, at
100%. That was the enumeration order: the search iterated moduli ascending and tried `L` before `U`,
so the first hit was necessarily rank 0 and `L`. Re-measured without order bias, the ranks spread and
the ends split evenly. The `0` misses were the only real content of that run.
