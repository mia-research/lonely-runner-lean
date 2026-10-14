# Two opposing patterns, two opposing reflection centres

The owner's hunch — that the reflection obstruction relates to the two opposing patterns — is
correct, and it is computable. Mapping it extends "never a singleton" from a third of the category to
all of it, though the extension is measured rather than proved.

## The centre is determined by the pattern type

The general reflection is `q ↦ c − q`. It preserves the constraint at modulus `b` exactly when

> `c ≡ L(b) + U(b) (mod b)`.

Computing those sums (0 exceptions for `b < 2000`):

| | `L(b) + U(b)` | required `c` |
|---|---|---|
| `b mod 8 ∉ {0,1}` | `b` | `c ≡ 0 (mod b)` |
| `b mod 8 ∈ {0,1}` | `b − 1` | `c ≡ −1 (mod b)` |

**The two pattern-types demand opposite centres.** Since every modulus divides `m`:

- all moduli good → `c = 0`, i.e. the familiar `q ↦ m − q`;
- all moduli obstructed → `c = m − 1` works, because `b ∣ m` gives `c ≡ −1 (mod b)` for free;
- **mixed → neither**, and no `c` exists at all: `c ≡ 0` and `c ≡ −1` mod a common `b ≥ 2` is
  impossible.

**Measured, exactly as predicted:**

| | profiles | reflection acts | `|S|` even |
|---|---|---|---|
| all good, `c = 0` | 6,728 | **100.00%** | 99.60% |
| all obstructed, `c = m−1` | 30 | **100.00%** | **100.00%** |
| mixed | 13,122 | **0.00%** | 59.75% |

So the obstruction at `b ≡ 0, 1 (mod 8)` is not that the reflection fails — it is that the **centre
moves**, and a mixed profile has no single centre to move to.

## Mixed profiles: closure is not what is needed

Mixed profiles still satisfy `|S| ≥ 2` everywhere. Two candidate mechanisms:

- **two consecutive solutions** — only 59.52%, so not it;
- **a surviving orbit**: some `q ∈ S` with `m − q ∈ S` and distinct — **100.00% of all 19,880
  profiles**, mixed included.

Full closure was never necessary. One surviving orbit gives `|S| ≥ 2`, and `m−q` supplies one every
time. The failure of global closure is real but irrelevant to the conclusion.

## What a surviving orbit is, exactly

Let `S' = {m − q : q ∈ S}`. Then `q ∈ S'` iff `q mod b ∈ [b−U, b−L]`, which is `[L,U]` for good
moduli and **shifted up by one** for obstructed ones. Hence

> **`S ∩ S'` is the original system with each obstructed interval shrunk by one residue**, `[L,U]`
> becoming `[L+1, U]`.

**Verified: 0 mismatches over 14,257 profiles, and the shrunk system was never empty.**

So "a surviving orbit exists" is exactly "the shrunk system is solvable" — one residue tighter at
each obstructed modulus, and nothing else changed.

## Status

**Proved:** `|S| ≥ 2` when a reflection centre exists and `S ⊄ {c/2}` — now covering both pure cases,
`6,758` of `19,880` (34.0%), up from 33.8%.

**Measured, not proved:** the surviving orbit, hence `|S| ≥ 2`, on all 19,880 including every mixed
profile. Reducing it to the shrunk system does not prove it — the shrunk system's solvability is
itself an existence question, one residue harder than the original. That is an honest description of
where it stands, not a proof.

Existence at order 8 is unchanged.
