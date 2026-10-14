# C1-mixed — the move off a reference instant

2026-09-15. A swing at the branch that matters: mixed readings, 68% of runners at span 600 and
the only place where C1 asks more than LRC(`n`). What follows is a **construction** — eight
explicit candidate instants, no search — and its measured reach. **It is not a proof.**

---

## 1. The construction

At a reference instant `u = p/8`, `p` a unit mod 8, each runner reads phase `frac(s_j p/8)`.
Call it **clear** when that phase lies in `[1/8, 7/8]` and **blocked** otherwise. Move by `ε` in
one direction:

| | moving right | moving left |
|---|---|---|
| clear `j` stays clear while | `s_j ε ≤ 7/8 − phase` | `s_j ε ≤ phase − 1/8` |
| blocked low (`phase < 1/8`) needs | `s_j ε ≥ 1/8 − phase` | `s_j ε ≥ phase + 1/8` |
| blocked high (`phase > 7/8`) needs | `s_j ε ≥ 1 − phase + 1/8` | `s_j ε ≥ phase − 7/8` |

Take `ε` = the largest requirement over the blocked runners — the earliest instant at which all
of them have cleared — and check it against the smallest room over the clear ones. Eight
candidates in all: four units, two directions.

**The two directions are not independent for an integral reading** — `u ↦ 1−u` pairs them — but
for a mixed reading they are, because the palindrome needs integrality to preserve the reading.

## 2. Reach  `[VERIFIED]`

Every instant returned was re-checked to be a genuine isolation instant lying in `[1/8, 7/8]`;
no exceptions, at any span.

**On the open mixed population** — mixed reading, and `d_max > 7·d_min` so the ratio condition
does not already settle it:

| span | runners | settled | |
|---|---|---|---|
| `[0, 120)` | 5,544 | 5,398 | **97.4%** |
| `[0, 600)` | 6,551 | 6,377 | 97.3% |
| `[0, 3000)` | 6,741 | 6,541 | 97.0% |
| `[0, 20000)` | 6,821 | 6,610 | **96.9%** |

Stable across a 170-fold range of span.

**On everything**, 24,000 runner-instances at span 600:

| route | share |
|---|---|
| the move off a reference instant | **68.1%** |
| the ratio condition `d_max ≤ 7·d_min` | 29.3% |
| **open** | **2.5%** |

Against `C1_STATUS_v1` §1's **31.4%** settled, this is **97.5%**.

## 3. What it is not

**Not a proof.** The construction's feasibility — that the largest blocked requirement fits inside
the smallest clear room, and that the resulting point really clears everything rather than passing
through and re-blocking — is *checked per case*, not characterised. 2.5% of runners fail it.

So this is a construction with a measured hit rate, not a lemma. What would make it one is a
condition on the reading under which the requirement is guaranteed to fit, in the way
`C1_INTEGER_CONSTRUCTION_v1` §2 gives one for the integral blocked case (`s_j ≤ S(7−c_j)`).

## 4. Where it fails

The failures are concentrated, and nameably so: four of the first five carry a runner at distance
**exactly 0** from a multiple of 8 — an exact lap-line sitter, `s_j ≡ 0 (mod 8)`:

```
s = 1, 11/9, 8, 107/9, 119/9, 76/3, 31            distances 1, 11/9, 0, 35/9, 25/9, 4/3, 1
s = 11/2, 1, 61/2, 48, 54, 217/2, 134             distances 5/2, 1, 3/2, 0, 2, 7/2, 2
s = 305/2, 185/2, 60, 40, 33/2, 1, 65/2           distances 1/2, 7/2, 4, 0, 1/2, 1, 1/2
s = 165, 145, 269/2, 245/2, 64, 21, 1             distances 3, 1, 3/2, 5/2, 0, 3, 1
```

An exact sitter needs a full `1/8` of movement to clear, which is the largest requirement the
construction can be handed; when a second runner is also tight, the room runs out. That is the
same obstruction the integral branch has, arriving in the mixed branch through the one runner
whose reading happens to be integral.

## 5. Status

`[PROVED]` §1's inequalities — each is the arithmetic of a phase moving inside or out of the band.
`[VERIFIED]` §2's reach, four spans, every instant re-checked.
**`[OPEN]` C1.** This settles 97.5% of runners by construction and characterises none of it. The
2.5% is a named population — exact lap-line sitters with a second tight runner — not a residue.

**n = 8 is not proved. C1 is not proved.** What changed is the size and the shape of what is left:
from 68.6% open and unstructured, to 2.5% open and concentrated on a stated configuration.
