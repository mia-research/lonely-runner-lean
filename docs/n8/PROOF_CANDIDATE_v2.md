# n = 8 — proof candidate, v2

2026-09-12. Supersedes `PROOF_CANDIDATE_v1.md`. **Individual isolation throughout.**

v2 changes one thing and it is the framing of the gap. v1 ended by calling the transit
argument a one-dimensional reduction leaving seven unbounded coordinates, and proposed an
induction over them. **That was wrong**, and §1 says why.

## 0. Architecture (unchanged from v1)

| step | statement | status |
|---|---|---|
| **S1** reference | `π` a complete residue system mod 8 ⟹ globally isolated at `t = p/8`, `φ(8)=4` times | `[PROVED]` |
| **S2** partial reference | residue of `i` unique mod some `m ≤ 8` ⟹ lonely at `t = a/m` | `[PROVED]` |
| **S3** parity | `i`'s parity class has ≥ 5 members, `16 ∤ d` ⟹ lonely at `t = a/16`; a `π`-condition, survives every deviation | `[PROVED]` |
| **S4** transit | loneliness at `t = a/m` depends on a sliding speed only through `e mod m` | `[PROVED]` |
| **S5** resolution | `|G(e)| ≥ (3/4)|G_F| − N_F/(2e)` | `[PROVED]` |
| **S6** branch | `e > 2N_F/(3|G_F|)` ⟹ `G ≠ ∅` | `[PROVED]` given `|G_F| > 0` |
| **S7** thinness | `|G_D| = 0` ⟹ `G_D = {p/8 : p odd}` | `[VERIFIED]` 1,180,572 sets |

Coverage of S2 ∪ S3 ∪ S6 over 349,920 runner-instances in `[1..18]`: 94.13%
(96.51% with an unproved sharper constant). All uncovered instances are lonely — BSM finds
`G` nonempty in 12,208 of 12,208.

## 1. The correction: there is no unbounded base to induct over

Loneliness of runner `i` at `t = a/m` is the condition `‖(u_j − u_i)a/m‖ ≥ 1/8` for all `j`.
It reads the speeds **only through `u mod m`**. Therefore for any bounded family of moduli
`m ≤ M`, the whole question depends only on

    u  mod  lcm(1..M)

— a finite state space. In the coordinates `u_i = π(i) + 8 q_i`, this is the statement that
at modulus `8k` one sees `π(i) + 8(q_i mod k)` and nothing further: the deviations are
unbounded as integers but **invisible past the modulus**. `π` itself ranges over a finite
set regardless of spread.

So the transit argument is not one dimension out of eight unbounded ones. The base is
residue classes, and it is finite as soon as `M` is. **No induction over coordinates is
needed, and v1's proposal of one was a mis-framing.**

This relocates the entire remaining question onto a single quantity.

## 2. Is `M` bounded?  `[VERIFIED — three independent probes, not proved]`

`M(V) = max_i min{ m : runner i has a witness at t = a/m }`.

**(a) Scale.** 300 random primitive 8-sets at each scale, all eight runners each:

| speed range | sets | max `M` | runners with no witness (cap 200) |
|---|---|---|---|
| `[1..50]` | 300 | 19 | 0 |
| `[1..200]` | 300 | 18 | 0 |
| `[1..10³]` | 300 | 23 | 0 |
| `[1..10⁴]` | 300 | 24 | 0 |
| `[1..10⁶]` | 300 | 22 | 0 |
| `[1..10⁹]` | 300 | 25 | 0 |

Seven orders of magnitude, no growth.

**(b) The `lcm` adversary** — the construction that refuted the universal-`D` bound in
`DENOMINATOR_TOWER_v1`. `V = [0, l, 2l, …, 6l, 7l+1]` with `l = lcm(1..k)`:

| `k` | 4 | 5 | 7 | 9 | 11 | 13 | 16 | 17 | 18 |
|---|---|---|---|---|---|---|---|---|---|
| `l` | 12 | 60 | 420 | 2,520 | 27,720 | 360,360 | 720,720 | 12,252,240 | 12,252,240 |
| max `M` | 7 | 11 | 23 | **29** | 23 | 23 | 23 | 23 | 23 |

`M` peaks at 29 and returns to 23, holding while `l` grows to 12 million. The adversary
does not drive it up.

**(c) Exhaustive boxes.**

| box | primitive 8-sets | max `M` | never-lonely |
|---|---|---|---|
| `[0..14]` | 6,434 | 19 | 0 |
| `[0..16]` | 24,300 | 23 | 0 |
| `[0..18]` | 75,528 | 23 | 0 |

Extremal sets are near-reference: `(0,1,2,3,4,5,17,18)`, `(0,1,2,3,4,6,14,16)` — consistent
with §3 of v1, where the uncovered band was the collar around the AP.

## 3. The remaining gap, as a single statement

> **Conjecture M.** There is an absolute `M₀` such that every runner in every 8-set has a
> witness at some modulus `m ≤ M₀`. Evidence puts `M₀` at 29.

Conjecture M implies LRC(8) is a finite condition on `u mod lcm(1..M₀)`, by §1.

Two caveats, stated rather than buried:

- **Finite is not tractable.** `lcm(1..29) ≈ 2.3 × 10¹²`, and the state space is its 8th
  power before symmetry reduction. §1 makes the problem finite; it does not make the check
  runnable. A proof of Conjecture M would need to be an argument, not an enumeration.
- **Conjecture M is a strengthening of LRC(8), not a weakening.** LRC(8) says a witness
  exists; Conjecture M says one exists at bounded modulus. Proving it is therefore at least
  as hard. What §1 buys is that it is a *single* statement about one quantity, replacing
  v1's two gaps (the `O(1/e)` constant, and the small-`e` collar) with one.

## 4. Status

n = 8 is **not proved**. S1–S6 are proved; S7 and all of §2 are verified on stated ranges.
Conjecture M is a conjecture — the three probes in §2 are evidence of boundedness and not
an argument for it. v1's dimensionality framing is retracted by §1.
