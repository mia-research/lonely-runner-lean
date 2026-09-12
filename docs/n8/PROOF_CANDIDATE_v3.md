# n = 8 — proof candidate v3, in the reference / deviation frame

2026-09-12. Supersedes `PROOF_CANDIDATE_v2.md` entirely. **Individual isolation throughout.**

This argument uses none of the machinery of v1/v2 or of the earlier programme — no union
bounds, no modulus towers, no Farey gaps, no denominator routes. It runs on the reference,
the deviation coordinates, the palindrome, and one geometric bound.

## 1. Objects

For runner `i` with difference set `D` (its 7 differences), `G_D = { t : ‖dt‖ ≥ 1/8 ∀ d ∈ D }`.
Runner `i` is lonely iff `G_D ≠ ∅`. The **count** is the number of components of `G_D`.

- **Coordinates.** `u_i = π(i) + 8 q_i`. `π` is the permutation part, `q` the deviation.
  `[PROVED]` `WHICH_GRIDS_ISOLATE_v1` §2.
- **Grid distance.** `k(V) = 8 − |{residues mod 8}|`. A property of `π` alone, hence
  **independent of spread**.
- **Span.** `d_max = max D`.

## 2. The proved chain

**(P1) The palindrome.** `‖d(1−t)‖ = ‖dt‖`, so `G_D` is symmetric under `t → 1−t`. Components
pair; a self-symmetric one is centred at `t = 0` (never in `G`) or `t = 1/2` (in `G` iff every
`d` is odd). Hence the count is odd ⟺ every `d` is odd, so **the count counts mirror pairs**,
and count = 1 is impossible whenever any `d` is even.
`[PROVED]` `WN_count_parity` Step 2.

**(P2) The reference.** `k = 0` ⟺ the reduced residues are a complete system mod 8 ⟺ global
isolation, occurring at exactly `φ(8) = 4` times `t = p/(8g)`. Every runner then has 4 events
— two mirror pairs — **whatever the spread**, since `q` is invisible to `π`.
`[PROVED]` `WHICH_GRIDS_ISOLATE_v1` §1.

**(P3) Components are short.** `G_D ⊆ G_{d_max}`, and the components of `G_{d_max}` have
length exactly `3/(4 d_max)` (the bad interval at `j/d_max` has width `1/(4 d_max)`; the good
gap between consecutive ones is `1/d_max − 1/(4 d_max)`). So every component of `G_D` has
length `≤ 3/(4 d_max)`.
`[PROVED]` — two lines. Verified: 0 violations in 11,432 primitive `D ⊂ [1..16]`.

**(P4) The count bound.** Dividing the measure by the maximum component length,

> **count ≥ (4 d_max / 3) · |G_D|.**

`[PROVED]` from (P3). Verified: held in all 11,432 sets.

## 3. The shape of the argument

(P4) says: **large span forces a large count, provided the measure does not collapse.**
So the configuration space splits by span, not by any residue condition.

**Small span — enumerated.** All 7-element difference sets in a box, i.e. every 8-set of that
span from one runner's view:

| `N` | primitive sets | min count |
|---|---|---|
| 16 | 11,440 | 2 |
| 20 | 77,400 | 2 |
| 22 | 170,213 | 2 |
| 24 | **345,304** | **2** |

Never 0, never 1. Minimiser `(1,2,3,4,5,7,8)` at every `N`; the others are `8 → 16`
substitutions. `[VERIFIED — exhaustive]`

**Large span — (P4) applies.** If `|G_D| ≥ c` for every non-tight `D`, then
`count > 2` as soon as `d_max > 3/(2c)`, and by (P1) a count above 2 is at least 4.

| `c` | span threshold `3/(2c)` |
|---|---|
| 0.0064 | 235 |
| 0.040 | 38 |
| 0.090 | 17 |

**The floor moves the right way.** Both relevant quantities rise with span:

| span | `[0..20]` | `[0..40]` | `[0..80]` | `[0..200]` |
|---|---|---|---|---|
| floor at `k=1` | 2 | 4 | 8 | 16 |
| floor at `k=2` | 2 | 4 | 6 | 22 |
| min non-zero `|G_D|` | 0.0057 (at 16) | 0.042 (at 30) | 0.068 (at 60) | 0.091 (at 150) |

and `|G_D| → (3/4)⁷ = 0.1335`. Small measures and low floors occur **only** at small span.
This is the join between the two regions, and it runs in the direction the argument needs.

## 4. The single remaining step

> **Lemma needed.** A lower bound `|G_D| ≥ c(d_max)` for non-tight `D`, with
> `c(d_max) · d_max → ∞`, or simply `|G_D| ≥ c` for all `D` of span above some `S`.

With it, (P4) closes every configuration of span `> 3/(2c)`, and the finite remainder is the
enumeration in §3 — already done to span 24, needing extension to `3/(2c)`.

Two facts constrain the lemma and neither is an obstruction:

- `|G_D| = 0` occurs only at the three tight instances, all of span ≤ 8
  (`WN_reference_collapse`, exhaustive over 1,180,572 sets to `[1..28]`). So for span > 8 the
  measure is positive; what is missing is *quantitative*.
- The measured minimum rises with span rather than falling, so the lemma is not fighting the
  data.

## 5. What is not claimed

The lemma in §4 is not proved, so **n = 8 is not proved here**. §3's enumeration covers span
≤ 24 only. The `k`-versus-span table is sampled, not exhaustive. Nothing in this note bears
on the published proof (Rosenfeld 2025).

Prior results this replaces rather than uses: Conjecture M (refuted, and about the wrong
quantity — `MMIN_RETRACTION_v1`); the S1–S6 branch architecture of v1/v2 (superseded); the
`Σα`, denominator-tower and union-bound routes (all shown equivalent to `|G| > 0` rather than
reductions of it).

## 6. Status

`[PROVED]` P1, P2, P3, P4.
`[VERIFIED — exhaustive]` §3's four boxes to 345,304 sets; the component-length check.
`[VERIFIED — sampled]` §3's floor-versus-span table.
`[OPEN]` §4's lemma. It is the only step between this chain and a proof.
