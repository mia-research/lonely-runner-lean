# Attacking `∫X ≥ 93/1820` on Case 2: one method killed, one lemma proved

2026-09-10. Follows `U_REFORMULATION_v2.md`. Scripts `experiments/n8/ok_{bonf,extremal,slack}_v1.py`,
exact rationals throughout.

---

## 1. Bonferroni is dead  `[PROVED — counterexample]`

At each `x` the blocked set is a union of 7 subsets of `ℤ/8`, so with
`S_k = Σ_{|F|=k} |⋂_{e∈F} bad_e|`, every **odd** truncation of Bonferroni is a valid lower
bound on `X = 8 − |⋃ bad_e|`, and integrating preserves it. At the extremal tuple
`E = (2,6,7,8,10,13,14)`:

| `k` | `∫S_k` exact | `~` | independence `8·C(7,k)/4^k` |
|---|---|---|---|
| 1 | `14` | 14.000 | 14.000 |
| 2 | `14549/1365` | 10.659 | 10.500 |
| 3 | `1553/182` | 8.533 | **4.375** |
| 4 | `6893/1092` | 6.312 | **1.094** |
| 5 | `1481/455` | 3.255 | **0.164** |
| 6 | `92/91` | 1.011 | **0.014** |
| 7 | `1/7` | 0.143 | **0.0005** |

Resulting lower bounds: order 1 → `−6`; order 3 → `−1511/390 = −3.874`; order 5 →
`−1487/1820 = −0.817`; order 7 → `93/1820`, the exact value. **Every truncation short of
the full sum is negative and therefore useless.**

The reason is in the table: `∫S_7 = 1/7` says **all seven runners share a blocked residue
on a set of measure `1/7`** — 290× the independent value. The runners are massively
correlated, and no truncated moment method survives that. Any proof must be exact in the
high-order terms, or avoid moments entirely.

## 2. Anatomy of the extremum  `[PROVED]`

`E = (2,6,7,8,10,13,14)`, `L = 10920`, `N = 8L = 87360`. Direct count in `t`-space: **566**
witnesses, `|G| = 283/43680`. The strict criterion gives `∫X = 93/1820 = 279/5460`, and
`283 − 279 = 4`: exactly four **boundary** witnesses, the isolated points
`t = 1/16, 3/16, 13/16, 15/16`, where `‖2t‖ = ‖14t‖ = 1/8` **exactly**. The two counts
reconcile completely, and the boundary points are the same phenomenon as the tight instances.

The remaining witnesses form four genuine intervals, in a mirror-symmetric pair of pairs —
as Theorem R (`x ↦ 1−x`) requires:

    t ∈ [9/104, 7/80]   and  [17/64, 15/56],   plus their reflections in t = 1/2.

**The decomposition.** `{2,6,8,10,14} = 2·{1,3,4,5,7}` — the doubled `(H′)` extremal set,
the unique cell where that leaf failed — and `E = 2·{1,3,4,5,7} ∪ {7,13}`. The lonely set
roughly halves per added runner:

    |G(1,3,4,5,7)| = |G(2,6,8,10,14)| = 127/1680   (dilation invariance, confirmed)
      + 7  → 3/70          + 13 → 563/14560          + both → 283/43680

So the global extremum of the whole n=8 problem is built on the local extremum of `(H′)`.

## 3. The Slack Lemma  `[PROVED]`

Case 1's proof is `t = a/8` with `a` odd: `‖e·a/8‖ = ‖ρa/8‖ ≥ 1/8` whenever `8 ∤ e`. It is
**tight** exactly when `ρa ≡ ±1 (mod 8)`; units are self-inverse mod 8, so `a^{-1} = a` and
that means `ρ ≡ ±a`.

> **Slack Lemma.** Let `a ∈ {1,3,5,7}` and suppose no non-divisible runner has `e ≡ ±a
> (mod 8)`. Then `‖e·(a/8)‖ ≥ 1/4` for every non-divisible `e` — a full `1/8` of slack — so
> `‖e(a/8 + δ)‖ ≥ 1/8` for all `|δ| ≤ 1/(8V)`, `V = max` non-divisible speed.

Verified: `‖ρa/8‖ = 1/8` at `ρ ∈ {1,7}` for `a ∈ {1,7}`, and at `ρ ∈ {3,5}` for `a ∈ {3,5}`;
`1/4` or more at every other `ρ`. So the hypothesis is exactly

    R_non misses both 1 and 7,   or   R_non misses both 3 and 5.

**Reach:** 1344 of the 3312 realisable residue multisets — **40.6%** — and it fully covers
7 of the 37 shapes. **It covers zero Unit-Complete shapes**, necessarily: Unit-Complete
means `{1,3,5,7} ⊆ R_non`, which meets both pairs. That is a structural explanation of why
Unit-Complete is the hard branch, and the lemma also fails at the extremal tuple
(`R_non = {2,5,6,7}` meets both pairs) — as it must, since a proof cannot be easy there.

**What it does not do.** At `t₀ = a/8` every divisible runner is at `‖8m·a/8‖ = 0`, maximally
unsafe. The lemma gives a *window*, not a witness; the divisible runners must still be
placed inside it. So this **reduces** 40.6% of the problem, it does not close it.

## 4. The `(a,σ)` decomposition  `[PROVED]`

Write `t = (a+σ)/8` with `a ∈ {0,…,7}` and `σ ∈ [0,1)`. Then `8m·t = m(a+σ)` and `ma ∈ ℤ`, so
the two runner types separate exactly:

| runner | condition |
|---|---|
| divisible `e = 8m` | `‖mσ‖ ≥ 1/8` — **`σ` alone**, `a` irrelevant |
| non-divisible `e` | `(ea + eσ) mod 8 ∈ [1,7]` |

The divisible half is now a **pure LRC problem on the `m_i`**: there are `d ≤ 6` of them, and
`LRC(d+1)` — ours, axiom-clean for `d+1 ≤ 7` — gives `‖m_iσ‖ ≥ 1/(d+1) ≥ 1/7 > 1/8`, hence an
**open set** of admissible `σ`, not just a point. Under the Slack Lemma's hypothesis the
non-divisible half needs only `|σ| < 1/V`, since `ea mod 8 ∈ {2,…,6}` leaves a unit of room
either way.

So Case 2, under the slack hypothesis, becomes: **does the open set `{σ : ‖m_iσ‖ ≥ 1/8 ∀i}`
meet the window `|σ| < 1/V`?** That is a genuine question about `d ≤ 6` speeds in a short
interval, and it is where this line now sits.

## 5. Grades

§1: **PROVED — counterexample** (exact `S_k` at one tuple; it refutes the *method*, not any
claim). §2: **PROVED**, exact counts, both criteria reconciled. §3: **PROVED** (arithmetic),
reach by exhaustive enumeration; explicitly **not** a closure. §4: **PROVED** (algebra); the
`LRC(d+1)` step cites our own axiom-clean small-`n` results.

**Open:** the window question of §4; the Unit-Complete branch, which no `a` reaches; and
`∫X ≥ 93/1820` itself. A scan of `min |G|` against a rising speed floor — testing whether
Case 2 admits a finite reduction — is still running and is **not** reported here.
