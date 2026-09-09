# (A) the ray law and its caps; (B) why `(2,6,7,8,10,13,14)` is extremal

2026-09-10. Follows `AB_SPLIT_v1.md`. Scripts `experiments/n8/ok_fourier_v4.py`,
`ok_raylaw_v1.py`, `ok_Bbase_v1.py`.

---

## A1. Every ray sum is rational  `[PROVED — numerically exact]`

For a primitive resonance `p` (no coordinate `≡ 0 mod 4`, else the term vanishes) put
`R(p) = Σ_{m≠0} ∏_j f̂(mp_j)`. Expanding `∏ sin(πmp_j/4)` into exponentials and using
`Σ_{m≥1} e^{imφ}/m^s` at rational `φ/π` (Clausen / Bernoulli) makes the `π^s` cancel against
`1/π^s`. So `R(p)` is **rational**, and numerically:

    (1,1,−1) → −1/32     (1,2,−1) → −1/64     (1,3,−2) → −1/192
    (2,3,−1) → −1/192    (1,1,−2) → −1/64     (3,5,−2) → 1/960     (1,5,−3) → 1/480

each matching to `< 10⁻¹⁵`. Writing `C(p) = R(p)·∏_j|p_j|`, the observed value sets are

| support | `C` values | `cap(s) = max|C|` |
|---|---|---|
| 2 | `1/8, 1/16, 3/16` | **`3/16`** |
| 3 | `±1/32, ±1/64, ±3/64` | **`3/64`** |
| 4 | `11/1536, 1/96, 1/256, 11/768, 5/768` | **`11/768`** |

> **Ray law.** `R(p) = C(p)/∏_j|p_j|` with `C(p)` in a finite set, hence
> **`|R(p)| ≤ cap(s)/∏_j|p_j|`**, `cap = 3/16, 3/64, 11/768` at supports 2, 3, 4.

This is the `Ray(p)`-rationality of `O_RESONANCE` re-derived for `|G|` itself, with the caps
made explicit — and it gives the exact arithmetic skeleton
`|G| = (3/4)⁷ + Σ_{primitive rays} C(p)/∏|p_j|`.

**A hypothesis I tested and it failed.** The tiny value sets suggested `C(p)` might be a
function of the residues `p_j mod 8`. It is not: over 183 primitive support-3 vectors with
coordinates to `|15|`, **41 of 49 residue classes carry two different `C` values**
(spreads exactly `1/32`, `1/16`, `3/32` — sign flips). The value *set* is tiny; the *rule*
is not residue-local. Recorded because the caps survive and the residue law does not.

## A2. Signed truncation fails too  `[PROVED — counterexample]`

Signed totals by support at the extremum, against the main term `(3/4)⁷ = 0.1335`:

    support 2: +0.0047     support 3: −0.1560     support 4: +0.0627

(absolute values `0.065`, `0.275`, `0.228`). The series **alternates with terms larger than
the main term and does not decay** — `|signed|/absolute` is 7–45% at support 2 but ~50% at
supports 3 and 4, so the cancellation that rescues support 2 is not available higher up.
`AB_SPLIT_v1` §A2 killed absolute truncation; this kills signed truncation. Any proof must
sum the ray series *globally*, not support by support.

## B. Why the extremum is what it is  `[PROVED — exhaustive in the stated box]`

An `ov ≥ 5` tuple is five speeds from `λT` plus two free speeds. Since `|G|` is
scale-invariant, `|G(λT′)| = |G(T′)|`, so the 63 five-subsets of the three tight instances
carry fixed base measures:

    min  41/560 = 0.073214   at T′ = {1,3,4,5,7} ⊂ {1,…,7}
    max  29/112 = 0.258929   at T′ = {2,3,4,6,7}
    mean 0.171194                          (for reference (3/4)⁵ = 0.237305)

**The minimising base is `{1,3,4,5,7}`** — the same set that is the unique failing cell of
`(H′)`. Over all 9 501 completions with `λ ∈ {1,2}` and free speeds `≤ 24`:

> `min |G| = 93/14560`, attained at `E = (2,6,7,8,10,13,14)` — base `2·{1,3,4,5,7}`, free
> speeds `{7,13}` — **exactly the global target, ratio 1.000**.

So the extremal tuple is fully explained: *the minimal five-subset of the AP tight instance,
doubled, plus two free speeds.* And `{1,3,4,5,7}` is simultaneously the `(H′)` extremal set
and the minimal base — the local and global extrema of this project are the same set.

> **(B) target, now well-posed.** For every tight instance `T`, five-subset `T′`, dilation
> `λ`, and pair of free speeds, `|G| ≥ 93/14560`, with equality only at
> `λ = 2, T′ = {1,3,4,5,7}`, free `{7,13}`.

Two free speeds is the only unbounded part, and large free speeds push `|G|` toward
`|G(T′)|·(3/4)²  ≥ (41/560)(9/16) = 0.0412`, six times the target — so the danger is
confined to small free speeds.

## Grades

A1: **PROVED** for rationality and for the observed value sets (numerically exact to
`10⁻¹⁵`); the caps are **EMPIRICAL** over the tested coordinate ranges, not proved maximal.
The residue-law hypothesis is **REFUTED**. A2: **PROVED — counterexample**. B: **PROVED**
for the base measures (exact rationals over all 63 subsets); the completion minimum is
**EMPIRICAL**, exhaustive for `λ ∈ {1,2}` and free speeds `≤ 24`. The heuristic for large
free speeds is **not** a proof — it ignores the intersection structure.
