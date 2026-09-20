# What is proved, what is observed, and where the difficulty actually sits

2026-09-13. n = 8, individual isolation, threshold 1/8, speeds any distinct reals.

The prediction method has four components. **Three are already analytic** — they hold for all
reals by algebra, and the empirical runs were testing the implementation, not the mathematics.
The fourth is not, and is stronger than it looks.

---

## 1. Proved, for all real speeds  `[PROVED — arithmetic]`

**(A) The bound.** For `t < 1/(8·d_min)` we have `d_min·t < 1/8`, so
`‖d_min·t‖ = d_min·t < 1/8` and the runner is not lonely. Hence

    t*  ≥  1 / (8 · d_min)                                                  ∎

**(B) Locality of `d_min`.** Speeds are sorted, so the nearest speed to `v_i` is `v_{i−1}` or
`v_{i+1}`. Therefore `d_min = min(v_i − v_{i−1}, v_{i+1} − v_i)` — the two neighbours and nothing
else. ∎

**(C) The band test is an identity.** Lonely at `t₀ = 1/(8·d_min)` means `‖d/(8·d_min)‖ ≥ 1/8`
for every other difference `d`. Putting `s = d/d_min`,

    ‖s/8‖ = (1/8) · dist(s, 8ℤ)      so     ‖s/8‖ ≥ 1/8  ⟺  dist(s, 8ℤ) ≥ 1      ∎

"Blocked iff some `d/d_min` lies within 1 of a multiple of 8" is therefore **algebra**, not an
empirical law.

**This covers irrationals with no testing at all.** The 24,000, 11,200 and 32,000 runs reported
earlier were code checks; the statements they check are proved above for arbitrary reals.

Corollary, also proved: at the AP every `d_min = 1`, so `s = d`, and only r1 and r8 have a
difference of 7 with `dist(7, 8ℤ) = 1` — exactly the band edge. Every other runner tops out at 6,
distance 2. That is why the ends are the fragile pair.

## 2. Not proved: the good set meets the FIRST interval

The remaining step is that runner `i`'s good set meets

    I = [ 1/(8·d_min),  7/(8·d_min) ],        |I| = 3/(4·d_min)

Verified on 21,600 runner-instances across seven populations including adversarial ones. No proof.

**The naive union bound fails, and not narrowly.** Constraint `d_j` is bad on a set of density
exactly `1/4`, so its bad measure inside `I` is about `|I|/4`, independent of `d_j`. Over the six
other constraints:

| | |
|---|---|
| `|I|` | `3/(4·d_min)` |
| total bad measure | `≈ 9/(8·d_min)` |
| **ratio** | **3/2** |

The bad sets have half again as much measure as the interval they sit in. Nothing stops them
covering `I` entirely, on measure grounds alone. A proof needs structure, not counting.

## 3. Why that step is hard — it implies LRC(8)

If the good set meets `I`, then in particular **it is nonempty**. So

    FIRST-INTERVAL  ⟹  LRC(8)

and the one unproved link in the chain is at least as strong as the theorem the whole programme
is about. LRC(8) is settled in the literature (Rosenfeld 2025) but by a 27-prime computation, not
analytically — so this is not a step that can be borrowed from anywhere.

It is in fact **strictly stronger** than LRC(8) as stated: LRC says the good set is nonempty,
first-interval says it meets a specific interval of length `3/(4·d_min)` starting at the earliest
arithmetically possible moment. LRC(8) does not imply it back.

So the transit work has not merely produced a prediction method. It has **isolated the difficulty
into a single, precisely stated, empirically solid claim** — one that implies the theorem and is
sharper than it.

## 4. Status

`[PROVED — arithmetic]` §1 (A), (B), (C), and the AP end-runner corollary. All reals.
`[PROVED — arithmetic]` §2's union-bound failure; §3's implication.
`[VERIFIED — 21,600, unproved]` the first-interval claim.

**Scope.** n = 8. Whether the band generalises to `nk ± 1` for other n is untested; if it does,
§1 carries over unchanged since none of (A)–(C) uses n = 8 beyond the threshold `1/n`.

**Not established.** The first-interval claim. Whether a non-measure argument (structure of the
`d_j` as a difference set, or the palindrome symmetry) reaches it.

**n = 8 is not proved here. What is new here is where the remaining difficulty is located.**
