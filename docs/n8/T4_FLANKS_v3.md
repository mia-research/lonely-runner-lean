# T4 / W3 — the lattice route, re-read through flanks

2026-09-15, version 3: §3(d) proves the flank sum criterion, which settles two (and three) irrational ratios at order 8. v2 corrected §3(a) for odd `n`. Scripts in `experiments/n8/` (outputs `.out`), exact arithmetic: `t4_gap_adversarial_v1.py`,
`t4_exhaustive_v1.py`, `flank_shadow_v1.py`, `flank_irrational_v1.py`. Correction to `WHAT_STOPS_PROOF_v2` §3: a reading near `8m/q` sits on the subject
at every `q`-th instant `p/8`, a **coarser** family of instants (spacing `q/8`), not a finer lattice.

---

## 1. The gap is not bounded by a constant  `[VERIFIED — exact; supersedes TARGETS_v3 §4A's "gap ≤ 3"]`

The earlier gap figures (at most 3) came from random samples.

| search | largest gap (least lonely lattice − first live) | largest least lonely lattice |
|---|---|---|
| adversarial, order 5, speeds ≤ 120 | **6**: `(2, 47, 57, 102, 103)`, subject 102 (readings 1, 45, 55, 100; dead 1–5, 9, 10, 11, 20; lonely at lattice 12) | 12 |
| adversarial, order 8, speeds ≤ 120 | **4** (eight arrangements) | 7 |
| exhaustive, order 5, every 5-subset of `[1, 30]`, every runner | 2 | 7 |
| exhaustive, order 8, every 8-subset of `[1, 20]`, every runner | 4 | 6 |

No runner in either exhaustive run lacked a lonely lattice. But "gap ≤ c" is not a statement to prove, and neither is "least lonely
lattice ≤ ⌊s_max/n⌋ + 1 + c" (exceeded by 4 at order 8). The lattice numbering was the wrong coordinate. §2 gives the right one.

---

## 2. Flanks: the coordinates the lattices came from  `[PROVED]`

By Proposition 6.1 (`reading_complete`), every lonely instant is matched by a lonely **opening** `t_k = (k + 1/n)/d_e` of one of
the subject's own differences `e`. Conversely a lonely opening is a lonely instant. So

> **Existence for the subject ⟺ some difference `e` (the flank) has a lonely opening.**

A flank's openings form one lattice, with number the numerator of its reading. That is where the lattice route's lattices came
from.

**Flank lemma.** Fix a flank `e`. Every other runner `j` reads `ρ_j = d_j/d_e`, a ratio of speed differences that does not depend
on any scale. At the `k`-th opening, `j` sits at `ρ_j·(k + 1/n)` laps. Write `ρ_j = A_j + f_j` (whole part and fractional part).
Then
- **`f_j = 0`:** `j` is never in the way, unless `ρ_j ≡ 0 (mod n)`, in which case it is in the way at every opening. That is
  the dead lattice: the flank is shadowed.
- **`f_j > 0`:** `j` is in the way exactly when `k·f_j mod 1` lies in the open arc of length `2/n` centred at `−ρ_j/n (mod 1)`.

`[PROVED — arithmetic; checked 143,520 times against direct evaluation from speeds, 0 disagreements]`

The flank lemma is the framework's own ideal read from each runner: at a flank's openings, integer-ratio runners sit on the
ideal (clear, or a slot-sharer). Only fractional parts move, each by a fixed step `f_j` per opening.

---

## 3. When a flank is shadowed — every opening in the way  `[PROVED where stated]`

Call a live flank (no ratio `≡ 0 mod n`) **shadowed** if every one of its openings has some runner in the way.

**(a) One fractional runner never shadows a live flank** (any real `f`, every `n ≥ 3`). The points `k·f mod 1` advance by the
fixed step `f`. An open arc of length `2/n ≤ 2/3` cannot hold them all: moving forward by `f < 1 − 2/n`, the sequence leaves the
arc and lands in its complement; if `f > 1 − 2/n`, the same holds moving backward by `1 − f`. (If the point `k = 0` is outside the
arc, that opening is already clear.) For `f = 1 − 2/n` the orbit is finite and evenly spaced:
- `n` even: `n/2 ≥ 2` points spaced `2/n`, of which an open arc of length `2/n` holds at most one;
- `n` odd: `n ≥ 3` points spaced `1/n`, of which it holds at most two.

`[PROVED — elementary]`

**(b) Two fractional runners, at order 8:**
- **Both rational:** a runner of denominator `c` is in the way at a set of residues `k mod c`. An open arc of length `1/4` holds at
  most `⌈c/4⌉` of the points `0, 1/c, …`, so at most `⌈c/4⌉/c` of the residues. That is below `1/2` for every `c ≥ 3`, and equals
  `1/2` only at `c = 2`. For the pair to hold every residue mod `lcm(c₁, c₂)`, the two shares must add to at least 1, so
  **both fractional parts are exactly `1/2`**. The enumeration finds exactly 4 such pairs, by whole part mod 8; 0 others up to
  denominator 12. `[PROVED — residue count, all denominators; exact enumeration for which half-integer pairs]`
- **One rational, one irrational:** the rational runner leaves some residue `k₀ mod c` clear, and on `k = k₀ + c·i` the irrational
  runner advances by the irrational step `c·f mod 1`, which by (a) leaves its arc. **Never shadows.** `[PROVED]`
- **Both irrational:** never shadows — §3(d). `[PROVED]`

**(c) Three fractional runners, at order 8, rational, denominators up to 8, no shadowing pair inside:** exactly the signatures
`(2, 4, 4)` (64 combinations), `(3, 3, 3)` (32), `(3, 6, 6)` (32), `(5, 5, 5)` (16). `[VERIFIED — exact enumeration in range]`
The residue count does not reduce triples to finitely many signatures: `(2, 5, c)` passes it for every `c`. The full list is open.

At order 5 (arc `2/5`) pairs are again only half-integers, but shadowing triples are more numerous: `(5, 5, 5)`, `(7, 7, 7)` and
others up to 8.

**(d) The flank sum criterion.** `[PROVED — pigeonhole (simultaneous approximation) and a residue count]`

> Let `e` be a live flank, and `J` the runners whose ratio to `e` is not an integer. For `j ∈ J` let `c_j` be the denominator of its
> fractional part `f_j`, with `1/c_j = 0` when `f_j` is irrational. If
>
>     Σ_{j ∈ J} ( 2/n + 1/c_j )  <  1,
>
> then `e` has a lonely opening.

*Proof.* Suppose every opening `k ≥ 0` has some `j ∈ J` with `k·f_j mod 1` in its open arc `A_j` of length `ℓ = 2/n`. Runners with
integer ratios are clear at every opening of a live flank (§2), so they play no part.

1. *Choosing `q`.* Let `L` be the least common multiple of the rational denominators, and `m` the number of irrational `f_j`. For
   any `Q ≥ 1`, apply the pigeonhole principle to the `Q^m + 1` points `(q′L·f_j mod 1)_j`, `q′ = 0, …, Q^m`, in the `Q^m` boxes
   of side `1/Q`. This gives `1 ≤ q′ ≤ Q^m` and integers `p_j` with `|q′L·f_j − p_j| ≤ 1/Q` for every irrational `j`. Put `q = q′L`.
   Then `|f_j − p_j/q| ≤ 1/(qQ)`, so for every `k < q`, `k·f_j` and `k·p_j/q` differ by less than `1/Q`.
2. *The rational picture.* Hence for every `k ∈ [0, q)` some `j ∈ J` has `k·r_j mod 1` in the arc `A_j` widened by `1/Q` on each
   side, where `r_j = f_j` for rational `j` and `r_j = p_j/q` for irrational `j`.
3. *Counting residues.* If `r_j` has reduced denominator `d_j` (dividing `q`), then as `k` runs over `[0, q)`, `k·r_j mod 1` takes
   each multiple of `1/d_j` exactly `q/d_j` times. An open arc of length `λ` holds at most `λ·d_j + 1` of those multiples. So `j` is
   in the way at no more than `q·(λ + 1/d_j)` of the `q` residues, with `λ = ℓ` for rational `j` and `λ = ℓ + 2/Q` for irrational
   `j`. For every residue to be covered:

       1  ≤  Σ_{rational j} (ℓ + 1/c_j)  +  Σ_{irrational j} (ℓ + 2/Q + 1/d_j(Q)).

4. *Letting `Q` grow.* For irrational `j`, `|f_j − p_j/q| ≤ 1/Q → 0`. Only finitely many rationals with bounded denominator lie
   near `f_j`, and `f_j` is none of them, so `d_j(Q) → ∞`. The right side then tends to `Σ_{j∈J}(2/n + 1/c_j) < 1`, a
   contradiction. ∎

**Consequences at order 8** (`2/n = 1/4`):
- **any one, two or three irrational ratios never shadow a live flank** (sums `1/4`, `1/2`, `3/4`);
- rational ratios count `1/4 + 1/c`, so two rational ratios can shadow only when `1/c₁ + 1/c₂ ≥ 1/2`. The exact enumeration
  narrows that to both `c = 2` (§3b).

The criterion needs `|J| < n/2` for irrational ratios. At order 8 four irrational ratios reach the sum 1, and it says nothing.

**Checks** (`flank_irrational_v1.out`, exact in `ℚ(√2)`, so the fractional parts are rationally dependent, the harder case):
- 400 random irrational pairs and 400 triples: every one has a clear opening, the latest at `k = 85` (pairs) and `k = 131`
  (triples);
- the shadowing half-integer pair `(1/2, 7/2)` perturbed to `(1/2 + ε√2, 7/2 − ε√2)`: first clear opening at `k = 1, 5, 45, 442,
  4420` for `ε = 10⁻¹ … 10⁻⁵`.

The criterion gives an opening, not how soon: near a shadowing configuration the first clear opening comes late, about `0.44/ε`
here. That is consistent with the owner's rule that the framework names an instant without bounding when.

**Reading.** A flank is shadowed by few runners only when their ratios to it have small denominators, meaning the arrangement is
close to an ideal at a related scale. That is the dead-lattice ladder in exact form: denominator 2 is the pair rule (v7 list item
17), and the triples are its next rungs.

---

## 4. What this gives, and what it does not

**Proved now:**
- Existence for a subject whenever some live flank has at most one runner with a non-integer ratio (§3a). This extends
  Theorem 4.10(a), where all ratios are integers.
- At order 8, Existence whenever some live flank has exactly two non-integer ratios, not both half-integers (§3b, §3d).
- Existence whenever some live flank's non-integer ratios satisfy the flank sum criterion (§3d). At order 8 that includes every
  live flank with at most three non-integer ratios, all irrational.

**Not closed, stated plainly.** At order 8 a flank has six other runners. Up to six of them can have non-integer ratios, and then
§3's small-denominator structure is no longer forced: four ratios of large denominator can together hold every opening in the way.
So the per-flank lemmas alone do not settle order 8.

**The native target this leaves: a subject cannot have every flank shadowed.** The ratios to different flanks are tied together:
`d_j/d_e = (d_j/d_{e′})·(d_{e′}/d_e)`. Shadowing one flank with few runners needs small-denominator ratios to that flank, and those
ratios then fix ratios to the other flanks. The question is whether all seven flanks can be shadowed at once.

**Next actions:**
1. For each exhaustive arrangement, record for every flank whether it is shadowed, and by which runners. Find the arrangements
   where the most flanks are shadowed, and the structure that does it. Exact; reuses `t4_exhaustive_v1.py`.
2. ~~Prove §3(b) for two irrational ratios~~ — done, §3(d).
3. Formalise the flank lemma and §3(a) in Lean: they follow from `reading_complete`, the band identity and an elementary step
   argument.

**For the owner:** §3(b) and §3(d) use a count of residues in a finite cyclic group, and §3(d) also uses the pigeonhole principle
on boxes for simultaneous approximation (how many of `k mod c` one runner holds). It is exact
arithmetic, not a measure or density, but it is a count. Whether it sits inside the framework is your call. §3(a) and the
rational–irrational case use no count.
