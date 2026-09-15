# T4 / W3 — the lattice route, re-read through flanks

2026-09-15. Scripts in `experiments/n8/` (outputs `.out`), exact arithmetic: `t4_gap_adversarial_v1.py`,
`t4_exhaustive_v1.py`, `flank_shadow_v1.py`. Correction to `WHAT_STOPS_PROOF_v2` §3: a reading near `8m/q` sits on the subject
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
arc and lands in its complement; if `f > 1 − 2/n`, the same holds moving backward by `1 − f`. For `f = 1 − 2/n` the points are
spaced `2/n` apart, and an open arc of that length holds at most one of them. `[PROVED — elementary]`

**(b) Two fractional runners, at order 8:**
- **Both rational:** a runner of denominator `c` is in the way at a set of residues `k mod c`. An open arc of length `1/4` holds at
  most `⌈c/4⌉` of the points `0, 1/c, …`, so at most `⌈c/4⌉/c` of the residues. That is below `1/2` for every `c ≥ 3`, and equals
  `1/2` only at `c = 2`. For the pair to hold every residue mod `lcm(c₁, c₂)`, the two shares must add to at least 1, so
  **both fractional parts are exactly `1/2`**. The enumeration finds exactly 4 such pairs, by whole part mod 8; 0 others up to
  denominator 12. `[PROVED — residue count, all denominators; exact enumeration for which half-integer pairs]`
- **One rational, one irrational:** the rational runner leaves some residue `k₀ mod c` clear, and on `k = k₀ + c·i` the irrational
  runner advances by the irrational step `c·f mod 1`, which by (a) leaves its arc. **Never shadows.** `[PROVED]`
- **Both irrational:** open.

**(c) Three fractional runners, at order 8, rational, denominators up to 8, no shadowing pair inside:** exactly the signatures
`(2, 4, 4)` (64 combinations), `(3, 3, 3)` (32), `(3, 6, 6)` (32), `(5, 5, 5)` (16). `[VERIFIED — exact enumeration in range]`
The residue count does not reduce triples to finitely many signatures: `(2, 5, c)` passes it for every `c`. The full list is open.

At order 5 (arc `2/5`) pairs are again only half-integers, but shadowing triples are more numerous: `(5, 5, 5)`, `(7, 7, 7)` and
others up to 8.

**Reading.** A flank is shadowed by few runners only when their ratios to it have small denominators, meaning the arrangement is
close to an ideal at a related scale. That is the dead-lattice ladder in exact form: denominator 2 is the pair rule (v7 list item
17), and the triples are its next rungs.

---

## 4. What this gives, and what it does not

**Proved now:**
- Existence for a subject whenever some live flank has at most one runner with a non-integer ratio (§3a). This extends
  Theorem 4.10(a), where all ratios are integers.
- At order 8, Existence whenever some live flank has exactly two non-integer ratios, not both half-integers and not both
  irrational (§3b).

**Not closed, stated plainly.** At order 8 a flank has six other runners. Up to six of them can have non-integer ratios, and then
§3's small-denominator structure is no longer forced: four ratios of large denominator can together hold every opening in the way.
So the per-flank lemmas alone do not settle order 8.

**The native target this leaves: a subject cannot have every flank shadowed.** The ratios to different flanks are tied together:
`d_j/d_e = (d_j/d_{e′})·(d_{e′}/d_e)`. Shadowing one flank with few runners needs small-denominator ratios to that flank, and those
ratios then fix ratios to the other flanks. The question is whether all seven flanks can be shadowed at once.

**Next actions:**
1. For each exhaustive arrangement, record for every flank whether it is shadowed, and by which runners. Find the arrangements
   where the most flanks are shadowed, and the structure that does it. Exact; reuses `t4_exhaustive_v1.py`.
2. Prove §3(b) for two irrational ratios. The step argument of (a) needs a joint version.
3. Formalise the flank lemma and §3(a) in Lean: they follow from `reading_complete`, the band identity and an elementary step
   argument.

**For the owner:** §3(b) uses a count of residues in a finite cyclic group (how many of `k mod c` one runner holds). It is exact
arithmetic, not a measure or density, but it is a count. Whether it sits inside the framework is your call. §3(a) and the
rational–irrational case use no count.
