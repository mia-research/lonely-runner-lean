# Handover — session of 2026-09-07 (second)

Continues `docs/HANDOVER_2026_09_07.md`. That document's §5 named the next task as
"the `8 | v` collapse to `ℤ/163`". This session did that, and re-graded the claims
the previous one left standing too strongly.

## 1. Re-grading  (`docs/n8/CLAIM_GRADES_v1.md`)

Eight claims restated at the grade the evidence carries. The one that mattered:

> "Covering is **not** the obstruction — the gcd condition is."

was inferred from two witnesses and is **wrong in emphasis**. It redirected the
line away from covering for a whole session. Corrected in §2 below. Going the
other way, "the asymmetry is structural, not quantitative" was an assertion and is
now **proved** — and proving it is what produced this session's results.

## 2. The collapse, resolved  (`docs/n8/COLLAPSE_Z163_v1.md`)

Everything below is at `k = 7`, `p = 163`, `N = 1304`, `H = 652`, with the 652
targets partitioned into the 163 classes `C_r = {r, r+163, r+326, r+489}` mod 163.

**The block identity** [PROVED, and checked exhaustively]. For `j = r + 163t`,
`jv mod 1304 = (rv mod 1304) + 163·((tv) mod 8)`. Only `v mod 8` enters. The
`8|v` collapse is the case `tv ≡ 0`, and the general case gives a **2-adic cap
table**: `8|v` covers 4 or 0 of a class, `v=4u` covers 2 or 0 as an *opposite*
pair `{0,2}/{1,3}`, `v=2u` covers exactly 1, `v` odd covers at most 2 and only as
an *adjacent* pair. Verified over all 648 admissible speeds × 163 classes, zero
violations. The four coverage totals measured last session (164/162/163/162) are
now derived rather than observed.

Consequence: adjacent and opposite pairs are never complementary, so a class
completed by two speeds contributing 2 each needs **both odd, or both `4u`** —
never one of each.

**`f(8,163) = 7`** [PROVED, exhaustive]. The minimum number of dilates of the
41-element arc needed to cover `ℤ/163` is exactly 7 — branch-and-bound finds no
6-cover, and last session's greedy witness gives 7. The density bound is 4, so the
truth exceeds it by `7/4 = 1.75`: **that is the same 1.75 recorded last session as
unexplained "slack".** It is not slack; it is the gap between the counting bound
and the truth for this covering problem.

**This answers the question the previous handover posed.** Seven multiples of 8
can cover `{1,…,652}` because 7 is exactly the minimum, with nothing to spare. The
gcd condition (two odd speeds required) caps the number of `8|v` speeds at 5.
Covering *is* the obstruction; the gcd condition chooses which covering problem
must be solved.

**Two sectors decided** [PROVED, exhaustive; seconds of compute each]. Writing
`x = #{v ∈ T : 8|v}`:

- `x = 5` — the two remaining speeds are both odd; all `C(324,2) = 52 326` pairs
  enumerated, 227 pass the count filter, all 227 fail exact coverability. **No bad
  cover.**
- `x = 4` — all triples with two or more odd speeds; 2801 pass the filter, all
  fail. **No bad cover.**
- `x ≥ 1` is forced (§3 below).

So the open sectors at `p = 163` are `x ∈ {1,2,3}`. This is a partial result: the
`p = 163` verification is **not** replaced.

## 3. Two search reductions  (`docs/n8/SEARCH_REDUCTION_v3.md`)

**Unit scaling** [PROVED]. `v ↦ cv`, `j ↦ c^{-1}j` for a unit `c` mod `N` preserves
covering and the gcd condition; the gcd condition forces a speed coprime to `N`
when `n` is a prime power. Hence **WLOG `1 ∈ T`**, a factor `φ(N)/2 = 324`. The
paper does not use this symmetry (§6 lists the one symmetry it leaves unused, and
this is not it).

**A coarse speed is forced** [PROVED]. `p·v mod N = p·(v mod n) < p` only when
`n | v`, so the target `j = p` can only be covered by an `n`-divisible speed.

## 4. Corrections to our own record

- `run_k7_primes_v1.py` (written this session) listed **28** primes; Rosenfeld's
  `S` has **27** — 41 is omitted, and §7 says so in words. Corrected, with an
  assertion on the length.
- Our search found the `p = 41` bad cover `T = {1,4,12,13,14,16,20}`
  independently, before the sentence was read: it covers all 164 targets, passes
  the gcd condition, and has the LR property (`0.14284 > 1/8`).
- **A retraction.** `SEARCH_REDUCTION_v2.md` §1 accused `WHY_13_AND_19_v2.md` of
  recording the `p = 41` exception with the sense inverted. It had not; §3 of that
  document derives the exception correctly and quotes the source. v3 retracts it.
  The pattern is the one already in memory: an accusation against a source or our
  own record, written before running the check that settles it.

## 5. Validation of the search implementations

`normalised_search_v2.py` reproduces every data point Rosenfeld states in §7:
`k=3` fails at 5 and applies at 7, 11; `k=6` applies at 13, 19, 31, 37 and fails
at 17, 23, 29; `k=7` applies at 31, 37 and **fails at 41**. The unnormalised
`lemma7_criterion_v1.py` agrees wherever both were run.

## 6. Next

1. Sectors `x = 3, 2, 1`. Same machinery; the enumeration grows as `C(567, 7−x)`,
   so the pair-type structure of §2 has to become a branching rule rather than a
   post-hoc filter. Enumerating the **coarse** side instead (`C(81,x)` is small)
   and asking what the non-coarse speeds must then supply is the obvious inversion
   and has not been tried.
2. Timing is not a claim. Our Python is ~38 s at `p = 31` and ~162 s at `p = 37`,
   roughly fourfold per prime step, against the author's C++. Nothing here
   supports any statement about wall-clock at `p = 163`.
3. `f(n,p) ≤ n−3 ⟹ Lemma 7 fails at (n−1, p)` is proved one-way; the converse is
   false (`f(7,23) = f(7,29) = 5` yet Lemma 7 fails at both). The coarse sector
   explains some exceptions, not all.

Artifacts added: `docs/n8/{CLAIM_GRADES_v1, COLLAPSE_Z163_v1, SEARCH_REDUCTION_v3}.md`;
`experiments/n8/{collapse_z163, two_adic_blocks, pair_types, max_union, x5_two_odd,
x4_sector, normalised_search_v1, normalised_search_v2, run_k7_primes}_v1.py`.
