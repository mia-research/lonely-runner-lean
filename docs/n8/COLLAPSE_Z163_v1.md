# The `8 | v` collapse, and the 2-adic block structure it belongs to

2026-09-07, continuing `P163_ARGUMENT_v1.md` §6. Target: understand why the
`p = 163` instance of Rosenfeld's Lemma 7 (`k = 7`, `N = 1304`, `H = 652`)
resists, in terms of the small object the `8 | v` speeds collapse onto.

Every claim below carries a grade. Scripts are in `experiments/n8/`.

---

## 0. Setup and notation

`n = k+1 = 8`, `p = 163`, `N = np = 1304`, targets `j ∈ {1,…,652}`, speeds
`v ∈ {1,…,652}` with `163 ∤ v`. `v` covers `j` iff `‖jv/N‖ < 1/8`, i.e.
`jv mod N < 163` or `> 1141`.

Partition the 652 targets into the **163 residue classes mod 163**,

    C_r = { r, r+163, r+326, r+489 },   r = 1,…,163,

each of size exactly 4 (because `652 = 4·163`). Index the four members by
`t = 0,1,2,3`. Write `S_v(r) ⊆ {0,1,2,3}` for the set of members of `C_r` that
`v` covers. A bad cover requires `⋃_{v∈T} S_v(r) = {0,1,2,3}` for every `r`.

---

## 1. The block identity — the collapse, and its generalisation

**[PROVED — one line of arithmetic; checked exhaustively by `two_adic_blocks_v1.py`]**

For `j = r + 163t`,

    j·v mod 1304 = (r·v mod 1304) + 163·((t·v) mod 8)   (mod 1304),

so writing `a = ⌊(r·v mod 1304)/163⌋ ∈ {0,…,7}` for the *block index*, `v` covers
the member `t` of `C_r` iff `(a + t·v) mod 8 ∈ {0,7}`.

Only `v mod 8` enters. The `8 | v` collapse of `P163_ARGUMENT_v1` §6 is the case
`t·v ≡ 0 (mod 8)`: the block index does not move, so `v` covers all four members
of `C_r` or none — which is exactly the statement that the configuration lives in
`ℤ/163`, and `‖jv/1304‖ = ‖j(v/8)/163‖` with covering arc
`A = { s : |s|₁₆₃ ≤ 20 }`, `|A| = 41`.

## 2. The 2-adic cap table

**[PROVED — the identity of §1; VERIFIED EXHAUSTIVELY over all 648 admissible
speeds × 163 classes, `two_adic_blocks_v1.py`, zero cap violations]**

| `e = v₂(v)` | `S_v(r)` can be | per class | # such speeds | total coverage |
|---|---|---|---|---|
| `e ≥ 3` (`8∣v`) | `∅` or `{0,1,2,3}` | 0 or **4** | 81 | 164 = 41·4 |
| `e = 2` (`v=4u`) | `∅`, `{0,2}`, `{1,3}` | 0 or **2** | 81 | 162 = 81·2 |
| `e = 1` (`v=2u`) | a singleton, always | exactly **1** | 162 | 163 = 163·1 |
| `e = 0` (`v` odd) | `∅`, singleton, or an **adjacent** pair `{t,t+1 mod 4}` | 0,1 or **2** | 324 | 162 |

The four coverage totals are the ones measured in `P163_ARGUMENT_v1` §3
(164/162/163/162). They are now derived rather than observed: the table's last
column is forced by the middle columns.

**The pair types are disjoint.** `e = 2` speeds contribute *opposite* pairs
(`{0,2}`, `{1,3}`); odd speeds contribute *adjacent* pairs (`{0,1}`, `{1,2}`,
`{2,3}`, `{0,3}`) — the constraint is `t − t′ ≡ v (mod 8)`, and `v` odd forces
`t−t′ ≡ ±1 (mod 4)`. Verified exhaustively (`pair_types_v1.py`): no odd speed
ever contributes an opposite pair, no `4u` speed ever contributes an adjacent one.

> **Consequence.** An adjacent pair and an opposite pair are never complementary.
> So a class completed by exactly two speeds each contributing 2 needs **both odd
> or both `≡ 4 (mod 8)`** — never one of each.

## 3. What the gcd condition actually does

**[PROVED]** `N = 1304 = 2³·163`; every admissible speed has `163 ∤ v`; so
`gcd(R ∪ {N}) = 1` for every 6-subset `R ⊆ T` iff no 6-subset is entirely even
iff **`T` contains at least two odd speeds** (`P163_ARGUMENT_v1` §2).

Since `8 | v ⟹ v` even, this caps

    x := #{ v ∈ T : 8 | v }  ≤  5.

## 4. The collapsed covering problem, solved exactly

Let `f(n,p)` be the **minimum number of dilates of `A` needed to cover `ℤ/p`**.
Scaling all `w_i` by a unit permutes `ℤ/p`, so this is scale-invariant and the
enumeration over sets containing `w = 1` is exhaustive; the available dilate
classes are `w = 1,…,81`, which is one representative of every non-zero `±`-class,
so **no generality is lost**.

**[PROVED — exhaustive enumeration, `collapse_z163_v1.py`, `max_union_v1.py`]**

    f(8,163) = 7.

Lower bound: branch-and-bound to depth 6 finds no cover. Upper bound: the greedy
witness of `P163_ARGUMENT_v1` §1, `T = {8,32,40,48,56,88,104}` (`w = 1,4,5,6,7,11,13`),
covers `{1,…,652}` with zero uncovered targets — re-checked directly.

Best partial covers (`max_union_v1.py`, exhaustive):

| `x` dilates | max classes covered | `U_min(x)` = classes necessarily missed |
|---|---|---|
| 1 | 41 | 122 |
| 2 | 77 | 86 |
| 3 | 105 | 58 |
| 4 | 129 | 34 |
| 5 | **151** | **12** |
| 7 | 163 | 0 |

**This is the answer to the question `P163_ARGUMENT_v1` §6 posed.** Seven
multiples of 8 can cover `{1,…,652}` because `f(8,163) = 7` exactly — not with
room to spare. The gcd condition caps `x` at 5. The density bound is
`⌈163/41⌉ = 4`, so the true minimum exceeds the counting bound by a factor
`7/4 = 1.75` — **the same 1.75 that appears as unexplained "slack" in
`P163_ARGUMENT_v1` §3.** It is not slack in the argument; it is the gap between
the density bound and the truth for this covering problem.

## 5. The `x = 5` sector, decided

With `x = 5` the remaining two speeds must both be odd. The five dilates miss at
least `U_min(5) = 12` classes, and by §2 an odd speed contributes at most 2
targets per class, so both odd speeds must contribute complementary adjacent
pairs on **every** missed class. Define

    D(v₁,v₂) = { r : S_{v₁}(r) ∪ S_{v₂}(r) = {0,1,2,3} }.

A bad cover with `x = 5` exists iff some odd pair has `ℤ/163 ∖ D` coverable by 5
dilates; `|D| ≥ 12` is necessary.

**[PROVED — exhaustive over all `C(324,2) = 52 326` odd pairs, `x5_two_odd_v1.py`]**

- `max |D| = 27`; the distribution is concentrated at `|D| ≤ 7` (48 699 pairs).
- 227 pairs pass `|D| ≥ 12`.
- **All 227 fail the exact 5-dilate coverability test. No bad cover has `x = 5`.**

Scope: this closes one sector of the `p = 163` verification (`x = 5`), not the
verification. Sectors `x = 0,…,4` are untouched by it. Runtime: seconds, against
the ~32 hours the full search took.

## 6. Where this leaves the line

The framing in `P163_ARGUMENT_v1` §1 — "covering is not the obstruction, the gcd
condition is" — needs a correction, and it is this document's main revision to
the record. **Covering is the obstruction; the gcd condition selects which
covering problem you must solve.** Concretely: unrestricted, the covering problem
has solutions, and `f(8,163) = 7` says the cheapest is exactly `k` speeds. The
gcd condition removes two coarse speeds from the budget and forces their
replacements to be odd — and odd speeds cannot contribute 4 to a class, cannot
pair with `4u` speeds (§2), and are capped at 2. The obstruction is the
interaction, not either half.

Open, in decreasing tractability:

1. **Sectors `x = 4,3,2,1,0`.** Same machinery, `m = 7−x` non-coarse speeds and
   threshold `U_min(x)`. `x = 4` is running. The enumeration grows as `C(567,m)`,
   so `x ≤ 2` will need the §2 pair-type structure as a pruning rule rather than
   as a filter after the fact.
2. **Whether `f(n,p) = n−1` for all large `p`.** Observed `f(8,163) = 7 = n−1`;
   `collapse_z163_v1.py` finds `f(7,17) = 4 = n−3`, which is exactly a prime where
   the paper records Lemma 7 failing for `k = 6`. That is one hit, not a law —
   `f(7,23) = f(7,29) = 5`, and Lemma 7 fails at 23 and 29 too, so the coarse
   sector does not explain those failures. **The relation `f(n,p) ≤ n−3 ⟹ Lemma 7
   fails at (n−1,p)` is a proved one-way implication; the converse is false.**
