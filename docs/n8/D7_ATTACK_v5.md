# D7 — why every route failed: the conjecture is LRC in disguise

2026-09-07. Continues `D7_ATTACK_v4.md`. The blocking-grammar frame
(`lrc_blocking_grammar_v1.md`) supplied the missing normalisation, and it settles
the whole line.

## 1. The blocking grammar was the right frame

`B(a) := {m ∈ {1,…,10} : {am/11} ∉ [1/11, 10/11]}` is defined for **real** `a`,
and `m ∈ B(a) ⟺ ‖am/11‖ < 1/11`. That is character-for-character the covering
relation with `n = 11`. Its two symmetries — `B(a+11) = B(a)` and
`B(11−a) = B(a)` — are the periodicity and the `v ↔ N−v` reflection used to halve
Rosenfeld's search range.

Its §5 supplies what my earlier attempts lacked. I had concluded (v1 §4) that
"the content is in the **arrangement**" and that the speeds are coupled, without a
handle on the coupling. The grammar has one: the **trajectory constraint** —

> "as `Q` decreases, all normalised speeds increase proportionally, and their
> folded images trace coupled paths … The cells occupied at one scale are not
> independently re-selectable at another."

## 2. Normalising by `p` — the rigidity is three-distance

Put `x = j/p` and `a_i = v_i/p`, `n = k+1`. Then

    v covers j   ⟺   ‖x·a/n‖ < 1/n,

so family `i` covers intervals of length `2/a_i` spaced `n/a_i` apart — a
rotation orbit hitting a fixed arc. **Verified:** every speed's covered set in the
`k=6, p=23` and `k=7, p=41` obstructions has at most **3 distinct gap lengths**
(three-distance theorem), and the sets are runs of consecutive `j` separated by
long gaps. Each speed contributes `≈ v/2` clusters of length `≈ 2p/v`.

This is genuine rigidity, far stronger than the density `2/n` that the counting
route used — and it is the arrangement structure v1 said was missing.

## 3. And it settles the question — the limit is LRC itself

With `x = j/p`, a target `x` is **uncovered** iff `‖x·a_i/n‖ ≥ 1/n` for all `i`;
setting `t = x/n`,

    x uncovered   ⟺   ‖t·a_i‖ ≥ 1/n = 1/(k+1)  for every i,

i.e. **the normalised speeds `a_i` have the LR property**. As `p` grows the grid
`{j/p}` becomes dense in `(0, n/2]`, so

> "no bad cover for all large `p`"  ⟹  every `k`-tuple of real speeds has the LR
> property  ⟹  **LRC for `k` runners.**

The implication is immediate in Rosenfeld's own logic: if Lemma 6 holds for all
large `p`, then `p | ∏vᵢ` for arbitrarily large `p`, so no counterexample exists.
That is exactly why he writes that it "could lead to a proof of the lonely runner
conjecture".

**Verified numerically.** For the `k=6` obstruction `T = {1,6,7,8,9,15}`, whose
lonely interval is `[15/49, 13/42]`: uncovered `j` should satisfy
`x = j/p ∈ n·[15/49, 13/42] = [15/7, 13/6] = [2.1429, 2.1667]`. At `p = 1009` the
uncovered `x` are `2.14371, 2.14470, 2.14569` — inside, as predicted. At `p = 23`
there are none (the grid misses the window), which is the exception.

## 4. Consequence: D7 in full generality is not a shortcut

**Proving "Lemma 6 for all large `p`" is at least as hard as LRC for `k`.** For
`k = 7` that is precisely Theorem 1 — the thing we set out to prove. So the
target named in `ROSENFELD_REVIEW_v1.md` §4 as "the well-posed analytic goal" is
well-posed but **not a reduction**: it is the problem itself, restated.

That explains, retrospectively and uniformly, why all six routes failed. They were
not near-misses; each was an attempt on something of the same strength as the
goal.

| route | why it failed | now understood as |
|---|---|---|
| counting | slack `≈2`, `p`-independent | too weak by a fixed factor |
| window width | `kill(T)` unbounded | tuple-wise, no uniformity available |
| `j = tp` chain | is Lemma 4 | recovers known content |
| block counting | sub-tuples nest | no competition to exploit |
| block recursion | no exclusive zone at `r ≡ −1` | boundary degeneracy |
| φ(n) law | same points, AP-only | measure zero |

## 5. What is actually tractable

Rosenfeld does **not** need "all large `p`". He needs **27 specific primes**,
`S = {31,…,163}`, and the margin is only `2.49` so none can be dropped
(`ROSENFELD_REVIEW_v1.md`). The realistic analytic target is therefore:

> **Replace the 32-hour search at each of 27 fixed primes with an argument.**

That is a finite, `p`-by-`p` question — not equivalent to LRC — and success would
make `n = 8` computer-free and hence Lean-verifiable, which is the original
objective. The three-distance rigidity of §2 is the natural tool: at fixed `p`
each candidate speed contributes `≈ v/2` clusters of length `≈ 2p/v` at period
`np/v`, and one must show `k` such rigid families cannot tile `(0, n/2]`.

Whether that is easier at `p = 163` than the 32-hour search is untested — but it
is the only version of the goal that is not circular.

## 6. Status

- §1–§3: **derived and verified** (three-distance on the obstructions; the
  `p → ∞` identification confirmed numerically at `p = 101, 1009`).
- §4: the hardness implication follows from Rosenfeld's own Lemma 6 logic; it is
  an argument, not a computation.
- §5 is a **redirection**, untested.
- **D7 in full generality is not open-and-attackable; it is LRC.** The finite-`p`
  version remains genuinely open and is the one worth pursuing.
