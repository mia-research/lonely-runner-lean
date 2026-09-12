# Reasoning over the AP/grid + permutation framework — what it proves and what it does not

2026-09-12. n = 8, individual isolation. Four passes over the owner's argument:
*any arrangement is the reference under permutation; every permutation has a deterministic,
mapped effect on loneliness; therefore n = 8.*

## Pass 1 — are the premises true?

**Premise A — every arrangement is the reference plus permutation.** True, and easy.
After translation and division by the gcd, `V` is an 8-subset of a grid `{0,…,M−1}` which
also contains the reference `{0,…,7}`. With `M ≥ 8` the runners can be moved one at a time
into the target slots (when `M > 8` a vacant slot serves as a buffer; when `M = 8` the sets
coincide). So every arrangement is reachable from the reference by single moves. `[PROVED]`

**Premise B — every permutation has a deterministic, mapped effect.** True, but weaker than
it reads. *Deterministic* only says the outcome is a function of (configuration, move), which
is automatic. What this session mapped is that function's **statistics** — the floor of 2,
the `4 → 2` first-move cost, the recovery curve `100% → 3.7%` stuck, the `δ ≡ 4 (mod 8)`
sublattice recovery to exactly 36. Those are properties of the map, not the map. `[PARTIAL]`

## Pass 2 — what would make the two combine?

An induction needs an invariant `I` with `I(reference)`, `I` preserved by every single move,
and `I ⟹ every runner lonely`. The natural candidate is `I` = *every runner holds at least
one mirror pair* (count ≥ 2), true at the reference where every runner has two.

**This does not reduce the problem, and the reason is exact.** Suppose some `V*` had a runner
at count 0. By Premise A there is a path reference → `V*`; some move on it is the first to
break `I`. So

> "`I` is preserved by every move" ⟺ "no configuration has a runner at count 0".

The framework re-indexes LRC(8) by move instead of by configuration. The two premises are
both true and their conjunction is equivalent to the conclusion, not a proof of it. Any
argument of this shape needs the step proved *locally* — from the fact that one speed changed,
without global information.

## Pass 3 — does the step localise?

A single move changes exactly **one** constraint for each non-moved runner. Runner `i` goes
from `A ∩ G_{d_old}` to `A ∩ G_{d_new}`, where `A = G_F` is the intersection of its six
unchanged constraints. The move kills runner `i` iff

> `A ⊆ B_{d_new}` — one bad set swallows a six-constraint good set.

That is the seven-constraint emptiness question again, so there is no localisation *unless
something protects `A`*. Measured over 65,912 `(F,d)` pairs, ratio `R = |G_{F∪d}|/|G_F|`:

| `R` | 0.0 | 0.1 | 0.2 | 0.3 | 0.4 | 0.5 | 0.6 | 0.7 | 0.8 | 0.9 | 1.0 |
|---|---|---|---|---|---|---|---|---|---|---|---|
| pairs | **26** | 81 | 304 | 879 | 2125 | 5465 | 11012 | 18215 | 18033 | 7613 | 2159 |

The measure **is** swallowed in 21 cases. But in every one the resulting count is **4** — the
set is not swallowed. The survivors are always `{1/8, 3/8, 5/8, 7/8}`.

## Pass 4 — what protects them, and the dichotomy

For `p` odd, `gcd(p,8) = 1`, so `8 | dp ⟺ 8 | d`. Hence `‖d·p/8‖ ≥ 1/8` for every `d` unless
`8 | d`. Therefore:

> **Case A — no difference `≡ 0 mod 8`.** All four `p/8` are witnesses. **count ≥ 4.**
> `[PROVED]`
>
> **Case B — some difference `≡ 0 mod 8`.** That single difference destroys all four
> reference witnesses at once. Open.

A runner is in Case A exactly when its residue mod 8 is unique — it is uniquely placed at the
reference. Verified exhaustively:

| box | Case A sets | count < 4 in Case A | measure-zero in Case A | Case B sets | `\|G_D\| = 0` in Case B |
|---|---|---|---|---|---|
| `[1..16]` | 3,432 | **0** | 3 | 8,000 | **0** |
| `[1..20]` | 31,816 | **0** | 3 | 45,584 | **0** |

**All three measure-zero instances lie in Case A.** They are the configurations that survive
on exactly the reference points with no slack — the runner is uniquely placed, and that
uniqueness is the only thing keeping it lonely.

So the framework delivers:

- **Case A proved outright**, with an explicit witness set, covering 30% of difference sets
  in `[1..16]` and 41% in `[1..20]`.
- **Case B** reduced from "is `G_D` nonempty" to "is `|G_D| > 0`" — because measure zero
  forces `G_D = {p/8}` (`WN_reference_collapse`, verified over 1,180,572 sets), and `p/8` is
  unavailable in Case B. So in Case B, measure zero *implies* empty.

## Verdict

The two premises do not prove n = 8. Their conjunction is logically equivalent to it, because
the induction step is the theorem re-indexed. That is not a defect of the idea — it is what
Pass 2 establishes, and it is worth knowing precisely.

What the framework does produce, by pushing the step until it localises, is the Case A / Case
B dichotomy with **Case A fully proved**. And it converts the open half from an emptiness
question into a **measure** question, conditional on the collapse statement. Measure is a more
tractable object than emptiness; that conversion is the framework's real contribution.

The stricter form the owner anticipated is real but free: count ≥ 2 rather than ≥ 1 follows
from the parity law once nonemptiness is had, and Case A gives ≥ 4 outright.

## Status

`[PROVED]` Premise A; Case A (count ≥ 4), with derivation; Pass 2's equivalence.
`[VERIFIED]` Pass 3's 65,912 ratio pairs; Pass 4's two boxes.
`[OPEN]` Case B. Equivalent to LRC(8) given the collapse statement, which is itself verified
and not proved.

**n = 8 is not proved.**
