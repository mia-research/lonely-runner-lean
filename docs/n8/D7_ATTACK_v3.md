# Attacking D7 — the `j = 1,2,3,…` chain

2026-09-07. Continues `D7_ATTACK_v1.md` (width route: refuted). Artifacts:
`experiments/n8/window_width_v1.py`, `enumerate_bad_covers_v1.py`.

## Result in one line

The chain is real and exact, but at `j = tp` it **recovers Rosenfeld's Lemma 4**
rather than adding to it. Its genuinely new content is a **self-similar block
structure** around multiples of `p`, verified exactly. D7 is not closed.

## 1. `j = 1`: every bad cover has a speed `< p`

`v` covers `j = 1` iff `v mod N ∈ [0,p) ∪ (N−p, N)`. Since `v ≤ N/2` and
`N − p = kp > N/2` for `k ≥ 2`, the upper arc is unreachable. So some `v < p`.
(Proved in v1.)

## 2. `j = tp`: the chain recovers Lemma 4

At `j = tp` the time is `tp/N = t/(k+1)`, and

    ‖j·v/N‖ = ‖t·v/(k+1)‖ < 1/(k+1)  ⟺  |t·v − m(k+1)| < 1  ⟺  (k+1) | t·v,

both sides being integers. Writing `d_t = (k+1)/gcd(t, k+1)`:

> For every `t = 1,…,⌊(k+1)/2⌋` (so that `tp ≤ H`), a bad cover must contain a
> speed divisible by `d_t`.

Verified on every known obstruction:

| `k` | `p` | tuple | `d_t` witnesses |
|---|---|---|---|
| 5 | 17 | `(1,21,24,40,41)` | `d₁=6`→24, `d₂=3`→21,24, `d₃=2`→24,40 |
| 5 | 19 | `(1,5,53,54,55)` | 54 for all `t` |
| 6 | 23 | `(1,6,7,8,9,15)` | `d_t=7` → 7 |
| 7 | 41 | `(1,4,12,13,14,16,20)` | `d₁=8`→16, `d₂=4`→4,12,16,20, `d₄=2`→… |

**But this is Lemma 4.** Rosenfeld proves `lcm(2,…,k+1) | ∏vᵢ` by exhibiting the
lonely time `t = 1/j`; the chain here exhibits the same times `t/(k+1)` from the
covering side. Independent rederivation, not new leverage.

## 3. The new part: exact self-similarity in blocks around `tp`

For `j = tp + s`,

    j·v/N  =  t·v/(k+1)  +  s·v/N.

If `(k+1) | t·v` the first term is an **integer**, so `‖j·v/N‖ = ‖s·v/N‖` and:

> **If `(k+1) | t·v`, then `v` covers `tp + s` if and only if `v` covers `s`.**
> Exact — no approximation.

Checked over `k ∈ {5,6,7}`, `p ∈ {11,…,41}`, all valid `t`, all admissible `v`,
`s < 40`: **zero counterexamples**.

Conversely, if `(k+1) ∤ t·v` then `t·v/(k+1)` has fractional part at least
`1/(k+1)`, so `v` can only cover `tp+s` once `s·v` is comparable to `p`. Hence
for small `s` the block around `tp` is the exclusive responsibility of
`T_t := {v ∈ T : d_t | v}`, and `T_t` must cover that block *exactly as it covers
the corresponding block around 0*.

So the covering problem is **self-similar**: each multiple of `p` carries a
scaled copy of the problem at the origin, restricted to a sub-tuple selected by a
divisibility condition.

## 4. Why this did not close D7

The recursion weakens rather than tightens. For `k = 6` all `d_t = 7`, so every
block delegates to the same sub-tuple `T_t = {v ∈ T : 7 | v}` — typically a
single speed — and the block it must cover is short enough that one speed
suffices. The constraint is satisfied comfortably by the real obstructions rather
than being near-tight, so it does not propagate into a contradiction.

Combined with `D7_ATTACK_v1.md`, three routes are now closed with reasons:

| route | why it fails |
|---|---|
| counting | slack factor `2k/(k+1) ≈ 2`, **independent of `p`** — never improves |
| window width | `kill(T)` unbounded; `k=5, p=19` gives `kill = 2862` while death is at `p = 23` |
| `j`-chain | at `j = tp` it *is* Lemma 4; the self-similar structure is not tight |

## 5. What is now on the table

The self-similarity of §3 is the one asset produced here, and it is exact. It
says the covering problem has a recursive block decomposition indexed by
`t = 1,…,⌊(k+1)/2⌋`, with block `t` handled by the divisibility-selected
sub-tuple `T_t`. Two untested directions follow:

1. **Iterate the recursion.** `T_t` must cover a block; apply `j = 1` and
   `j = tp` *within that block* to constrain `T_t` further. Whether the nesting
   terminates in a contradiction for large `p` is open.
2. ~~**Count the blocks, not the points.**~~ **RETRACTED — see below.**

### Retraction of direction 2

I proposed counting blocks against divisibility-selected sub-tuples, on the
grounds that for `k+1` composite the `d_t` differ and "the demands may genuinely
compete". **They do not.** `d_t = (k+1)/gcd(t,k+1)` always *divides* `k+1`, so the
sub-tuples `T_t = {v : d_t | v}` are indexed by divisors of `k+1` and form a
**nested** family:

| `k` | `k+1` | distinct `d_t` | structure |
|---|---|---|---|
| 5 | 6 | 2, 3, 6 | `T₆ ⊆ T₃, T₂` |
| 6 | 7 | 7 | single |
| **7** | **8** | **2, 4, 8** | `T₈ ⊆ T₄ ⊆ T₂` |
| 9 | 10 | 2, 5, 10 | `T₁₀ ⊆ T₅, T₂` |

Nested constraints do not compete for distinct speeds: satisfying the strongest
(`d = k+1`, attained at any `t` coprime to `k+1`) implies every weaker one. The
`k = 7` case is visible in the data — its `d_t = {8,4,8,2}` are witnessed by
`16, {4,12,16,20}, 16, {4,12,14,16,20}` in the `p = 41` obstruction, and the
`d = 8` blocks both delegate to the *same* single speed `16`.

**So the entire `j = tp` chain collapses to one requirement — some `v` divisible
by `k+1` — which is Lemma 4 at `j = k+1` and nothing further.** Direction 2 is
closed before being attempted, and the composite-`k+1` framing was wrong.

That leaves direction 1 (iterating the recursion inside a block) as the only
live continuation from this line, and it is unexamined.

## 6. Status

- §1, §2, §3: **derived and verified exactly** (zero counterexamples on the
  search ranges stated).
- §2 is a rederivation of known content (Lemma 4), not an advance.
- §4: three routes closed, each with a stated reason.
- **D7 remains open.** Nothing here bounds anything uniformly in `p`.
