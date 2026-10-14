# n=7 BS §7 (`|A| = 5`, `m = 1`) — search reproduced, and why `five_avoid_m1`
# cannot be repaired in place

2026-09-05. Artifact: `LonelyRunner/scripts/n7/verify_section7_m1.py` (runs in
~30s, asserts every claim below).

## 1. BS §7 reproduces exactly, both stages

BS §7 asserts a computer search without publishing it. It reproduces.

**Stage 1 (`N = 49`).** 969 dilation orbits, 3 exceptions — exactly BS's
`{1,4,11,39,43}`, `{1,4,18,22,29}`, `{1,4,18,44,46}`.

**Stage 2 (`N' = 98`).** 3 failing 5-set lifts — exactly BS's
`{4,18,22,50,78}`, `{4,18,44,46,50}`, `{4,50,60,88,92}` — each with
`gcd = 2`, so the LRC normalisation `gcd(D) = 1` disposes of all of them.
BS's closing argument holds.

Two conventions decide the answer, and both are easy to get wrong. They are
recorded in the script's docstring because getting either wrong produces a
plausible-looking wrong result:

- The stage-1 universe is **not** the 42 units mod 49. It is the **21** residues
  whose class mod 7 lies in `{1,2,4}` — the `hres` hypothesis of the Lean
  statement. That is the source of BS's `(1/21)·C(21,5) = 969`. Over all 42
  units one gets 20254 orbits and 48 exceptions, which matches nothing in BS.
- In stage 2 the multiplier ranges over **all** of `1..97`, not the units mod 98.
  Restricting to units manufactures a fourth exception, `(4,44,46,50,67)` with
  `d₆ = 21`, which has `gcd = 1` and so would *not* be covered by BS's gcd
  argument — it looks like a gap in the paper and is not one. The multipliers
  `7, 21, 77, 91` all work for it, and as a real instance those speeds reach a
  minimum distance of `0.283 ≫ 1/7`.

Refinement over the paper: BS lists the failing `d₆` as `{14,28,42}`. The full
set mod 98 is `{14,28,42,56,70,84}` — the same residues mod 49, plus their `+49`
lifts. No disagreement, just BS quoting representatives.

## 2. `five_avoid_m1` cannot be repaired by adding `d₆`

`ROADMAP.md` records that `five_avoid_m1` is false as stated and proposes a
redraft carrying `d₆` and the `gcd = 1` hypothesis, keeping the
`∃ lam, ¬ 7 ∣ lam ∧ qz 1 (lam · dᵢ) ∉ {0,6}` shape. **That redraft does not
work either**, for two independent reasons.

**(a) `d₆` cannot help at `N = 49`.** At `m = 1` a level-1 element is `d₆ = 7k`,
so `λ·d₆ mod 49 = 7·(λk mod 7)` and `q(λ·d₆) = λk mod 7`. Adding `d₆` therefore
only ever *adds* a constraint on `λ`; it can never rescue a `λ` that the five
units already ruled out. The three exceptional 5-sets stay unsolvable at
`N = 49` for every `d₆`. The resolution genuinely requires leaving `N = 49`.

**(b) The `Λ₀` constraint `¬ 7 ∣ lam` fails at `N' = 98`.** Of the 1134
`gcd = 1` configurations at `N' = 98`, **1114** admit a multiplier coprime to 7,
but **20 admit only multipliers divisible by 7** — the three bad 5-sets paired
with an *odd* multiple of 7 as `d₆` (odd `d₆` is what makes the 6-set gcd 1).
For those the only working multipliers are `{7,21,35,63,77,91}`. So no statement
of the form `∃ lam, ¬ 7 ∣ lam ∧ …` is true for them.

**(c) `N' = 98` is outside the framework.** `98 = 2·7²` is not a power of 7. The
whole `qz`/`nu`/`qval` apparatus in `Defs.lean` is defined against `N = 7^(m+1)`.
Stage 2 does not typecheck in it, let alone prove.

## 3. Consequence for the plan

The `m = 1` case is **not** a sorry to be filled at its current site. It needs the
`bs_discrete_q` dispatch restructured so that at `m = 1` a witness may be
produced at a modulus other than `7^(m+1)` and with a multiplier not constrained
to `Λ₀`. The `bs_discrete_to_real` bridge already accepts an arbitrary `N > 0`
and `lam`, so the target interface can absorb this — but the `m = 1` branch has
to be routed around the `qz` layer rather than through it.

This is an architectural change, not a proof-filling task. It should not be
handed to an unattended sorry-filling loop: the only way such a loop can make
`five_avoid_m1` compile is by weakening it, and every weakening available is
false. Items 1-3 of the work order are unaffected.

## 4. Kernel feasibility — SETTLED, and both searches are now done in Lean

An earlier draft of this section said the kernel feasibility of these searches
was unestablished and should not be assumed. It has since been established, in
the affirmative, and both searches are now carried out **inside the Lean kernel**
in `LonelyRunner/LRC/SmallN/IntLRC_7_BS/Section7_M1.lean`:

| theorem | content | time |
|---|---|---|
| `stage1_bad_count` | of the 20349 five-subsets, exactly 63 admit no good multiplier | ~21s |
| `stage1_bad_are_dilates` | those 63 are exactly the dilates of BS's three sets | ~13s |
| `stage1_exc_are_bad` | each of BS's three sets really is exceptional | <1s |
| `stage2_clean` | every `gcd = 1` configuration over `N' = 98` is solvable | ~3s |

All four are proved by `rfl` on `Nat`-valued `Bool` computations — no
`native_decide`, no `decide` over `Finset`, and the **default elaboration stack**
suffices. `#print axioms` reports *no axioms at all* for each: they are pure
kernel computation.

What made it work: phrasing the search over `List Nat` with `Nat` arithmetic,
where the kernel has GMP acceleration, rather than over `Finset (ZMod 49)`.
`maxRecDepth 8000000` and `maxHeartbeats 4000000` are needed; `--tstack` is not,
provided the two heavy theorems are the only ones in the file (adding a fifth
`rfl` of comparable size did overflow the stack).

So the finite core of the `m = 1` case is **done and axiom-free**. What remains
is only the architectural work in §3: routing the `m = 1` branch around the `qz`
layer so these facts can be connected to `bs_discrete`. The reasons the current
`five_avoid_m1` statement cannot be repaired in place (§2) are unchanged.
