# n=7 BS §7 (`|A| = 5`, `m = 1`) — a route that stays inside the 7-adic framework

2026-09-06. Supersedes `SECTION7_M1_ANALYSIS_v1.md`, which stands as the record
of BS's own route and why it is unusable here. This file records a different
route that is usable, and what remains before it is a Lean proof.

Artifacts: `LonelyRunner/scripts/n7/verify_section7_m1.py` (BS's route
reproduced), `LonelyRunner/scripts/n7/verify_m1_at_343.py` (this route),
`LonelyRunner/LRC/SmallN/IntLRC_7_BS/Section7_M1.lean` (BS's searches, kernel-verified).

## 1. Why BS's route cannot be used (unchanged from v1)

BS resolve the three exceptional 5-sets by passing to `N' = 2·49 = 98` and
appealing to `gcd(D) ≥ 2`. Three independent obstructions, all verified:

1. `98 = 2·7²` is not a power of 7, so it is outside the `qz`/`nu`/`qval`
   apparatus, which is defined against `N = 7^(m+1)`.
2. Of the 1134 `gcd = 1` configurations at `N' = 98`, **20 admit only multipliers
   divisible by 7**. No statement of the form `∃ lam, ¬ 7 ∣ lam ∧ …` is true for
   them, so the `Λ₀` conclusion shape cannot be preserved.
3. `d₆` cannot help at `N = 49`: a level-1 `d₆ = 7k` has
   `q(λ·d₆) = λk mod 7`, so it only ever *adds* a constraint on `λ`.

## 2. The route that works: go one level UP, not sideways

Instead of `49 → 98`, take `49 → 343`. Then everything stays a power of 7.

**Verified claim.** For every lift mod 343 of every exceptional 5-set, combined
with every valid `d₆` (`7 ∣ d₆`, `49 ∤ d₆`), there is a multiplier **coprime to
7** placing all six elements in the central band. 2,117,682 configurations, zero
failures, under both the strict `qz 2 ∉ {0,6}` band `[49,293]` and the
`circDist ≥ 1/7` band `[49,294]`.

The lifts are the substance, not a detail: a genuine `D` is pinned only mod 49,
so checking BS's three published representatives would establish nothing. Each of
the five elements has 7 lifts mod 343.

**Stronger, and simpler to state.** The exceptionality test appears to be
unnecessary. On 40,000 random configurations drawn from *arbitrary* 5-subsets of
the 21 residues — not only the exceptional ones — there were again zero failures.
So the target statement is plausibly:

> for any five units `d₁…d₅` with residues in `{1,2,4}`, and any `d₆` with
> `7 ∣ d₆`, `49 ∤ d₆`, there is `lam` coprime to 7 with
> `qz 2 (lam·dᵢ) ∉ {0,6}` for all six.

That is a single uniform statement with no carve-out. It is **not yet proved**,
and 40,000 samples is evidence of a general law, not a proof of one — the
exhaustive result above covers only the exceptional sets.

This route also type-checks against the existing code as it stands: `bs_discrete`
already takes `N` existentially, and nothing forces the returned `m` to equal
`max ν(D)`, so returning `m = 2` for an `m = 1` input needs no interface change
at that level.

## 3. Two exact identities the route rests on (both verified)

For `N = 7^3` and `qz 2 x = ⌊(x mod 343)/49⌋ mod 7`:

* `qz 2 ((1 + 49k)·y) = qz 2 y + k·(y mod 7)` — exact, by floor division, since
  `49ky` is a multiple of 49.
* Hence for `d₆ = 7u`: `qz 2 ((1+49k)·lam·d₆) = qz 2 (lam·d₆)`, because
  `(lam·d₆) mod 7 = 0`. **The `Λ₂` freedom moves the five unit arcs and leaves
  `d₆`'s arc fixed.**

So the natural proof shape is: choose `lam₀` fixing `d₆`, then choose
`k ∈ ZMod 7` fixing the five units, whose arcs move by `k·rᵢ` with
`rᵢ ∈ {1,2,4}·(lam₀ mod 7)` — exactly `lemma5`'s three-shift setup.

## 4. What actually remains, stated honestly

The step above is **not free**. `lemma5` needs the five arcs to fit windows of
total length `≤ 5`, which is precisely the §6 compression problem. `five_compress`
proves that for `m ≥ 2`, but it chooses its own multiplier, and there is no
guarantee that multiplier is `Λ₂`-compatible with a pre-chosen `lam₀` that fixes
`d₆`. So one of the following is needed:

**(a) Structural.** Strengthen `five_compress` (or extract from its proof) the
statement that its multiplier can be taken of the form `lam₀·(1 + 49k)` for an
arbitrary pre-chosen unit `lam₀`. Then the `d₆` step composes cleanly and the
`m = 1` case follows with no search at all.

The shape is right: `lambda0_lift` already returns exactly `1 + k·7^m`, and
`five_compress_relabel` composes that with a chosen `lam₀`, so
`five_compress`'s multiplier IS of the form `lam₀·(1 + 49k)` at `m = 2`. The
obstruction is *which* `lam₀`: the compression picks its own, and the ordering
of the Λ-filtration cuts the wrong way.

  * `Λ₂` multipliers `1 + 49k` move the five level-0 arcs and **fix** `d₆`'s arc
    (§3 above). So if `d₆` is fixed first, `Λ₂` cannot break it.
  * But §6's compression works with `Λ_h` for `h < m = 2`, i.e. `Λ₀` and `Λ₁`,
    and those **do** move `d₆`'s arc: under `1 + 7c` it moves by `c·(u mod 7)`
    where `d₆ = 7u`. So the compression is free to destroy a pre-fixed `d₆`.

Re-fixing afterwards is not available, since `Λ₂` is exactly the freedom that
does not touch `d₆`. So (a) requires carrying `d₆` *through* the compression as a
sixth, level-1 element rather than fixing it before or after. That configuration
— `|D₇(0)| = 5`, `|D₇(1)| = 1`, `|D₇(2)| = 0` at `N = 7³` — is not one BS treat:
their `m` is always `max ν(D)`, so they never have an empty top level. It is a
genuine extension of the paper's case analysis, not a transcription of it.

**(b) Computational.** Do the finite check in the kernel. Naively this is
1.06M configurations (after normalizing `d₆ = 7` by dilation) × 294 multipliers
× 6 elements ≈ 1.9×10⁹ kernel operations. Measured kernel throughput on this
tree is ~100k ops/s (`Section7_M1.stage1_bad_count`: ~2M ops in 21s), so that is
several hours — too slow as it stands. A second normalization using the residual
`v ≡ 1 mod 49` dilations divides the config count by about 7, bringing it to
roughly 45 minutes, which is borderline. Route (a) is preferable.

Do **not** attempt to close this by weakening `five_avoid_m1` in place. Its
current statement is false, and every weakening reachable from the `qz 1` /
`¬ 7 ∣ lam` shape is also false — see §1 above and v1 §2.
