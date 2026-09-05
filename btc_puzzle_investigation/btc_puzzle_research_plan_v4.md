# BTC Puzzle — Research Plan v4 (a test for every idea on the menu)

Date: 2026-07-08. Replaces v3's triage. **No idea is benched a priori.** Each
menu item gets a concrete, runnable, exact test. Governed by `CLAUDE.md`
(NO FLOATING POINT in the signal path) and the signal-vs-noise scaling
discipline in `power_scaling.py`.

## 0. The one engine that makes every test informative

The mistake to avoid is asserting "that reduces to ECDLP, so a null is
uninformative." That is a verdict, not a test. The way to make *any* structural
idea produce an informative result — including a null — is the method this
project already uses:

> **Small-scale brute-forceable testbed + measured predictive lift + scaling.**
>
> Pick a bit-width `N` where the true `d` is *knowable* (brute force at
> N ∈ {20,24,28,32}). Build the candidate structural feature. Measure whether it
> gives **lift over blind baseline** at predicting `d` (or bits of `d`). Then
> **sweep `N` and fit the scaling** (`power_scaling.py`): a real structural break
> shows lift that **plateaus** as N grows (it would reach 135-bit and win); an
> artifact shows lift **decaying like 1/N** (matched-null noise). Verdict comes
> from the *scaling*, not one run, and not from a reduction argument.

This turns "you can't beat ECDLP" from an assumption into a **measured**
outcome for each idea — and if any idea's lift plateaus, that IS the break.

Shared harness to build first: **`struct_test_harness.py`** — generates
brute-forceable testbeds `(d, Q=dG)` at a given N, provides a matched null
(random function with the same interface), and wraps `mi_bits` + the
`power_scaling` slope classifier. Every test below plugs into it. Integer/point
ops only; verdict via permutation p-value + scaling slope, never a float
threshold.

---

## The tests (one per menu idea)

### Test A — Ladder / double-and-add trajectory leakage  *(your headline idea)*
- **Idea.** Probe the double-and-add ladder trajectory of a candidate `k` against
  the trajectory implied by `Q`. "Is there a Z-order-sort equivalent for the
  ladder?"
- **Measurable.** Define `T(k)` = the sequence of intermediate points when
  computing `kG` by double-and-add. For many `(d,k)` at width `N`, measure the
  agreement depth between `T(k)` and `T(d)` (longest shared prefix / #shared
  intermediate points) and correlate it with (i) shared high-bit count of `d,k`
  and (ii) `|d−k|`. If a monotone metric sorts candidates toward `d` faster than
  random, that is the ladder-sort.
- **Statistic.** Rank correlation (Kendall, as a *ranked* statistic) between
  trajectory-agreement and shared-high-bits, vs a **matched null** = random
  bijections with the same trajectory-length interface. Exact: integer point ops,
  permutation p-value.
- **Scaling verdict.** Sweep N; lift plateaus ⇒ ladder sort exists (escalate);
  lift decays ⇒ **measured** answer that the ladder has no Z-order analog.

### Test B — Additive-combinatorics / sum-product structure of point sets
- **Idea.** Curve points carry additive (point add) + multiplicative (field
  coords) structure; sum-product says a set can't be both structured — invert to
  look for *constructive* structure.
- **Measurable.** For a point set `S` (real DP table, and orbits `{jG}`), take the
  X-coordinate set `A ⊂ F_p`. Compute **additive energy** `E_+(A)` = #{a+b=c+d}
  and **multiplicative energy** `E_×(A)` = #{ab=cd}, both exact integer counts.
  Compare `(E_+, E_×)` to a random subset of `F_p` of equal size.
- **Statistic.** Permutation null over random equal-size subsets; report where the
  real set falls in the null distribution (exact rank).
- **Scaling verdict.** Sweep `|S|`; persistent deviation ⇒ exploitable structure;
  deviation vanishing to null ⇒ coords are sum-product-random at scale.

### Test C — Isogeny probe
- **Idea.** Map `Q` under an ℓ-isogeny `φ: E → E'`; does the pair `(E,E')` or
  `φ(Q)` leak residue info about `d`?
- **Measurable.** For small ℓ, compute a rational ℓ-isogeny (Vélu) on the
  brute-forceable testbed. Check whether `d mod ℓ`, or any low bits, are
  recoverable from `φ(Q)` faster than blind (i.e., does the isogeny expose a
  Pohlig-Hellman-style residue the prime order is supposed to forbid).
- **Statistic.** Exact integer check on known-`d` testbed: recovered residue
  matches or not; fraction correct vs 1/ℓ chance baseline, permutation null.
- **Scaling verdict.** Any residue lift persisting across N ⇒ escalate; matches
  baseline ⇒ measured null that isogenies give no residue leverage here.

### Test D — Distinguished-point near / multi-collision information
- **Idea.** Near-collisions (walks landing close but not equal, 3-way
  coincidences) may carry partial bits.
- **Measurable.** Instrument a solvable-width kangaroo run. Log near-collisions
  (points sharing top-`b` bits, not equal) and 3-way clusters. Since the offset
  is *known* at solvable width, measure MI between near-collision features
  (gap, cluster size, coordinate deltas) and the true offset.
- **Statistic.** `mi_bits` + matched permutation null + `power_scaling` slope.
- **Scaling verdict.** MI plateau ⇒ exploitable partial info; MI ~1/N ⇒ birthday
  noise.

### Test E — Cross-key generator state-recovery (nonce/RNG bias, #1–160)
- **Idea.** Keys #1–160 from one seeded PRNG stream; recover state and predict.
  Distinct from nulled *known-seed single-key* work: recover **state from the
  outputs themselves**, unknown seed, tested across keys.
- **Measurable.** Offsets `o_i = d_i − 2^{i−1}` for solved keys #1–134 (exact).
  Consumption models {rejection-uniform, `draw mod 2^{i−1}`, 256-bit-mask}. For
  MT19937: untemper the reconstructed words across the whole sequence
  (~134·⌈bits/32⌉ ≥ 624 words = full state) and solve for state **without the
  seed**. For LCG/xorshift: LLL over integer relations among consecutive `o_i`.
- **Statistic / verdict.** **Held-out, integer-exact:** fit on #1..m, check the
  recovered generator reproduces #(m+1)..134 by exact equality. Controls: a real
  MT stream sliced the same way (must succeed); 134 `secrets.randbelow` offsets
  (must null).
- **Outcome.** Reproduces held-out ⇒ regenerate #135 (Coppersmith/LLL back-end,
  Test I, if only partial bits recover). Else bounded conditional negative over
  the enumerated model/family set.

### Test F — CM / GLV endomorphism structure  *(the "genus theory" idea, made concrete)*
- **Idea.** secp256k1 has `j=0`, CM by `Z[ω]`, discriminant −3 — it carries the
  **GLV endomorphism** `(β,λ)`. Does the CM structure partition or bias the DLP?
- **Measurable.** GLV-decompose each solved key `d = d₁ + d₂·λ (mod n)` via the
  integer GLV lattice (`d₁,d₂ ≈ √n`). Test the `(d₁,d₂)` distribution for
  structure vs random; and measure whether GLV halving changes kangaroo's
  jumps-to-collision beyond the known ~√2.
- **Statistic.** Exact GLV lattice reduction (integer); distribution test with
  permutation null; measured jump counts A/B.
- **Scaling verdict.** Bias in `(d₁,d₂)` persisting ⇒ exploit; uniform ⇒ measured
  confirmation GLV yields only the known constant.

### Test G — DP-table percolation / density threshold
- **Idea.** Does effective collision probability rise smoothly with DP density or
  jump sharply at a critical `ρ_c`?
- **Measurable.** Instrument `puzzle_kangaroo_pool.py`; define
  `ρ = #DPs / (√W·2^{−dp_bits})`; log time-to-first-collision and `p_eff(ρ)`;
  sweep `dp_bits`.
- **Statistic.** Integer-exact collision detection (already is); fit `p_eff(ρ)`.
- **Outcome.** Sharp knee ⇒ retune `dp_bits` to the boundary (real constant-factor
  win). Smooth ⇒ birthday model validated.

### Test H — Ladder / Cayley graph classical hitting time  *(quantum-walk idea, classical)*
- **Idea.** Do quantum walks' speedups need the quantum walk, or is the ladder
  graph itself "glued-tree-like"? Test the *classical* structure.
- **Measurable.** Build the kangaroo jump-map functional graph (and the Cayley
  graph of the jump generators) at small width. Measure classical hitting time
  and the transition-matrix spectral gap; compare to an **expander baseline** and
  a **glued-tree baseline**.
- **Statistic.** Measured hitting times + spectral gap vs the two baselines.
- **Scaling verdict.** Glued-tree signature ⇒ escalate; expander-like ⇒ measured
  answer that the graph is unstructured.

### Test I — Coppersmith / lattice with interval + partial-known bits
- **Idea.** Kangaroo's known interval + any "almost-known bits" (from Test D
  near-collisions or Test F GLV) → lattice partial recovery, à la biased-nonce.
- **Measurable.** On small-`N` known-`d` instances, build the lattice from the
  interval `[lo,hi]` + `t` almost-known bits; run LLL; find the **threshold `t`**
  at which recovery succeeds.
- **Statistic.** Recovery success vs `t`, exact integer check.
- **Outcome.** Recovery below the naive known-bit count ⇒ real leverage; only at
  ~all bits ⇒ quantified bound on how much partial info is needed (feeds E/D/F).

### Test J — Biased jump-size / MCMC mixing  *(diffusion/denoising idea)*
- **Idea.** Is uniform `i = X[0] % K` mixing optimally, or is there a
  constant-factor gain from conditioning jump size on a cheap local statistic?
- **Measurable.** A/B at solvable width: uniform vs jump-size conditioned on
  Hamming weight of `X[0]` / distance-to-nearest-DP. Measure interval-coverage
  uniformity and jumps-to-collision.
- **Statistic.** Exact jump counts; distribution comparison.
- **Outcome.** Fewer jumps ⇒ real tuned constant-factor; same ⇒ uniform already
  optimal.

### Test K — DP-coordinate uniformity in practice  *(sum-product, on a real DP table)*
- **Idea.** In-practice shadow of Test B: does the *running* kangaroo's DP table
  show measurable non-uniformity?
- **Measurable.** Dump visited X coords; test `X mod m` (m ∈ {7,251,256,2^k}) and
  jump-increment uniformity vs a matched null of random `r·G`.
- **Statistic.** Exact permutation / rank chi-square vs matched null; run through
  `power_scaling` so a noise-floor blip is classified by N-scaling.
- **Outcome.** Deviation ⇒ escalate; uniform ⇒ kangaroo assumption confirmed at
  scale.

---

## Build / run order
1. **`struct_test_harness.py`** — shared brute-forceable testbed + matched null +
   scaling classifier. Everything plugs in.
2. **Test A** (ladder trajectory) — your headline; first to run on the harness.
3. **Test E** (cross-key state recovery) — self-verifying, own win condition.
4. **Tests B, C, F** (point-set energy, isogeny, GLV/CM) — structural, on harness.
5. **Tests D, G, K, J** — instrument the pool run once, harvest all four.
6. **Test H** (graph hitting time), **Test I** (Coppersmith threshold) — support
   tests; I also serves as back-end if E or D fire.

Every script routes through `check_no_float.sh` before any result is reported.
A null is reported as a **bounded conditional negative** (method + N-range +
matched null), never "impossible."
