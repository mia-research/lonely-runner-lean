# BTC Puzzle — Research Plan v6 (gap audit: what the null battery never touched)

Date: 2026-07-09. A fresh-eyes pass over the entire investigation to find
avenues that the exhaustive null battery (v1–v5) structurally *could not* have
covered. Governed by `CLAUDE.md` (NO FLOATING POINT in the signal path) and the
scaling discipline in `power_scaling.py`.

## What is genuinely exhausted (do not relitigate)

- **Selection process** (how the *integers* were chosen): weak-seed, single-key
  MT fingerprint, `(n,k,D)` channels, `D_terms`, cross-key PRNG state (Test E),
  GLV scalar bias (Test F). All NULL. v5 correctly closed this: 82 keys is below
  the power floor for generator recovery, and manual selection leaves nothing.
- **Curve structure** (intrinsic secp256k1): ladder branch (A), sum-product
  energy (B), isogeny/twist (C), near-collision info (D), DP percolation (G),
  jump-mixing (J), jump-map graph (H), X-mod-m uniformity (K). All NULL, all with
  matched nulls + scaling.
- **NEW this session — single-master-key / masked-nesting.** Tested exactly, both
  bit-directions, all 3240 solved pairs, *and* restricted to `a≥20` where a chance
  collision is ~`2^-19` (so one match = real structure): **0 matches** for
  low-nest `off_a≡off_b (mod 2^{a-1})`, high-nest (top bits equal), raw-key nest
  both ways, and `d_b = c·d_a` for `c≤64`. The "keys are one master AND-masked"
  folklore is now a hard both-directions null, not just a memory note.

The common thread: every test above operates on **scalars we already know** (82
solved `d`). Two datasets were never used because no scalar test can reach them.

## The genuine gaps (ranked by payoff × feasibility)

### GAP 1 — ECDSA nonce analysis of the exposure/spend signatures  ⭐ top
The reason `#135`'s pubkey `02145d…` is *public at all* is that its address had
an on-chain **outgoing transaction** — which carries an ECDSA signature `(r,s)`
over a known message hash `z`, signed **with the puzzle key** under some nonce
`k`. Same for every other exposed-but-unsolved pubkey (`#140/145/150/155/160`)
and every spent puzzle address. **These signatures have never been examined in
this investigation.** This is the *standard real-world* Bitcoin key-recovery
vector (Randstorm, PS3, biased-nonce lattices) and it targets the actual unsolved
prizes, not a structural curiosity.

- **Instant win:** any repeated `r` across two signatures ⇒ reused nonce ⇒
  algebraic recovery of `k` then `d` in closed form. Cheap grep once sigs pulled.
- **Lattice win:** partial nonce bias (short/leading-zero/low-entropy `k`) ⇒
  HNP → LLL/BKZ recovers `d` from a handful of signatures.
- **Honest prior:** if the exposures used RFC6979 deterministic nonces (wallet
  default since ~2014) this is NULL. But the exposures were a deliberate,
  possibly custom-tooled act — checking is cheap and the payoff is total.
- **Input needed:** the raw signature triples `(r,s,z)` for the exposure/spend
  txs. Public, retrievable from any block explorer / node (needs one network
  pull; the rest is offline integer/lattice math). Build `nonce_lattice.py`:
  (1) dedupe `r`; (2) if none, HNP lattice over the collected `(r,s,z)` with a
  small-`k` assumption sweep; exact integer + LLL, verdict via `d·G==Q`.

### GAP 2 — Point-set relations among the exposed unsolved pubkeys
`#135/140/145/150/155/160` are *points*, not scalars — no prior test used them.
Cheap exact checks the scalar battery could not do: is `P_140 = 2·P_135`?
`P_{i+5} = c·P_i` for small `c`? `P_b − P_a` equal to a solved key's point or a
small multiple of `G`? Low prior (GAP-0 scalar-nesting null makes shared-master
unlikely), but it targets the prize and every check is one point-op.
- **Input needed:** the 5 public pubkeys (repo has only `#135`). Then
  `pubkey_relations.py` — all pairwise small-`c` multiples + differences vs the
  solved point-set. Offline, exact.

### GAP 3 — The CM/GLV structure cashed as a SOLVER speedup (not a leak)  ⭐ productive
Tests A/B/C/F rightly nulled the curve's special structure as an *information
leak*. But the current engine (`puzzle_kangaroo_distributed.py:54` `scan_herd`)
is a **naive Pollard kangaroo** and leaves the standard speedups unimplemented —
this is where secp256k1's `j=0` / CM-by-Z[ω] structure actually pays out:

- **No negation map** (`P ~ −P`, i.e. `(x,y)~(x,−y)`): a free, always-valid
  **√2**. (JeanLucPons' Kangaroo uses it; needs the standard fruitless-cycle
  handling.)
- **No GLV endomorphism** `φ(x,y)=(βx,y)=λP`: secp256k1's order-6 automorphism
  group gives up to **√3** more on top of negation. Combined class ≈ √6.
- **Herd design is ~10× off ideal** — the scoreboard says so
  (`puzzle_kangaroo_pool.py:148`). Jump set is powers of two with mean jump
  `~2^{K}/K` (too small); no Gaudry–Schost / 4-kangaroo tuning (2√W → ~1.36√W).

Combined, going from "~10× ideal, no symmetry" to "near-optimal + negation map"
is a realistic **several-× wall-clock cut on the real #135 solve** — the only
avenue here that changes the actual outcome. This is engineering, but it is
*unimplemented*, *real*, and the correct home for the "genus theory / GLV / CM"
idea that was (correctly) dead as a leak.

## Order of work
1. **GAP 1** — pull the exposure-tx signatures (one network step), then
   `nonce_lattice.py` (offline). Highest payoff, standard method, untested.
2. **GAP 3** — negation map first (clean √2, small diff to `scan_herd`), then
   herd/jump tuning, then GLV. Each an A/B at solvable width vs the current engine.
3. **GAP 2** — cheap, low-prior; run once the 5 pubkeys are in hand.

Everything routes through `check_no_float.sh`. Nulls reported as bounded
conditional negatives (method + input set), never "impossible."
