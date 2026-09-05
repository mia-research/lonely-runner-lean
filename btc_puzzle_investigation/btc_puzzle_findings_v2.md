# Bitcoin Puzzle — Investigation Record (Draft v2)

**Supersedes / extends** `btc_puzzle_findings_v1.md`. This version adds (1) a
methodology section that is load-bearing, not decorative, and (2) the results of a
session of experiments that went beyond re-confirming the known ECDLP flatness and
into tests of things that were genuinely not known.

**How to read this (unchanged in spirit from v1, sharpened):** every negative
result below is stated *with the parameters that produced it*, because the
negative and its conditions are the same fact. There is no line here that says a
thing is impossible, ruled out "at any scale", or "known to be nothing". Where a
test has a validated positive control, that is stated; a negative *without* a
firing control is worthless and is marked as such.

---

## 0. Methodology & mindset (read first — this is the point)

These are the working rules the investigation converged on. They are the reason
the later experiments were worth more than the early ones.

1. **A negative is inseparable from its conditions.** Never "impossible", "at any
   scale", "nothing more", "all channels". Always: *not observed, with these
   features / this sample size / this seed window / this predicate set.* The
   conditions are the content. (This was the single most repeated correction.)
2. **A positive control is mandatory.** An unvalidated null cannot distinguish
   "no effect" from "underpowered / mis-specified test". Twice this session a
   control (a) failed to fire and exposed a broken test, or (b) fired at z≈60 and
   turned a null into a real result. If the control does not fire, the null is
   discarded, not reported.
3. **Confirming ≠ experimenting.** Re-measuring the known (e.g. "does (X,Y) predict
   d" → ECDLP flatness) has near-zero value. Prioritise tests whose outcome is
   *not already in the literature / training data*. Measure on fresh data we
   generate or on the real keys; do not defer to "it is believed hard".
4. **One-way functions are unproven-hard, only seemingly hard.** History: Shor +
   QFT (factoring/DLP), Merkle–Hellman knapsack broken by LLL, LP by the ellipsoid
   method, PRIMES∈P (AKS), FFT, graph-isomorphism (Babai). The *lesson* that
   matters here: real breaks exploit **structure in the specific construction**
   (weak parameters, the PRNG, small secrets) — not the general hard problem.
   secp256k1's ECDLP has specifically resisted the transforms (index calculus)
   that broke its cousins, so the promising road is the *selection process*, not
   the curve.
5. **Target the right object.** d, n, k, the position, the *pair* (n,k) — these
   are different objects. "No leak of d" does not imply "no leak of n".
6. **Look for shadows / exclusions, not only direct prediction.** "This (X,Y) is
   *incompatible* with these n" is a different (and weaker-signal, so easier to
   miss) test than "this (X,Y) predicts n".
7. **Psychology is a valid vector.** The creator's tooling/habits (2015, casual,
   *deliberately weak* keys → no reason to reach for a CSPRNG) narrows the search.
8. **No false dichotomies.** When two avenues are both cheap, do one then the
   other; don't force a choice.

---

## 1. Established facts (high confidence)

1.1 **The keys are deliberately-selected small scalars of an exact bit-length —
   not "masked", not truncated from something larger.** Proven, not assumed: a
   1-bit key (value exactly 1) and an 8-bit key cannot arise from unconstrained
   256-bit generation, which emits ~256-bit values essentially always. The leading
   zeros are automatic fixed-width formatting of a small integer; there is no
   masking *operation*. The construction of an N-bit key is: force bit N−1 to 1,
   fill bits 0…N−2 with N−1 bits from a generator. Entropy was deliberately
   sacrificed down to ~N−1 bits — that sacrifice *is* the search interval.

1.2 **The (n,k,d) decomposition is an encoder, not a predictor.** n and k are
   computed *from* d (n = best rational-approximation denominator of the position
   u=(d−2^{N−1})/2^{N−1}, n≤256; k the numerator). Recovering n ≡ recovering the
   top ~8 bits of the key. Knowing exact (n,k) is worth only ~8–9 bits (v1 §2),
   and getting it "for free" requires the position, i.e. the thing being solved.

1.3 **The consumed randomness is large-state and high-quality.** Positions pass a
   KS uniformity test (D=0.074 < 0.150 crit); no autocorrelation; Berlekamp–Massey
   linear complexity of the consumed-bit stream is maximal (≈n/2) → **rules out
   short LFSRs and power-of-2-modulus LCGs** (their low bits would have tiny linear
   complexity). The low bits are independent per key (first bit-conflict at puzzle
   4) → not a single masked master number. Net: the generator emits ~N−1 fresh
   bits per key, so it is *large-state* (MT19937 / hash-stream / large-modulus
   LCG), not a small-state generator scaled up.

1.4 **The public key's only exploitable leak is algebraic: the kangaroo
   √-speedup.** Address = hash(pubkey), and hashing destroys the group structure →
   address-only search is brute force ~2^{N−1}. An exposed public key is the actual
   curve point → discrete log in a known interval → Pollard's kangaroo in ~2^{(N−1)/2}.
   This is why exposed-pubkey puzzles (multiples of 5) fell up to 130 bits while
   address-only ones stall near 66–71. For puzzle 135: 2^134 interval → ~2^67 with
   the exposed pubkey.

1.5 **Exact bit-length is a two-sided pin worth 122 bits total for #135.**
   Front-end (excluding all *longer* numbers, 136–256 bits): 121 bits
   (2^256→2^135). Back-end (excluding all *shorter*, 1–134 bits, which sum via the
   geometric series to 2^134−1 ≈ one band): exactly 1 bit (2^135→2^134). Both real,
   asymmetric, and already what kangaroo runs on ([2^{N−1},2^N), not [0,2^N)).

1.6 **Generation is causally independent of the block.** Wallet → keys → addresses
   → (later) funding. 77/82 keys funded together in block 339085 (Jan 15 2015), but
   that block is the *funding*, an upper bound on creation time only; the block
   hash/nonce did not exist at key-generation time. Block, timing, balance are
   downstream of the keys and useless as key *inputs*.

---

## 2. Conditionally ruled out (with the conditions, and control status)

Each line: *not observed, under these conditions.* "CTRL✓" = a positive control
fired, proving the test had power; "no CTRL" = power not demonstrated.

2.1 **(X,Y) → d / position.** Powered mutual-information + permutation nulls +
   control-keypair nulls, on real keys and on fresh synthetic keys; single-feature
   and pairwise interactions; feature family = residues mod small primes, bit
   slices, Legendre symbols. **Exhaustive** (whole population) for bit-lengths 6–20;
   sampled (M=4000) for 20–256. Flat at the noise floor at every bit-length tested.
   CTRL✓ (planted 20–25% leaks detected at 3–25× the floor). *Open:* higher-order /
   learned features beyond pairwise+algebraic.

2.2 **(X,Y) ↔ n, k, and the (n,k) pair.** Algebraic-predicate battery: Kronecker/
   Jacobi symbols mod n, gcd(X,·)/gcd(Y,·) against n/k/nk, multiplicative order
   mod m, X mod n vs k, X·k mod n, divisibility. Permutation null shuffling the
   (n,k) pair across 75 puzzles. All null (nothing at Bonferroni p<0.004). CTRL✓
   (real n-coupling, real k-coupling, synthetic X~k coupling all fire at z≈61–64).
   One flicker: gcd(Y,n)>1 low at z≈−2.0, jackknife-stable but p≈0.067 and
   sign-flips at n±1 → most likely noise, not deleted. *Open:* exotic predicate
   classes (class-group order, higher-degree forms).

2.3 **Weak/guessable generation — seed side.**
   - Python MT (getrandbits / randrange) + SHA256 time-seed, **second**-resolution,
     window 2013-01 … 2015-01, subsampling removed. Null, no CTRL needed (exact
     match discriminator at N≥25).
   - Memorable explicit seeds: Python `random.seed(s)` and Java `Random(s)` +
     idiomatic N-bit generation, s ∈ [0,10^6] ∪ common words/dates. Null.
   - SHA brainwallets (v1 seed_brute), Electrum-v1 + BIP32 common mnemonics
     (v1 wallet_brute). Null.
   - Forward-engine from block-339085 data (time/nonce/hash/prev-hash/merkle) ×
     {MT, SHA, glibc-LCG} × mappings. Null; CTRL✓ (null-target control shows the
     apparent hits are at the random rate).

2.4 **Generator lattice structure (same-block run, puzzles 3–65, n=63).**
   Spectral test (Weyl sums, multiplier-agnostic) at dims k=2,3. No lattice above
   the null. **Control did NOT clear the bar** at n=63 (planted LCGs sit inside the
   random band) → this is *underpowered*, not a clean negative. The binding limit
   is 63 consecutive samples; power grows only as more contiguous puzzles are
   solved.

---

## 3. Open vectors (prioritised — genuinely not exhausted)

3.1 **PRNG, still-recoverable slice (highest-interest generation vector).**
   - **Millisecond / float-resolution seeds.** Every seed sweep so far is
     second-resolution; a `Date.now()` / `time.time()`-float / `currentTimeMillis`
     seed multiplies the space ~10^3–10^6× and is untouched. This single parameter
     would invalidate *all* our second-resolution sweeps if the creator used it.
     Tractable only with a bet on creation ≈ funding ± hours.
   - **Non-Python/Java PRNG families:** JS `Math.random` (2015 V8 = weak MWC1616),
     C `rand()`/glibc additive-feedback, PHP `mt_rand`, .NET. Default-constructor
     *time* seeds.
   - Other generation idioms/order (reverse 160→1, rejection sampling vs top-bit
     forcing — different RNG consumption).

3.2 **Higher-order / learned coordinate structure.** Everything on (X,Y) so far is
   single-feature, pairwise, or hand-built algebraic predicates. A learned model
   (gradient-boosted trees / small net) over a rich joint feature space, targeting
   n or k, is untested. Needs a validated planted-leak control.

3.3 **LLL truncated-generator recovery.** The "right transform" for a hidden LCG,
   able to recover large multipliers the tiny-multiplier scans and n=63 spectral
   test cannot. *Obstruction:* each key is truncated to a different width, so the
   outputs are not uniform truncations of a common modulus; unknown-modulus +
   heterogeneous truncation is research-grade. Not attempted; not dismissed.

3.4 **Intended solve path.** Kangaroo compute on exposed-pubkey puzzles (135 etc.).
   Engineering/compute, ~2^67 for #135. This is how puzzles actually fall.

---

## 4. What moved this session (the headway)

- Reframed from "does the public key leak d" (known-flat) to testing **unknowns**:
  n / k / (n,k) algebraic couplings, shadows/exclusions, generation psychology.
- Established the keys are **selected small integers**, not a diminished use of a
  full-256 wallet key in any recoverable-from-outputs sense (§1.1, §1.3).
- Opened a concrete **PRNG vector** (§3.1) with a clear untested parameter
  (sub-second seed resolution).
- Installed the **methodology** (§0) — controls, conditional negatives, target the
  right object, psychology, no absolutes — which is what makes the open vectors
  worth pursuing rather than re-confirming.

---

*Draft v2 — a snapshot of a search in progress, not a verdict. Every negative is
re-testable and several become more testable as more keys are solved. Scripts for
every experiment above are in `scripts/session_2026-07/`.*
