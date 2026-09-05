# Bitcoin Puzzle — Investigation Record (Draft v1 — for review, NOT final)

**Purpose.** A working record of what has been *verified*, what has been *tested
and not observed under specific conditions*, and what remains *open or untested*.

**How to read this document (important).** Every "not observed" / negative result
below is conditional on the stated sample size, detector sensitivity, and search
space. **None of them is a proof of impossibility.** Read each as "not observed
under these conditions, so far" — re-testable, and in several cases expected to
become *more* testable as additional puzzle keys are solved (which increases
statistical power). Please do not treat any line here as "settled" or "cannot
work"; that framing is explicitly avoided on purpose.

---

## 1. Verified foundations (independently checked, high confidence)

1.1 **Clean-room dataset — `puzzles_verified.csv` (82 solved puzzles).** For every
row, the private key was run through our own code to compute (X, Y), and the
resulting X was checked against the *actual public key recorded on-chain* in that
address's spend transaction. Result: **82/82 match.** The dataset does not depend
on any prior or third-party file.

1.2 **The (n, k, d) decomposition reconstructs every known key.** Using
`base = 2^(P-1) + floor(2^(P-1)·k/n)` followed by the D-error recursion, all 82
known private keys reconstruct **exactly** (0–3 D-terms, median 2).
- *Verified:* the decomposition is a correct, exact representation of each key.
- *Boundary of the claim:* it is a **universal** representation — it reconstructs
  any integer in ~2–3 terms (confirmed on random numbers), and the D-terms are
  computed from the target value. So it is a verified *encoder / verifier*. On its
  own it is not yet a *forward predictor*; its predictive value is conditional on
  obtaining `n` from public data (see §2).

1.3 **Puzzle structure (matches the sourced description).** Puzzle N's key is an
N-bit number — it lies in `[2^(N-1), 2^N)`, i.e. written as 256 bits it is
`(256−N)` leading zeros followed by N significant bits. This matches the creator's
stated method (a **sourced but unverified** statement): *"consecutive keys from a
deterministic wallet, masked with leading 000…0001 to set difficulty."* The
bit-length window is the one deliberate, documented constraint, and it is what
makes interval search (Pollard's kangaroo) applicable.

1.4 **Key mechanics (clarified and checked).** A raw private key (integer) maps to
exactly one address — a deterministic total function over `[1, n−1]`. WIF-format
keys carry a 4-byte checksum, so a single-character change is rejected as invalid
(checked: 51/51 single-character edits rejected). Note the distinction: *deriving*
an address is not the same as *accessing a funded wallet* — the overwhelming
majority of derivable addresses have never been used on-chain.

---

## 2. Central working hypothesis (the crux)

The effort reduces to one question:

> **Can even a *hint* (a probabilistic lean) about `n` be obtained from the public
> data — the public key (X, Y), block/transaction metadata, or a combination of
> them?**

Rationale: if `n` is hinted, then `k` is constrained to the `φ(n)` residues coprime
to `n`, and the base formula + D-structure narrows the location of `d`. A *full*
determination of `n` is not required — a partial prior is enough to weight a
search. This is the sharpest reduction of the whole effort: we are hunting for
public→`n` *information*, not a closed-form solution.

*Measured magnitude (for context).* Knowing the exact best `(n,k)` narrows the
residual by ~8–9 bits on the tested keys (e.g. puzzle 130: `2^65 → ~2^56`
kangaroo-equivalent work). That reduction is real but is **conditional on already
knowing the right `(n,k)`**, which currently requires the key. Getting `n` *without*
the key is exactly the open question above.

---

## 3. What has been tested toward §2, and under what conditions

*(Read each line as "not observed under these conditions, so far.")*

3.1 **Public → `n`, single functions of (X, Y).** Residues under many moduli;
bit-slices; Legendre symbols; the documented invariants (`gcd(X,n)`, `X·Y mod n²`,
`X mod (n±1)`); and curve-native transforms (GLV endomorphism, point arithmetic
2P/3P/P±G, field operations).
- *Result:* no information gain about `n` above the noise floor of a detector that
  was validated to catch a planted 40%-strength leak.
- *Conditions / limits:* 58–82 samples; single-feature detectors; sensitivity
  roughly to leaks of ≳40% strength. Weaker leaks, and leaks living in
  *combinations* of features, are below what this setup resolves (see 3.2).

3.2 **Public → `n`, feature *combinations* / interactions.**
- *Result:* **not resolvable at the current sample size.** A random-forest
  detector could not detect even a *100%*-strength planted interaction leak with
  58 samples.
- *Reading:* this avenue is **untested**, not negative. A combination-leak could
  exist and be invisible to us purely for lack of data. **This is the single most
  important item to re-run as more keys are solved.**

3.3 **Block / transaction metadata → `n`/`d`.** Funding is a single 2015
transaction (block 339085) for the puzzle set — a constant, so in the fields
examined it carries no per-key information; reveal blocks reflect *when a solver
acted*. No relationship observed under these fields.

3.4 **Generation side — was the wallet a weak/guessable one?** Tested, on the
verified keys, against: guessable-seed brainwallets (`SHA256(seed‖i)`, ~20k
seeds), index brainwallets, time-seeded SHA256 and Mersenne-Twister (≈6.9M Unix
seconds around the funding date), low-bit LCG / autocorrelation / uniformity,
Electrum-v1 (guessable seeds), and BIP32 (common test mnemonics × standard paths).
- *Result:* no scheme in these **bounded** seed-spaces reproduced the keys.
- *Conditions / limits:* only *guessable / bounded* seed spaces were searched. A
  proper high-entropy wallet seed is not brute-forceable and **remains fully
  consistent with the data** — i.e. this does not speak against a *strong*
  deterministic wallet; it only means the specific *weak/guessable* variants we
  could enumerate did not match.

3.5 **Nonce / signature analysis.** For solved puzzles (known `d`), 50 actual
signing nonces were recovered from sweep transactions (each self-verified via
`(k·G).x ≡ r`).
- *Result:* all full-entropy (250–256 bits), no reuse, no detectable bias, minimum
  pairwise gap ~`2^246`.
- *Conditions / limits:* these are the sweep signatures of *solved* puzzles; each
  key signs ~once, so classic per-key lattice (HNP) attacks — which need several
  signatures per key — do not apply to this set. The exposed *unsolved* puzzles'
  reveal signatures have not yet been analyzed the same way.

---

## 4. Reading of the results (bounded)

Under the specific conditions above, no public→`n` hint has been observed, and the
generation is consistent with a proper wallet. These findings **map where, with
current data and methods, no leak was seen.** They do **not** establish that no
such leak exists. At least two avenues — interaction-leaks (§3.2) and
higher-entropy wallet seeds (§3.4) — are limited by data/compute rather than by any
demonstrated absence, and are expected to become more testable over time. This
document should be read as a *snapshot of a search in progress*, not a verdict.

---

## 5. Open threads / explicitly re-testable

- **Interaction / combination public→`n` leaks** — re-run the multivariate hunt as
  the solved-key count grows (more statistical power). *(Highest-priority re-test.)*
- **Exposed *unsolved* puzzles' reveal signatures** — recover and inspect their
  nonces for bias directly.
- **Intended solve path** — Pollard's kangaroo on revealed-pubkey puzzles
  (engineering / compute; the method by which puzzles actually get solved).
- **Stronger detectors / more features** — with the caveat that broadening a
  single-feature search *raises* the multiple-testing floor, so gains there need the
  sample size to grow alongside.

---

## 6. Artifacts

- `puzzles_verified.csv` — 82 on-chain-verified rows: `puzzle, bits, private_key,
  X, Y, address, funding_block, reveal_block, onchain_pubkey_matches_our_X,
  u_position, n, k`.
- Analysis scripts were run during the session (seed/timestamp brutes, leak
  detectors, nonce recovery, decomposition check). They can be saved into this
  folder for reproducibility on request.

---

*Draft v1 — for review. Nothing here is intended as a settled conclusion. Please
flag anything that reads as too absolute and it will be re-worded before this is
locked in.*
