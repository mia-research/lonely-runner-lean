# GAP 1–3 results (plan v6) — 2026-07-09

All exact integer. On-chain data via blockstream.info (curl). Scripts:
`sig_lib.py`, `nonce_lattice.py`, `nonce_structure.py`, `pubkey_relations.py`,
`kangaroo_tuning.py`. Artifacts: `sweep2019_*.pkl`, `sweep2019_raw.hex`.

## The dataset nobody had looked at: the 2019 consolidation sweep

tx **`17e4e323cfbc68d7f0071cad09364e8193eedf8fefbcbd8a21b4b65717a4b3d3`**
(block 578732, 2019) spent **21 puzzle addresses in one transaction** →
21 ECDSA signatures from 21 different puzzle keys, one signer, one moment:

- inputs 0–13 = **SOLVED** #65,70,75,…,130 (private key known) — 14 sigs
- inputs 14–20 = **UNSOLVED** exposed keys (#135 confirmed by pubkey + 6 more) — 7 sigs

This is the *entire* on-chain signature surface for the exposed high keys (each
signed exactly once, in this tx). It had never been examined in this project.

## GAP 1 — ECDSA nonce analysis → NULL for recovery (definitive)

Reconstructed the legacy P2PKH SIGHASH_ALL message `z` for all 21 inputs from the
raw tx; **21/21 verify** as valid ECDSA. For the 14 solved inputs, recovered the
actual nonce `k = s⁻¹(z + r·d) mod n`; **14/14 check** (`k·G` has x-coord `= r`).

- **Repeated `r`:** none (21/21 distinct) → no reused-nonce instant win.
- **RFC6979 (the pivot):** **4/14** nonces match standard RFC6979 exactly
  (#85,90,120,125); **10/14 do not** (not raw- nor reduced-`z` convention, not any
  of the first ~6 HMAC-DRBG candidates). A 256-bit RFC6979 match can't be chance,
  so those 4 are genuinely deterministic and 10 are a different derivation
  (consistent with RFC6979 + random extra-entropy / anti-side-channel
  randomization, or a mixed-wallet signing). Forensically odd, not exploitable.
- **Structure of the 10 non-RFC6979 nonces:** full entropy (all ≥249 bits, no
  truncation/small-k); no LCG fit (input order); gcd of all pairwise differences
  = 1; min |kᵢ−kⱼ| = 252 bits (no shared base+counter); top-16-bit values spread
  297…51961 (no MSB bias); no fixed high/low prefix.
- **HNP/lattice:** requires biased or partially-known nonces — none are. Not
  applicable. Each unknown key signed once → no per-key multi-sig attack either.

**Verdict.** Bounded conditional negative: across all 21 signatures of the 2019
sweep, the signer's nonces are either RFC6979 (safe) or full-entropy non-RFC6979
(safe) — no reuse, bias, truncation, or linear structure. The 7 unsolved keys are
**not** recoverable from their on-chain signatures. This closes the standard
real-world Bitcoin key-recovery vector for the puzzle. (Open forensic curiosity:
why 4 plain-RFC6979 among 10 randomized, at input indices {4,5} and {11,12}.)

## GAP 2 — algebraic relations among the exposed pubkeys → NULL

Bonus from GAP 1: the sweep exposed pubkeys for all 7 unsolved keys, not just
#135. Tested the 7 unsolved **points** (+ 82 solved points) — checks no scalar
test could do:
- `P_i = c·P_j`, c ≤ 4096, among exposed pubkeys → none.
- `P_i − P_j` = a solved point or ±(c·G), c ≤ 2²⁰ (BSGS) → none.
- `P_i = a·P_j + b·G`, a ≤ 64, b in ±2²⁰ → none.
- exposed X-coord colliding with a solved X → none.

**Verdict.** The exposed pubkeys carry no small-coefficient algebraic relation
with each other or the solved set — consistent with the GAP-0 scalar-nesting null.
Independent keys.

## GAP 3 — CM/GLV structure as a SOLVER speedup → REAL, unimplemented

Confirmed by code audit that the engine (`scan_herd`,
`puzzle_kangaroo_distributed.py:54`) is a naive Pollard kangaroo with **no
negation map, no GLV endomorphism**, and a **mistuned jump size**: mean jump
`≈2^K/K` with `K=B/2+2` is `0.058·√W` at B=135 vs the van Oorschot–Wiener optimum
`~0.5·√W` (≈9× too small — a big contributor to the "~10× ideal" the scoreboard
flags; the random-restart herd design is the rest).

**Empirical (`kangaroo_jumptune.py`, width 2^18, 40 trials, median jumps):**

| mean jump | median jumps | vs current |
|---|---|---|
| current engine (0.36·√W) | 6,100 | 1.00× |
| 0.25·√W | 5,761 | 1.06× |
| **0.50·√W (optimum)** | **4,723** | **1.29×** |
| 1.00·√W | 6,008 | 1.02× |

The measured cost curve bottoms out exactly at `0.5·√W` (confirms the theory), and
the engine sits below it. At B=18 the engine is already near-optimal (0.36·√W) so
the penalty is only 1.29×; at B=135 the engine is at `0.058·√W`, far down the
steep side, so the tuning penalty is much larger. (Absolute constant ~11.9·√W here
reflects the random-restart harness overhead — persistent herds would drop it
toward ~2·√W; that restart design is a second, separable inefficiency.)

**Standard wins the engine leaves unimplemented (audited-absent):**
- **negation map** `P~−P`: √2, always valid; needs fruitless-cycle handling (the
  reason it's not a one-line change).
- **GLV endomorphism** `φ(x,y)=(βx,y)=λP`: secp256k1's order-6 automorphism, a
  further factor. This is the "genus theory / CM / j=0" idea correctly cashed —
  useless as an information *leak* (GAP tests A/F), real as a solver constant.
- **jump retune** to `√W/2` and **persistent herds** (Gaudry–Schost): recover the
  ~10× toward the 2√W ideal.

Reference implementation that already does all of this: JeanLucPons/Kangaroo.

## STRUCTURE FOUND / MEASURED (discovery framing — reframed 2026-07-09)

Reoriented from "can it break a key" to "what previously-unknown structure is
here, even tiny." Scripts: `nonce_variant_id.py`, `curve_structure_probe.py`.

**FOUND (genuine, previously-unnoticed, in public data): nonce heterogeneity in
the 2019 sweep.** The 21 signatures were made under **two different nonce
regimes**: 4 use plain deterministic RFC6979 (#85,90,120,125), 10 use a
non-deterministic nonce (random added entropy — not reproduced by RFC6979 raw/
reduced-z, ndata counters 0–19 in both byte orders, or naive hash schemes). The 4
deterministic ones **cluster at adjacent input pairs** (idx 4–5, 11–12). r-values
are ~uniform (10 low / 11 high) so it is NOT low-R grinding. This is a real
forensic fingerprint of how the creator signed — heterogeneous tooling — that no
prior work had extracted. Not exploitable; genuinely new.

**PRESENT (the curve's actual structure, laid out exactly): CM / GLV.**
- j = 0, CM by Z[ω], discriminant −3. p ≡ n ≡ 1 (mod 3).
- Frobenius trace `t = p+1−n` (129-bit). **CM norm form `4p = t² + 3f²` verified
  exactly**, f = 303414439467246543595250775667605759171 (128-bit).
- GLV: `λ²+λ+1 ≡ 0 (mod n)`, `β³ ≡ 1 (mod p)` — the order-6 automorphism.
- **Twist order `2p+2−n` carries small square factors `3²·13²`** (·3319·22639·big
  prime) — real structure, inert for on-curve pubkeys.

**MEASURED uniform — and provably so, not an underpowered null:**
- valid-x density = ½ with no residue-class bias (max|z|<1.8 at 2e5); the global
  QR bias is `(t−1)/p ~ 3.7e−39`, pinned by the trace — **below detection by the
  Weil character-sum bound**, i.e. a theorem, not a sampling limit.
- consecutive-multiple X-coords: Weyl-equidistributed (top-byte χ²=254/255).
- p≠2²⁵⁶ top-bit deficit = `2⁻⁶⁸` per sample (undetectable below ~2⁶⁴ draws).
- 82 solved keys: uniform mod {2..16}, uniform offset bits, random factorization —
  no generation quirk. Nonce↔key: no bit-correlation (14 sigs).

## High-power leak scan on the 100k dataset (not the 82 keys) — `leak_scan_100k.py`

Correcting a methodology error: structure/leak questions belong on the **100k**
dataset (78,540 rows with bits ≥ 42), not the 82 real keys. Exact bit-correlation
of every low bit of the private `d` against every bit of the public columns,
z-scored vs the multiple-testing max:

| public value → low bit of d | pairs | max|z| | null-max | verdict |
|---|---|---|---|---|
| **X** (point x-coord) | 10240 | 3.85 | 4.30 | noise |
| **Y** (point y-coord) | 10240 | 4.05 | 4.30 | noise |
| n (CF denominator) | 640 | 3.56 | 3.59 | noise |
| k (CF numerator) | 2560 | 3.07 | 3.96 | noise |
| D (residual) | 2560 | **7.74** | 3.96 | trivial* |
| control: d↔d (self) | 1600 | 280 | 3.84 | (sanity ✓) |
| control: random col | 1600 | 4.01 | 3.84 | noise ✓ |

*D↔d fires only because `D = d − base` is a deterministic invertible function of
`d` — expected, not a leak.

**Per-band scaling (the 100k's unique asset, bits 42→160):** max|z| for X/Y↔d
stays pinned at the null-max (3.8–4.9, no upward trend) across all four bands
(N=12k–26k each). A real leak would grow with N; this is flat.

**Linear-combination probe (`linear_leak_100k.py`):** a ridge-linear predictor of
a private-d bit from ALL 256 bits of X (or Y), held-out accuracy vs shuffled-label
null. Every target bit: held-out 0.496–0.505 (z ∈ [−1.0, +1.3]) = chance; shuffled
null ~0.50; sanity control (d-bits→d-bit) = 1.0000 (z=140). No leak even to a
linear model over the whole coordinate.

**The curve map `d→(X,Y)` leaks no scalar bit — demonstrated with power on 78,540
real points (single-bit, scaling, and linear-combination), not asserted.**

## Overall verdict

The curve's intrinsic statistical structure is **provably minimal** (Weil bounds),
its algebraic structure is exactly the **CM/GLV** package (present, exact), the
keys are indistinguishable from uniform random, and the points are algebraically
independent. The one genuinely new empirical structure surfaced is the **2019
sweep's nonce heterogeneity**. Separately, GAP 3 (engine constant factors) is the
only avenue that speeds up an actual #135 solve.
