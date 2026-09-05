# secp256k1 feature atlas — v1 (exact algebraic/dynamical structure)

Date: 2026-07-09. Mapping the curve's EXACT structure (not statistics — those are
Weil-bounded and provably featureless). Scripts: `secp256k1_atlas_v1.py`,
`secp256k1_atlas_v2.py`. All features verified by independent computation.

## Verified features

### Arithmetic type
- `p ≡ 3 (mod 4)` → sqrt = a^((p+1)/4).  `p ≡ n ≡ 1 (mod 3)` → cube roots exist (GLV).
- `p ≡ 1 (mod 7)` and `(p−1)` divisible by `2·3·7=42`.
- `n ≡ 1 (mod 64)` (2-adic valuation of n−1 is 6).  `n ≡ 1 (mod 4)`.

### Special points over F_p
- **No 2-torsion**: `x³+7 = 0` has no root mod p (−7 is a non-cube) ⇒ #E odd. ✓
- **7 is a non-QR mod p** ⇒ the point `(0, √7)` lives in `E(F_{p²})`, not `E(F_p)`.
- `x=y` locus (`x³−x²+7=0`) has **no** F_p point.

### Small-torsion x-coordinate map (the headline)
How each division polynomial ψ_m splits over F_p (= how many m-torsion
x-coordinates are F_p-rational):

| m | x-tors deg | #F_p roots | meaning |
|---|---|---|---|
| 2 | 3 | 0 | no 2-torsion |
| **3** | 4 | **4 (all)** | **entire 3-torsion x-set is F_p-rational** |
| 4 | 6 | 0 | none |
| 5 | 12 | 0 | none |
| 6 | 16 | 4 | exactly the embedded 3-torsion (gcd w/ ψ₃ = deg 4) |
| 7 | 24 | 0 | none |
| 8 | 30 | 0 | none |
| 9 | 40 | 4 | exactly the embedded 3-torsion |

**secp256k1's only F_p-rational torsion x-coordinates are the four 3-torsion
ones.** Yet E(F_p) has NO order-3 point (n ≡ 1 mod 3) — the 3-torsion POINTS live
in `E(F_{p²})`. **Verified:** `(0,√7) ∈ E(F_{p²})` has order 3 (`[2]P=−P`).
- `x=0` is a 3-torsion x-coord for EVERY j=0 curve `y²=x³+b` (since
  `[2](0,√b)=(0,−√b)=−(0,√b)`) — a CM/j=0 structural feature.
- The *full* ψ₃ split is the extra mod-p fact that `−4b = −28` is a cube mod p.

### Embedding-degree tower  (ord_ℓ(p) = field where μ_ℓ / ℓ-pairings live)
| ℓ | 2 | 3 | 5 | 7 | 11 | 13 | 17 | 19 | 23 | 29 | 31 | 37 |
|---|---|---|---|---|---|---|---|---|---|---|---|---|
| ord_ℓ(p) | 1 | 1 | 4 | 1 | 10 | 4 | 8 | 18 | 11 | 14 | 30 | 4 |

`ℓ ∈ {2,3,7}` have embedding degree 1 (μ_ℓ ⊂ F_p); a cluster `{5,13,37}` have
degree 4. No small ℓ divides n (n prime), so none give F_p torsion.

### Automorphism group (order 6: ±1, ±[β], ±[β²])
β³≡1 (mod p), λ²+λ+1≡0 (mod n); the λ-orbit of any x is the β-triple
`{x, βx, β²x}` (3 distinct x-coords), confirmed on Gx.

## Thread 1 — x-line multiplication-map dynamics (DONE, verified)

`secp256k1_dynamics_v2.py`. The doubling map descends to the Lattès map
`φ₂(x) = (x⁴ − 56x)/(4(x³+7))` on P¹.

- **Core identity (verified):** `φ₂(x(jG)) = x((2j)G)` for all j — φ₂ is literally
  "double the index." So the entire φ₂ functional graph on P¹(F_p) decomposes as
  **(doubling on E(F_p)=Z/n, folded by ±) ⊔ (doubling on twist E′(F_p)=Z/n′,
  folded)**. Verified exactly on a small prime-order j=0 curve (F₆₁): curve→one
  30-cycle+O, twist→4 fixed(3-torsion)+3-cycle+four 6-cycles, summing to all 62
  P¹ nodes.
- **Fixed points = 5**: `x=∞` (=O) + the four 3-torsion x-coords. On secp256k1 the
  four are *twist* 3-torsion (`3² | n′`), F_p-rational as x-coords.
- **secp256k1 curve-side cycle length = `ord_n(2)`** (verified via the n−1
  factorization `2⁶·3·149·631·107361793816595537·174723607534414371449·
  341948486974166000522343609283189`): `ord_n(2) = (n−1)/64` exactly (250-bit) —
  2 generates the full **odd** part of (Z/n)*, index 64=2⁶. ⇒ the curve-side
  doubling dynamics is **32 giant cycles of length ≈2²⁵⁰** + the lone fixed point
  O. No small cycles on the curve; all short cycles live on the twist (forced by
  `3²·13² | n′`).

## Thread 2 — twist & isogeny structure (DONE, verified)

`secp256k1_twist_isogeny.py`.
- **Twist** `E′`, order `n′ = 2p+2−n = 3²·13²·3319·22639·(220-bit prime)`. So
  `E′(F_p)` has F_p-rational torsion of orders 3, 9, 13, 169, 3319, 22639. The
  `3² | n′` is exactly why the four 3-torsion x-coords are F_p-rational (thread 0).
- **Rational ℓ-isogeny count = CM law, verified.** #F_p-rational ℓ-isogenies from
  E = #roots of `x²−tx+p (mod ℓ)`, and since `disc = t²−4p = −3f²`, this is fixed
  by ℓ mod 3: **2 if ℓ≡1, 0 if ℓ≡2, 1 if ℓ=3** — matched exactly for every ℓ up to 61.
- **Class number `h(−3)=1`** ⇒ only j=0 has CM by Z[ω]; the ℓ-isogeny graph is a
  degenerate volcano (crater only, no descent). **This is the structural reason the
  earlier isogeny probe (Test C) was null** — there is nowhere to descend to.

## Thread 3 — notable / exceptional points (DONE)

`secp256k1_notable_points.py`.
- **Smallest curve point is `(1, √8)`** — x=1 lies on the curve (1³+7=8 is a QR).
  Every non-O point has order n (n prime), so notability is purely the coordinate.
- Many small powers of two are x-coords (0,1,2,3,4,5,6,10,11,13,…); ~half of k.
- **GLV endomorphism has no nontrivial ±fixed point** (gcd(λ∓1, n)=1) — n prime.
- **Generator small-factor curiosity (verified):** `Gx = 2³·3³·5·7·11 · (239-bit
  cofactor)` — smooth part 83160, a ~1/83000 rarity; `Gy = 2³·(cofactor)` only.
  Honest caveat: across the several notability checks run, one coincidence at this
  level is ~expected (multiple comparisons) — noted, not claimed meaningful.
- Gx/Gy Hamming weights 135/123 of 256 (balanced ⇒ unstructured), consistent with
  the documented generator choice.

## Thread 4 — extended arithmetic atlas (DONE) + a correction

`secp256k1_arith_extend.py`.
- **Factorizations (small part · big cofactor C):**
  - `p−1 = 2·3·7·13441·C` (C 237-bit prime)
  - `p+1 = 2⁴·C` (C 252-bit composite)
  - `n−1 = 2⁶·3·149·631·C` (full factorization in thread 1)
  - `n+1 = 2·13·83·45751·509879·C` (C 211-bit prime)
- **Embedding tower ℓ<100:** the only ℓ with ord_ℓ(p) ≤ 3 are {2,3,7} (all =1,
  i.e. ℓ|p−1); no prime <100 has embedding degree 2 or 3. secp256k1 is
  pairing-unfriendly (large embedding degree for n) — no MOV anomaly.
- **CORRECTION to the torsion law (thread 0 said "only 3-torsion"):** extending to
  m=13, ψ₁₃ has **6 F_p-rational roots** — the *twist's* 13-torsion (`13² | n′`).
  The correct statement: **an m-torsion x-coordinate is F_p-rational iff m | n or
  m | n′.** Since n is prime (no small divisor), all F_p-rational torsion x-coords
  come from the twist factors of `n′ = 3²·13²·3319·22639·(prime)` — i.e. levels
  3, 13, 3319, 22639 (and combinations). m=12 → 4 (embedded 3-torsion); m=13 → 6
  (twist 13-torsion). This ties threads 0/2/4 together cleanly.

## Pure-math pivot (2026-07-09): "hitherto-unknown facts" hunt (disciplined)

Reframed to pure discovery about the curve (no exploit/puzzle angle), with random
controls to separate genuine features from expected coincidences.

**Constant-structure hunt (`secp256k1_constant_hunt.py`) → disciplined NULL.**
Apparent outliers all dissolve into *known* structure: `n/p` max-PQ = Hasse bound;
`p` HW 250/256 and `n` HW 192/256 = pseudo-Mersenne form of p / n≈2²⁵⁶; Gx smooth
part (97.7 pct) and β/p over-uniform CF (0.6 pct) within multiple-comparison
expectation over ~20 probes. No hidden structure in the fundamental constants.

**Order fingerprint (`secp256k1_order_fingerprint.py`).** Smallest primitive root
**mod p is 3** (also 5,23,41); **mod n is 7** (also 17,19,37); 2 is a primitive
root of neither (index 14 mod p, 64 mod n). Largest subgroup indices (m=79 mod n
→192, m=47 mod p →42) are within multiple-comparison expectation — no anomalous
small-order element.

**Generator provenance (`secp256k1_generator_origin.py`) → NULL.** G is not a
small multiple of the smallest point (1,√8) up to 3M, P1 not a small multiple of
G, and Gx is not a simple hash of 12 obvious seeds. No recoverable origin.

**META-CONCLUSION:** secp256k1 is **structurally generic given its three defining
features** (pseudo-Mersenne p, CM by Z[ω], twist factors 3²·13²·… of n′). Every
controlled probe recovers a consequence of those or a within-expectation coincidence.

## Global recontextualization — secp256k1 = reduction of a Mordell curve

`secp256k1_global_mordell.py`. secp256k1 is the reduction mod p of the **global
curve E: y²=x³+7 over Q** — a classical Mordell curve with **no integer solutions**.
- **E(Q): no rational points found up to height 200** (consistent with rank 0,
  trivial torsion; E(Q)={O}).
- **Bad primes 2, 3, 7.** At ℓ=7 the curve degenerates to y²=x³ (a cusp) →
  **additive reduction**, `a₇=0`, and `7² | conductor` (so the crypto constant
  b=7 is exactly what makes 7 a bad prime). Conductor = 2^·3^·7²·… (exact value
  needs Tate's algorithm — not the "3888" my script wrongly printed).
- **L-function CM pattern (verified):** `a_ℓ = ℓ+1−#E(F_ℓ) = 0` iff **ℓ ≡ 2 (mod 3)**
  (supersingular) — plus ℓ=7 (bad). This is the same CM law as the isogeny count
  (thread 2), now on the global L-function.
- secp256k1's **trace `t = a_p`** is the p-th L-coefficient; `p≡1 mod 3` ⇒ p is
  **ordinary** and splits as ππ̄ in Z[ω] (thread: CM structure).

## Next threads to map (candidates)
1. **x-line multiplication-map dynamics** — the doubling map φ₂ (deg-4 rational
   map) and φ_m on the x-line: periodic points (= torsion of order | 2^k±1),
   functional-graph structure. Fixed points already = 3-torsion (mapped).
2. **CM / ideal structure** — factor p in Z[ω] (`p=ππ̄`), the Frobenius π, how n
   sits in the CM lattice; the exact GLV lattice basis.
3. **Twist structure** — E′ order `2p+2−n` has small squares `3²·13²`; map E′'s
   accessible torsion and any transfer.
4. **Notable points** — points with special coordinates (small x, low Hamming,
   perfect powers, x tied to Gx).
