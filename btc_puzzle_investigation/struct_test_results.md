# struct_test_harness — results log (Plan v4)

Exact-integer secp256k1 (imported from `puzzle_kangaroo.py`). Verdicts from
integer success counts + N/M scaling; z printed as diagnostic only (CLAUDE.md).

## Test A — reverse-ladder branch predictor  →  NULL (measured 2026-07-08)

**Question (your headline idea).** Is there a "Z-order-sort for the ladder"? At
each MSB step down from `Q=dG`, the two candidate predecessors are
`half(R_j)` and `half(R_j−G)`; one is the true `R_{j−1}`, chosen by bit `b_j`.
Does any cheap local feature of the candidate pair predict `b_j` above 1/2?

**Runs.**
- Width sweep, M=300 keys/width, N∈{20,24,28,32,36}: features sat at
  acc 0.46–0.53. Persistent sign per feature (x_val ~+, x_low/x_mod7/y_ham ~−).
- Scaling in M at fixed N=24 (M 300→3000): |z| grew ~√10 (x_low −2.9→−9.4,
  x_mod7 −2.5→−8.9) while accuracy held ~0.464 → a **stable ~3% bias**, not
  sampling noise. Left open whether curve-leak or testbed artifact.
- **Decisive control** — uniform `Rprev=r·G`, T=15000: **all features → 0.5**
  (z ∈ [−0.4,+0.4]).

**Why the control is decisive (algebra).** The two candidates always differ by
the fixed point `Ghalf=INV2·G`. If `Rprev` is uniform on the curve, the ordered
pair `(c0,c1)` is identically distributed under `b=0` and `b=1`, forcing exact
0.5. So any bias must come from `Rprev` being **non-uniform** — which at width N
it is (concentrated on `{m·G : m∈[2^{N−1},2^N)}`). That is an interval artifact,
absent at 135-bit scale. The uniform control removes it and the signal vanishes.

**Verdict.** Bounded conditional negative: over N∈[20,36], with the local
features {x/y parity, x mod 7, X-Hamming, X-value, Y-Hamming}, the double-and-add
ladder exposes no per-bit structure beyond the finite-interval sampling artifact.
No ladder-sort. Consistent with the literature frontier (all real ladder leakage
is side-channel → EHNP → lattice, not pure-math trajectory reading).

**Not yet tested (would extend, not overturn):** richer features (multi-step
trajectory windows, endpoint `Q−kG` statistics), and whether *any* nonlinear
learner beats the hand features — but the uniform-`Rprev` symmetry argument caps
all pair-only predictors at 0.5, so these are unlikely to move it.

## Test B — sum-product energy of point-coordinate sets  →  NULL (2026-07-08)
`struct_probes.py B`. Additive energy `#{a+b=c+d}` and multiplicative `#{ab=cd}`,
exact integer counts, vs matched random-F_p-subset nulls. Curve-structure test →
uses real curve points at scale, NOT the 82 solved keys.
- **m=2000** (2000 real curve X-coords from the 100k set, + `{jG}` orbit), 12
  nulls: both real sets at the **Sidon floor E_add=E_mul=7,998,000 = m+4·C(m,2)**,
  ratio exactly 2.000·m², rank 12/12 (indistinguishable from random).
- **AP control**: E_add = 5.33e9 = 1333×, rank 0/12 — detector fires hard.
- (Earlier m=80 run on solved keys agreed: floor 12720, AP 53×.)
- Verdict: secp256k1 point coordinates carry no simultaneous additive+
  multiplicative structure above random, now confirmed at 25× the points. The
  sum-product bound's only empirical shadow here is a confirmation, not an attack.
  Curve-only test → unlimited data, so this scales.

## Test C — isogeny / twist probe  →  NULL (2026-07-08)
`struct_probes.py C`.
- `n·G = O` verified; curve order `n` is prime (Miller–Rabin, cofactor 1) ⇒
  E(F_p) cyclic of prime order: no nontrivial subgroup, no small-order point, no
  Pohlig-Hellman / isogeny-descent residue. There is no `d mod ℓ` for small ℓ
  (ℓ|n impossible). 
- Twist order `n' = 2p+2−n`: small factors {3,13,3319,22639}, large prime
  cofactor (not smooth); moot for on-curve published pubkeys anyway.
- Verdict: no subgroup/isogeny leverage exists to test further.

## Test F — GLV / CM endomorphism  →  NULL (only the known √2) (2026-07-08)
`struct_probes.py F`. 82 solved keys.
- `β³≡1 (mod p)`, `λ³≡1 (mod n)`, and `(βx,y)=λ·P` verified on random points.
- All 82 GLV decompositions `d = d₁+d₂λ (mod n)` valid; `max(|d₁|,|d₂|)` up to
  127 bits ≈ n/2 = balanced GLV (the known ~√2 kangaroo speedup, nothing more).
- `d₁` parity real {38,44} vs random-same-bits {41,41}: no gross bias (n=82, a
  probe not a powered test).
- Verdict: CM structure yields only the standard √2 constant; no exploitable
  bias in the puzzle keys.

## Test K — point-coordinate uniformity (X mod m)  →  NULL (2026-07-08)
`struct_test_K.py`. Three incremental streams (orbit `+G`, kangaroo `walk`,
`stride +BIGSTEP`), X mod m for m∈{2,3,7,17,256,257,65537}, N∈{2k,5k,10k,20k},
chi-square ranked vs 60 matched integer-uniform null draws (no float threshold).
- Signal signature (exploitable clustering bias) = rank→0 AND deepening with N:
  **no modulus in any stream shows it.** Low ranks that appear (orbit m3=1,
  stride m257=0 at small N) rebound as N grows — noise; with 84 cells a couple
  near the floor are expected by chance.
- Only consistent non-random effect: orbit `m65537` → rank 60 (too *uniform*) =
  Weyl equidistribution of consecutive multiples, benign, and absent in the
  walk/stride streams relevant to DP detection.
- Verdict: X mod m uniform on the curve at scale ⇒ kangaroo/DP uniformity
  assumption holds. Curve-only ⇒ scales.

## Test D — near-collision information  →  NULL (2026-07-08)
`struct_test_D.py`. Solvable kangaroo, W=2^28, 40 instances, walk L=2500. Near-
collision = tame/wild points agreeing in top-16 X bits but not equal; candidate
`c = m0 + t_acc − w_acc` (what `d` would be if exact). 3924 near-collisions.
- Candidates within ±W/100 of the TRUE `d`: 0.0232 vs uniform baseline 0.020;
  permutation rank 46/500 (mid-null).
- Verdict: near-collisions are no closer to `d` than to a random instance's `d`
  — no partial information. X-proximity ≠ scalar-proximity at the collision level
  too (consistent with Test A). Only exact collisions carry `d`.

## Test G — DP-table percolation / density threshold  →  NULL (2026-07-08)
`struct_test_G.py`. 50 solvable kangaroos per dp_bits at W=2^26; #DPs in table at
collision. Percolation threshold ⇒ CV→0; birthday/crossing ⇒ CV~O(1).
- dp_bits 6/8/10: solved 50/50 each; DPs@collision mean 325.8/88.7/29.7,
  CV 0.655/0.494/0.407 — all broad (e.g. dp6 spans 47..811), no CV collapse.
- Verdict: no phase transition — smooth birthday/crossing-time. `dp_bits` is a
  smooth memory/latency tradeoff; no critical density to sit past. (Mild CV drop
  with higher dp_bits is just coarser/fewer DPs, not a threshold.)

## Test J — jump-selection mixing  →  NULL (X%K fine) (2026-07-08, hardened 07-09)
`struct_test_J.py` (M=50→200) + `struct_test_J2.py` (PAIRED confirmation).
- Underpowered M=50 run was ambiguous; M=200 showed R1 `highbits` 4626 vs R0
  `X%K` 5110 — a ~2.2σ apparent edge (unpaired, high variance).
- **Paired confirmation** (`J2`, 300 instances, same d,Q across rules, W=2^22)
  KILLED it: A `X%K` − B `highbits` = **+6.3 ± 27.5 = +0.23σ** (identical). The
  2.2σ was unpaired-design noise. My hypothesised mechanism (low-bit selector
  overlapping the DP mask hurts mixing) is **refuted** — A overlaps and equals B.
  C `higher-bits` is 7–8σ *slower*, so the selector choice does affect the
  constant, but `X%K` is already on the good side.
- Verdict: `i=X%K` leaves no constant-factor on the table vs the natural
  alternative. Methodology note: paired design + a pre-registered mechanism test
  dissolved a plausible-looking false positive.

## Test H — jump-map graph structure (glued-tree?)  →  NULL (2026-07-08)
`struct_test_H.py`. Functional graph `f(x)=(x+jump(xG)) mod M` built by incremental
point addition; rho/cyclic/component stats vs a random-function control + Flajolet–
Odlyzko. **First run used power-of-2 jumps mod 2^16 → 2-adic artifact (comps=168);
refixed with prime M=65521 + random jump constants.**
- Fixed: JUMP-MAP rho=210, cyclic=456, comps=9 vs control rho=525, cyclic=301,
  comps=6, F-O expected cyclic 321 / comps 5.5 — same regime (control cyclic 301
  ≈ F-O 321 validates the counter).
- Verdict: generic random-function graph, single-digit components, cyclic ~√M —
  NOT glued-tree-like (which would show ~1 component, a bottleneck, huge rho). No
  structural or quantum-walk leverage in the jump-map graph.

## Test E — cross-key generator structure  →  NULL for linear/LCG class (2026-07-08)
`struct_test_E.py`. 81 solved keys (bits 2..130). Word `w_i` = top-32-bits of the
in-range position `o_i = d_i − 2^{i−1}`, `w_i = (o_i<<32)//2^{i−1}` (the
`u_position` coordinate; if keys were `lo + floor(u·range)` these are the top 32
bits of consecutive RNG draws). Detectors vs MT19937 + crypto controls:

| dataset | GF2 rank(words) | GF2 rank(affine) | BM(LSB) | serial conc (null n/3=26.3) |
|---|---|---|---|---|
| REAL | 32/32 | 65/65 | 41 | 26 |
| MT19937 ctrl | 32/32 | 65/65 | 41 | 32 |
| secrets ctrl | 32/32 | 65/65 | 40 | 21 |
| LCG positive | **31/32** | **61/65** | **2** | 26 |

- REAL matches both random controls on every linear detector; the LCG positive
  control is caught cleanly (BM linear complexity 2 vs ~40; rank-deficient).
- Verdict: **no weak/linear generator (LFSR / LCG-mod-2^k class) is detectable
  across the solved-key sequence** — extends the earlier weak-*seed* null from
  seeds to generator *structure*.
- **Scope (honest limitation):** a null here does NOT clear a correctly-seeded
  MT19937 — that needs ≥624 consecutive full 32-bit words, and the 81 sparse
  milestone keys (2624 bits total) cannot fill the state. To test MT proper you
  need a dense consecutive run of keys (e.g. #1..#40 all solved at full width),
  which this dataset doesn't contain.
