# Does any residue/resonance of (X,Y) REDUCE n, k, or d? — MI findings v1 (2026-07-10)

**Question (user, precise):** not a 1-1 map — does *any* residue/resonance channel
of the public coordinates shave *any* bits off n, k, or d, however small?
**Tool:** mutual information in BITS (MI = expected bits of the target pinned by
the feature = the reduction itself), with the finite-sample bias trap handled by a
permutation null and the detection floor quantified. Subset N≥64 (64,020 keys),
n,k,D recomputed EXACTLY from d. Signal path exact int; MI/log = ranked statistic
(no-float rule allows this). Scripts: `phi_n_MI_reduction_scan_v{1,2}.py`,
`phi_n_MI_confirm_v1.py`, `phi_n_MI_XYmod_decisive_v1.py`.

## Answer: NO reduction of the private key d (or n, k) by any residue/resonance
## channel, to a floor of ~1e-5 bits (clean channels) / ~5e-3 bits (moderate q).

### The bias trap, made explicit (why naive readings scream false leaks)
- Ranking by raw/analytic-bias-corrected MI put q=210 (=2·3·5·7) on top at
  **MI≈0.57 bits, G-test z=+24** — looks like a massive leak. Permutation null:
  **p=0.385.** The χ² asymptotic breaks on sparse tables (210×210 cells, ~1.5
  samples/cell); z AND split-half "replication" just reproduce the bias. Only the
  permutation null exposes it. Every high-z channel (q=128/256, z=10–15) is the
  same artifact — and q=256 shows the smoking gun: full-sample z=+14.6 but BOTH
  split-halves z≈−14 (Simpson reversal from pooling bit-length bands).
- Clean 1-bit channels (X&1, Y-parity, Legendre(X)) vs (n&1, k&1, D&1, sign D):
  all |MI_bc| ≤ ~1e-5 bits, permutation p ≥ 0.17. Nothing.

### The one stable non-null — and why it is NOT a key reduction
`(X*Y) mod 64  vs  D mod 64`: z=+4.87, **permutation p=0.001**, replicates in both
split-halves (z=+4.40, +4.27), MI_bc ≈ **+4.9e-3 bits**. Real association in the
data. But the decisive discriminator settles what it is:
- vs **d mod 64** (actual key low bits): p=0.667 — NULL.
- vs **n mod 64**: p=0.728 — NULL.  vs **k**: null.
So it tracks **D (the residual, D=d−base, base=A+⌊Ak/n⌋)** but NOT the key d, the
denominator n, or k. It is an artifact of how D is *defined* relative to the point
through `base`, confined to the residual, and cryptographically inert: since base
depends on the unknown (n,k), knowing D mod 64 does not yield d mod 64 — and d mod
64 is directly null. 2-adic sweep confirms locality: q=16,32 null; q=64 fires;
q=128,256 artifact-dominated (sparse table + band pooling). Consistent with
look-elsewhere + a 6-bit interaction of the D-term recursion, not fundamental.

### Detection floor (the "even tiny" bound)
- Clean low-cardinality channels: **~1e-5 bits** — we would have seen a reduction
  of the parity/sign of n,k,d larger than that. None exists.
- Moderate channels (permutation-validated): **~5e-3 bits**; the only thing at that
  level is the D-artifact above, which does not reduce the key.

## Verdict for the puzzle
The public coordinates give **no usable reduction of the private key** through any
residue or resonance channel tested — consistent with ECDLP one-wayness, now
QUANTIFIED (≤~1e-5 bits on clean channels) rather than assumed. The method here
(permutation-validated MI in bits + a d-vs-D discriminator + split-half + 2-adic
sweep) WOULD have surfaced a genuine tiny reduction; it surfaced only bias
artifacts and one construction-residual curiosity. Not dismissal — a bounded,
quantified null with the exact sensitivity stated.

## Not closed / next forms (if a mechanism motivates them)
- Higher-order joint features beyond single/CRT residues (grow bias faster than any
  plausible signal — diminishing returns, but nameable specific forms testable).
- The (X,Y)-as-a-point reduction E(𝔽_ℓ) channel (ties to Frobenius a_ℓ — thread B).
- Anything the user's propagation math predicts as a specific (X,Y)→{n,k,D} form.
