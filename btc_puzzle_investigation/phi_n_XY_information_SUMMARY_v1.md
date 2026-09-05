# Is there ANY information about n/k/d in (X,Y)? — consolidated summary (2026-07-10)

The full φ(n)-native investigation of whether the public coordinates (X,Y) carry
*any* recoverable information about the private-key structure (n, k, d). Every test
is exact (int/Fraction signal path; MI/residuals are permutation-validated ranked
statistics), on the 100k constructed keys (N≥64 subset = 64,020, points ≈ uniform),
with a POSITIVE CONTROL (n-vs-k coprimality) that fires on every run — so each null
is a validated null, not a dead detector. Shared machinery: `knd_common.py`.

## Bottom line
**No channel reduces the private key d (or n, k).** Detection floor ~1e-5 bits
(clean 1-bit channels) / ~5e-3 bits (moderate). Every apparent hit was chased to
ground and is either finite-sample/sparse-table bias, a construction artifact
confined to the residual D (never reaching d), or a look-elsewhere flag that fails
split-half replication. This is exactly the ECDLP-one-wayness prediction — now
MEASURED from ~10 independent directions, not assumed.

## Lenses tested (all null for d; positive control fires each time)
| Lens | Result |
|---|---|
| Marginal residues X,Y mod q (q≤64) + quad/cubic/sextic char | null; μ₆/sextic invisible statistically |
| Combinations X±Y, X·Y | null; X·Y "z=125" = product-mod-q baseline artifact |
| Mutual information in BITS (bias-corrected + permutation) | null; q=210 "0.57 bits/z=24" exposed as sparse-table bias (perm p=0.385) |
| Exclusion / negative correlation / depleted cells | null; 0 forbidden cells; odds ratios 0.98–1.01; control fires at min-resid −84 |
| **#1 E(𝔽_ℓ) point-vs-curve, a_ℓ stratified** | null; split (L-active) 0/9 vs supersingular 3/13 flagged → no Frobenius/a_ℓ leakage |
| **#2 cross-key / same-n coupling** | null; constructed keys are random draws; same-n pairs uncorrelated (perm p 0.21–0.74) |
| **#3 propagation / D-recursion targets** (D₁, D_terms, D mod n) | null; 1 flag on d ((X·Y)mod7) FAILS split-half (half1 p=0.925, half2 p=0.003) |
| **#4 derived-point coords** x(λP) GLV, x(2P) doubling, joint | null; triage flags nothing; control fires |

## The recurring "signal" — always the same inert D-artifact
Two lenses (MI: (X·Y)mod64; exclusion: (X+Y)mod16) surfaced a stable, replicating
~5e-3-bit association — but the d-vs-D discriminator settled both identically: they
track the construction residual D (=d−base, base=A+⌊Ak/n⌋), NOT d (p≈0.3–0.7), n,
or k. Predicting D mod m needs the unknown base to reach d, and d mod m is directly
null. Cryptographically inert.

## Where the exploitable structure actually is (localized, not lost)
- NOT in (X,Y): the public coordinates are information-free about the key to ~1e-5 bits.
- IN the private-side POSITION selection: real keys' denominators n lean to high
  ω / base-10 smoothness (primes 2,5) — a ~0.7–1.4-bit search prior
  (`nk_reduction_spec_v1.md`, `phi_n_native_knd_findings_v1.md`). This does NOT
  propagate to (X,Y) (verified). Leverage is the position prior, not coordinates.
- Deep φ(n) reach is ARITHMETIC (curve L-function / μ₆ / CM), not statistical in
  point coordinates (`secp256k1_Lfunction_intersections.md`).

## Untested perspectives remaining (offered, not dismissed)
- The REAL 82 solved keys as target (they carry selection structure the constructed
  set lacks) — but n≈63 at N≥64 is underpowered for residue-MI; leverage stays on
  the position prior.
- Higher doubling iterates x(2ʲP) (doubling-cycle orbit) — x(2P) already null.
- A specific functional form from the user's propagation model — harness ready;
  swap the target, identical validated pipeline.
