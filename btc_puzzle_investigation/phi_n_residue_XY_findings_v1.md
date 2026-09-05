# φ(n)-residue lens on the public coordinates X, Y — findings v1 (2026-07-10)

**Frame.** Systematically test the public-point coordinates X, Y (100k constructed
keys, `constructed_keys_1to160_100k.csv`) through the φ(n)-residue / character
lens — the framework's OWN basis, not generic ML. Statistics: the Ramanujan-sum
`S_q(V)=Σ_i c_q(V_i mod q)` (exact integer projection onto the reduced-residue
"surviving mode" of the averaging operator P_q), full-histogram χ² (any mode),
and the curve-native characters (quadratic/cubic/sextic of X, Y-parity, primes
3/6/7). All exact (int/Fraction, `check_no_float` clean). Analyzed both the full
set and the N≥64 large-d subset (point ≈ uniform). Scripts:
`phi_n_residue_XY_battery_v{1,2}.py`, `phi_n_residue_q53_replicate_v1.py`.

## Verdict: X and Y carry NO φ(n)-residue / character structure, to the 2–3σ
## floor of 100k, and NO leakage of the private-key position. Systematic null.

### Detail
1. **Ramanujan reduced-residue mode S_q (q=2..64), X and Y:** flat. Max |z|≈2.8
   over 126 tests — exactly the survey-maximum of noise. The operator's surviving
   mode is empty for both coordinates.
2. **Full-histogram χ² mod q=2..64:** flat. One apparent spike, q=53 (pooled
   χ²=84.8/df52, standalone perm p=0.003), was the survey maximum over 63 moduli.
   **Split-half replication kills it:** half-1 p=0.312, half-2 p=0.102, and the
   argmax modulus wanders (34, then 48, never 53). Look-elsewhere. Closed.
3. **Quadratic / cubic / sextic character of X:** flat (cubic χ²=1.2/df2, sextic
   χ²=3.2/df5; quadratic balance z=0.30). **Notable negative:** the curve's j=0
   CM / μ₆ structure does NOT imprint on the coordinate distribution — the sextic
   symmetry is invisible statistically. It lives in the curve's arithmetic
   (Frobenius/L-function/isogenies), not in point-coordinate residues.
4. **Curve / χ₋₃ primes 3, 6, 7:** X uniform mod each. No curve-arithmetic imprint.
5. **Joint combinations:** X+Y, X−Y = noise (max |z|≈3.4 over 63, survey-max).
   **X·Y shows z≈125 mod small q — an ARTIFACT, not a finding:** products of
   residues mod q are inherently non-uniform (mod 2, X·Y odd only 1/4 of the
   time), so a uniform null is the wrong baseline; the magnitude would appear for
   any random points. Not key structure. (A product-of-coordinate matched null
   would show ~0 excess — untested, offered.)
6. **Leakage X mod q → position denominator n (exact n recomputed):** null.
   Contingency perm p: q=3→0.129, 5→0.840, 6→0.746, 7→0.965, 8→0.243, 10→0.656.
   No ω(n) leakage either. Confirms the prior "(X,Y)→n/k NULL" the framework-native
   way — with exact contingency + permutation p, not an ML battery.

## What the null MEANS (not "dead"; a precise boundary)
- ECDLP one-wayness holds at the residue level here — verified, not assumed. The
  public coordinates are residue-uniform and reveal nothing about the private-key
  position through any φ(n)/character channel at 100k resolution.
- **It cleanly separates the two sides:** the private-key POSITION selection IS
  structured (base-10 smoothness, `phi_n_native_knd_findings_v1.md`), but that
  structure does NOT propagate to the public coordinates. Exploitable structure,
  if any, lives on the private/position side, not the public/coordinate side.
- The cubic/sextic null redirects the μ₆ thread: the sextic organizing principle
  is real but ARITHMETIC (curve L-function / Frobenius), confirming thread (B)
  — the curve's CM Hecke L — as where φ(n) depth actually lives, not coordinates.

## Honest scope
Null is to the ~2–3σ sensitivity of 100k in the tested lenses (q≤64, marginal +
these joint combos, these characters). Untested: q≫64, higher-order joint
statistics, the product-matched null for X·Y. None dismissed — offered as next
probes if a specific mechanism motivates them.
