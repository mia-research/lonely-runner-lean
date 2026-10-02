# Literature search: reductions of the lonely runner problem, wall-crossing, hand-off (v1)

2026-10-02. Produced by a `general-purpose` subagent at the owner's request (E275); condensed here. **It is the subagent's account,
not a result of this project.** Convention of the sources: `k` nonzero speeds = `k + 1` runners, so this project's eight runners is
`k = 7`. **Checked by me against the arXiv abstract pages (E276): Rosenfeld, Tao, Beck–Everett.** Everything else is the agent's
reading (it says which it read in full, which at abstract level, which only as a snippet). Nothing here is adopted; any technique
taken up goes through the place test and the pre-use check, as for every import (memory `feedback_n8_no_prereg_no_imports`).

## What exists (verified items first)
- **Rosenfeld, "The lonely runner conjecture holds for eight runners", arXiv:2509.14111** (submitted 17 Sep 2025, revised 16 Oct 2025).
  Computer-assisted. Mechanism (agent's reading of the full text): the Malikiosis–Santos–Schymura bound confines a minimal
  counterexample to `gcd = 1` and `∏ v_i < ~7.4·10⁵⁴` (`k = 7`); a prime-divisibility lemma (for a prime `p`, a finite check over residues
  with times in `(1/((k+1)p))ℤ`) forces `p | ∏ v_i`; verified primes up to 163 force `lcm > 7.4·10⁵⁴`, a contradiction. Finite residues and
  rational times only; no continuity or deformation.
- **Tao, "Some remarks on the lonely runner conjecture", arXiv:1701.02048** (Contrib. Discrete Math. 13, 2018). It suffices to check integer
  speeds of size `n^{O(n²)}`. Mechanism: induction on `n`; speeds placed in a generalised arithmetic progression of rank `r`; rank 1 by
  rescaling; rank `≥ 2` by a Freiman projection creating a collision, then Fourier/Bohr-set bounds. A near-rational versus generic
  dichotomy; rank 1 (all speeds in one AP) carries every known tight instance.
- **Beck–Everett, "Lonely Runner Relations", arXiv:2609.06259** (5 Sep 2026, revised 23 Sep 2026). Any counterexample or tight instance
  satisfies `m·n = 0` for a nonzero integer `m` with `0 < ‖m‖₁ ≤ min(2k+3, ((k+1)/(k−1))·flt(k))`: potential counterexamples lie on finitely
  many integer hyperplanes. The tight instance `(1,…,k)` lies on one (`2x₁ − x₂ = 0`, agent). These are the walls where counterexamples
  must live, not where the isolation hands over.

## Reported by the agent, not checked by me
- Malikiosis–Santos–Schymura, arXiv:2411.06903 (Forum Math. Sigma 2025): `n → n+1` unless a lattice-point sum is `≤ ((n+1)/2)^{n−1}`;
  velocities up to about `n^{2n}`; Remark 1.3: regular `m`-gons fail their property except triangle, square, hexagon (rationality of the
  extremal configuration is load-bearing). Giri–Kravitz give a similar bound.
- Trakulthongchai, "Nine and ten lonely runners", arXiv:2511.22427 (and Rosenfeld, arXiv:2512.01912 for nine); the same skeleton plus a
  sieve lemma; the AP `(1,…,k)` appears as the exactly tight case in the criterion. Sungkawichai–Trakulthongchai, arXiv:2604.23906: tuples
  `≡ (1,…,k) (mod p)` satisfy the property (a local result around the AP residue class).
- Perarnau–Serra survey, arXiv:2409.20160: eq. (4), at a maximising time two runners are simultaneously at minimal distance (a static pinch
  statement); Problem 4, closure of the conjecture under translation `a + V`, is open; Rifford's timely conjecture (a uniform bound on the
  laps before the origin is lonely) is Conjecture 29.
- Rifford, arXiv:2111.13688 (abstract only): the time in laps is equivalent to a covering problem in dimension `n − 2`; verified for small `n`.
- Kravitz, arXiv:1912.06034: a gap either equals `s/(sn+1)` or is `≥ 1/n`; a discreteness-near-the-extremum statement.
- Real-to-integer speeds: Wills, Betke–Wills (linear algebra, not deformation). Beck–Hosten–Schymura, Henze–Malikiosis (zonotopes): not read.
- Classical genericity (Cerf, Thom transversality; a generic path avoids strata of codimension `≥ 2`): snippet level, **UNVERIFIED**; no theorem
  found for arithmetic (lattice) hyperplane arrangements with a path starting at a lattice point such as the AP.
- Three-gap theorem (Sós, Surányi, Świerczkowski): gaps of `{nα}` take at most three values, by continued-fraction descent; a loose match
  (one-dimensional, no rigid extremal configuration).

## Negative findings (stated by the agent)
- No paper found that deforms a general arrangement to the AP along a path with a carried witness.
- Nothing found on relay, hand-off or sweep, on tracking the isolation instant as a function of a continuous deformation parameter, or on
  multi-pinch (codimension `≥ 2`) events; nothing on "wall-crossing" or Cerf-type arguments in the lonely-runner literature itself.

## Agent's five most relevant sources
Perarnau–Serra; Beck–Everett; Tao with MSS; Rosenfeld with Trakulthongchai; Rifford with Kravitz.
