# secp256k1 — computed values from the 21-cycle roadmap (2026-07-09)

Engaging the user's cycle-by-cycle map of genuine unknowns by actually COMPUTING
the feasible ones. These are specific values genuinely uncatalogued for secp256k1
(not "derive-and-confirm" — the numbers themselves were not on hand). Honest about
which are clean and which hit the feasibility frontier.

## Cycle 2 — Aut(E) = μ₆ orbit structure of E(F_p)  [CLEAN]
[ω] fixes only E[ω−1] (order | 3); 3∤n. Negation fixes 2-torsion; 2∤n. So **μ₆
acts FREELY on E(F_p)\{O}**: the group is `O` (fixed) plus exactly
**(n−1)/6 = 19298681539552699237261830834781317975472927379845817397100860523586360249056
free orbits of size 6**. (The G-set structure the user noted is uncharacterized.)

## Cycle 3–5 — endomorphism ring / conductor / class number  [RESOLVED + SELF-CORRECTION]
`disc(Z[π]) = t²−4p = −3f²`, **f fully factored (new):**
`f = 3 · 79 · 349 · 2698097 · 1359580455984873519493666411` (last is a 90-bit prime).

**I first called this "open/infeasible" (32 crater/floor bits, 90-bit prime out of
reach). That was WRONG.** I built a mod-ℓ² crater/floor test (crater ⟺
`ℓ² | #E(F_{p^d})`, `d=ord_ℓ(t/2)`), validated it on 8112 (curve,ℓ) cases against
exact brute force (0 mismatches) — and **every single case was CRATER, zero floors.**
The reason: for ANY j=0 curve the cube-root map `φ:(x,y)↦(βx,y)` is a *visible*
endomorphism (β³=1 ⟹ (βx)³+7 = x³+7) with `φ²+φ+1=0`, so **Z[ω] ⊆ End(E)** always,
and End(E) ⊆ O_K forces **End(E) = Z[ω] = the MAXIMAL order.** Confirmed on
secp256k1 directly: `φ(G) = (βGx, Gy) = [λ]G`, `λ²+λ+1 ≡ 0 (mod n)`.

Cascade (corrects Cycles 3, 4, 5):
- **Cycle 3:** End(secp256k1) = Z[ω], maximal. `[End(E):Z[π]] = f` (all of it); the f
  I factored is the conductor of the **Frobenius order Z[π]**, NOT of End(E).
- **Cycle 4:** secp256k1 sits on the **crater** of every isogeny volcano; the crater
  is a **single vertex** (below). The 90-bit prime is irrelevant to End.
- **Cycle 5:** class number `h(End(E)) = h(−3) = 1` (NOT `h(−3f²) ≈ f` — that is the
  class number of Z[π], the wrong order). The class group acting on the crater is
  trivial.

## Cycle 6 — Frobenius angle  [CLEAN]
`cos θ = t/(2√p) = 0.63538465198540339…`, **θ = 0.88229 rad = 50.55°**. The trace
is ~64% of the Hasse maximum — a moderately large trace, not near an extreme, not
at the center. Specific uncatalogued value.

## Cycle 7/16/17 — p-adic unit root & Hasse invariant  [CLEAN]
- **Hasse invariant = a_p mod p = t** (verified: coeff of x^{q−1} in (x³+7)^{(q−1)/2}
  equals a_q mod q on all small j=0 curves). For secp256k1 it's exactly the trace
  `t = 432420386565659656852420866390673177327` as an element of F_p.
- **p-adic unit root** α (Frobenius eigenvalue that is a p-adic unit, αβ=p):
  Hensel-lifts from α ≡ t (mod p); the next digit (α mod p²)/p =
  `103482995291570382327745514962295612511852368578636630096241337387108360383642`.
  Verified `α² − tα + p ≡ 0 (mod p³)`. Genuinely uncomputed p-adic number.

## Cycle 10 — mod-2 Galois representation  [CLEAN]
2-division poly `x³+7` is **irreducible over F_p** (−7 is a non-cube). So the
**2-torsion field is F_{p³}**, and Frobenius acts on E[2] as a **3-cycle
(image Z/3)**. No rational 2-torsion; mod-2 image is exactly order 3.

## Cycle 7/8 — L-function, p-torsion degree, extension group structure  [COMPUTED]
Using End(E)=O_K ⇒ `E(F_{p^k}) ≅ O_K/(π^k−1)`, π=a+bω (a=(t+f)/2, b=f, norm p).

- **Cycle 7 — first p-torsion degree:** `ord_p(t) = (p−1)/6` (254-bit). p first divides
  #E(F_{p^k}) at `k=(p−1)/6`; below that every extension is prime-to-p. The trace has
  multiplicative **index 6 = |Aut(E)| = |μ₆|** in F_p*. (Parallels `ord_n(2)=(n−1)/64`.)
- **Cycle 8 — exact extension group structure:** `E(F_{p^k}) ≅ Z/d1 × Z/d2`,
  `d1(k) = gcd(A_k−1, B_k)` where `π^k = A_k + B_k ω`. Computed k=1..40. A clean
  **torsion-degree tower**: full E[ℓ] enters E(F_{p^k}) iff deg(ℓ) | k, with
  **deg(3)=2, deg(2)=deg(7)=3, deg(13)=4**, … (matches the embedding tower ord_ℓ(p)
  & twist factors). E(F_p) cyclic (order n prime); **first non-cyclic at k=2** (d1=3);
  d1 peaks at highly-composite k (d1(36) ≈ 1.5·10⁹). Always d1 | p^k−1 (Weil), verified.
- **Trace factorizations t_k (k≤12):** generic — a few small primes each
  (t₂=−11·13·…, t₃=−2²·5·19·23·67·…), no anomalous smoothness.

## Closed flagged threads (2026-07-10) — all typical/clean
- **Cycle 6 Sato–Tate position:** θ=50.55° at the 30th percentile (z=−0.75) of the CM
  ordinary-prime angle law (~uniform on [0,π], Hecke equidistribution — not semicircle).
  Typical, not an outlier.
- **Cycle 9/10 mod-ℓ Galois image:** Frobenius ⊂ Cartan for all ℓ — split-Cartan (ℓ≡1
  mod3), nonsplit-Cartan (ℓ≡2), scalar at ℓ=3. Orders in GL₂(F_ℓ) computed. CM structure.
- **GLV lattice:** reduced basis balanced ~128-bit (standard √2), no anomalously short
  vector. No exploitable geometry.
- **WP7 feature battery:** only spectral/compression/kmer ran (all NULL, control fired);
  6 families un-run but data-starved (synthetic 100k) ⇒ low value.

## Cycles 11–21 — honest scope
These (Selmer/Sha/BSD/Iwasawa, canonical-lift periods, Dieudonné, deformation
stack) mostly require a **lift**: secp256k1 is over F_p, so Selmer/BSD/Iwasawa are
only defined for the Serre–Tate canonical lift over Z_p (or a number-field descent
that may not exist). The lift's **formal group** IS computable and we already have
it: `L(T) = Σ 7^k C(3k,k)/(6k+1) T^{6k+1}` (μ₆-sparse) and the unit root above.
Iwasawa μ,λ and the transcendental periods are genuinely infeasible here.

## Net
The feasible stations of the roadmap now have their actual numbers. The one
genuinely-open-and-partly-infeasible station is **Cycle 3–5: is End(secp256k1)
maximal?** — reduced to 5 crater/floor bits, 4 checkable in principle, 1 (the
90-bit prime) out of reach. That is the honest edge.
