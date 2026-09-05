# What We Positively Know — secp256k1, its CM structure, and the puzzle keys

**Version 1 · 2026-07-11.** A consolidation of *established, verified* facts from the
investigation. Everything here was checked by independent computation (point counts,
Cornacchia in ℤ[ω], direct factorization, brute cross-checks) unless marked otherwise.
Negatives appear only where they are **tightly bound to a method** — stated as "probe
X, by method Y, did not show Z," never as an open-ended "there is nothing."

Conventions: `p` = field prime `2²⁵⁶−2³²−977`; `n` = group order (prime); `t = p+1−n`
= Frobenius trace; `ω` = primitive cube root of unity; `ℤ[ω]` = Eisenstein integers;
`μ₆ = ℤ[ω]*` = the six units `{±1, ±ω, ±ω²}`.

---

## 1. The base object: Eisenstein / CM by ℤ[ω]

- **secp256k1 has complex multiplication by the maximal order ℤ[ω]** (`j = 0`,
  discriminant `−3`, class number `h(−3) = 1`). This is *forced* structure, not a
  coincidence: the map `φ(x,y) = (β·x, y)` with `β³ = 1` is a visible endomorphism
  satisfying `φ² + φ + 1 = 0`, so `ℤ[ω] ⊆ End(E)`, and being maximal, `End(E) = ℤ[ω]`.
  Verified `φ(G) = (β·Gₓ, G_y) = [λ]G`.
- **The curve is the reduction mod p of the Mordell curve `y² = x³ + 7 / ℚ`.** That
  global curve has rank 0 (no rational points to height 200), trivial torsion, and
  conductor `N_E = 21168 = 2⁴·3³·7²`. Bad primes `{2,3,7}`; additive at 7 (`b = 7 ⇒
  y² = x³` cusp ⇒ `a₇ = 0`, `7² | N_E`).
- **Frobenius as an Eisenstein prime.** `π_p = a + b·ω` with `N(π_p) = p`, `2a − b = t`.
  Primary generator (ψ-normalized, unit 1):
  `π_p = 367917413016453100223835821029139468249 + 303414439467246543595250775667605759171·ω`.
- **Classical CM norm form:** `4p = t² + 27M²` with
  `M = 101138146489082181198416925222535253057`, `t = 2a − b = 3M`-linked
  (`disc(charpoly) = t² − 4p = −27M²`).
- **The "angular" structure is real and it is μ₆.** At the complex place of `K = ℚ(√−3)`,
  `ℂ* = ℝ_{>0} × S¹` (polar), and `μ₆ = ℤ[ω]*` sits inside the `S¹`. The Hecke
  Grössencharacter `ψ` has ∞-type `(1,0)`, coupling **radius ↔ angle**. The six units
  are the six angular sectors (60° apart); they index the six sextic twists (§3).
  *Method-bound note:* the Eisenstein **lift direction** of a key's X-coordinate is a
  genuine angle in `ℤ[ω]`, but its distribution over solved keys matched the
  fundamental-domain (hexagon) geometry, not any key property — so the angle is a
  curve-native coordinate, not a key signature.

---

## 2. The deployed constants are (almost) cornered by design goals

- **Why `b = 7`.** With `a = 0` forced by CM, over this `p` the six sextic-twist classes
  of `y² = x³ + b` have six distinct orders; **exactly one class is prime-order**, and
  `b = 7` is the *smallest positive integer landing in it* (`b = 1..6` all give
  composite order; `12/7` is a 6th power mod p, so `b ∈ {7,12}` share the class). So "7"
  is the minimal `b` hitting the unique prime-order twist.
- **Why the offset `977`.** `977` is the first prime found scanning *downward* from
  `2²⁵⁶−2³²−1024` (Solinas fast-reduction convention); `978…1023` are composite. As a
  *bonus*, its field carries a prime-order `j = 0` curve (an ~3% property). The naive
  ascending smallest prime would be `263`, whose field has **no** prime-order `j = 0`
  curve. So the descending convention sidesteps a field that fails the curve test.
- **Why `j = 0` at all — it is forced.** Given "efficient CM endomorphism + cofactor 1":
  the only two efficient CM endos are `j = 0` (`ℤ[ω]`) and `j = 1728` (`ℤ[i]`). Every
  `j = 1728` curve contains `(0,0)`, a 2-torsion point ⇒ **even order ⇒ can never be
  prime-order**. So cofactor-1 + GLV ⇒ uniquely `j = 0 / ℤ[ω]`.
- Across the SEC2 Koblitz family (160/192/224/256), each offset is **the smallest `c`
  where that curve's chosen `b` has prime order**; `b`-choice is a human workflow
  (prefer 7; switch only if another `b` is much better). The generator `G`'s provenance
  is the one genuinely undocumented free choice (not a small multiple of `(1,√8)` to 3M,
  not a hash of common seeds — both tested null).

---

## 3. The twist structure (six sextic twists ↔ six units)

- **Bijection twists ↔ units.** Each of the six sextic twists of `E/𝔽_p` has Frobenius
  `u·π_p` for exactly one unit `u ∈ μ₆`; `b = 7 ↔ u = 1+ω`. The six twist orders are
  `N(π_p + u)` over the six units, and they sum to `6(p+1)` (trace symmetry). secp256k1's
  `t` is the middle magnitude of the six.
- **Unique prime-order twist = the main group.** Of the six, only `π_p − 1` has prime
  norm, `= n`. Three views of one fact: "unique prime neighbor of Frobenius" = "unique
  prime-order twist" = "unique amicable twist" — all hang on `(π_p − 1) = (π_n)`.
- **Twist order factorization (exact):**
  `n_t = 2(p+1) − n = 3² · 13² · 3319 · 22639 · C`, with `C` a 216-bit **prime**.
  The quadratic-twist family member (`b ∈ {2,9}`) has order with a 220-bit prime factor.
- **Embedding degrees on the twist:** `ord_r(p)`: `13 → 4`, `3 → 1`, `3319 → 474`,
  `22639 → 22638`. So the low-embedding-degree pairing corner (`13²`-torsion accessible
  in `𝔽_{p⁴}`) lives **only on the twist**, not the main field. Explicit order-13 point
  on `E₂/𝔽_p` realizing the deg-4 corner is computed and verified.
- **Why 13 specifically.** On `E[13]` the twist Frobenius factors `x² − 6x + 5 ≡
  (x−1)(x−5) mod 13`: root 1 ⇒ rational 13-torsion (`13 | n_t`); companion root 5 has
  order 4 in `𝔽₁₃*` = the embedding degree. `13` is the smallest prime both on a twist
  and with nontrivial small degree.

---

## 4. The amicable pair (p, n) — verified by direct point count

- **`(p, n)` is an elliptic amicable pair:** `#E₇(𝔽_p) = n` and `#E₇(𝔽_n) = p`, a
  length-2 cycle of the map `q ↦ #E(𝔽_q)`. The second equality was **verified by direct
  point-order testing** over `𝔽_n` (Cornacchia in `ℤ[ω]` gives `π` above `n =
  (64502973549206556628585045361533709077, 367917413016453100223835821029139468248)`;
  a point-order test isolates order `p` exactly). **Zero reciprocity symbols used.**
- **Structural reason:** Frobenius at `n` is `1 − π_p`; `(1 − π_p) − 1 = −π_p`, norm `p`.
  At the level of the CM norm form this is the *shared-M* identity:
  `4p = t² + 27M²` and `4n = (t−2)² + 27M²` with the **same** `M` — `p, n` differ only by
  `t → t − 2`, i.e. `π_n = π_p − 1`.
- **The Frobenius quadratic.** `Q(c) = N(π_p − c) = c² − t·c + p` gives `Q(0) = p`,
  `Q(1) = n`, `Q(−1) = n_t`. Over `c ∈ [−200,200]` the longest run of consecutive `c`
  with `Q(c)` prime is exactly `{0,1}` — the amicable pair is that run.
- **Why `Q` is prime-rich:** `disc(Q) = −27M²` (CM disc `−3` × square). By the splitting
  law, `Q` has `1 + χ₋₃(ℓ)` roots mod `ℓ`: **0 at inert primes** (`ℓ ≡ 2 mod 3`), 2 at
  split, 1 at 3. So inert primes (half of all primes) never divide any `Q(c)` — `Q`'s
  values are structurally coprime to half the primes. Hardy–Littlewood constant `≈ 2.28`.
- **Context (known-in-principle):** CM curves have *abundant* length-2 amicable pairs
  (Silverman–Stange); `y² = x³ + 7` averages ~19 pairs over primes `< 15000`, density
  `~0.10·X/(log X)²`. secp256k1's `(p,n)` is the 256-bit member of that family; the small
  members are e.g. `(67,79)`. Length-≥3 cycles: none found in bounded sweeps (conditional
  null, matches S–S rarity — *not* a proof of nonexistence).

---

## 5. GLV = the CM ideal (the exact "lattice/angular" object)

- **The GLV decomposition lattice IS the CM ideal `(π_n) ⊂ ℤ[ω]`.** For the standard
  endomorphism with
  `β = 0x851695d49a83f8ef919bb86153cbcb16630fb68aed0a766a3ec693d68e6afa40`,
  `λ = 0xac9c52b33fa3cf1f5ad9e3fd77ed9ba4a880b9fc8ec739c2e0cfc810b51283ce`,
  the reduced GLV basis of `L = {(a,b) : a + bλ ≡ 0 mod n}` is **exactly `{π_n, ω²·π_n}`**,
  determinant `n`. So the GLV "magic constants" are the Frobenius coordinates.
- On the base field the analogous lattice `L_p = {(a,b): a + bβ ≡ 0 mod p}` has basis
  `{π_p, ω·π_p}`; the two cube-root choices of `β` select the two conjugate primes
  (`π_p` vs `π̄_p`).
- `ord_λ(n) = 3` (GLV eigenvalue is a primitive cube root, verified). `ord_n(2) =
  (n−1)/64` exactly (2 generates the odd part; index `2⁶`). MOV embedding degree of the
  main group `ord_n(p)` is a 254-bit divisor of `n−1` (MOV/FR-safe).
- **One object, many faces:** `(π_n) = (π_p − 1)` ties the GLV lattice, the shared-`M`
  norm form, the unique prime-order twist, and the amicable pair together — they are all
  the single ideal `(π_n)`.

---

## 6. The L-function / Hecke side (all computed from point counts)

- **The CM newform is a theta series (verified to `n ≤ 120`, zero mismatches):**
  `f = Σ_{𝔞 ⊂ ℤ[ω]} ψ(𝔞) q^{N(𝔞)}` equals the point-count newform;
  `f = q + 7q¹³ + 8q¹⁹ − 5q²⁵ + …`. Only `ℤ[ω]`-norms appear; **inert primes give
  `a_ℓ = 0`** (supersingular), split give `ψ(𝔭) + ψ(𝔭̄)`, inert `ℓ²` gives `−ℓ`.
- **Hecke Grössencharacter `ψ` computed, not hand-derived.** `L(E₇/ℚ,s) = L(ψ,s)`,
  ∞-type `(1,0)`, weight 2, `ψ((α)) = χ(α)·α`. **Conductor `𝔣 = (2²)(√−3)²(7)`**,
  `N_{K/ℚ}(𝔣) = 7056`, cross-checked by conductor–discriminant `N_E = 3·7056 = 21168`.
  The finite part `χ` is a **primitive order-6 ray-class character** of `Cl_𝔣` (order 432),
  ramified at 2,3,7 — a genuine product of local characters, *not* a single rational
  sextic symbol. Explicit local formula:
  `χ(π) = χ₄(π mod 4) · (π/π₇)₆⁵ · (π/π̄₇)₆⁵`, `π₇ = −1 − 3ω`.
- **Capstone:** `χ` learned from primes `< 3000` predicts the 256-bit Frobenius exactly
  (`χ(π_p mod 28) = 1 ⇒ ψ(𝔭_p) = π_p ⇒ trace t, #E = n`).
- **Root number `W(E₇) = +1`, self-verified** (no external tables): even theta parity and
  `L(1) = Ω = 3.041417228 > 0` (analytic rank 0), matched to the independently integrated
  real period `Ω = Γ(1/3)Γ(1/6)/(2√π·7^{1/6})`.
- **Formal-group logarithm, closed form (novel-explicit for secp256k1):**
  `L(T) = Σ_{k≥0} 7^k·C(3k,k)/(6k+1)·T^{6k+1} = T + 3T⁷ + (735/13)T¹³ + …`, verified to
  `T³⁷`. Nonzero only at exponents `≡ 1 mod 6` = the full `μ₆` automorphism. Family fact:
  `y² = x³ + b ⇒ Σ b^k C(3k,k)/(6k+1) T^{6k+1}`.
- **CM imprint / twist divisibility law (verified; = Pajaziti–Sadek Thm 4.3):**
  `ℓ | n_t ⟺ Frobenius has eigenvalue −1 mod ℓ`. Inert primes force it, so
  `freq(3 | n_t) = 0.76` for `D = −3`. Sign-reversal: `P(ℓ|n_t | supersingular) >
  P(ℓ|n_t | ordinary) ⟺ ℓ inert in K` (24/24 across two CM fields). Our contribution is
  the worked 256-bit example / statistical reformulation, not the theorem.

---

## 7. The key coordinate: the (n, k, D) decomposition

- **It is a universal, tautological, scale-invariant decomposition.** Any integer `d` in
  `[2^{P−1}, 2^P)` has a best rational approximation `k/n` (denominator capped) to its
  normalized position `(d − A)/A`, `A = 2^{P−1}`, with residual error `D`; `D` itself
  recurses the same way. The decomposition **always exists** for any integer — it is a
  Farey / continued-fraction *coordinate on position*, not a discovered property. This
  "always decomposes / the signature always exists" tautology is the correct, positive
  statement of the `(n,k,D)` framework.
- **Correct implementation:** the best rational approximation of position is
  `Fraction(d − A, A).limit_denominator(NMAX)` (equivalently minimizing
  `|(d−A)/A − k/n|`). This matches the CSV's stored `n_exact` column.
  *Method-bound caveat, established 2026-07-11:* the local helper `best_nk` in
  `knd_common.py` minimizes the *unnormalized* residual `|n(d−A) − kA|` (missing the
  `/n`), biasing it toward small denominators; it disagrees with the standard
  approximation on 15/82 solved keys. Any `(n,k)`-grouped result should be recomputed
  with `limit_denominator`. The **cap `NMAX` is a free parameter** — decompositions and
  any denominator "coincidences" are cap-dependent, so a fixed principled cap (or
  cap-invariance) is required before reading structure into `(n,k)`.

---

## 8. How the keys relate to the curve

- **`d ↔ (X, Y)` is a bijection.** `G` has full order `n`, so the scalar determines the
  point and vice-versa: `d → (X,Y) → d` round-trips with no loss. The *entire* structure
  of a key is fully **present** in its public point. What the ECDLP does is *scramble*
  the readout, not delete information.
- **Consequence (structural):** every low-complexity function of `(X,Y)` is, by the
  scramble, statistically independent of `d`. So a cheap per-point readout recovering `d`
  would itself be a break; the only thing that could survive is a **joint property of a
  set** of keys left by the generator.
- **The key coordinate and the curve's CM coordinate are independent (tightly-bound,
  four exact tests over the 82 solved keys, Round 8 `glv_puzzle.py`):** (1) no
  GLV-conjugate keys (`d_j = λ^s d_i mod n`, both cube roots); (2) no `λ·d_i mod n` lands
  in any small puzzle band; (3) no endomorphism-related public keys
  (`φ(Q_i) = (β·X_i, Y_i)` never equals another known `X_j`); (4) the CF denominator
  `n_exact` is flat across CM classes `d mod 3`. The `(n,k,D)` coordinate is a property
  of `d`'s binary position; the CM atlas is public curve structure; the only bridge (GLV)
  carries no key imprint. **The two real structures do not meet in these keys.**
- **Why "reviving suppressed signal" never reaches a secret (unifying insight):** every
  suppression in the CM picture keeps the *mean* and drops the *oscillation*; un-averaging
  recovers only raw *public* curve arithmetic. The discrete log is **parity-like** —
  invisible to any linear/averaging functional of `Q` (the ECDLP form of the sieve-parity
  obstruction). Extracting `d` needs a bilinear/Type-II handle, which does not exist for a
  prime-order curve over a prime field. This is *why* the inverted-sieve, φ-residue, and
  spectral-rigidity approaches all fail from one cause.

---

## 9. The search picture (what the structure does and does not buy)

- **Unconditional win:** the public endomorphism gives a **GLV + negation-map constant
  speedup** (`√3` from `μ₃`, `√2` from negation) on any interval search. Always on, no key
  exploit.
- **The (n,k) cell decomposition is a lever with a threshold, not a free reduction.**
  Tiling the interval into Farey cells and searching per-cell costs `√Σ(cells)` vs `Σ√`
  — the concave-sum penalty means splitting *raises* cost unless cells can be **excluded**.
  Coprimality (`gcd(k,n)=1`) is a real mutual constraint but it removes *labels*, not
  *d-regions* (coprime cells tile the interval with no gaps). A search reduction needs a
  **region-forbidding** constraint, which could only come from the key-generation recipe.
- *Method-bound status of the generation question:* probes for a generation-level
  `(n,k)` sub-family (denominator coupling of consecutive puzzles) did not survive an
  audit — the one candidate was an artifact of the free cap `NMAX = 256` and the
  small-denominator bias of `best_nk`, and vanished under the correct decomposition and
  other caps. So **no exploitable key-generation structure has been established**; the
  honest path to a specific puzzle remains a Pollard kangaroo on the interval with the
  GLV/negation speedup.

---

## 10. Honest ledger: novel vs known-in-principle

**Genuinely novel / first-computed (for secp256k1, at 256-bit):** the direct point-count
verification of the amicable pair `(p,n)`; the explicit `π_n = π_p − 1` primary identity;
the GLV basis `= {π_n, ω²π_n}` shown equal to the CM ideal; the explicit Hecke `χ` local
formula and self-verified root number; the closed-form formal-group log; the "why `b=7`"
and "why `977`/`j=0` forced" characterizations; the parity-obstruction unification of why
key-extraction approaches fail.

**Verified but known-in-principle (value = a calibrated worked example):** CM by `ℤ[ω]`
and all its consequences; the twist-divisibility law (Pajaziti–Sadek Thm 4.3); abundance
of CM amicable pairs (Silverman–Stange); CM formal groups being hypergeometric.

**Tightly-bound negatives (method-scoped, not open claims):** per-point `(X,Y) → d`
readouts (all null, and null *by construction* per §8); CM-atlas ∩ keys (four exact tests,
null); consecutive-denominator key coupling (audited to a cap artifact). Each says "this
probe, by this method, showed no key signal" — none asserts impossibility.
