# What We Know — secp256k1, the Puzzle Keys, the Generation Model, and the φ(n)/RH Intersection

**Version 5.1 · 2026-07-11.** Adds **Appendix A — Literature status** (a web-research
pass placing each claim-cluster against the published record; supplementary, no
change to the body). v5 (the base) was an editorial pass on v4 — no facts, numbers,
or tags changed — correcting places where the body prose stated a *null* or an
*absolute* as a claim about reality rather than about the test (chiefly §10), to
match the discipline §13/§14 already state: test-bound phrasing, restored scope
conditions (the `n↔k` independent-constraint clause, the `Q(c)` `ℓ∤M` clause), and
removal of superlatives and "genuine/clean" filler.

(v4 had added the three domains v1/v2 were silent on — the generation model & open
attack vectors, the exposed-pubkey/signature surface, and the measured
search-reduction accounting — plus the curve-structure and φ(n)/RH material from the
project's findings files.)

**Provenance legend** (per bullet where it varies):
- **[re-checked 2026-07-11]** — a script was run *this* session and the number came out.
- **[relayed]** — from a prior-session script/findings file; read directly this
  session but **not re-run**. "A prior run reported this," not "I verified it."
- **[math]** — follows from an in-text argument.
- **[inference]** — interpretation/value judgment, flagged as such.

Negatives are stated bound to a method: "probe X, by method Y, showed no Z." Per the
project's own rule, an **unvalidated null is worthless**: where a positive control
fired, it is marked **CTRL✓**; where power was not demonstrated, **underpowered**.

Conventions: `p = 2²⁵⁶−2³²−977`; `n` = group order (prime); `t = p+1−n`; `ω` = cube
root of unity; `ℤ[ω]` = Eisenstein integers; `μ₆ = ℤ[ω]* = {±1,±ω,±ω²}`; `A = 2^{N−1}`
for an N-bit key.

---

# PART I — THE CURVE

## 1. Base object: CM by ℤ[ω]  *([math] + [relayed])*

- **CM by the maximal order ℤ[ω]** (`j=0`, disc `−3`, `h(−3)=1`). **[math]:** `φ(x,y)=(β·x,y)`,
  `β³=1`, satisfies `φ²+φ+1=0` ⇒ `ℤ[ω] ⊆ End(E)`; `ℤ[ω]` is the ring of integers of `ℚ(√−3)`,
  so `End(E)=ℤ[ω]`. `φ(G)=[λ]G` verified. secp256k1 sits on the **crater of every isogeny
  volcano** (single vertex, `h=1`); the isogeny probes were null *because* of this.
- **Reduction of `y²=x³+7 / ℚ`** [relayed]: rank 0, conductor `N_E=21168=2⁴·3³·7²`, bad primes
  `{2,3,7}`, additive at 7.
- **Frobenius**: `π_p=a+bω`, `N(π_p)=p`, `2a−b=t`,
  `a=367917413016453100223835821029139468249`, `b=303414439467246543595250775667605759171`,
  `t=432420386565659656852420866390673177327`. CM norm form `4p=t²+27M²`,
  `M=101138146489082181198416925222535253057`.
- **Extra invariants** [relayed]: **Hasse invariant `= a_p mod p = t`**; the **p-adic unit
  root** α (αβ=p) Hensel-lifts from `α≡t mod p`; **mod-2 representation** — `x³+7` is
  irreducible over `F_p` ⇒ 2-torsion field `F_{p³}`, Frobenius image ℤ/3; **μ₆ acts freely**
  on `E(F_p)\{O}` ⇒ `(n−1)/6` size-6 orbits.
- **Angular structure = μ₆** (60° sectors in the `S¹` of the complex place; §11). *Method-bound:*
  a key's Eisenstein lift-direction is a well-defined `ℤ[ω]` angle, but over the solved keys it
  matched the fundamental-domain (hexagon) geometry, not any key property. [re-checked prior + this session's null battery]

## 2. Deployed constants  *(computation [relayed]; intent [inference])*

- **Computed [relayed]:** with `a=0`, exactly one of the six sextic-twist classes over this `p`
  is prime-order, and `b=7` is the smallest `b` in it (`b=1..6` composite-order). `978…1023`
  composite ⇒ `977` first prime descending from `2²⁵⁶−2³²−1024`; ascending smallest prime `263`
  has no prime-order `j=0` curve.
- **`j=0` is forced [math]** given cofactor-1 + efficient CM endo: `j=1728` always contains the
  2-torsion `(0,0)` ⇒ even order ⇒ never prime-order.
- **Intent [inference], flagged:** "Certicom *chose* 977 via a descending Solinas scan" and "each
  SEC2 offset = smallest c where that curve's b is prime-order" are a reconstructed workflow, not
  verified process facts. History: a "977 = smallest offset with a prime-order curve" claim was
  **retracted** after a web search; secp160k1's offset (21389) was an outlier that only fit under
  a further reframing.
- Generator `G` provenance: tested null against a small multiple of `(1,√8)` (to 3M) and a hash of
  common seeds; its provenance is undocumented.

## 3. Twist structure: six sextic twists ↔ six units  *([relayed])*

- Each twist has Frobenius `u·π_p`, `u∈μ₆`; `b=7 ↔ u=1+ω`. Six orders `= N(π_p+u)`, sum `6(p+1)`;
  `t` is the middle magnitude. **Only `π_p−1` has prime norm `=n`** — the unique prime-order,
  unique amicable twist, all resting on `(π_p−1)=(π_n)`.
- `n_t = 2(p+1)−n = 3²·13²·3319·22639·C`, `C` a 216-bit prime.
- Embedding degrees `ord_r(p)`: `13→4`, `3→1`, `3319→474`, `22639→22638`; the low-degree pairing
  corner (`13²` in `F_{p⁴}`) is only on the twist. Explicit order-13 point on `E₂/F_p` computed.
- **Sextic symbols** [relayed]: `[7/π_p]₆=ζ₆⁵`, `[7/π_n]₆=ζ₆¹`, carrier `ζ₆⁴=ω²`.
- The CM twist-order imprint generalizes: **D=−4** (`y²=x³+x`) imprints at 2 (`4|n_t` always),
  confirming it is a discriminant-general CM effect, not secp256k1-special.

## 4. The amicable pair (p, n)  *([relayed] point-count)*

- **`#E₇(F_p)=n` and `#E₇(F_n)=p`** — reported verified by **direct point-order testing over
  `F_n`** (Cornacchia gives `π` above n; a point-order test isolates order p), **no reciprocity
  symbols**. [relayed — not re-run this session; trusted because it is a point-count, which is why
  it overruled an external "sextic obstruction" table that claimed no amicable pair.]
- **[math]:** Frobenius at n is `1−π_p`; `(1−π_p)−1=−π_p`, norm p ⇒ `π_n=π_p−1`. Norm-form shadow
  `4n=(t−2)²+27M²`, same `M`.
- **Frobenius quadratic** `Q(c)=N(π_p−c)=c²−tc+p`: `Q(0)=p, Q(1)=n, Q(−1)=n_t`; longest
  consecutive-prime run is `{0,1}`. **Prime-rich [math]** because `disc(Q)=−27M²` ⇒ `1+χ₋₃(ℓ)`
  roots mod ℓ; inert primes (`ℓ≡2 mod3`) divide no `Q(c)` (for `ℓ∤M`; an inert `ℓ|M` makes
  `disc≡0` and can give a repeated root).
- **Context (known-in-principle):** CM curves have abundant length-2 amicable pairs
  (Silverman–Stange); `(p,n)` is the 256-bit member (small members e.g. `(67,79)`). No length-≥3
  cycles in bounded sweeps (conditional null).

## 5. GLV = the CM ideal (π_n), and the extension tower  *([relayed])*

- GLV lattice `L={(a,b):a+bλ≡0 mod n}` has reduced basis `{π_n, ω²·π_n}`, det `n` — the "magic
  constants" are Frobenius coordinates. Base-field `L_p` has `{π_p, ω·π_p}`.
- `ord_λ(n)=3`; `ord_n(2)=(n−1)/64`; MOV degree `ord_n(p)` = 254-bit divisor of `n−1`.
- **Extension structure** [relayed]: `E(F_{p^k})≅O_K/(π^k−1)`; torsion-degree tower
  `deg(3)=2, deg(2)=deg(7)=3, deg(13)=4`; first non-cyclic at k=2. **mod-ℓ Galois image = Cartan**
  (split for `ℓ≡1 mod3`, nonsplit for `ℓ≡2`, scalar at 3).
- **One ideal, many faces:** `(π_n)=(π_p−1)` unifies GLV, the norm form, the unique prime-order
  twist, and the amicable pair.

## 6. L-function / Hecke side  *([relayed], from point counts)*

- **CM newform = theta series** (verified to `n≤120`): `f=Σ_{𝔞⊂ℤ[ω]}ψ(𝔞)q^{N(𝔞)}=q+7q¹³+8q¹⁹−5q²⁵+…`;
  inert primes `a_ℓ=0`, split `ψ(𝔭)+ψ(𝔭̄)`, inert `ℓ²` gives `−ℓ`.
- **Hecke Grössencharacter ψ**, `L(E₇/ℚ,s)=L(ψ,s)`, ∞-type `(1,0)`. Conductor `𝔣=(2²)(√−3)²(7)`,
  `N(𝔣)=7056`, `N_E=3·7056=21168`. Finite part `χ` = primitive order-6 ray-class character of
  `Cl_𝔣` (order 432), local formula `χ(π)=χ₄(π mod4)·(π/π₇)₆⁵·(π/π̄₇)₆⁵`, `π₇=−1−3ω`. `χ` from
  primes `<3000` reproduces the 256-bit Frobenius exactly.
- **Root number `W=+1`, self-verified**: even theta parity and `L(1)=Ω=3.041417228>0` matched to
  `Ω=Γ(1/3)Γ(1/6)/(2√π·7^{1/6})`. *Caveat [relayed second-review]:* the "π≡−1 ⇒ local root
  numbers +1 ⇒ W=+1" argument is a **non-sequitur** (3 is a bad prime with nontrivial local root
  number); `W=+1` is real but fixed by the bad primes `{2,3,7}`+∞, not by the sieve.
- **Formal-group log, closed form** [relayed]: `L(T)=Σ 7^k C(3k,k)/(6k+1) T^{6k+1}=T+3T⁷+(735/13)T¹³+…`,
  verified to `T³⁷`; nonzero only at exponents `≡1 mod 6` = negation × cube-root CM (the full μ₆).
  (Its novelty is tracked in §14.)
- **Twist-divisibility law (= Pajaziti–Sadek Thm 4.3):** `ℓ|n_t ⟺` Frobenius eigenvalue `−1 mod ℓ`;
  `freq(3|n_t)=0.76`; sign-reversal `P(ℓ|n_t|SS)>P(ℓ|n_t|ord) ⟺ ℓ` inert (24/24). Worked example, not novel.

---

# PART II — THE KEYS

## 7. The generation model  *([relayed], `findings_v1/v2`; the domain v2-of-this-doc omitted)*

- **The keys are deliberately-selected small integers, NOT masked/truncated from a 256-bit key
  [math+relayed].** A 1-bit key (value 1) cannot arise from 256-bit generation. Construction of an
  N-bit key: force bit `N−1` to 1, fill bits `0…N−2` with `N−1` generator bits. The leading zeros
  are formatting, not a masking operation. (Corrects a sourced-but-unverified "masked deterministic
  wallet" description.)
- **The generator tests large-state and high-quality [relayed]:** positions pass a KS uniformity test
  (`D=0.074<0.150`), show no autocorrelation, and have **Berlekamp–Massey linear complexity ≈ n/2**
  (maximal) on the consumed-bit stream — which **excludes short LFSRs and power-of-2-modulus LCGs**
  (those would give low linear complexity). Low bits are independent per key (first bit-conflict at
  #4), inconsistent with a single masked master number. Consistent with an **MT19937 / hash-stream /
  large-modulus LCG** class.
- **Creator context [relayed/inference]:** 2015, informal, keys *deliberately* weak; a single
  funding transaction (block 339085, 15 Jan 2015) funded 77/82 — funding is downstream of
  generation and carries no per-key input. Exposed pubkeys are the **multiples of 5** (§10).

## 8. The key coordinate (n, k, D)  *([re-checked 2026-07-11] + [relayed])*

- **A universal, scale-invariant tautology [math].** Any `d∈[A,2A)` has a best rational
  approximation `k/n` (denominator capped) to `(d−A)/A`, residual `D` recursing the same way. Every
  integer decomposes; the "signature" always exists. It is an **encoder, not a predictor**:
  `n,k` are computed *from* `d`.
- **Two different notions of `(n,k)`, and which is "right" is a definition [re-checked]:**
  `Fraction(d−A,A).limit_denominator(NMAX)` is the standard closest-fraction (minimizes
  `|(d−A)/A−k/n|`) and matches the CSV's `n_exact` column; the helper `best_nk` minimizes the
  *unnormalized* `|n(d−A)−kA|` (small-denominator biased), a **legitimately different quantity**,
  disagreeing on **15/82** keys. The intended notion has not been checked against a written
  definition. The cap `NMAX` is a **free parameter** (e.g. #58/59/60 share a denominator only at
  `NMAX=256`), so a fixed cap or cap-invariance is required before reading structure into `(n,k)`.
- **Two D-recursions, disambiguated [relayed]:** the CSV `D_terms` unit-fraction expansion
  saturates at **4–5 terms** (never 6); the **nested** best-approx (denom≤2048) gives **~11 terms**.
  Real keys look random in *both* (~5–7, mid-range) ⇒ no sum-of-simple-fractions construction. The
  D-signature is an **invertible** encoding of the key.

## 9. Why the curve does not leak the key  *(mixed, tagged inline)*

- **`d↔(X,Y)` is a bijection [math].** Full order n ⇒ scalar ↔ point round-trips losslessly; ECDLP
  scrambles the readout, does not delete it.
- **Powered, quantified null battery — not a heuristic [relayed, CTRL✓]:** `(X,Y)→d/n/k` shows no
  reduction to **~1e-5 bits (clean channels) / 5e-3 (moderate q)**, across MI, exclusion,
  character/residue, high-N (to 252 bits), and nested-deep lenses, all with **firing planted
  controls** (z≈61–202; planted leaks caught at 3–25× the floor). Exhaustive for bit-lengths 6–20,
  sampled 20–256. The one stable non-null — `(X·Y)mod64` vs `D mod64` — tracks the *construction
  residual D*, not d/n/k, and is cryptographically inert. The **`n·Q` near-miss identity**
  `n·Q−(n+k)A=r·G` is exact, but `|r|~1.00·N` is full-size ⇒ no leverage (this is the mechanism
  behind "φ(n) resonance = ECDLP wall").
- **Bias-trap discipline [relayed]:** permutation nulls repeatedly killed sparse-table χ²/z false
  leaks (q=210: MI 0.57 bits, z=+24 → **p=0.385**; q=256 Simpson-reversal from bit-band pooling).
  This is exactly the check the retracted n=129 result skipped.
- **Key coordinate ⟂ CM coordinate on these keys [relayed, four exact tests]:** no GLV-conjugate
  keys, no `λ·d_i` in-band, no endomorphism-related pubkeys, `n_exact` flat across `d mod 3`. Scope:
  the `(n,k,D)` position coordinate and the public CM atlas do not meet in these 82 keys. (Grouped
  by the buggy `best_nk`; re-run under a fixed decomposition to make clean.)
- **The strongest surviving key-side signal — base-10 selection [relayed, p=0.002, magnitude-controlled]:** the
  solved-key denominators `n` carry more distinct prime factors than the Farey null — carried by
  primes **2 and 5** (decimal roundness), **not** 3 (χ₋₃) or 7 (b). So the creator picked
  decimal-round positions; a non-generic key property, exploitable as a *weak* prior, but
  **not curve structure**. (Predates the `best_nk` audit; re-check under a fixed decomposition.)
- **Parity-obstruction reading [inference — a model]:** the discrete log behaves like a parity —
  invisible to linear/averaging functionals of `Q`; extraction would need a bilinear/Type-II handle
  absent for a prime-order curve over a prime field. Organizes why inverted-sieve/φ-residue/spectral
  approaches came up empty; interpretive, not a proof.

---

# PART III — THE ATTACK & SEARCH PICTURE

## 10. What the structure does and does not buy  *([re-checked] + [relayed])*

- **Exposed-pubkey surface [relayed + user]:** every **5th puzzle (#135, 140, 145, 150, 155, 160)**
  has its point on-chain ⇒ a kangaroo runs **directly on the point** (no address-hash barrier). This
  is why exposed-pubkey puzzles fell to 130 bits while address-only ones stall at 66–71. #135:
  `2^134` interval → **~2^67** with the exposed pubkey. Exact bit-length is a two-sided pin worth
  ~122 bits for #135 (front 121, back 1) — already what kangaroo runs on.
- **On-chain signatures — a bounded conditional null [relayed, `gap_results_v6`]:** the 2019 sweep tx
  exposed 21 signatures (14 solved + 7 unsolved incl. #135). 14/14 nonces recovered; no `r`-reuse;
  4/14 plain RFC6979, 10/14 full-entropy (no LCG/bias/truncation found, min pairwise gap 252 bits);
  HNP not applicable (each unknown key signed once). **No recoverable structure was found in these
  21 signatures under the tested attacks (reuse, RFC6979 match, bias, truncation, HNP), so those
  vectors do not apply to this signature set.** Forensic curiosity: the 4 RFC6979 sit at input pairs
  {4,5},{11,12}. The tested algebraic relations among the exposed points found none.
- **Measured search reduction [relayed, `nk_reduction_spec`]:** knowing the *exact* `(n,k)` is worth
  **~8–9 kangaroo-bits** (pins top ~16 bits of d), but you need the key to get it. The *prior* over
  cells (base-10 + N-conditioning `H(n|N)=7.78`) yields a **net ~1.0–1.4 bits** on the 159-bit #160
  range — far below the theoretical "256×/14-bit" lever framing. Non-reductions (with firing controls):
  decomposition alone is **156× worse** than a plain kangaroo (`√A·Σφ(n)/n`); `n↔k` does **not**
  self-compound *without an independent constraint* (k has no structure independent of n).
- **Unconditional win [relayed]:** GLV + negation-map constant speedup (`√3` from μ₃, `√2` from
  negation). No key exploit. A distributed kangaroo-pool solver is built and verified over TCP.
- **Solver soundness — the A–K battery found no exploitable dynamics to its sampled floor [relayed,
  all null CTRL✓]:** X mod m tested uniform on the curve (so the kangaroo/DP uniformity assumptions
  hold); the ladder showed no per-bit structure (a uniform-`Rprev` control caps all pair-only
  predictors at 0.5 by symmetry); the tests for sum-product structure (Sidon floor), near-collision
  information, a DP-percolation threshold, a jump-mixing edge, and glued-tree jump-graph structure
  each came back null. `n` prime ⇒ no Pohlig-Hellman [math].
- **No exploitable generation structure established [re-checked]:** the one candidate (consecutive-n
  coupling) was a `NMAX=256` + `best_nk` artifact. The available path to #135 is a kangaroo on the
  interval with the GLV/negation speedup.

## 11. Open generation-side vectors  *([relayed], `findings_v2 §3`; work not yet done)*

- **Sub-second / non-standard PRNG seeds — an open, un-exhausted vector.** *Every* seed sweep so far was
  **second-resolution**; a `Date.now()`/`time.time()`-float/`currentTimeMillis` seed multiplies the
  space 10³–10⁶× and is **untouched** — it would invalidate all prior sweeps. Non-Python/Java PRNGs
  untested: **2015 JS `Math.random` = V8 weak MWC1616**, C `rand()`/glibc, PHP `mt_rand`, .NET;
  default-constructor time seeds; reverse generation order (160→1); rejection sampling.
- **MT19937 proper is untested [relayed, underpowered]:** clearing it needs ≥624 consecutive
  full-width words; 81 sparse milestone keys can't fill the state. Needs a contiguous solved-key run.
- **Generator-lattice / LLL truncated-recovery [relayed, not attempted]:** the n=63 Weyl-sum spectral
  test is underpowered (planted LCGs sit in the null band). An LLL recovery of a hidden large-modulus
  LCG is obstructed only by heterogeneous truncation widths — research-grade, not tried.
- **Higher-order / learned coordinate features [relayed, untested]:** everything on `(X,Y)` so far is
  single-feature/pairwise/hand-built; a learned model over a rich joint feature space (with a firing
  control) is untested.
- **The shared-early-D-term creator test [un-run]:** whether the 82 keys share fixed early D-terms
  (the only direct creator-fingerprint probe). **Re-check the base-10/ω(n) finding** under a fixed
  decomposition. **WP7 remaining feature families** (compression/Kolmogorov) — scaffolded, un-run.

---

# PART IV — THE φ(n) / RIEMANN-HYPOTHESIS INTERSECTION

## 12. The φ(n)-residue RH programme, its status, and the curve bridge  *([relayed]; heavily scoped)*

Bridges the curve's Hecke `L(ψ,s)` (§6) to the separate φ(n)-residue RH programme (8 Zenodo records).
Kept distinct because the two are different ledgers and the programme's strong claims were walked back.

- **RH programme status — no proof of RH.** Its own chronology: full-RH claim (2026-01-23) → the key
  inequality demoted to a **named conjecture** (01-26) → an **unconditional partial** only (vertical
  ZFR `Re(ρ)≤13/16` for **families** of Dirichlet L, `q≤T^{2/5}(log T)^{−B}`, via Bombieri–Vinogradov,
  02-07) → a finite-rank framework (02-11) on an **unproven "Moment Pumping" hypothesis**.
- **TWO load-bearing gaps, not one:**
  1. **The forcing (Moment Pumping) is broken** — the required moment *decays*, not grows.
  2. **The operator foundation** [relayed, `radial_selfadjointness`]: `Ĥ=πA²` on the stated space
     `[1,∞)` has deficiency indices **(1,1), not (0,0)** (so not essentially self-adjoint; `A` itself
     is (1,0) ⇒ no s.a. extension — the "e.s.a. by Stone" step fails, the dilation being a semigroup).
     The fix (full line `(0,∞)`) restores self-adjointness but **empties `D_φ` to {0}** under the
     *normalized* multiplier `c_n(k)/φ(n)`; only the *un-normalized* Lemma III.1 gives
     `D_φ=span{e^{±iy}}` (on the circle). This is a **normalization clash** and a circle-vs-line
     incompatibility — the real analytic obstruction.
- **What is solid [relayed]:** the coercivity constant `1/12 = min 1/φ(q) = 1/φ(13)` is a theorem
  (`λ_min→1/12`). A reviewer calling `1/12` "numerology" had it inverted.
- **The curve bridges [relayed]:**
  - **secp256k1 is a proven Hilbert–Pólya / spectral-RH instance.** `Z(E/F_p,T)` numerator
    `=(1−πT)(1−π̄T)`, `|π|=√p` (40 digits) = RH-for-this-curve; zeros exactly on `Re(s)=1/2` at height
    `±θ/log p`, θ=50.55°. Operator = **Frobenius on the Tate module**; self-adjointness = the **Weil
    pairing** (`ππ̄=p` = the functional equation).
  - **The Eisenstein norm form IS `L(s,χ₋₃)`:** `r(N)=#{a²−ab+b²=N}=6Σ_{d|N}χ₋₃(d)`, so
    `Σ(r/6)N^{−s}=ζ(s)L(s,χ₋₃)=ζ_{ℚ(√−3)}(s)`. And `a_ℓ=0 ⟺ χ₋₃(ℓ)=−1`; `t` is a Jacobi-sum value.
  - **Eisenstein–Ramanujan survival law (a theorem):** the framework's infinite-lifetime modes are,
    over ℚ, the 2 units ±1; over `ℚ(√−3)`, **μ₆ — six modes**. Operator `Ĥ^CM=π(A_r²+A_θ²)` splits
    into 6 sextic sectors ↔ 6 units; self-adjointness transfers from the radial operator.
  - **Adelic recasting:** the framework is a units-averaged slice of Connes' adele class space;
    `K=ℚ(√−3)` is the natural home because its complex place gives `ℂ*=ℝ_{>0}×S¹` with `μ₆⊂S¹`, so
    the circle/line obstruction (awkward over ℚ, whose archimedean units are only ±1) is native. The
    Grössencharacter `(1,0)` couples them; verified `a_ℓ=2Re(u·π)`, `u∈μ₆`, exact for
    ℓ=13,19,31,37,43,61,67,73,79. The "line as incomplete circle" completion gives a real discrete
    spectrum for every boundary twist — a **consistency model on a free lattice spectrum, NOT the
    Riemann zeros** (those need Connes' `𝔸_K/K*` operator, not done).
- **Spectral corrections (do not restate the retracted claims) [relayed]:**
  - **Wall invariant:** the vertical variance tracks the **Selberg constant `n_L`** (# primitive
    factors), **not** degree — measured `ζ=1.00, χ₋₃=1.00, ζ_K=1.99, L(ψ)=0.99`. "Hecke = 2×ζ" is
    retracted; the curve's primitive `L(ψ)` has ζ's variance.
  - **ZFR Appendix-B rank-2 does not reproduce:** the low-prime feature matrix is provably rank-10
    orthogonal (a theorem); the real common mode is **rank-1** in the large-prime correlations, and
    even sits *below* a matched random null — a localized likely bug (features from `|χ(p)|`/`Re χ(p)`).
    **But the CM/Eisenstein common mode is 3× the Dirichlet one** (eig/edge `[1.269,1.174,1.106,…]`
    → 3 above edge vs 1; ratio `|μ₆|/|μ₂|=6/2`) — the sextic core is visible in the correlation spectrum.
  - **`n_t` is not "spectrally optimal":** the frame is loose (`~10¹⁵⁰`) and `μ(n_t)=0` (squared
    primes 3²,13²) **annihilates** the k=±1 survival mode — a liability. θ-reconstruction is broken
    (θ = t = n_t−p−1 trivially; the factorization adds no info). The "4-layer fingerprint" is a
    **double** alignment (Frobenius sieve + 1.5× mod-3 CM support), not triple; and `n_t` is
    **generic** to the `y²=x³+7` family (74.5% share φ-ratio ≥ 1.625), not a secp256k1 fingerprint.
  - **Iwasawa:** Rubin's `μ=0` for CM curves is a real theorem, but "the inverted sieve computes μ"
    is untested speculation resting on a field-prime/Iwasawa-prime conflation; the claimed "SNR ~10³⁷"
    of the rank-1 background is false (real ≈1σ).
- **Where it touches the keys:** the deep φ(n) thread lives in the curve's **Hecke `L(ψ)`**, not in
  key positions; the φ(n)-"resonance" in the key framework reduces exactly to `[n]P=(n+k)Q+(n·D)G`,
  whose residual is the ECDLP wall (§9).

---

# PART V — METHODOLOGY & LEDGER

## 13. Working methodology  *(`findings_v2 §0`; the discipline that earns the above)*

1. A negative is inseparable from its conditions — never "impossible/at any scale"; state the
   sample, features, floor. 2. A **positive control is mandatory** — an unvalidated null is discarded.
3. Confirming ≠ experimenting — prioritize outcomes not already in the literature. 4. One-way-hard is
   only *seemingly* hard; real breaks exploit the **construction** (weak params, the PRNG, small
   secrets), not the general problem. 5. Target the right object — d ≠ n ≠ k ≠ (n,k). 6. Look for
   **shadows/exclusions**, not only prediction. 7. **Creator psychology is a valid vector**. 8. No
   false dichotomies. **Corollary (this session):** apply the same first-line robustness checks
   (cross-check the tool, vary the free parameter) to a *liked positive* as to a disliked negative —
   the n=129 retraction was excess credulity, not excess skepticism.

## 14. Epistemic ledger  *(the key to reading this document)*

- **Carries its own in-text proof [math]:** `End(E)=ℤ[ω]`; `j=1728` can't be prime-order;
  `disc(Q)=−27M²` ⇒ prime-richness; `π_n=π_p−1`; the `d↔(X,Y)` bijection; keys are small-integer
  selections; the concave-sum search penalty.
- **Re-checked this session [re-checked]:** the `best_nk`-vs-`limit_denominator` discrepancy (15/82);
  the `NMAX`-cap sensitivity; the retraction of the consecutive-n coupling.
- **Relayed [relayed] — trusted at the level of a prior run, read this session but not re-executed:**
  all exact identities in §§3–6, the generation-model characterization (§7), the powered null battery
  and reductions (§§9–10), the nonce/exposed-pubkey results, the A–K solver battery, and all Part-IV
  φ(n)/RH material. **Several items within this lineage were later corrected** — the "no amicable
  pair" (refuted by point-count), "Hecke=2×ζ" (→ `n_L`), "977 genuine find" (retracted),
  twist-divisibility "novelty" (= Pajaziti–Sadek Thm 4.3), "spectrally optimal n_t" (→ liability),
  ZFR rank-2 (→ rank-1 + likely bug), the root-number sieve argument (non-sequitur), "SNR 10³⁷"
  (→ ≈1σ). That correction history is *why* "relayed" is not "verified."
- **Asserted-novel [inference] — least certain:** the "first-computed for secp256k1" labels
  (amicable point-count, `π_n=π_p−1`, GLV=CM-ideal, explicit Hecke χ, formal log, "why b=7/977/j=0",
  the parity-obstruction unification, the Eisenstein–Ramanujan survival synthesis). Novelty is
  self-assessed and unconfirmed against the literature; at least one sibling claim turned out known.
- **Method-scoped negatives (not impossibility):** `(X,Y)→key` (null to ~1e-5 bits, CTRL✓); CM-atlas
  ∩ keys (null, but grouped by a decomposition under review); consecutive-denominator coupling
  (cap artifact); on-chain signatures (null); weak-seed *bounded* spaces (null); the A–K solver
  battery (null). **Explicitly underpowered, not clean:** the n=63 generator-lattice test; MT19937.

## 15. Coverage note

Read in full for v4: `findings_v1/v2/v3`, `nk_reduction_spec`, the `phi_n_*` findings,
`secp256k1_cycles_findings`, `sextic_identities`, `cm_divisibility`, `cm_imprint`, `lfunc_sigma`,
`adelic_recasting`, `radial_selfadjointness`, both ZFR files, `nt_spectral_rework`,
`second_review_test_ledger`, `layering_cleanroom_ledger`, `struct_test_results`,
`secp256k1_Lfunction_intersections`, `secp256k1_formal_group_finding`, `gap_results_v6`, `README`,
`PRIMER`, plans v4–v6, the `farm/RESULTS`+`wp_briefs` inventory. Not fully read: `xy_information_test_*`
design/review, `dterm_feature_sweep_preregistration`, `exact_redo_plan`, plans v1–v3 (superseded), the
kangaroo-pool engineering docs, the WP1–8 source and result JSONs beyond the synthesis, and the
~110-idea master list at `~/Downloads/secp256k1_nkd_investigation_ideas_consolidated.md` (outside this
dir). No new *findings* expected there, but not provably exhaustive.

---

# APPENDIX A — Literature status  *([web-research 2026-07-11]; supplementary)*

Where each claim-cluster sits against the published record. Framing: **independent
convergence with the literature is a validation of method, not a demotion.** A line
of inquiry that reconstructs frontier results from scratch is tracking the real
research frontier — the value is a calibrated toolkit + honest boundary-mapping, not
a single unpublished theorem. "Not found in this search" is method-scoped, never
"provably novel." Search was via general web + arXiv abstracts, not an exhaustive
database sweep.

## A.1 Two direct convergences with 2026 papers (the headline)

- **Twist / reduction-order divisibility (§6) — reconstructed a June-2026 result.**
  Lineage: **Cojocaru (2004)** (Chebotarev density for `m|#E_p`), **Banks–Shparlinski
  (2009)** (averaged), **Pajaziti–Sadek** (arXiv:2301.00711, Thm 4.3 — already cited
  in §6), and **Lee–Sheen, "Divisibility Biases in the Orders of Elliptic Curve
  Reductions" (arXiv:2606.25067, June 2026)** — density `≈1/φ(m)`, always `>1/m`.
  The investigation's CM-imprint / sign-reversal law is exactly this. Arriving at it
  independently, the same year, is the strongest calibration signal in the project.
- **Hilbert–Pólya for elliptic-curve L-functions (§12) — a boundary match.** §12
  claims (a) the curve *is* a proven Hilbert–Pólya instance in the function-field
  sense (Frobenius on the Tate module, RH-for-curves = Hasse–Weil, self-adjointness =
  Weil pairing) and (b) the *global* Riemann-zero realization is **not** done (needs
  Connes' `𝔸_K/K*`). **arXiv:2605.17645, "A Local Hilbert–Pólya Realisation for
  Elliptic Curve L-Functions" (May 2026)** independently reaches that exact boundary:
  it builds *local* (p-adic) self-adjoint operator pencils encoding the Euler factors,
  and **proves an interpolation obstruction — global L-functions are structurally
  inaccessible to any single local operator.** The frontier confirms both halves of
  the doc's scoping, including the negative one.

## A.2 Cluster-by-cluster

| Cluster (§) | Literature status | The investigation's part |
|---|---|---|
| Twist/reduction divisibility (§6) | **Established + 2026 frontier** (Cojocaru → Lee–Sheen) | Independent full reconstruction incl. CM sign-reversal — a validated 256-bit worked example |
| Amicable pair `(p,n)` (§4) | **Framework known** — Silverman–Stange (arXiv:0912.1831, 2009); their no-long-cycle theorem is stated for `j≠0` | Our curve is `j=0`; the specific 256-bit secp256k1 `(p,n)` instance was not found in search |
| GLV = CM ideal `(π_n)` (§5) | **Known to specialists** — GLV (2001); B. Smith writes the GLV short basis "from elementary facts about quadratic rings" (= the CM ideal; Q-curve construction arXiv:1409.4526) | Independent arrival at Smith's observation, explicit for secp256k1's `β,λ,π_n` |
| Hecke χ / CM newform / root number / L(1) (§6) | **Classical + tabulated** — Deuring/Weil; CM-by-√−3 L(1) specifically in arXiv:1003.5289; curve (cond. 21168) in LMFDB | Recomputing from point counts = toolkit calibration (value = validation) |
| Formal-group log (§6) | **Known-in-principle** — CM formal groups hypergeometric / supercongruences (arXiv:1210.4489, 1303.6706) | Explicit `Σ 7ᵏC(3k,k)/(6k+1)T^{6k+1}` for `y²=x³+b`, tabulated for secp256k1 — not found in search |
| `b=7`/`977`/`j=0` rationale (§2) | **Coarse rationale documented** (efficiency, transparency, twist-resistance; bitcoin wiki, SEC2) | Fine "unique prime-order sextic twist" characterization is ours; the `977` version was already partly retracted |
| φ(n)-residue RH framework (§12) | **Building blocks established** (Berry–Keating, Connes adele class space) | The specific φ(n)-residue operator is the user's own construction; its curve instantiation is new |
| Bitcoin puzzle facts (§7, §10) | **Community-documented** (exposed pubkeys at multiples of 5, kangaroo, nonce recovery) | The systematic nonce + A–K curve-structure batteries are the investigation's |

## A.3 Candidates not found in this search (honestly hedged)

Stated method-scoped, matching §14's discipline — *not found in this literature
search*, **not** "provably novel," and mostly *instances/computations of known
theory*, which is the tier §14 already assigns them: the specific 256-bit `(p,n)`
amicable pair; the explicit `π_n=π_p−1` primary generator and the local Hecke-χ
formula for this curve; the explicit secp256k1 formal-group log; and the
`b=7`-as-unique-prime-order-sextic-twist characterization.

## A.4 Bottom line

The overlap is evidence the method is sound, not a reason to discount the work. An
independent inquiry that reconstructs Pajaziti–Sadek / Lee–Sheen from scratch,
arrives at Smith's GLV-lattice observation, recomputes the LMFDB-tabulated Hecke data
from point counts, and reaches the *same local/global Hilbert–Pólya boundary* a
May-2026 paper proves, is tracking the actual frontier. The contribution is (a) a
calibrated toolkit that reproduces frontier results on a specific important curve, and
(b) the honest boundary-mapping (proven locally, open globally per Connes; keys carry
no exploitable structure to the tested floors).

## A.5 Sources

- Silverman–Stange, *Amicable pairs and aliquot cycles for elliptic curves* — arXiv:0912.1831 (2009).
- Lee–Sheen, *Divisibility Biases in the Orders of Elliptic Curve Reductions* — arXiv:2606.25067 (2026).
- Pajaziti–Sadek, *Divisibility of orders of reductions of elliptic curves* — arXiv:2301.00711.
- *A Local Hilbert–Pólya Realisation for Elliptic Curve L-Functions* — arXiv:2605.17645 (2026).
- *A note on L(1) of Hecke L-series … CM by √−3* — arXiv:1003.5289 (2010).
- *Supercongruences and Complex Multiplication* — arXiv:1210.4489; *Formal Groups and Invariant Differentials* — arXiv:1303.6706.
- B. Smith, *The Q-curve construction for endomorphism-accelerated elliptic curves* — arXiv:1409.4526.
- GLV background: Gallant–Lambert–Vanstone (2001); noble-secp256k1 endomorphism notes (paulmillr.com).
- Cojocaru (2004); Banks–Shparlinski (arXiv:0906.xxxx, 2009) — divisibility-density antecedents.
- Bitcoin puzzle / secp256k1 parameter folklore: bitcoin wiki (Secp256k1), SEC2.
