# What We Know — secp256k1, its CM structure, the keys, and the φ(n)/RH intersection

**Version 2 · 2026-07-11.** Supersedes v1. v1 opened by calling everything
"established, verified … checked by independent computation." That was borrowed
authority: almost none of it was re-run in the session that wrote it, and that same
session had just caught a prior-session-grade bug (`best_nk`). v2 fixes the epistemic
framing.

**Provenance legend** (applied per section and per bullet where it varies):
- **[re-checked 2026-07-11]** — a script was run *this* session and the stated number
  came out.
- **[relayed]** — taken from prior-session memory/scripts; the computation is as strong
  as that session was, and was **not** re-run here. Treat as "a prior run reported this,"
  not "I verified this."
- **[math]** — follows from an in-text argument, not a computation.
- **[inference]** — an interpretation/value judgment, not a measured or proven fact;
  flagged as such.

Negatives appear only bound to a method: "probe X, by method Y, showed no Z."

Conventions: `p = 2²⁵⁶−2³²−977`; `n` = group order (prime); `t = p+1−n`; `ω` = cube
root of unity; `ℤ[ω]` = Eisenstein integers; `μ₆ = ℤ[ω]* = {±1,±ω,±ω²}`.

---

## 1. The base object: CM by ℤ[ω]  *(provenance: [math] + [relayed])*

- **secp256k1 has CM by the maximal order ℤ[ω]** (`j=0`, disc `−3`, `h(−3)=1`). **[math]**:
  `φ(x,y)=(β·x,y)` with `β³=1` satisfies `φ²+φ+1=0`, so `ℤ[ω] ⊆ End(E)`; `ℤ[ω]` is the
  full ring of integers of `ℚ(√−3)` (a maximal order), and `End(E)` is an order in that
  field containing it, so `End(E)=ℤ[ω]`. `φ(G)=(β·Gₓ,G_y)=[λ]G` [relayed].
- **Reduction of the Mordell curve `y²=x³+7 / ℚ`** [relayed]: rank 0 (no rational points
  to height 200), conductor `N_E=21168=2⁴·3³·7²`, bad primes `{2,3,7}`, additive at 7
  (`a₇=0`).
- **Frobenius as an Eisenstein prime** [relayed]: `π_p=a+bω`, `N(π_p)=p`, `2a−b=t`.
  Primary generator
  `π_p = 367917413016453100223835821029139468249 + 303414439467246543595250775667605759171·ω`.
- **CM norm form** [relayed]: `4p=t²+27M²`, `M=101138146489082181198416925222535253057`;
  `disc(charpoly)=t²−4p=−27M²`.
- **The angular structure is μ₆.** At the complex place of `K=ℚ(√−3)`, `ℂ*=ℝ_{>0}×S¹`
  (polar) and `μ₆=ℤ[ω]*` sits in the `S¹`; the six units are six 60°-sectors indexing the
  six sextic twists (§3). [relayed] *Method-bound note:* the Eisenstein lift-direction of a
  key's X-coordinate is a genuine `ℤ[ω]` angle, but over the solved keys its distribution
  matched the fundamental-domain (hexagon) geometry, not any key property — so the angle is
  a curve coordinate, not a key signature. [re-checked prior session; consistent with this
  session's null battery]

---

## 2. The deployed constants  *(provenance: mixed — computation is [relayed], intent is [inference])*

Separating the two, because v1 blurred them:

- **Computed facts [relayed]:** with `a=0` (forced by `j=0`), of the six sextic-twist
  classes of `y²=x³+b` over this `p`, exactly one is prime-order, and `b=7` is the
  smallest positive `b` in it (`b=1..6` composite-order; `b∈{7,12}` share the class).
  Separately, `978…1023` are composite and `977` is the first prime descending from
  `2²⁵⁶−2³²−1024`; the ascending smallest prime `263` has no prime-order `j=0` curve.
- **`j=0` is forced given "cofactor 1 + efficient CM endo" [math]:** the two efficient CM
  endos are `j=0` (`ℤ[ω]`) and `j=1728` (`ℤ[i]`); every `j=1728` curve contains the
  2-torsion point `(0,0)` ⇒ even order ⇒ never prime-order. So `j=0` is the only option.
- **Intent [inference], flagged:** the reading that Certicom *chose* 977 via a
  descending-from-1024 Solinas scan, and that each SEC2 offset is "the smallest `c` where
  that curve's `b` has prime order," is a reconstructed-workflow story, not a verified
  fact about their process. History note: an earlier "977 is the smallest offset with a
  prime-order curve" claim was **retracted** this investigation after a web search showed
  the descending-scan convention; the secp160k1 offset (21389) was an outlier that only
  "fit" under a further reframing. Trust the computed facts above; treat the intent as a
  plausible reconstruction.
- Generator `G` provenance: not a small multiple of `(1,√8)` to 3M, not a hash of common
  seeds — both **[relayed] null**. The one genuinely undocumented free choice.

---

## 3. Twist structure: six sextic twists ↔ six units  *(provenance: [relayed])*

- Each sextic twist of `E/𝔽_p` has Frobenius `u·π_p` for one unit `u∈μ₆`; `b=7 ↔ u=1+ω`.
  Six twist orders `= N(π_p+u)`, summing to `6(p+1)`; `t` is the middle magnitude.
- **Unique prime-order twist = the main group:** only `π_p−1` has prime norm `= n`.
  "unique prime neighbor of Frobenius" = "unique prime-order twist" = "unique amicable
  twist" — all resting on `(π_p−1)=(π_n)`.
- **Twist order:** `n_t=2(p+1)−n = 3²·13²·3319·22639·C`, `C` a 216-bit prime.
- **Embedding degrees** `ord_r(p)`: `13→4`, `3→1`, `3319→474`, `22639→22638`; the low-degree
  pairing corner (`13²` in `𝔽_{p⁴}`) lives only on the twist. Explicit order-13 point on
  `E₂/𝔽_p` realizing it is computed.
- **Why 13 [math+relayed]:** on `E[13]`, `x²−6x+5≡(x−1)(x−5) mod 13`; root 1 ⇒ rational
  13-torsion, companion root 5 has order 4 in `𝔽₁₃*` = the embedding degree.

---

## 4. The amicable pair (p, n)  *(provenance: [relayed] point-count)*

- **`#E₇(𝔽_p)=n` and `#E₇(𝔽_n)=p`** — a length-2 cycle of `q↦#E(𝔽_q)`. The second
  equality was reported verified by **direct point-order testing over `𝔽_n`** (Cornacchia
  gives `π` above `n`; a point-order test isolates order `p`), **zero reciprocity symbols**.
  [relayed — not re-run this session; but it is a decisive point-count, not a symbol
  manipulation, which is why it was trusted over an external "sextic obstruction" table.]
- **Structural reason [math]:** Frobenius at `n` is `1−π_p`; `(1−π_p)−1=−π_p`, norm `p`.
  Norm-form shadow: `4p=t²+27M²`, `4n=(t−2)²+27M²`, same `M` ⇒ `π_n=π_p−1`.
- **Frobenius quadratic:** `Q(c)=N(π_p−c)=c²−tc+p`; `Q(0)=p`, `Q(1)=n`, `Q(−1)=n_t`. Over
  `c∈[−200,200]` the longest run of consecutive-prime `Q(c)` is exactly `{0,1}`.
- **Why `Q` is prime-rich [math]:** `disc(Q)=−27M²`, so mod `ℓ` it has `1+χ₋₃(ℓ)` roots —
  0 at inert primes (`ℓ≡2 mod3`), 2 at split, 1 at 3. Inert primes never divide any `Q(c)`.
- **Context (known-in-principle):** CM curves have abundant length-2 amicable pairs
  (Silverman–Stange); `y²=x³+7` averages ~19 pairs over primes `<15000`. `(p,n)` is the
  256-bit member; small members e.g. `(67,79)`. Length-≥3 cycles: none in bounded sweeps
  (conditional null, not a nonexistence proof).

---

## 5. GLV = the CM ideal (π_n)  *(provenance: [relayed])*

- The GLV lattice `L={(a,b):a+bλ≡0 mod n}` has reduced basis `{π_n, ω²·π_n}`, determinant
  `n` — the "magic constants" are Frobenius coordinates.
  `β=0x851695d49a83f8ef919bb86153cbcb16630fb68aed0a766a3ec693d68e6afa40`,
  `λ=0xac9c52b33fa3cf1f5ad9e3fd77ed9ba4a880b9fc8ec739c2e0cfc810b51283ce`.
- Base-field lattice `L_p` has basis `{π_p, ω·π_p}`; the two cube-root choices of `β`
  select the conjugate primes.
- `ord_λ(n)=3`; `ord_n(2)=(n−1)/64`; `ord_n(p)` (MOV degree) is a 254-bit divisor of `n−1`.
- **One ideal, many faces:** `(π_n)=(π_p−1)` ties GLV, the norm form, the unique
  prime-order twist, and the amicable pair into the single ideal `(π_n)`.

---

## 6. The L-function / Hecke side  *(provenance: [relayed], from point counts)*

- **CM newform = theta series** (reported verified to `n≤120`, 0 mismatches):
  `f=Σ_{𝔞⊂ℤ[ω]} ψ(𝔞) q^{N(𝔞)}=q+7q¹³+8q¹⁹−5q²⁵+…`; inert primes give `a_ℓ=0`, split give
  `ψ(𝔭)+ψ(𝔭̄)`, inert `ℓ²` gives `−ℓ`.
- **Hecke Grössencharacter `ψ`**: `L(E₇/ℚ,s)=L(ψ,s)`, ∞-type `(1,0)`, `ψ((α))=χ(α)·α`.
  Conductor `𝔣=(2²)(√−3)²(7)`, `N_{K/ℚ}(𝔣)=7056`, cross-checked `N_E=3·7056=21168`. Finite
  part `χ` = primitive order-6 ray-class character of `Cl_𝔣` (order 432), ramified at 2,3,7.
  Local formula `χ(π)=χ₄(π mod 4)·(π/π₇)₆⁵·(π/π̄₇)₆⁵`, `π₇=−1−3ω`.
- `χ` learned from primes `<3000` reproduced the 256-bit Frobenius (`χ(π_p mod 28)=1 ⇒
  ψ(𝔭_p)=π_p ⇒ t, #E=n`).
- **Root number `W(E₇)=+1`, self-verified** (no external tables): even theta parity, and
  `L(1)=Ω=3.041417228>0` matched to the integrated period `Ω=Γ(1/3)Γ(1/6)/(2√π·7^{1/6})`.
- **Formal-group log, closed form:** `L(T)=Σ_{k≥0} 7^k C(3k,k)/(6k+1) T^{6k+1}=T+3T⁷+
  (735/13)T¹³+…`, reported to `T³⁷`; nonzero only at exponents `≡1 mod 6` (full `μ₆`).
- **Twist-divisibility law (= Pajaziti–Sadek Thm 4.3):** `ℓ|n_t ⟺` Frobenius has eigenvalue
  `−1 mod ℓ`; `freq(3|n_t)=0.76` for `D=−3`; sign-reversal `P(ℓ|n_t|SS)>P(ℓ|n_t|ord) ⟺ ℓ`
  inert (24/24). Contribution = worked 256-bit example, **not** the theorem.

---

## 7. The key coordinate (n, k, D)  *(provenance: [re-checked 2026-07-11])*

- **It is a universal, scale-invariant tautology [math].** Any `d∈[2^{P−1},2^P)` has a
  best rational approximation `k/n` (denominator capped) to its normalized position
  `(d−A)/A`, `A=2^{P−1}`, with residual `D` that recurses the same way. The decomposition
  *always exists* for every integer — a Farey/continued-fraction coordinate on position,
  not a discovered property.
- **Two different notions of `(n,k)`, and which is "right" is a definition, not a fact
  [re-checked]:**
  - `Fraction(d−A, A).limit_denominator(NMAX)` is the **standard "closest fraction with
    bounded denominator"** — it minimizes the actual approximation error `|(d−A)/A − k/n|`.
    It agrees with the CSV's stored `n_exact` column.
  - The local helper `best_nk` (in `knd_common.py`) minimizes a **different** quantity, the
    unnormalized residual `|n(d−A)−kA|` (i.e. `error × n·A`), which biases toward small
    denominators. It is *not a wrong computation of the same thing* — it is a legitimate
    different quantity. The two disagree on **15/82** solved keys.
  - Which one the `(n,k)` framework *intends*, I have **not** checked against a written
    definition. If the intent is "closest fraction to the position" (as the memory note
    "`(n,k)` = best rational approx of position `u`" suggests), use `limit_denominator`; if
    the intent is the numerator-scale residual, `best_nk` is what it computes. Any
    `(n,k)`-grouped result should be recomputed under whichever definition is fixed, and the
    two compared.
- **The cap `NMAX` is a free parameter [re-checked]:** decompositions and any denominator
  "coincidences" change with it (e.g. puzzles 58/59/60 share a denominator only at
  `NMAX=256`, not at 128 or 512). A fixed principled cap, or explicit cap-invariance, is
  required before reading structure into `(n,k)`.

---

## 8. How the keys relate to the curve  *(provenance: mixed, tagged inline)*

- **`d ↔ (X,Y)` is a bijection [math].** `G` has full order `n`, so scalar ↔ point
  round-trips with no loss. The full information of a key is present in its point; ECDLP
  scrambles the readout, it does not delete it.
- **Heuristic, not a theorem [inference — corrected from v1]:** cheap (low-complexity)
  functions of `(X,Y)` *empirically* come out statistically independent of `d`, and a cheap
  per-point readout that recovered `d` would be a break — so blind per-point probes are
  expected to be null. This is a working expectation backed by every null probe so far,
  **not** a proof, and "every low-complexity function is independent" is false as a literal
  statement (the ECDLP itself is a function of `(X,Y)` equal to `d`). The usable form: the
  only thing that could plausibly survive is a joint property of a *set* of generated keys.
- **Key coordinate ⟂ CM coordinate on these keys [relayed, four exact tests, Round 8
  `glv_puzzle.py`]:** (1) no GLV-conjugate keys (`d_j=λ^s d_i mod n`); (2) no `λ·d_i mod n`
  in any small band; (3) no endomorphism-related pubkeys (`φ(Q_i)=(β·X_i,Y_i)` never another
  known `X_j`); (4) `n_exact` flat across CM classes `d mod 3`. Scope: the `(n,k,D)`
  position coordinate and the public CM atlas do not meet **in these 82 keys**. This session's
  own d-level/CM/GLV/sextic battery on the same keys was also null (caveat: it grouped by the
  buggy `best_nk`, so it is null on the wrong groups — "nothing on wrong groups" ≠ "nothing on
  right groups"; re-run under a fixed decomposition to make it clean).
- **Parity-obstruction reading [inference — a model, not a proof]:** the recurring
  explanation for why "reviving suppressed CM signal" never reaches a key is that the
  discrete log behaves like a parity — invisible to linear/averaging functionals of `Q`
  (Selberg sieve-parity analogy), so extraction would need a bilinear/Type-II handle absent
  for a prime-order curve over a prime field. This *organizes* why the inverted-sieve,
  φ-residue, and spectral approaches came up empty; it is an interpretive model, not a
  demonstrated impossibility.

---

## 9. The search picture  *(provenance: [re-checked] + [relayed])*

- **Unconditional win [relayed]:** GLV + negation-map constant speedup (`√3` from `μ₃`,
  `√2` from negation) on any interval search. No key exploit.
- **The (n,k) cell decomposition is a threshold lever, not a free reduction [math]:**
  per-cell search costs `√Σ(cells)` vs `Σ√` — the concave-sum penalty means splitting
  *raises* cost unless cells can be excluded. Coprimality removes *labels*, not *d-regions*
  (coprime cells tile the interval gaplessly), so a reduction needs a **region-forbidding**
  constraint, which could only come from a generation recipe.
- **No exploitable generation structure established [re-checked 2026-07-11]:** the one
  candidate (consecutive-puzzle denominator coupling) did not survive audit — it was an
  artifact of the free cap `NMAX=256` plus `best_nk`'s small-denominator bias, and vanished
  under the standard decomposition and other caps. The available path to a specific puzzle
  remains a Pollard kangaroo on the interval with the GLV/negation speedup.

---

## 10. The φ(n) / Riemann-Hypothesis intersection  *(provenance: [relayed]; heavily scoped)*

This is the bridge between the curve's Hecke `L(ψ,s)` (§6) and the separate **φ(n)-residue
RH programme** (T. Palelei et al., 8 Zenodo records). Kept as its own section because the two
are different ledgers, and the programme's strong claims were themselves walked back — so
this must not be read as any statement about RH being proved.

**Status of the RH programme itself (its own record, chronological):** a full-RH claim
(*RH via φ-Residue Rigidity*, 2026-01-23) → the key inequality **isolated as a named
conjecture** (2026-01-26) → an **unconditional partial** result only (*Vertical Zero-Free
Region*, 2026-02-07: `Re(ρ)≤13/16` for **families** of Dirichlet L, `q≤T^{2/5}(log T)^{−B}`,
via Bombieri–Vinogradov machinery) → a finite-rank framework (2026-02-11) whose **remaining
input is an unproven "Moment Pumping" hypothesis**. The programme's own latest consolidation
(Feb 9) records the Bridge Lemma as "bridged-not-proved" and moment-optimization beyond
13/16 as open. **So: no proof of RH; one unconditional partial family ZFR; the rest
conditional on a stated, unproven hypothesis.**

**What the framework is:** an operator `D_φ` = a Dirichlet **residue-Gram** form over a
squarefree frame `Q₀`, with an explicit-formula **forcing** (a hypothetical off-line zero)
pushed against an arithmetic/spectral **ceiling** (large sieve / dispersion / operator
coercivity).

**What is solid inside it [relayed]:**
- **Coercivity constant `1/12` is a theorem:** `c∞ = min_{Q₀} 1/φ(q) = 1/φ(13) = 1/12`,
  verified numerically (`λ_min → 1/12`, `Q₀={3,5,7,11,13}`). This is the *sound* half.
- **What is broken:** the **forcing** (the "Moment Pumping" step) — the required moment was
  found to **decay, not grow**, so the ceiling does not close the argument. A reviewer who
  called `1/12` "numerology" had it **inverted**: `1/12` is the proven part; the forcing is
  the gap.
- **Operator identity:** `D_φ` is the Dirichlet residue-Gram, **not** a CM/Hecke operator —
  conflating the two is an error to avoid.

**The intersection with secp256k1 (the genuinely-connective part) [relayed]:**
- **The φ(n)-framework is a units-averaged slice of Connes' adele class space.** The
  operator's "multiplicative circle `B`" vs the zeros' "additive line `C`" obstruction
  resolves on the idele class group `C_ℚ = ℝ_{>0} × Ẑ*`, where `B` and `C` are two **direct
  factors**, not rival spaces.
- **The CM field `K=ℚ(√−3)` is the natural home:** its complex place gives `ℂ*=ℝ_{>0}×S¹`
  exactly, `μ₆=ℤ[ω]*` sits in the `S¹`, and the curve's Grössencharacter `ψ` (§6) has ∞-type
  `(1,0)` coupling radius↔angle. Verified `ψ(𝔭)=u·π`, `u∈μ₆` = the sextic-residue character
  at split `ℓ` — the *same* `μ₆` that indexes the six twists (§3).
- **"Line as an incomplete circle" test — passes, as a consistency check only.** Completing
  the radial line to a circle with a boundary twist `α` (a von Neumann extension parameter)
  gives `Ĥ=πA²` Hermitian with a **real discrete spectrum for every `α`**; the deficiency-
  `(1,1)` obstruction *is* the `S¹` of self-adjoint completions, and `μ₆` = the six canonical
  completions (`α_j=2πj/6`). **Scope, stated plainly:** this is a model/consistency result on
  a *free lattice spectrum* — it shows `μ₆` is a *selector, not a wall* — and is **not** the
  actual Riemann zeros. Producing the real zeros needs the `𝔸_K/K*` scaling operator with a
  cutoff (Connes' open program), which is not done.
- **L-function wall invariant, corrected [relayed]:** an earlier "the spectral-wall variance
  tracks L-degree, Hecke = 2×ζ" claim was **tested and corrected** on 4 L-functions — the
  `log|S(σ+it)|` vertical variance tracks the **Selberg constant `n_L`** (number of primitive
  factors), **not** degree: measured `ζ=1.00`, `L(χ₋₃)=1.00`, reducible `ζ_K=1.99`, and the
  **secp256k1 curve's primitive `L(ψ)=0.99`**. The "2×" holds only for the *reducible*
  Dedekind `ζ_K`; the curve's primitive `L(ψ,s)` has ζ's variance (Selberg CLT:
  `½ log log T`, degree-independent for primitive L). **Do not cite "Hecke = 2×ζ."**
- **Where it touches the keys:** the deep φ(n) thread lives in the **curve's Hecke `L(ψ)`**,
  not in the key positions. The φ(n)-"resonance" that appears in the key framework, made
  exact, is just the curve identity `[n]P=(n+k)Q+(n·D)G`, whose residual is the ECDLP wall —
  i.e. it does not carry key information (consistent with §8).

---

## 11. Ledger: what is verified vs asserted-novel  *(read this as the epistemic key)*

- **Carries its own in-text proof [math]:** `End(E)=ℤ[ω]`; `j=1728` can't be prime-order;
  `disc(Q)=−27M²` ⇒ prime-richness; `π_n=π_p−1`; the concave-sum search penalty; the
  `d↔(X,Y)` bijection.
- **Relayed computations [relayed] — trusted at the level of a prior run, not re-verified
  here:** all exact identities in §§3–6 (twist orders, amicable point-count, GLV=CM-ideal
  basis, theta series, Hecke `χ`, root number, formal-group log) and the §10 φ(n)/RH
  material. Several *within this lineage were later corrected* (the "no amicable pair"
  obstruction — refuted by point-count; the "Hecke=2×ζ" wall — corrected to `n_L`; the "977
  genuine find" — retracted; the twist-divisibility "novelty" — found to be Pajaziti–Sadek
  Thm 4.3). That correction history is the reason "relayed" is not "verified."
- **Asserted-novel [inference] — the least certain class:** the "first-computed for
  secp256k1" labels (amicable point-count, primary `π_n=π_p−1`, GLV=CM-ideal, explicit Hecke
  `χ`, closed-form formal log, the "why-b=7/977/j=0" characterizations, the parity-obstruction
  unification). Novelty is self-assessed and unconfirmed against the literature; at least one
  sibling claim in this project turned out to be known. Treat as "not found elsewhere by us,"
  not "new."
- **Tightly-bound negatives [method-scoped]:** per-point `(X,Y)→d` readouts (null); CM-atlas
  ∩ keys (four exact tests, null, but grouped by a decomposition now under review);
  consecutive-denominator coupling (audited to a cap artifact). Each = "this probe, by this
  method, showed no key signal" — none asserts impossibility.
