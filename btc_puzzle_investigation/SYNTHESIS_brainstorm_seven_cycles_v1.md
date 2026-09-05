# Seven cycles — an unfiltered brainstorm, with the prior-work check run first

*2026-07-26. Open brainstorm at the user's request: no prefiltering, ideas generating ideas. **Nothing
is promoted; no grade moves; nothing was run.** No leakage, key-recovery or ECDLP claim.*

> **PROVENANCE.** Built on the previous session's read (`btc_puzzle_INDEX.md` 1–726,
> `OPEN_ITEMS_LEDGER_v1.md`, `NEXT_DIRECTIONS_v1.md`, `MASTER_v4` Parts I–VII + P6b + the retraction
> ledger) plus, this session, `RESULT_cap_reducibility_analysis_v1.md §4–5`,
> `y_channel_eisn_findings_v1.md`, `RESULT_n1_v_sign_mechanism_v1.md §§2–4`, and greps for
> Wiener/monodromy/incomplete-sum across all `*.md`. **Still not read:** master Parts VIII–XII bodies,
> the Addendum, most `RESULT_*`. **Four numeric checks were run** (`sin` collapse, eigenvalue trace,
> `|1+ζ₃|`, Sato–Tate moments) and are reproduced in §0.

---

## §0 — The prior-work check, run BEFORE writing (this record's named recurring failure)

Four of this brainstorm's best-looking ideas are **already on file**. Attribute, do not re-claim:

| idea | already on file | where |
|---|---|---|
| `V(a)` is the **finite-field Mellin transform**; Katz AM-180 is the right home; monodromy is the framework | yes | `RESULT_cap_reducibility_analysis_v1.md §4` |
| The eigenvalue pattern `{z,−z̄,w,−w̄}`, unitarized trace `τ = 2i(Im z + Im w)`, **CAP ⟺ `|τ| ≤ 2`** | yes | same, §4 |
| **`E[(|V|/√p)²] = n/p ≈ 1` exactly** (from `Σ_a|V|² = n(n−1)`) = the SU(2) Sato–Tate variance; "a variance of 1 and a ceiling of 2 are the signature of a **2-dimensional** SU(2)-type object" | yes | same, §4 — ⚠ **so the previous synthesis's "Parseval forces `E[u²]=1/4`" is this restated, NOT new.** Correction owed to `SYNTHESIS_..._v1.md §2.6(a)` |
| The Wiener-norm bound is **vacuous exactly when `‖F‖_A ≳ √p`, i.e. for multiplicative characters** | yes | `masked_structure_findings_v3.md:28–29` |
| **"Wiener norm is the only analytic door" is RETRACTED** (#5, "a red herring") | yes | `MASTER_v4` retraction ledger |
| The `(★)` monodromy-containment statement, and the guess that it is *"an SU(2) mapped in so the two conjugate-pair factors are **locked together**"* | yes | `RESULT_cap_reducibility_analysis_v1.md §4` |

That last row is the important one. **The record guessed the mechanism and called the computation
research-grade.** §1 argues the lock is now explicit and elementary — and that the verdict which called
it research-grade was rendered on **2026-07-24**, one day **before** the fact that supplies the lock.

---

## §1 — Cycle 1: the lock is explicit, and item 2's verdict predates it

### 1.1 The eigenvalue configuration

`RESULT_cap_reducibility_analysis_v1.md §5` verdict: *"(c) GENUINE GAP … `|V(a)| ≤ 2√p` is not
reducible to a cited theorem and not one elementary lemma from the record's proved structure"*, with
the gap pinned to `(★)` — a monodromy containment judged *"not in the record and itself
research-grade."*

That was **2026-07-24**. On **2026-07-25**, `RESULT_n1_v_sign_mechanism_v1.md` established, at
357/357 classes to `9.5×10⁻⁴⁰`:

> `u = cos t`, `s₁ = cos(t−60°)`, `s₂ = cos(t+60°)` — **the two Frobenius half-angles differ by
> exactly 120°.**

**Nothing in the record re-opens item 2 after that lands.** The two files never meet.

Put the 120° fact into the record's own `{z,−z̄,w,−w̄}` pattern. The two half-angles differing by
120° means `w = z·ζ₃`, so the multiset is

```
{ α, αζ₃, −ᾱ, −ᾱζ̄₃ },    |α| = √p
```

and the trace is

```
V = α(1+ζ₃) − conj(α(1+ζ₃)) = 2i·Im( α·(1+ζ₃) )
```

**with `|1 + ζ₃| = 1` exactly** (`1+ζ₃ = e^{iπ/3}`; the two shortest vectors of the hexagonal lattice
at 120° — Cap Law Thm A's own geometry). Therefore

```
V = 2i·√p·sin(θ + 60°)          ⇒     |V| ≤ 2√p,  attained.
```

Numerically confirmed this session (§0 provenance): the collapse `sin θ + sin(θ+120°) = sin(θ+60°)`
to `3×10⁻¹⁶`; the four-eigenvalue trace against `2i√p·sin(θ+60°)` to `4×10⁻¹⁴`; `|1+ζ₃| = 1`,
`arg = 60°`.

**A third fact falls out unasked:** that configuration forces the trace **purely imaginary** — which
the record carries as a separate exact measured fact (`V(a)` purely imaginary at `p≡3 mod 4`, purely
real at `p≡1 mod 4`, "exact, every row"). One configuration explains the cap, the `½` saturation, and
the reality pattern together.

### 1.2 What this does to `(★)`

`(★)` asked for a subgroup `G` with `|Tr(g)| ≤ 2√p` for every `g ∈ G`. With the lock made explicit,
`G` is **`SU(2)` embedded as `g ↦ g ⊗ (1 ⊕ ζ₃)`** — the 4-dim rep is a 2-dim rep tensored by a fixed
rank-2 `μ₃`-factor whose own trace has modulus exactly 1. Then `|Tr| = |Tr(g)|·|1+ζ₃| ≤ 2√p` **as a
group-theoretic identity**, not as a distributional statement — which is precisely the objection the
audit raised against monodromy (*"gives the distribution, not the pointwise ceiling"*). **The
objection is correct for generic monodromy and does not apply once the tensor factor is named.**

### 1.3 Where the `ζ₃` comes from — a mechanism to check, not a proof

The record's own ramification data: `H¹_c(L_{χ₂(y)} ⊗ L_{χ_a})` is ramified at **the three 2-torsion
points and `O`** — four tame points, `dim = 2g−2+4 = 4`. The three 2-torsion points are
`(x_i, 0)` with `x_i³ = −7`, i.e. **`x_i = −7^{1/3}·ζ₃^j` — a single `μ₃`-orbit**, permuted cyclically
by `β`, with `O` fixed.

So the four punctures are `3 + 1` under the `μ₃` action, and `E/μ₃ ≅ P¹` (coordinate `y`, since
`x³ = y²−7`) makes `E → P¹` a cyclic cubic cover. **A cyclic cubic cover's pushforward decomposes into
cubic-character isotypes, and Frobenius eigenvalues across those isotypes differ by cube roots of
unity.** That is the natural source of the `ζ₃`, and it is exactly what "the two conjugate-pair
factors are locked together" has to mean.

`[MINE — in-session, UNVERIFIED]` for the whole of §1.1–1.3. The algebra is elementary and checked
numerically; the sheaf-theoretic step in §1.3 is a sketch, not a derivation. **The identity itself is
still `[VERIFIED — exact]` at 8–10 primes and not derived.**

### 1.4 The one control that decides it, and it is cheap

The mechanism is `μ₃` on the cover — a property of `j = 0`, **not** of secp. So:

- **The 120° law should hold at every `j=0` curve, every `p`, every `b`.** If it does, the `2√p` cap is
  a general `j=0` theorem — publishable, secp-irrelevant, and pure structure.
- **It must FAIL off `j=0`.** A curve with `j ≠ 0` has no `μ₃`, so its four eigenvalues should be
  genuinely free and `S_y` should run toward the `#R=4` ceiling.

Two predictions, opposite directions, both cheap at `p ≤ 10³`. **No control in the record has ever
varied the cap's mechanism** — every one varied the readout or the null. `experiment-designer` prereg
first (CLAUDE.md §2 names "sweep").

### 1.5 A genuinely new forced prediction — the FOURTH moment

The record has the **second** moment as forced (`E[(|V|/√p)²] = n/p ≈ 1`, §0). It does not have the
fourth. If the monodromy is full `SU(2)`, the trace moments are Catalan numbers:

```
E[(2u)²] = C₁ = 1  ⇒  E[u²] = 1/4     ← on file (forced by Parseval)
E[(2u)⁴] = C₂ = 2  ⇒  E[u⁴] = 1/8     ← NOT on file, and it is a real discriminator
```

Verified numerically this session against the `SU(2)` measure `(2/π)sin²θ`: `E[u²] = 0.250000`,
`E[u⁴] = 0.125000`, `E[|u|] = 0.42441` (record measured `mean|u| = 0.4083` — consistent with
Sato–Tate at finite size).

**`E[u²]` is forced by Parseval and therefore carries no information about the monodromy.
`E[u⁴]` is not forced.** It separates full `SU(2)` (`1/8`) from a smaller group. Computable from data
already on disk. **This is the cheapest live discriminator in the whole N1 story.**

---

## §2 — Cycle 2: which verified coincidences still have no group-theoretic account?

The Cycle-1 method — *go from the numerology to the group, not to the estimate* — applied down the list.

**Accounted:** `¾:⅛:⅛` (rhombus geometry), frame `½`/`¾`/`¼` (Schur), `C_T` tensor, `|FLD| = 6h`
(now `2 × 3h`, and see §5.3), `m=1` (Stickelberger), `ord_n(p)`, `ord_n(2)`, the 33.33% collision,
`R^(2) = T + 3T⁷` (the coefficient is `b·C(3,1)/7 = 3b/7`, integral exactly because `b = 7`).

**Not accounted, and each gets a candidate below:** the sub-Rayleigh low-tail excess (§4.2); the
`0.93` joint alignment (§2.2); the `(X·Y) mod 64 → D mod 64` shadow (§2.3).

### 2.1 `b = 7` is forced ⇒ the whole curve is a function of `p` alone

The record: among the six sextic twists, **exactly one has prime order, and it is the class of `b=7`**
(`u = 1+ω`). So given `p` and the requirement "j=0, prime order", **the curve is determined**. There is
no free choice, and `b=7` is not a design decision — it is `p`'s output.

Two consequences worth stating plainly:

1. **Every structural finding in this record is a property of `p`.** Amicability, `m=1`, `ord_n(p)`,
   the `μ₆` laws, `f`'s factorization — all functions of `p = 2²⁵⁶ − 2³² − 977`.
2. ⚠ The record's amicability framing says twist-selection is "the unforced part". If exactly one twist
   has prime order, **that phrasing is stale** and should be re-checked.

**⇒ The right reference class is primes, not curves.** For each `p` in a family, compute the unique
prime-order `j=0` twist and its full invariant vector; see which of secp's values are typical. And
because `p` is a pseudo-Mersenne chosen for fast reduction, the sharper question is: **are secp's
invariants typical for random primes, or typical for pseudo-Mersenne primes?** A systematic
"forced vs free" census would also stop the recurring re-discovery of forced facts as findings (the
retraction ledger is at #27).

⚠ **Scope note:** this is arithmetic of the curve's defining prime, not key generation. It does **not**
touch the standing no-PRNG/generation-side rule. Keep the distinction explicit in any write-up.

### 2.2 The `0.93` — an accounting that has not been done

Joint `(x,y)` aligned readout reaches `0.93`; `x`-only reaches `0.37`. The record proves odd and even
`d`-spectra carry **equal mass**, and `x` is even in `d`, so `x`-only can see at most half the mass —
predicting `≈0.93/√2 ≈ 0.66`, not `0.37`. **The gap is unexplained by parity alone.** Decompose the
`0.93` into even-part and odd-part contributions and check they add up. Cheap, decidable, and if the
split does not close, something else is in the readout.

### 2.3 The two `64`s

`ν₂(n−1) = 6`, so `ord_n(2) = (n−1)/64` (explained as a selection effect). Separately, the record
carries `(X·Y) mod 64 → D mod 64` as an observed shadow with **no account**. Both moduli are `2⁶`.

**Decidable, mechanism-varying test:** on other curves, does the shadow's modulus track
`2^{ν₂(n−1)}`? If yes, the shadow is a 2-Sylow phenomenon and is explained. If no, it is something
else and becomes a sharper anomaly. Either outcome converts an unexplained empirical shadow.

---

## §3 — Cycles 3–4: the Wiener-norm map, and a named loophole that closes

⚠ **Retraction #5 stands** — *"the `‖F‖_A` gap is the only analytic door" is wrong; Wiener norm is a
red herring.* Nothing below re-opens that. What follows **shrinks** the frontier, it does not widen it.

### 3.1 The organizing principle (on file), and what it explains

`|Corr_F(a)| ≤ ‖F‖_A · max_b|T(a,b)|/n`, vacuous exactly when `‖F‖_A ≳ √p`
(`masked_structure_findings_v3`). And `‖χ₂‖_A ≈ √p` — because every additive-Fourier coefficient of a
multiplicative character is a Gauss sum of modulus `√p`. **So multiplicative characters sit exactly at
the borderline where the additive-Fourier method dies.** That is *why* §XII.10 exists and why `χ₂`
needs its own Kummer-sheaf theorem (P6b). The dichotomy has a one-line reason.

### 3.2 ★ The named-open loophole, and an elementary answer to it

`y_channel_eisn_findings_v1.md` leaves open, verbatim: *"whether the closure's `√p` bound extends from
the character `e_n(a·d)` to the non-bounded-degree target `eis_n(d)` via its Fourier/Wiener profile
(the same loophole as the band case)."*

`[MINE — in-session, UNVERIFIED]` **Every lift-geometry readout is a Boolean combination of interval
conditions on finitely many LINEAR forms mod `p`.** The record supplies the linearity itself:
`t(X) = p(u−v)` with `M ≡ t(1) mod p`, i.e. `u−v` is `(Mx mod p)/p` up to a branch, and the branch is
another linear-form cell. So

```
σ, ε, sextant indicator, norm band, pinned pair, eis coordinates, high bits of x, x mod 2
   =  indicators of boxes in the k-torus (M₁x, …, M_k x) mod p
```

and a box indicator in `k` dimensions has Wiener norm `O(log^k p)` (Fejér/Dirichlet kernel). Hence

```
|Σ_d F(x_d)·e_n(ad)|  ≤  O(log^k p)·(4√p+1)      ⇒     |Corr_F| = O(polylog·p^{−1/2})
```

**⇒ the entire lift-geometry family is analytically bounded as a Fourier leakage channel, by an
elementary argument, with no experiment.** Two named sub-items are covered:

- **§XI.1's remaining "non-`μ₆`-covariant cheap readouts (raw coordinate bits — `x mod 2`, high bits
  of `x`)"** — these are box/linear-phase functions; `‖·‖_A = O(log p)`. (`(−1)^x` on `ℤ/p` is a
  geometric series with coefficients `~1/|2b−p|`, summing to `O(log p)`.)
- **The `eis_n` loophole quoted above.**

And it **retracts a proposal from my own previous synthesis**: `SYNTHESIS_..._v1.md §2.3` proposed
running `σ_n(d) × χ₂(y_d)` as a parity-legal channel. `σ_n` is a lattice-cell function on `ℤ/n` by the
identical argument, so `‖σ_n‖_A = O(log^k n)` and the pairing is bounded by `2√p·polylog` **before any
data is drawn**. ⚠ **Do not run it.** The symmetry analysis in that section (bidegree `(1,0)×(1,0)`,
Claim-S permitted, parity obstruction genuinely bypassed) stands and is still the correct symmetry
story — but the channel is bounded, not live.

⚠ This is a negative, and the project's own stance is that only a rigorous analytical proof closes an
avenue. **An unexecuted derivation is not that.** The argument above needs to be written properly and
independently checked before it closes anything.

### 3.3 Where that leaves the single-point frontier

Every single-point readout is either bounded-degree (KS), a lattice cell (§3.2), or multiplicative
(P6b, `#R·√p`). To leak, a single-point readout needs complexity `≳ √p ≈ 2¹²⁸`. **The door is not
single-point.**

---

## §4 — Cycles 5–7: three regimes nothing in the record touches

### 4.1 ★ Incomplete sums / short scalars — no bound applies, and nothing has been run

Every bound in the record (Weil, KS, WD/Kummer, Parseval, the row budget) is a **complete-sum** bound:
a sum over the full orbit `d ∈ ℤ/n`. Every statistic sampled `d` uniformly.

**For a family of `~B` scalars with `B ≪ √p`, no character-sum bound says anything.** Incomplete sums
over a box of length `B` carry an error `~√p log p`, which exceeds the trivial bound `B` whenever
`B < √p log p`. This is not a gap in the record's execution — it is a genuine analytic vacuum, and it
is where cryptanalysis has always lived.

Grep for `incomplete sum` / `short scalar` / `short-scalar` across all `*.md`: **zero hits.**

**The move:** run the lift-geometry statistics on **short-scalar families** — `[z]G` for `z ∈ ℤ[ω]`
with `N(z) < B` — instead of the full orbit. Sextant law, norm band, flap density `¾:⅛:⅛`, `C_T`: all
are proved/verified for the complete orbit and are **not forced** on a subfamily. Any deviation is
(i) excluded by no theorem, (ii) directly meaningful.

Controls: match against random subsets of the same size (finite-size fluctuation is `O(1/√B)`), and
the record's standard firing-control discipline. ⚠ The record cites Galbraith–Ruprai
negation-on-intervals, so intervals are on the radar **algorithmically** but never **structurally**.

⚠ **Scope note:** short scalars are a curve-arithmetic question (the distribution of `[z]P` for `z` in
a box). This is not the PRNG/generation angle and must not drift into it.

### 4.2 ★ #17's Rayleigh null may be the wrong null

The sub-Rayleigh deficit (`Z = −13.99`, `+8%` excess of near-zero harmonics, locus = the low tail) has
twice **abstained**, with its mechanism refuted and its cause unlocated.

A Rayleigh null assumes the harmonics are complex-Gaussian — a sum of many independent random phases.
**They are not.** They are traces of Frobenius in a low-dimensional family with exact symmetries, and
the record already knows the family is `SU(2)`-like at the second moment (§0). The low tails differ by
an order:

```
complex Gaussian:            P(|U| < ε)  ~  ε²
real / low-dim trace:        P(|U| < ε)  ~  ε      (density is nonzero at 0; Sato–Tate is maximal there)
```

**An excess of near-zero harmonics is what you get when the true distribution is a low-dimensional
trace distribution and the null is complex Rayleigh.** The record has the correct null available —
it computed the `SU(2)` variance itself — and used a Rayleigh one.

**Decisive move:** re-run #17 against the Katz–Sarnak symmetry-type prediction for the family rather
than against Rayleigh. This is a **null-model** question, not a re-analysis of the data, and the record
already has three retractions of exactly this class (#6 "a null-mismatch artifact", #3 "tested a
proxy", #5). ⚠ It does not resolve #17 by itself — it re-types it from "is the excess a shadow of the
row budget?" to "is the excess anything beyond the family's own symmetry type?"

### 4.3 ★ Every statistic in the record is mean-based; lattice attacks live in the tail

Correlation, mutual information, moments, `G²`, rank statistics, copy-fraction bounds — all are
**average** statistics. **LLL/HNP-shaped attacks do not use averages.** They use the rare event: a
handful of unusually small residuals, found among many samples, then combined by lattice reduction. A
correlation null does **not** exclude an LLL-usable structure, because LLL exploits the tail.

**And the one persistent unexplained anomaly in the whole record is a tail phenomenon** (#17, the low
tail). Whether or not §4.2 dissolves it, the methodological point stands on its own: **extreme-value /
tail statistics are an untested instrument class here.** Concretely — over many `d`, how often is
`|eis(x_d) − (linear function of d)|` anomalously small, versus the Poisson/extreme-value prediction?
That is a different question from "is the correlation zero", and the record has only ever asked the
second.

### 4.4 Linear complexity — a classical frame for the same object

`#{a : V(a) ≠ 0}` is the **linear complexity** of the sequence `k ↦ χ₂(y_{[d+k]G})` — the curve's
"`y`-Legendre sequence", and the sequence an attacker actually sees, since from `Q = [d]G` you can
cheaply compute `Q + [k]G` for any `k`. There is a classical literature (Turyn; Ding–Helleseth–Shan;
Meidl–Winterhof) on linear and 2-adic complexity of Legendre and Sidelnikov sequences.

This also **explains DC5**: at prime `n` a full-orbit character sum cannot vanish exactly unless the
readout is constant ⇒ **no `V(a)` vanishes ⇒ linear complexity is full.** That is an analytic closure
of the exact-vanishing branch and it is already implicit in the record; naming it as linear complexity
makes it a citable statement rather than a spec footnote. Approximate predictability (many *small*
`|V|`) is **not** closed by it — which is §4.2/§4.3 again.

---

## §5 — Loose ends that fell out, kept because they were not filtered

### 5.1 `h(−p)` is not curve structure

`B_{1,χ} = (1/p)Σχ(t)t` and `B_{1,χ₂} = −h(−p)` is Dirichlet's class number formula. The proved
general sawtooth law has `B_{1,χ}` as its only non-elementary input. **So `h(−p)`'s appearance in
`|FLD| = 6h` is the first generalized Bernoulli number of `χ₂` — a property of the quadratic character
mod `p`, not of a curve with CM by `ℚ(√−3)`.** The mystery was in the framing.

### 5.2 The `μ₆`-cluster may be an eta/theta multiplier system

`H1` is `(−1)^{flap/6} = χ₂(2) = (−1)^{(p²−1)/8}`. **`(p²−1)/8` is the classical theta multiplier
exponent.** Dedekind sums are the eta multiplier; the record's proved law is a Dedekind–Rademacher
coboundary; `h` enters via `B_{1,χ}`. **Unifying hypothesis: the whole `σ`/flap/`FLD`/`H1`/`(†)`
cluster is the eta–theta multiplier system of the Eisenstein lattice, reduced mod `p`.**

**Concrete first move:** the change of basis from the standard basis of `(π_p)` to the **reduced**
basis is an explicit `SL₂(ℤ)` matrix, and Dedekind sums `s(c,d)` / the Rademacher `Φ` are exactly the
invariants of such a matrix. Compute `Φ` of that matrix and compare against `FLD`, `h`, and the flap
counts. If it lands, one classical object explains `(†)`, `H1`, the `FLD` sign (#9), and plausibly
`L1` — four open items at once. Cheap.

⚠ Retraction #12 is relevant and cuts the other way: *"L1 needs analytic machinery" was withdrawn — the
elementary `a→2a` fold applies to `T⁺`.* So do not assert that `L1` requires the modular machinery;
try the elementary route first.

### 5.3 The literature item, with a specific first source

The `★` priority/literature item has never been run. **Start with Ireland & Rosen, *A Classical
Introduction to Modern Number Theory*, Ch. 18** — it gives `#E(F_p)` for `y² = x³ + D` explicitly via
the **sextic residue character and Jacobi sums**. That is precisely the record's `m`-law / Jacobi-sign
territory, and it is older and more elementary than Silverman–Stange (whose Prop 23 was already found
to contain "the record's own manoeuvre verbatim"). **This record's history is that reading the source
dissolved the obstacle four times.**

### 5.4 Frontier #3's canonical object, named

The non-homomorphic amicable correspondence is described only as `π_n = π_p − 1`. The canonical map it
induces is concrete: since `ℤ/n = F_n` is the **base field** of `Ẽ` (with `#Ẽ(F_n) = p`), the scalar
`d` is a **field element** on `Ẽ`, and

```
Φ :  d  ↦  dlog_{Ẽ}( the point of Ẽ with x-coordinate d )      (2-to-1, defined ~half the time)
```

is a canonical `ℤ/n ⇢ ℤ/p` map that is **not** the CRT map. It is hard to evaluate (a 256-bit DLP on
`Ẽ`), so there is no free lunch — but it is the object frontier #3 is about, and it can be tabulated
exhaustively at small amicable pairs to ask whether it has any structure beyond the automatic `μ₃`
intertwining (which is forced by GLV on `Ẽ` and therefore carries no information).

### 5.5 Smaller things, unranked

- **The CM Lattès map.** Multiplication by `(1−ω)` has degree 3, giving an explicit degree-3 rational
  self-map of the `x`-line whose dynamics is the CM action. On the group it is multiplication by `s`
  with `s² = −3 mod n`. **One-line check: what is `ord_n(s)`?** — the same species as `ord_n(p)` and
  `ord_n(2)`, both already dissolved, so the prior is "a draw"; cheap enough to settle.
- **Is `3 | f` forced or a draw?** `f = 3·79·349·2698097·(91-bit)`. `3 | f` is what gives secp its
  `End = O_3` descendant. If it is a `1/3` draw, the volcano-descent direction is contingent.
- **Longer aliquot cycles.** secp's is a length-2 cycle. The six sextic twists give six candidate
  chains; Silverman–Stange Conj. 40 is the density statement. Cheap, pure structure, and it probes the
  same twist-selection question as §2.1.
- **CM makes the torsion covers abelian.** For a CM curve the mod-`ℓ` Galois image lies in the
  normalizer of a Cartan, so every torsion-level cover is essentially abelian ⇒ Kummer or
  Artin–Schreier ⇒ **already inside the two families the record has bounded.** Worth stating: it says
  there is no non-abelian cover structure at torsion level to hunt for.
- **`k = 8` cover** (genus 7, new dim 4) remains unbuilt; `8 ∤ p−1` at secp gives the same
  "character not over `F_p`" prior as `χ₄`/`χ₁₂`, unverified.

---

## §6 — Ranked, with the first move and the falsifier

Ordering is a proposal. Items 1–3 and 6–8 have no leakage content.

| # | move | why now | cost | falsifier |
|---|---|---|---|---|
| **1** | **§1.4 — the `j≠0` mechanism control for the cap** | the record has never varied the cap's mechanism, and §1 predicts failure off `j=0` and success at every `j=0` curve | low | `S_y ≤ 2` holds off `j=0` ⇒ §1's route is wrong |
| **2** | **§1.5 — the fourth moment `E[u⁴]` vs `1/8`** | 2nd moment is forced and carries no information; the 4th is not forced and separates full `SU(2)` from a smaller group | trivial, data on disk | `E[u⁴] = 1/8` ⇒ full `SU(2)`, no small-monodromy lock |
| **3** | **§1.1–1.3 — write the lock properly and re-open item 2** | item 2's "research-grade" verdict predates the 120° fact by one day and was never revisited | medium | the `μ₃` isotype argument does not produce the `ζ₃` relation |
| **4** | **§4.2 — re-run #17 against the correct symmetry-type null** | a null-model question, not a re-analysis; three retractions of this exact class already | low | the excess survives the correct null ⇒ #17 is real and sharper |
| **5** | **§4.1 — lift-geometry statistics on short-scalar families** | no bound applies in this regime and nothing has been run in it | medium | statistics match the complete-orbit laws within finite-size error |
| **6** | **§5.2 — Rademacher `Φ` of the reduced-basis `SL₂(ℤ)` matrix** | one classical object would cover `(†)`, `H1`, #9, plausibly `L1` | low | `Φ` bears no relation to `FLD`/`h`/flap counts |
| **7** | **§5.3 — Ireland–Rosen Ch. 18** | the `★` literature item, never run; source-first has dissolved four obstacles here | low | — |
| **8** | **§3.2 — write the lattice-cell Wiener bound properly** | closes §XI.1's bit sub-item and the named `eis_n` loophole **by proof** | low | a lift-geometry readout that is not a box condition on linear forms |

**Standing gates.** `experiment-designer` prereg before any sweep/scan/drill. Every bound carries
POWER + SCOPE. The control must fire. Retest out-of-sample before naming a zero; count only
**unforced** cells; reproduce the tally independently.

---

## §7 — What this document does not claim

No grade moves. **The cap is not proved** — §1 reduces `(★)` to an elementary tensor identity *given*
the 120° law, and that law is `[VERIFIED — exact]` at 8–10 primes and **not derived**; §1.3's
sheaf-theoretic source for the `ζ₃` is a sketch. §3.2's Wiener bound is an unexecuted derivation and
therefore closes nothing yet. §4.1, §4.2, §4.3 are unrun. §5.2 and §5.4 are hypotheses with no
measurement behind them.

**Four of the best-looking ideas here were already on file** (§0) and are attributed, including the
second-moment `SU(2)` argument that the previous synthesis mistakenly presented as new — a correction
is owed to `SYNTHESIS_curve_structure_and_new_directions_v1.md §2.6(a)`, and its §2.3 proposal is
withdrawn by §3.2 above.

**Scale banner #5 governs everything empirical.** Every measurement discussed sits at `p ≈ 10²–10⁵`
against secp's `2²⁵⁶`. The items that reach scale are the exact identities and, if it is ever derived
rather than verified, the N1 identity.
