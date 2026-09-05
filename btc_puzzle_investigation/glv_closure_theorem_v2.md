# Closure theorem for single-coordinate lift readouts (v2, 2026-07-14)

Supersedes v1. v1's one-line "correlation ≤ … = O(p^{-1/2}) — panel closes" was
sloppy: (a) the MI step was hand-waved as "Σ over character modes," which does **not**
close (there are ~p² modes; per-mode O(p^{-1}) can sum to O(p)); (b) two hypotheses
were unstated (bounded value-alphabet, marginals bounded below); (c) Lemma W was left
as a gesture. v2 gives the correct MI argument via **level-set covariances** (O(1)
value-pairs, not character modes), states all hypotheses, and closes with an explicit
rigor ledger. Anchors: `glv_closure_verification_v1.py`.

---

## 1. Setup

`E/𝔽_p : y²=x³+7`, `n=#E(𝔽_p)`, `G` a generator, `x(·)` the x-coordinate on `E∖{O}`.
`d ↦ [d]G` bijects `ℤ/nℤ → E(𝔽_p)`; `n = p+1−t = p(1+o(1))` (Hasse). For `F:𝔽_p→ℂ`,
`g:ℤ/nℤ→ℂ`, Wiener norms `‖F‖_A=Σ_b|F̂(b)|`, `F̂(b)=(1/p)Σ_x F(x)e_p(-bx)` (and `‖g‖_A`).
Twisted sum `T(a,b)=Σ_{d=0}^{n-1} e_p(b·x([d]G))·e_n(ad)`.

## 2. Cited input — the twisted-sum bound  **[CITED]**

> **(KS).** For `(a,b)≠(0,0)`, `|T(a,b)| ≤ C·p^{1/2}(\log p)^{O(1)}`, `C` absolute.

Reference: D. Kohel & I. Shparlinski, *On exponential sums and group generators for
elliptic curves over finite fields*, ANTS-IV, LNCS 1838 (2000), 395–404; I. Shparlinski,
*Cryptographic Applications of Analytic Number Theory* (Birkhäuser, 2003), Ch. 6, for the
mixed additive(coordinate)×additive(index) sum over the full group. Sub-cases handled by
orthogonality: `T(a,0)=0` (a≠0); `T(0,b)` is the pure x-coordinate sum, also `O(√p)`.
**[VERIFIED]** `max_{(a,b)≠0}|T|/√p` stays `O(\log p)` (0.97→2.66 over p=13..97), never √p.

## 3. Reduction  **[PROVED]**

> **Lemma R.** `|Cov_d(F(x([d]G)), g(d))| ≤ (max_{(a,b)≠(0,0)}|T(a,b)|/n)·‖F‖_A·‖g‖_A.`

*Proof.* `F=Σ_b F̂(b)e_p(bx)`, `g=Σ_a ĝ(a)e_n(ad)` ⇒
`(1/n)Σ_d F(x([d]G))g(d) = Σ_{a,b} F̂(b)ĝ(a)T(a,b)/n`. The `(0,0)` term is `E[F]E[g]`;
the covariance is the remaining sum. `b=0,a≠0` terms vanish (`T(a,0)=0`). Bound the rest
termwise by `|F̂(b)||ĝ(a)|·max|T|/n`; the double sum of `|F̂||ĝ|` is `‖F‖_A‖g‖_A`. ∎

**Corollary (correlation).** With [KS], `|Cov| = O(p^{-1/2+o(1)})·‖F‖_A‖g‖_A`. At secp
`p≈2^{256}`: `≤ ‖F‖_A‖g‖_A·2^{-128+o(1)}`.

## 4. Mutual-information corollary — the corrected argument  **[PROVED, given KS+H1–H3]**

Let `F:𝔽_p→𝓕`, `g:ℤ/nℤ→𝓖` be **finite-valued** with:
- **(H1)** bounded alphabet: `|𝓕|,|𝓖| = p^{o(1)}`;
- **(H2)** marginals bounded below: `P(F=f), P(g=g') ≥ p^{-o(1)}` for attained values;
- **(H3)** level-set Wiener norms `‖1_{F=f}‖_A, ‖1_{g=g'}‖_A = p^{o(1)}`.

For each pair `(f,g')`, `Δ_{fg'} := P(F=f,g=g') − P(F=f)P(g=g') = Cov_d(1_{F=f}, 1_{g=g'})`.
Lemma R on the {0,1}-valued readout `1_{F=f}` and target `1_{g=g'}` gives
`|Δ_{fg'}| ≤ (max|T|/n)·‖1_{F=f}‖_A‖1_{g=g'}‖_A = O(p^{-1/2+o(1)})`.
By the standard `D_{KL} ≤ χ²` inequality (nats; `MI ≤ χ²/\ln 2` in bits),
`MI(F;G) ≤ (1/\ln2)·Σ_{f,g'} Δ_{fg'}² / (P(F=f)P(g=g'))`.
By (H1) the sum has `p^{o(1)}` terms; each numerator is `O(p^{-1+o(1)})` and each
denominator is `≥ p^{-o(1)}` by (H2). Hence
> **`MI(F(x([d]G)); g(d)) = O(p^{-1+o(1)})`.**

*The fix vs v1:* the sum runs over the `p^{o(1)}` **value pairs** (not the ~p² character
modes); each term is controlled by a single **level-set covariance** via Lemma R. This is
why it closes where the per-mode version did not.

## 5. Readout classes

- **C1 (character-class) — [PROVED, given KS].** `χ_k`, additive characters, `O(1)`-combos:
  `‖·‖_A=O(1)`, (H1)–(H3) trivial ⇒ `MI=O(p^{-1+o(1)})`. Subsumes χ₆-uniformity, GLV shifts.
- **C2 (geometric lift readouts) — [given KS + Lemma W].** sextant, ε, norm-band, `k×k`
  cell: `F=Φ∘eis`. (H1)/(H2) hold (area law ⇒ each value has density `Θ(1)`); (H3) is:

> **Lemma W.** `‖1_{sector}∘eis‖_A = O(\log p)` (same for norm-band / bounded cells).
> *Proof sketch.* Via `eis: 𝔽_p ≅ ℤ[ω]∩P`, `F̂_s(b)=(1/p)Σ_{(u,v)∈S_s∩P} e_p(-(bu+b'v))`,
> `b'=bω_p`. `S_s∩P` is a lattice **triangle** with edges along ℤ[ω]-directions (unit
> associates of π_p). Iterating the 2-D sum along one edge gives per-row geometric sums
> `O(1/‖c/p‖)`; the row-sum gives a second geometric factor; corners `O(1)`. So
> `Σ_b|F̂_s(b)| = O(p^{-1}Σ_c 1/‖c/p‖) = O(\log p)`. ∎ (sketch)
> **Status: [VERIFIED] `≈0.65\log p`** (p=13..97, never √p); **[GAP]** full edge/corner
> accounting (standard lattice-polytope Fourier analysis; Brion–Barvinok / Hardy–Littlewood)
> not written to full rigor.

## 6. Rigor ledger (what is actually proved)

| Claim | Status |
|---|---|
| Lemma R (Fourier reduction) | **PROVED** (complete) |
| MI corollary given (H1–H3)+KS | **PROVED** (complete, §4) |
| KS twisted-sum bound `|T|=O(√p·polylog)` | **CITED** (theorem in the literature) + VERIFIED numerically |
| C1 class closure (χ_k etc.) | **PROVED** modulo the cited KS |
| Lemma W (`‖·‖_A=O(log p)` for sectors) | **PROVED-sketch + VERIFIED**; full rigor = **GAP** |
| C2 class closure (sextant/ε/norm) | Holds **given** Lemma W |
| Two-point (addition) & multi-key extensions | **GAP — named** (need bilinear KS, §7) |

**Honest bottom line:** the panel is closed **conditional on** a cited theorem (KS) and one
standard-but-unwritten lemma (W, empirically confirmed). It is a conditional theorem, not an
unconditional one — stated as such.

## 7. Scope — where the gate can still be

Lemma R bounds a **single** sum over one `d`. Not covered:
- **Joint/multi-key** readouts of the *set* `{x([d_i]G)}` — bilinear/multilinear sums,
  outside KS as stated. (The stance principle "only a joint SET property survives" is exactly
  this complement.)
- **Addition-law two-point panel** (independent P,Q): needs a bound on
  `Σ_{d_P,d_Q} F(x([d_P]G),x([d_Q]G),x_S)` with the group law coupling via `S₃=0` — a
  two-variable KS-type bilinear estimate, **not proved here**. Empirical null stands.
- **Generation side** (the RNG that chose the keys) — outside; this is the curve map only.

## 8. Reproducing the verification (and the false starts)

`glv_closure_verification_v1.py` — recompute both anchors on small prime-order `y²=x³+7`
curves. To rebuild from scratch:
1. Find `p≡1 mod 3` with `#E` prime; enumerate the group `[d]G`, store `x([d]G)`.
2. **Twisted sum:** for each `b`, FFT `f_d=e_p(b·x([d]G))` over `d` → `T(a,b)` for all `a`;
   report `max_{a,b≠0}|T|/√p`. (Float/`numpy.fft` is fine **here** — character sums are
   roots of unity; the no-float rule governs the *key/leakage signal path*, not analytic-size
   checks. Say so in the header or a reviewer will flag it.)
3. **Wiener norm:** build `eis` (`make_lift`), tabulate `sextant(eis(x))` for all `x`; for each
   value, FFT the {0,1} indicator, sum `|coeff|`; report growth vs `log p`.

**Coding false starts worth not repeating (from this session):**
- **Residue-vs-component tautology.** Correlating `r=v−w` against `w` gave `MI=0.48–0.64,
  z=+5000` — a subtraction artifact, not signal; the shuffle-control **passes** (→0) and thus
  *masks* it. Fix: features and targets must be of **disjoint construction**; the clean
  "residue vs bridge" test is *boundedness of r itself* (distinct/top-mass/N-bits).
- **Wrong additive baseline.** `U_S−U_P−U_Q` for the group law is wrong (`x_S=λ²−x_P−x_Q`, not
  additive on x); it spreads by construction. Use the CM-covariant object σ₁=−B/A of the `S₃`
  quadratic instead.
- **Miscalibrated null on skewed marginals.** A 3-bucket norm readout made the shuffle CONTROL
  fire at `z=+4.7`; a k=8 (4096-cell) grid made it fire at `z=+1.56`. If the control fires,
  the null — not the data — is the problem; drop the readout or add resamples. **Always print
  the control z next to the signal z.**
- **First usable print.** The decisive diagnostic is population scaling with a validated
  detector: run N, 2N, 4N and a *calibration* case with known answer (the endo correction
  should show distinct=3, top-mass≈0.75). Only then is a `z` interpretable.
