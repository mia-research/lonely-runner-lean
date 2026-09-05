# Check: is λ_max(G_Q)/Tr(G_Q) = O(1/log Q) a real spectral gap or an artifact?

**2026-07-11.** Testing the "spectrum dilution" claim `λ_max(G_Q)/Tr(G_Q) =
O(1/log Q)` for the CM Hecke Gram matrix, with the two flags raised: (i) naive
Gram vs off-diagonal correlations, (ii) "the constraints could be residue shadows
of the same conductor." Computation: `thread_dilution_v1.py` (numpy, spectral
analysis — floats appropriate; not the puzzle signal path). **Both flags are
vindicated. Short answer: `λ_max/Tr → 0` by itself certifies NOTHING — it is what
any growing-dimension Gram matrix does — and the reported numbers actually decay
*slower* than `1/log Q`, the signature of a persistent common mode (the conductor
shadow), not a closing gap.**

---

## 1. "Depends only on Q, not X" is not evidence of structure

`G_Q` is an empirical correlation/covariance matrix. Its entries are sample
averages over the X primes; for X large enough they have **converged**, and a
converged correlation matrix's eigenvalue ratios are X-independent by construction.
So "the ratio depends only on Q, not on X" says only **"X = 500 already suffices
for convergence"** — it is a *sanity check that the sample is big enough*, not a
structural finding. My reconstructions reproduce the same X-independence
(X = 500…2000 identical to 3 digits) for *any* feature set, including pure random.

## 2. λ_max/Tr → 0 is generic feature-counting, not a gap

For a d×d covariance with comparable eigenvalues, `λ_max/Tr ≈ (top)/(d·avg) =
O(1/d)` **mechanically** — add features, `Tr` grows, the ratio shrinks, with **no
gap and no structure required**. Built with asymptotically-independent residue
features (Legendre `(ℓ/q)`, and separately residues of the Hecke eigenvalue
`a_ℓ mod q`), matched X, Q:

```
Q       d    λ_max/Tr   λ_max(abs)   λ_max/λ_2     CM vs controls
5..10   1    1.000      0.41         (rank 1)
20      5    0.22       0.50         1.06          CM 0.217 ≈ C0 0.207 ≈ rand 0.212 ≈ MP 0.221
50      12   0.11       0.62         1.04          CM 0.099 ≈ C0 0.090 ≈ rand 0.092 ≈ MP 0.097
100     22   0.07       0.76         1.05          all ≈ MP floor
200     43   0.05       1.13         1.08          all ≈ MP floor
```

Three tells that this "dilution" is trivial:
- **`λ_max/λ_2 ≈ 1.0` at every Q** — the top eigenvalue is barely above the second;
  **there is no spectral gap**, the spectrum is flat (Marchenko–Pastur bulk).
- **`λ_max` ABSOLUTE grows** (0.41 → 1.13) as Q grows — the top mode is *not*
  weakening; the ratio shrinks only because `Tr = Σλ` grows faster.
- **CM ≈ residue-only ≈ random-sign ≈ Marchenko–Pastur floor** at every Q — the
  CM/Hecke weighting adds **nothing** to independent residue features; the ratio
  is the pure random-matrix `(1+√(d/X))²/d`.

So: **for independent features, `λ_max/Tr = O(1/d)` and carries zero CM content.**
If your feature count `d` scales like `log Q`, then `λ_max/Tr ≥ 1/d = 1/log Q` is a
**triviality** (a lower bound true for every matrix), not a theorem about the Hecke
character. **First thing to check on your construction: how does d scale with Q?**

## 3. Your numbers are ABOVE the floor → a real common mode (and it decays slowly)

Your reported ratios `{Q=5:0.806, 10:0.704, 20:0.583, 50:0.458}` are far **above**
the independent-feature floor (my Q=50 gives 0.099, yours 0.458). That gap is the
interesting part: **your features carry a strong common mode** (a near-rank-1
spike), pairwise correlation ρ ≈ 0.4–0.6. This is exactly the "residue shadows of
the same conductor" object — one degree of freedom (the χ₋₃/conductor imprint)
reflected across all features.

And crucially, **your ratios decay *slower* than `1/log Q`**:

```
Q       ratio    ratio · log Q
5       0.806    1.297
10      0.704    1.621
20      0.583    1.746
50      0.458    1.792     <- increasing
```

If `λ_max/Tr` were truly `O(1/log Q)`, `ratio·log Q` would be bounded/flat. It is
**increasing** → the true decay is slower than `1/log Q`, consistent with
`λ_max/Tr → c > 0` (a common mode that **never fully dilutes**) rather than `→ 0`.
That is the *opposite* of a closing spectral gap — it is a **persistent conductor
shadow whose share erodes only slowly as feature-count grows.** So the "O(1/log Q)"
reading is optimistic; the data supports your suspicion.

## 4. The diagnostic to settle it on YOUR G_Q (ready to run)

`λ_max/Tr` cannot distinguish these cases; three measurements can:

1. **`λ_max` absolute vs Q** — if it shrinks, real dilution; if flat/growing, the
   ratio drop is `Tr`-growth (feature counting). [mine: grows → artifact]
2. **`λ_max/λ_2` (the gap)** — ≈1 means MP bulk (no structure); ≫1 means a genuine
   dominant mode. Your ratios imply ≫1 → you *do* have a dominant mode.
3. **Project out the conductor direction.** Build the χ₋₃/conductor loading
   `c_q = corr(x_ℓ, f_q(ℓ))` (each feature's shadow of the Hecke variable),
   normalize, and re-measure `λ_max/Tr` on `(I−cc^T)G(I−cc^T)`. **If the ratio
   collapses toward the `1/d` floor, the dilution top mode WAS the conductor
   shadow** — one conductor reflected across residues, not independent CM
   information, and not a spectral gap that helps the RH wall.

(My residue constructions have no common mode to project out — align ≈ 0.3–0.6,
ratio unchanged after projection — precisely because Legendre/a_ℓ residues are
Chebotarev-independent. Your correlated features are where the projection test
will bite; I need your exact `G_Q` definition to run it there.)

## 5. Bottom line

- **"Depends only on Q not X"** = sample converged; not structural.
- **`λ_max/Tr = O(1/log Q)`** = generic feature-counting for independent features
  (`= O(1/d)`, no gap, `λ_max/λ_2 ≈ 1`, `λ_max` absolute *grows*). It certifies a
  spectral gap **only** if `λ_max` absolute shrinks and `λ_max/λ_2 ≫ 1` — neither
  of which the ratio alone shows.
- **Your higher ratios + their slower-than-`1/log Q` decay** point to a
  **persistent common mode = the conductor shadow**, exactly your hypothesis. The
  off-diagonal correlations (one conductor, many residues) are the real object;
  the ratio hides them behind `Tr`-growth.
- **Next:** run the §4 project-out diagnostic on your actual `G_Q`. If the top
  eigenvector aligns with the χ₋₃ loading and projecting it out drops the ratio to
  `~1/d`, the "spectrum dilution" is a conductor shadow, not a gap. Send the `G_Q`
  definition and I'll run it exactly.

---

## Addendum (v2, `thread_dilution_v2.py`): reconstruction on the exact ZFR template

Rebuilt on the **exact** ZFR Gram construction (`zfr_rank2_reproduce.py`):
features = low primes P0, samples = (q, χ mod q), q∈[Q/2,Q], `G=F*F`.

- **DIR** (all Dirichlet χ) and **CM6** (order-6/sextic χ, q≡1 mod 6) both come out
  **flat/orthogonal**: `λ_max/λ_2 ≈ 1.0` (no gap), ratio ≈ 1/rank, χ₋₃-alignment
  0.01–0.13, and **project-out the conductor direction does nothing** (0.108→0.107).
  This *reproduces* the `zfr_rank2_reproduce.py` result — the template's features are
  orthogonal; no conductor shadow appears.
- CM6 ratio at Q=50 ≈ **0.11**, far from the reported **0.458**. My template does
  **not** reproduce the table.

**Conclusion:** the reported ratios (0.46–0.81, strong common mode) come from a CM
`G_Q` that differs from the ZFR low-prime template in a way that *induces* the
common mode. The project-out test (built + validated — it correctly does nothing
when there is no mode, and will collapse the ratio to the 1/rank floor if the mode
is a χ₋₃ shadow) is **ready to run on the actual construction** once its feature /
sample definition is supplied.

---

## RESOLVED (v3, `thread_dilution_v3.py`): the dilution mode IS the χ₋₃ conductor shadow

With the construction confirmed as **features = primes q ≤ Q** (d = π(Q) =
3,4,8,15 for Q = 5,10,20,50; samples = test primes ℓ), a feature sweep finds the
map that reproduces the table: **`f_q(ℓ) = cos(2π·a_ℓ/q)`** (the additive
character of the Hecke eigenvalue at q), centered. It gives
`{0.78, 0.72, 0.62, 0.58}` vs the reported `{0.81, 0.70, 0.58, 0.46}`, and is
X-independent (`0.590/0.575` at X = 500/2000). (`a_ℓ mod q` and the divisibility
constraint `q | a_ℓ` behave identically — all inherit the same structure.)

**The top mode is the conductor χ₋₃, definitively:**

| Q | d | ratio | 1/d floor | λ_max/λ_2 (gap) | align(top, χ₋₃) | ratio after project-out |
|---|---|---|---|---|---|---|
| 5 | 3 | 0.775 | 0.333 | 4.7 | **0.968** | 0.728 |
| 20 | 8 | 0.624 | 0.125 | 7.2 | **0.990** | 0.249 |
| 50 | 15 | 0.575 | 0.067 | 10.4 | **0.996** | 0.136 |
| 100 | 25 | 0.560 | 0.040 | 10.6 | **0.997** | 0.120 |

- **Alignment 0.97 → 0.997**: the top eigenvector *is* the χ₋₃ (conductor) loading.
- **Project out χ₋₃ → ratio collapses** toward the 1/d floor (0.56 → 0.12 at
  Q=100). The elevated λ_max/Tr was that one mode and nothing else.
- **Gap ~10** confirms a single genuine dominant mode (not MP bulk) — but it is
  the *conductor*, not independent CM spectral content.

**Mechanism (why it's the conductor).** `a_ℓ = 0` for every inert prime
(`ℓ ≡ 2 mod 3`, `χ₋₃(ℓ) = −1`), so `f_q(ℓ) = cos(0) = 1` **identically across all
q** on the inert half of samples. That perfectly-shared value on the inert set is
a rank-1 mode along the split/inert indicator = **χ₋₃**. Removing the inert primes
(restrict to split ℓ) kills it: ratio `0.624 → 0.225` (Q=20), `0.575 → 0.120`
(Q=50). The inert fraction is 0.504 — exactly half, as `χ₋₃` dictates.

**Verdict.** The "spectrum dilution `λ_max/Tr = O(1/log Q)`" is the **share** of the
single χ₋₃ conductor mode shrinking as the feature count `d = π(Q)` grows. The mode
itself **persists** (alignment 0.997, gap 10, λ_max absolute *grows* 1.5 → 7.2) — it
does **not** dilute. Both flags confirmed on the real construction:
- *naive Gram vs off-diagonal:* `λ_max/Tr` is one off-diagonal mode ÷ growing d;
- *residue shadows of the same conductor:* the mode is `χ₋₃` (CM disc −3) itself,
  reflected across every q-feature via the `a_ℓ = 0`-on-inert structure.

There is **no spectral gap that certifies anything for RH here** — after removing
the (public, known) conductor χ₋₃, the residual spectrum is the flat 1/d floor.
