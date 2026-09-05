# CONFIRMED — k=3 phase channel: `3·arg T(a₀,b)` locks to `χ₂(b)` on Weierstrass x-coordinates

**Grade: EMPIRICAL / VERIFIED-scope** — survives a *negation-parity-matched* permutation null
(not just the free shuffle) on CM and non-CM prime-order curves. Date 2026-08-17.
Does NOT leak the scalar (coordinate-side structure). Object per point set, not per key.

## Object
For a prime-order curve `E/𝔽_q`, generator `G`, `x_d = x([d]G)`, the twisted sum
`T(a₀,b) = Σ_{d=1}^{n-1} e_q(b·x_d) · e_n(a₀·d)`. Claim: the cubic phase `3·arg T(a₀,b)`
phase-locks to the quadratic character `χ₂(b)`. Statistic `R = |mean_b χ₂(b)·e^{3i·arg T}|`.

## Verification (with the CORRECT matched null)

- **Mechanism step 1 PROVED empirically:** `arg T(a₀,−b) = −arg T(a₀,b)` for **100%** of `b`
  on every tested curve ⇒ `sin(3 arg T)` is odd under `b→−b`, matching `χ₂`'s oddness at `p≡3 mod4`.
- **Free-shuffle control is inadequate** (breaks the `b→−b` parity, overstates significance) — so the
  verdict rests on the **parity-matched control** (shuffle `χ₂` while preserving `χ₂(−b)=−χ₂(b)`):

| curve | n | R_real | parity-matched p |
|---|---|---|---|
| CM `x³+7` (p=43) | 31 | 0.441 | 0.016 |
| CM `x³+7` (p=547) | 547 | 0.289 | **0.001** |
| non-CM `x³+x+3` (p=43) | 47 | 0.336 | 0.047 |

**Survives the parity-matched null** ⇒ real beyond the forced oddness: the specific `χ₂` residue
pattern correlates with the phase, not merely its parity.

## 15-curve family map (parity-matched p, a₀=1)

- **CM j=0** (5 curves): all significant; **mean R = 0.314**.
- **non-CM** (4 curves): 2/4 significant, 2/4 marginal (p≈0.06, low n); **mean R = 0.314**.
- **j=1728** (`y²=x³+Ax`): **untested** — no prime-order curve found in the scanned range
  (these curves tend to non-prime order; needs a targeted `p≡1 mod4` search).

## Scope / what is and isn't established

- **Established:** the channel is real (survives the negation-matched null) and present on **both** CM
  and non-CM prime-order curves — supports "universal across CM/non-CM."
- **NOT reproduced:** the proposed amplitude hierarchy `CM(0.51) > non-CM(0.43) > j=1728(0.32)`. My map
  gives **CM ≈ non-CM ≈ 0.314** (equal), and j=1728 untested. The "CM carries the strongest amplitude"
  claim does not hold in this measurement.
- **NOT supported — the "stable archimedean amplitude invariant".** A 15-curve sweep report claims `|A|`
  is a rigid invariant bounded in `[0.2,0.6]` with narrow σ. Its OWN table refutes this: `|A|` ranges
  **0.104–0.445** (CV 32%, two curves below 0.2); the largest-p CM curve (p=127) has the LOWEST `|A|=0.104`
  (no asymptotic convergence to ~0.31); and the reported `σ_A ≈ 0.7` on every curve is just the RMS of a
  sine (`√½`), not an error bar — and it EXCEEDS `|A|` on all 15 curves. The real evidence is the
  permutation p-value on the correlation `r`, NOT a stable amplitude. The invariant framing is narrative
  overreach; the CORRELATION is what's confirmed.
- **Next refinement (owed):** a control that also preserves `χ₂`'s *multiplicative* character structure
  (the parity-matched null breaks multiplicativity); if the lock survives that too, upgrade toward PROVED.
  Mechanism steps 2–3 (why k=3 specifically) are a proof sketch, not yet a derivation.

## Update 2026-08-17 — two proposed refinements TESTED and resolved

- **The proposed `b→bᵏ` (odd k) "multiplicativity-matched control" is DEGENERATE (the identity).** For
  every odd `k` coprime to `p−1`, `R(b→bᵏ) = R_real` exactly (verified k∈{5,11,13,17,23,25}, p=43 CM).
  Reason: `χ₂` is invariant under `b→bᵏ`, so the map is a relabeling of the sum that preserves `R`.
  General obstruction: ANY `χ₂`-preserving frequency permutation ⟹ `R` unchanged, so **no permutation-based
  multiplicativity-matched null exists**. The parity-matched null is the strongest permutation control;
  the channel survived it. Upgrading past EMPIRICAL now requires the theoretical derivation, not a control.
- **Amplitude hierarchy does NOT emerge at large n.** Sweep at `n ≈ 547–797` (10–25× the earlier map),
  channel still significant (parity-matched p=0.005 all): CM mean R=0.310, non-CM mean R=0.304 — still
  equal. The "small-prime discretization artifact" explanation for the flatness is refuted; the amplitude
  is universal-and-flat (~0.31), not a separating CM>non-CM hierarchy.

## Update 2026-08-17 (3) — the p mod 4 dichotomy + the parity lemma is now PROVED

Reduce the channel to the QR-phase mean `mean_QR = (1/|QR|) Σ_{b∈QR} e^{3iθ(b)}`, `θ(b)=arg T(a₀,b)`.

**PROVED (parity lemma).** From `T(a₀,−b)=\overline{T(a₀,b)}` (w(x)∈ℝ, prior update) ⇒ `θ(−b)=−θ(b)`:
- **`p≡1 mod 4`** (`χ₂(−1)=+1`, χ₂ EVEN): `b∈QR ⟺ −b∈QR`, so `b↦−b` acts within QR; pairing gives
  `e^{3iθ(b)}+e^{3iθ(−b)} = 2cos 3θ(b) ∈ ℝ`. Hence `mean_QR` is **real, `Im≡0` identically**; the channel
  sits in `Re = cos 3θ` (even part, matches χ₂ even).
- **`p≡3 mod 4`** (`χ₂(−1)=−1`, χ₂ ODD): `b↦−b` maps `QR→nQR`, so `mean_{nQR}=\overline{mean_{QR}}`; the
  channel is `Im = sin 3θ` (odd part, matches χ₂ odd).

**Correction to earlier "universal amplitude" wording.** The invariant is **`|mean_QR| ≠ 0`** (universal on
all 15 tested curves, 0.13–0.78), NOT "`Im` nonzero on all" (a claim in a source report that is FALSE:
`Im=0` is forced for `p≡1 mod 4`) and NOT "channel vanishes there" (my own earlier mislabel — it's in `Re`).
The sin/cos component is set purely by `χ₂(−1)=(−1)^{(p−1)/2}`.

**Concentration is asymptotically REAL (empirical, strong).** `|mean_QR| ≠ 0` = the cubic phase `3θ(b)`
is CONCENTRATED over the QR class. Decay test, CM `x³+7`, `p≡3 mod4`, prime order: `|mean_QR|·√|QR|`
**grows 2→7** from p=43→967 (would be `O(1)` under equidistribution), while `|mean_QR|` stabilizes `≈0.33`,
`5–7×` the floor `1/√|QR|` and widening. So the channel is a genuine asymptotic phenomenon, not finite-`p`.
**Self-correction:** my earlier refutation of the "stable amplitude invariant" used small-`p` (finite-size)
scatter; at large `p` the CM amplitude clusters `0.33 ± 0.03` — essentially the `~0.31` the source claimed.
The invariant has real asymptotic support I dismissed too hard.

**MECHANISM FOUND + un-normalized channel PROVED** ([NOTE_k3_analytic_reduction_v2.md](NOTE_k3_analytic_reduction_v2.md)):
the k=3 × χ₂ coupling arises because three x-coords of `O`-summing points satisfy `x₁+x₂+x₃ = m²` (slope²),
so `χ₂=+1` — a coherent positive main term `W(0) = n² − O(n)`. This PROVES `Σ_b χ₂ T³ = i√p·(n²−O(n))`
(un-normalized channel) and explains `a₀`-genericity (flat `s=0` mode). **Still OPEN:** the PHASE-normalized
`|mean_QR| ≥ c` (the banked object) — gap reduced to a concrete `|T(a₀,b)|`-near-0 tail estimate.

## Update 2026-08-17 (4) — big family-amplitude sweep (p to ~370, + j=1728)

`|mean_QR|` by family (numpy sweep, prime order, both p mod 4 classes):

| family | full prime-order group | prime-order subgroup (q~50–130) |
|---|---|---|
| CM `j=0` | **0.295** (σ 0.065, n=8) | 0.192 |
| non-CM | **0.309** (σ 0.056, n=8) | 0.183 |
| `j=1728` | **impossible** — `y²=x³+Ax` has 2-torsion `(0,0)` ⇒ #E always even | 0.111 |

- **CM ≈ non-CM ≈ 0.30 in the full group — universal, no hierarchy.** Confirmed at scale.
- **j=1728 has no prime-order full group** (forced 2-torsion); only a subgroup probe exists. But the subgroup
  itself lowers ALL families (CM/non-CM drop 0.30→~0.18), so j=1728's 0.11 vs the subgroup baseline ~0.18 is
  a residual `~1.5σ` (n=6) dip — SUGGESTIVE, NOT established.
- **Tightness:** σ≈0.06 across mixed curves/primes; the σ≈0.028 "invariant" holds only for a single fixed
  curve at large p (~0.03), not across a family.

## Update 2026-08-17 (2) — a NEW valid control passed, and a false control claim caught

- **✅ Coordinate multiplicative-scramble control `x_d → x_dᵏ` (odd k, gcd(k,p−1)=1): channel PASSES.**
  Reproduced: CM p=547 `R_orig=−0.387 → R_x_ctrl=+0.001`; non-CM p=181 `0.595 → 0.176` (both near/at the
  parity floor). This is a genuine control (NOT the degenerate `b→bᵏ`): scrambling the coordinates through
  the field's multiplicative structure while breaking the additive group law kills the channel. Ergo the
  channel requires the **real Weierstrass group-law coordinates**, not generic field multiplicativity.
  Strengthens the finding.
- **❌ Scalar-side control claim (`d→αd`, `a₀=2`) is FALSE by the source's own data.** The report's prose
  says `a₀=2` drops R to the noise floor and that the lock is "restricted to GLV eigenvalues {1,λ,λ²}".
  Its own table (reproduced) shows `R_d_ctrl(a₀=2) ≈ R_orig`: CM 547 `−0.410 vs −0.387`, non-CM 181
  `0.591 vs 0.595`. The channel **survives** `a₀=2` — it is `a₀`-generic, NOT eigenvalue-restricted. Prose
  contradicts the numbers; the eigenvalue-restriction mechanism is refuted.

## Provenance (why this nearly got buried)
An earlier "powered null" (q=463, p≈0.88) was a **bug in my test**: I paired `x`-coordinates with
`e_n(a₀·idx)` using the point's index in an **x-sorted list**, not the discrete log `d`. Using the true
cyclic order `x_d = x([d]G)` makes the channel emerge (p≈0 on CM). Recorded as a suppression-bias miss
caught by the user. Reproduction: `scratchpad/k3_fixed.py`, `k3_parity_control.py`, `k3_map.py`.
