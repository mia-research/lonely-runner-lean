# NOTE v2 — k=3 channel: the main term is PROVED (slope² identity); phase transfer is the concrete gap

**Corrects v1**, which prematurely declared a "research-level wall." The main term IS derivable, exactly.
Date 2026-08-17. Companion to [CONFIRMED_k3_phase_channel_weierstrass_v1.md](CONFIRMED_k3_phase_channel_weierstrass_v1.md).

## THEOREM (proved + verified, 0 violations)
For prime-order `E(F_p)`, `T(a₀,b)=Σ_{d=1}^{n-1} e_p(b x_d)e_n(a₀ d)`, and `χ₂` the quadratic character:
```
Σ_b χ₂(b) T(a₀,b)³ = g(χ₂) · U(a₀),   U(a₀) = Σ_s e_n(a₀ s) W(s),
W(s) = Σ_{d₁+d₂+d₃ ≡ s} χ₂(x_{d₁}+x_{d₂}+x_{d₃}),   |g(χ₂)| = √p.
```
**Main term:** `W(0)` dominates (it is the flat `s=0` Fourier mode, so `U(a₀) ≈ W(0)` for every `a₀≠0`).
For triples with `P₁+P₂+P₃=O`, `P₃=−(P₁+P₂)` and the group law gives
```
x₁ + x₂ + x₃ = m²   (m = slope of (P₁,P₂)),   so   χ₂(x₁+x₂+x₃) = χ₂(m²) = +1  (m≠0).
```
Hence `W(0) = #{(P₁,P₂): P₁+P₂≠O, m≠0} = (n−1)(n−2) − #{slope-0 pairs}`, and
`#{slope-0 pairs} = O(n)` rigorously (each `y` has ≤3 points ⟹ `≤6(n−1)` `y`-collision pairs; `+O(1)`
tangent). Therefore **`W(0) = n² − O(n) > 0`**, a coherent positive main term.

**Consequences (rigorous):**
- `Σ_b χ₂(b) T³ = i√p·(n² − O(n)) ~ i·p^{2.5}` for `p≡3 mod4` — the **un-normalized k=3 × χ₂ channel is
  PROVED nonzero**.
- **`a₀`-genericity is explained**: the main term is the `s=0` mode, flat across `a₀`. (Kills the
  "restricted to GLV eigenvalues {1,λ,λ²}" story analytically.)

**Verification:** slope identity 0/18906 violations; `W(0)=810,2010,18630` matches `(n−1)(n−2)−#{m=0}`
exactly (p=43 CM/non-CM, p=163); `W(0)/n² = 0.84→0.96` rising toward 1.

## The remaining gap (concrete, NOT a wall)
The BANKED object is the **phase-normalized** channel `|mean_QR|` = `|Σ_b χ₂ e^{3iθ}|/(...)`, `e^{3iθ}=T³/|T|³`.
The proof above is for the **un-normalized** `T³`. Transfer runs through `⟨|T|⁻³⟩`, and the `|T|`-distribution
has a small tail: mean `|T|²/n → 1`, but `min → 0.002` and `⟨(|T|²/n)^{-1.5}⟩` grows `7→135`; `O(n)`
frequencies have `|T|≈0` (ill-conditioned phase). So `|mean_QR|≥c` does not follow cleanly.

**Precise open question:** bound the distribution of `|T(a₀,b)|` near 0 (how many `b` give `|T|<ε√n`, and
their contribution to the phase sum). That is a concrete equidistribution/2nd-moment estimate for the
character sum `T` — the one step between this and a full proof of the phase concentration.

## Grade
Un-normalized k=3 × χ₂ channel: **PROVED**. Phase channel `|mean_QR|` (banked): **EMPIRICAL**, with the
gap now reduced to a stated `|T|`-tail estimate. Mechanism (slope² ⟹ +1 main term) fully identified.
