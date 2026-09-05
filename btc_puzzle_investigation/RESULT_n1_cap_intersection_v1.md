# RESULT — the cap is a 2-line COROLLARY of the project's proved 120° law; my "120° refuted" was a base-change bug (v1, 2026-07-24)

**Context.** A separate two-session attack (`RESULT_n1_cap_proof_attempt_v1/v2.md`) reached the 2√p
cap from the **Fourier/autocorrelation** side and concluded "it's a geometric-monodromy statement,
needs Katz/Magma; three mechanisms refuted (incl. 120° conjugate pairs)." Checking against the
project's existing monodromy corpus shows that conclusion **converges with — and is superseded by —
the already-proved 120° law**, and that one of my "refutations" was a computational error.

---

## 1. The intersection

`RESULT_n1_120deg_exact_v1.md` **`[PROVED-exact]`** (22 primes, all cells, no-float multi-modular,
gate-verified, plant-validated): the statistic `g = deg gcd(L*(T), L*(ζ₃T)) = 2` at every cell, i.e.
the four Frobenius eigenvalues of `H¹_c(E, L_{χ₂(y)}⊗L_{χ_a})` form **two ζ₃-pairs** — `α₂/α₁ = ζ₃`.
`ANALYSIS_..._kronecker_route_v3.md §5` already records: *the cap `|V|≤2√p` needs purity + uniform
`u=ζ₃`.*

**My independent Fourier-side finding — that the cap is not algebraic but a sup-of-Fourier /
equidistribution statement about the monodromy — is the SAME conclusion**, reached from the dual
object. The two views meet exactly at: *the cap is governed by the monodromy relation `α₂/α₁=ζ₃`,
which the project has proved per-cell.*

---

## 2. The cap is a 2-line corollary of the 120° law + purity (explicit)

Given `g=2` (two ζ₃-pairs) and purity (`|αᵢ|=√p`, Deligne / control C-COEFF), write the spectrum
`{α₁, ζ₃α₁, α₃, ζ₃α₃}`. Then

```
V_y(a) = ± Σ αᵢ = ±(1+ζ₃)(α₁+α₃) = ∓ ζ₃²(α₁+α₃)  ⟹  |V_y(a)| = |α₁+α₃| ≤ |α₁|+|α₃| = 2√p.   ∎
```

(uses `1+ζ₃ = −ζ₃²`; the degenerate chain case `{α₁,ζ₃α₁,ζ₃²α₁,α₄}` gives `Σαᵢ = α₄`, `|V|=√p`,
even smaller). **No conjugation assumption, no `p mod 4` split, no "order-pinning" — the cap needs
NOTHING beyond `g=2` + purity.**

**Verified at p=13** (eigenvalues `√p·{e^{±i38°}, e^{±i158°}}`, ratio `e^{i120°}=ζ₃` exact):
`|α₁+α₃|/√p = 0.2783 = ` the measured `max|V_y|/√p = 0.277`, and `e₁ = −ζ₃²(α₁+α₃)` to machine
precision. The corollary is exact.

---

## 3. Retraction — my "M3 (120° conjugate pairs) REFUTED" was a base-change BUG

`RESULT_n1_cap_proof_attempt_v1.md §2` listed M3 ("eigenvalues = two 120°-separated conjugate pairs")
as **refuted**, because the predicted identity `m₁²+m₂ = 2p` "held at p=13 but failed at p≥43."

**That failure was a bug in my `S₂` base-change** — the *same* defect that made my `χ₂(x)` eigenvalue
moduli come out `1.34√p` instead of `√p` (`RESULT_arm2_eigenvalue_v1.md` never resolved it). The
project's **independent, gate-verified, no-float** computation (`C-COEFF`: all four eigenvalues
weight-1 `|α|=√p` to `2.2e-16`; `verify_e3_sign.sage`) proves the eigenvalue structure is exactly the
ζ₃-pair one. **M3 is NOT refuted — it is the correct, proved mechanism.** My m₁²+m₂ test was computing
`m₂` wrongly.

(M1 "dim-2" and M2 "[−1] couples to one 2-dim half" **stay refuted** — those were correct: χ₂(y) is
dim-4 and all four eigenvalues contribute. The right picture is dim-4 with the four eigenvalues in two
ζ₃-pairs, summing to `≤2√p` by the §2 algebra.)

---

## 4. What my Fourier-dual object adds — and what it does NOT

**New object (not in the eigenvalue-side corpus):** the exact autocorrelation identity
```
y_{R+Q}·y_{R−Q} = N(x_Q,x_R)/(x_Q−x_R)³ ,  N(u,v)=u³v³+B(u³+9u²v+9uv²+v³)−8B²    (symbolic, per-point verified)
⟹  c(t) = χ₂(−1)·Φ(x_{[t/2]G}) + O(1),   Φ(v)=Σ_x (1+χ₂(x³+B)) χ₂(N(x,v)(x−v)).
```
From it, **`Φ(βv)=Φ(v)` directly** (`N(βx,βv)=N(x,v)` since `β³=1`, `β` a square): the GLV μ₃ is
manifest on the autocorrelation.

**Honest assessment of whether it helps the open gap.** The sole remaining gap (`route_v3 §5`) is
**uniformity of `u=ζ₃` in `(a,p)`** — a *within-cell* ζ₃. The μ₃ my `Φ(βv)=Φ(v)` exhibits is the
**between-cell** ω-descent (`L*(a)=L*(λa)`), which the project already has and has shown **insufficient**
for the within-cell order-pinning. **So the autocorrelation view does NOT crack uniformity** — it
recovers the μ₃ the project already used, not the missing within-cell source. This is a scoped
negative, stated so it is not mistaken for a new lever.

---

## 5. Net — the corrected, converged picture

| item | status |
|---|---|
| 120° law `α₂/α₁=ζ₃` (two ζ₃-pairs) | **`[PROVED-exact]`, 22 primes** (project) |
| cap `\|V\|≤2√p` **per cell** | **`[PROVED]` corollary** of 120° + purity — explicit `\|V\|=\|α₁+α₃\|` (§2, this note) |
| my "cap is open monodromy, needs Katz/Magma" (v2) | **superseded** — the monodromy relation is *proved*; the cap is a corollary |
| my "M3 120° pairs refuted" (v1) | **RETRACTED** — base-change bug (§3) |
| cap **uniform** (all a,p) | **OPEN** — = uniformity of `u=ζ₃`, the project's sole structural gap |
| autocorrelation identity + `Φ(βv)=Φ(v)` | new exact object; gives only the *between-cell* μ₃, **does not** crack within-cell uniformity |

**Bottom line for the user's question.** The new (Fourier) insight **intersects the project's proved
120° law and collapses onto it**: the cap is not an open monodromy problem, it is a two-line corollary
of a result the project already proved per-cell, and the *only* thing missing is the exact same
uniformity gap the 120° law has. My autocorrelation object is genuinely new but, checked honestly,
supplies the between-cell μ₃ (already known), not the within-cell ζ₃ that uniformity needs. The
correct next step is unchanged from `route_v3 §5`: a uniform proof of `u=ζ₃` (all `a,p`), for which
the L-mono / `ℚ(ζ_n)^{⟨σ_λ⟩}` descent — not the autocorrelation — remains the live route.

**No ECDLP content.** `p ≤ 3853`; character sums over the public curve.
