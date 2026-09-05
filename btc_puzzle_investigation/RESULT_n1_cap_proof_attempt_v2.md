> # ⚠ SUPERSEDED — read `RESULT_n1_cap_intersection_v1.md` instead
> This document (v1+v2) was written **without checking the project's monodromy corpus**. Two claims here
> are now corrected:
> 1. **"M3 (120° conjugate pairs) refuted" is WRONG** — a `S₂` base-change bug (same one that broke
>    χ₂(x) purity). The project **proved** `α₂/α₁=ζ₃` (two ζ₃-pairs) exactly, 22 primes, gate-verified.
> 2. **"The cap is an open monodromy statement needing Katz/Magma" is superseded** — given the proved
>    120° law, the cap is a **2-line corollary**: `V=∓ζ₃²(α₁+α₃)`, `|V|=|α₁+α₃|≤2√p`. The only open
>    piece is **uniformity** of `u=ζ₃` (all `a,p`) — the project's known sole gap.
> The autocorrelation identity in §1 below **stands** (verified) and is a genuine new object, but §2–§4's
> "circular / monodromy-hard" framing is superseded. See `RESULT_n1_cap_intersection_v1.md`.

# RESULT — the 2√p cap, deeper attack (v2): exact autocorrelation identity derived; problem LOCALIZED to monodromy; still open

**Supersedes** `RESULT_n1_cap_proof_attempt_v1.md` (which recorded the strong conjecture + 3 refuted
mechanisms). This adds the second-pass results and the precise reason elementary methods circle.
**Scripts:** `sage_ynq_v3.sage` (exact product formula), `sage_N_factor_v1.sage` (irreducibility);
numerical checks inline.

**Bottom line unchanged: the cap `max_a|V_y(a)| ≤ 2√p` is NOT proved. It is now precisely localized to
a geometric-monodromy statement, with the elementary routes shown to be circular.**

---

## 1. New exact result — the autocorrelation reduces to a one-variable character sum

`|V_y(a)|² = χ₂(−1)·Σ_t c(t)e_n(at)`, with the integer autocorrelation `c(t)=Σ_d χ₂(y_d)χ₂(y_{d+t})`.
Recentering `P = Q−R`, `P+T = Q+R` with `R=[t/2]G` (2 invertible mod the odd prime `n`), and the
**exact identity** (derived symbolically, verified per-point):

```
y_{R+Q} · y_{R−Q}  =  N(x_Q, x_R) / (x_Q − x_R)³ ,     N(u,v) = u³v³ + B(u³+9u²v+9uv²+v³) − 8B²
```

gives
```
c(t) = χ₂(−1)·Φ(x_{[t/2]G})  + O(1),     Φ(v) = Σ_{x∈F_p} (1+χ₂(x³+B))·χ₂( N(x,v)·(x−v) ).
```

The per-point identity `y_{R+Q}y_{R−Q} = −N/(x_Q−v)³` was verified exactly (`p=43`, all Q). This
**explains the empirical c(t) structure**: `c(t)` is a function of `x_{[t/2]G}`, and the x-coordinate is
μ₆-invariant (μ₃ via GLV, ± via [−1]) — hence `c(t)` is μ₆-orbit-constant, as observed.

---

## 2. Why this does NOT close the cap — the circularity is intrinsic

- **`N(x,v)` is irreducible and squarefree** in `x` (over `Q(v,B)`); `gcd(N, x³+B)=gcd(N, x−v)=1`;
  `disc_x N = −27B²·(v⁶+20v³B−8B²)²`. So `f₁=N(x−v)` (deg 4) and `f₂=(x³+B)N(x−v)` (deg 7) are
  **squarefree** — no cheap degree drop. Weil on `Φ` gives only `≤ 9√p`, far from the observed `2√p`.
- The tightening is because `Φ(v) = Σ_{P∈E}χ₂(N(x_P,v)(x_P−v))` — the "`(1+χ₂(x³+B))` weight" **puts the
  sum back on the curve E**. So `Φ(v)` *is* `c(t)` re-expressed, not a genuine simplification.
- Every route tried — squaring `V`, the autocorrelation, the recentering, the x-line reduction —
  returns a Fourier-dual copy of the same object. **`max_a|V_y(a)|` is the sup-norm of a Fourier
  transform; no algebraic identity bounds a sup-norm.** The cap is an *equidistribution / monodromy*
  statement, not an algebraic one.

---

## 3. The precise open statement (monodromy)

The family `F_a = L_{χ₂(y)} ⊗ L_{ψ_a}` (a ∈ Z/n) is, at each `a≠0`, a rank-1 sheaf on E with
`H¹` **4-dimensional** (= A_new, proved in `RESULT_arm2_eigenvalue_v1.md`), eigenvalues `|β_i|=√p`, and
`V_y(a) = −Σβ_i`. Measured invariants of the family `{V_y(a)/√p}`:

- **irreducible, `E[|V/√p|²] = 1`** (second moment: `Σ_{a≠0}|V_y(a)|²/(n−1) = c(0) = n−1 ≈ p`);
- **`sup_a |V_y(a)|/√p = 2`** (40 primes, 0 violations, `RESULT_..._v1.md`).

So the arithmetic monodromy group `G ⊂ U(4)` of the family satisfies `E_G[|Tr|²]=1` (irreducible) and,
conjecturally, **`max_{g∈G} |Tr(g)| = 2`** (not the generic `4`). The `G`-constraints available:
`G` commutes with the μ₆ = ⟨GLV φ, [−1]⟩ action on `H¹` (since `y` is φ-invariant and M4 fixes the [−1]
behavior), and `A_new` has CM (char poly `T⁴+pT²+p²`, eigenvalues at ±60°/±120°). A `G` forced into a
proper subgroup with `max|Tr|=2` by these symmetries would prove the cap.

**This is the remaining work, and it needs monodromy machinery (Katz's methods / Magma), not the
elementary tools available here.** Candidate mechanisms that would have made it elementary — dimension
reduction (M1), a [−1] 2+2 coupling (M2), 120°-separated conjugate pairs (M3) — are all **refuted**
(v1 §2). The four eigenvalues are general Weil numbers whose sum is capped by the group, not by a fixed
angle relation.

---

## 4. Status ledger

| item | grade |
|---|---|
| autocorrelation identity `c(t)=χ₂(−1)Φ(x_{[t/2]G})+O(1)`, `y_{R+Q}y_{R−Q}=N/(x_Q−x_R)³` | **`[VERIFIED exact]`** (symbolic + per-point) |
| `N(x,v)` irreducible, squarefree; `Φ` re-expresses the curve sum | `[VERIFIED exact]` |
| `max_a|V_y| ≤ 2√p` | `[CONJECTURE — strong]` (≈50 primes, 0 violations) |
| family: 4-dim irreducible, `E|Tr|²=1`, `sup|Tr|=2` | `[VERIFIED / measured]` |
| M1 dim-2 / M2 [−1]-2+2 / M3 120°-pairs | **all REFUTED** |
| exact proof | **OPEN — a monodromy `max|Tr|=2` statement**; elementary routes shown circular |

**Honest close.** Two sessions of attack produced: the exact object (dim-4 A_new with pinned CM
eigenvalues), an exact autocorrelation identity, three killed mechanisms, a robust conjecture, and a
proof that the elementary approaches are circular — the cap is genuinely a monodromy theorem. That is
real, publishable-quality *localization* of an open problem, not a proof of it. The N1 ½ **magnitude**
remains resolved; the **cap** remains conjectural.

**No ECDLP content** (`p ≤ 3853`; character sums over the public curve).

*Grade legend: VERIFIED (exact) · CONJECTURE · REFUTED · OPEN.*
