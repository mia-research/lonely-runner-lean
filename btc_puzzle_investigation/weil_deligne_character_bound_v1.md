# A Weil–Deligne derivation of the single-sum character bound (the "unconditional Part V" input)

**Date 2026-07-19.** Goal: derive the bound on `U(a,b,c) = Σ_{d∈ℤ/n} e_p(b x_d + c y_d) e_n(a d)`
(and its χ₂-analogue) **directly from Grothendieck–Lefschetz + Grothendieck–Ogg–Shafarevich +
Deligne's Weil II**, rather than citing Kohel–Shparlinski (KS) as a black box. This is the input
that `bilinear_closure_proof_v1.md` (Theorem B) multiplies three times; the master lists an
"unconditional Part V (needs Weil–Deligne + KS reproved)" as a `[GAP]` and flags KS's scope limit
(additive ψ only, NOT χ₂, §XI.10). This document addresses both.

**Exact-language contract (self-imposed, per the session's audit).** Every deep input is **[CITED]**
by name; steps done here are **[PROVED-here]** (elementary, from the cited inputs); numeric
confirmations are **[VERIFIED]**. Predictions are committed in §7 **before** the numerical run
(`weil_deligne_bound_verify_v1.py`), so the derivation is the pre-registration. No claim that ECDLP
is hard; no claim beyond bounded-degree readouts; no claim to eliminate Weil II.

---

## 1. The object as a twisted character sum over `E(F_p)`

`E: y²=x³+7 / F_p`, `#E(F_p)=n` prime, `G` a generator, `d ↦ P_d=[d]G` the bijection `ℤ/n ↔ E(F_p)`.
The map `d ↦ e_n(a d)` is a **character `χ_a` of the finite group `E(F_p)`** (via `d ↔ P_d`). With
`ψ = e_p` (a nontrivial additive character of `F_p`) and `f = b x + c y` (a rational function on `E`):

> `U(a,b,c) = Σ_{P∈E(F_p)} ψ(f(P)) · χ_a(P)`,  the `d=0` (P=O) term handled separately (|·|≤1, a pole of f).

## 2. The two sheaves `[CITED]`

- **Lang-torsor sheaf `L_{χ_a}`.** By **Lang's theorem** the isogeny `𝓛 = Frob_p − 1 : E → E` is a
  connected finite **étale** Galois cover with group `E(F_p)`. A character `χ_a` of `E(F_p)` gives a
  rank-1 lisse `Q̄_ℓ`-sheaf `L_{χ_a}` on `E`, **lisse and tame (unramified) everywhere on `E`,
  including at `O`** (étale ⇒ no ramification), pointwise pure of weight 0. *(Lang 1956; Katz,
  GKM §4 / "Sommes exponentielles".)*
- **Artin–Schreier sheaf `L_ψ(f) = f* L_ψ`.** Rank-1 lisse on `U₀ = E ∖ {poles of f}`, pure weight 0.
  At a pole `x` of `f` of order `m` with `p ∤ m`, it is **wildly ramified with `Swan_x = m`**. For
  `f = bx+cy` the only pole is `O`, of order `ord_O(f) = 3` if `c≠0`, `2` if `c=0` (uniformizer
  `t=x/y` at `O`: `x∼t^{-2}`, `y∼t^{-3}`); `p>3 ⇒ p∤{2,3}`. *(Standard; Katz.)*

Set `F = L_ψ(f) ⊗ L_{χ_a}`, rank 1, lisse on `U₀ = E∖{O}`, pure weight 0, with
`Swan_O(F) = Swan_O(L_ψ(f)) = ord_O(f)` (tensoring by the tame `L_{χ_a}` does not change Swan).

## 3. Grothendieck–Lefschetz `[CITED]`

`Σ_{P∈U₀(F_p)} ψ(f(P))χ_a(P) = Σ_{i=0}^{2} (−1)^i Tr(Frob_p ∣ H^i_c(U₀⊗F̄_p, F))`. *(Grothendieck
trace formula.)* Then `U(a,b,c) = [this] + (O-term, |·|≤1)`.

## 4. Vanishing of `H^0_c` and `H^2_c` `[PROVED-here]`

- `H^0_c(U₀,F)=0`: `U₀` is a smooth **affine** (open, connected) curve and `F` is lisse nonzero; a
  section with compact support would be supported on a proper closed subset, impossible for a lisse
  sheaf on a connected non-proper curve.
- `H^2_c(U₀,F)=0` **iff `F` is geometrically nontrivial** (Poincaré duality: `H^2_c ≅ (F_{π₁^{geom}})(−1)`,
  the geometric coinvariants). For `f` nonconstant, `F` is **wildly ramified at `O`** (Swan `= ord_O(f) ≥ 2 > 0`)
  ⇒ geometrically nontrivial ⇒ `H^2_c=0`. *(The pure-character degenerate case `f≡0`, `a≠0`, is §6.)*

So for `f` nonconstant: `Σ_{P∈U₀(F_p)} ψ(f)χ_a = − Tr(Frob ∣ H^1_c(U₀,F))`.

## 5. The sharp constant via Grothendieck–Ogg–Shafarevich `[CITED formula, PROVED-here arithmetic]`

Euler–Poincaré: `χ_c(U₀,F) = rank(F)·χ_c(U₀) − Σ_{x∈E∖U₀} Swan_x(F)`, with
`χ_c(U₀) = χ_c(E) − #(E∖U₀) = (2−2g) − 1 = −1` (`g=1`, one pole). Hence

> `χ_c(U₀,F) = 1·(−1) − ord_O(f) = −(1 + ord_O(f))`,  so `dim H^1_c = 1 + ord_O(f)`.

- `c≠0`: `dim H^1_c = 1+3 = 4`. `c=0, b≠0`: `dim H^1_c = 1+2 = 3`.

The **`+1` is the genus-1 fingerprint** (`χ_c(U₀)=2−2g−1=−1`); a genus-0 base would give `Swan−1`.
This constant **coincides with KS Thm 1's refined bound** (`m₁ = pole+1 = 4`) — it is **not sharper
than KS**; it is the same sharp constant obtained without citing KS.

## 6. Deligne's Weil II + the degeneracy classification `[CITED + PROVED-here]`

`F` is pure of weight 0, so `H^1_c(U₀,F)` has weights `≤ 1` and every Frobenius eigenvalue satisfies
`|α| ≤ p^{1/2}` **[CITED: Deligne, Weil II, 1980]**. Therefore
`|Σ_{U₀(F_p)} ψ(f)χ_a| ≤ dim H^1_c · √p`, giving:

> **`|U(a,b,c)| ≤ (1 + ord_O(bx+cy))·√p + 1`**  `= 4√p+1` (`c≠0`) or `3√p+1` (`c=0`), **all p**, uniform in `(a,b,c)`.

**Degeneracy — the only exceptions `[PROVED-here]`:** the bound's hypotheses fail only if `F` is
geometrically trivial, i.e. `f` constant AND `χ_a` "trivial as a sheaf". Cases:
- `(b,c)=(0,0), a≠0`: `U = Σ_d e_n(ad) = 0` (complete character sum). *(Cohomology: `L_{χ_a}` tame
  everywhere on complete `E`, `χ_c(E,L_{χ_a}) = 1·(2−2g) = 0`, `H^0=H^2=0` for `a≠0` ⇒ `H^1=0` ⇒ sum `=0`.)*
- `a=b=c=0`: `U = n` (trivial). All other `(a,b,c)` are covered by §5–6. **No exceptional `(b,c)` escapes.**

## 6′. The χ₂ extension — beyond KS `[PROVED-here from the same machinery]`

KS's `ψ` is **additive** (Artin–Schreier); it does not bound multiplicative-character readouts
(§XI.10). The cohomological method covers them with **no new idea** — only a **Kummer** sheaf in
place of Artin–Schreier. For a multiplicative character `χ` of `F_p*` (e.g. `χ₂`=Legendre) and a
function `g` on `E`:

`V(a; χ, g) = Σ_{P∈E(F_p)} χ(g(P)) · χ_a(P) = − Tr(Frob ∣ H^1_c(U_g, L_χ(g) ⊗ L_{χ_a}))`,

where `L_χ(g)` is the **Kummer sheaf**: rank 1, **tame** (Swan `=0`), ramified exactly at the points
where `ord(g)` is **not ≡ 0 mod ord(χ)** — for `χ₂`, the points of **odd** order of `g`. Let
`R = {odd-order zeros/poles of g}` (geometric, over `F̄_p`). Then (tame ⇒ Swan `=0`):

> `χ_c(U_g, L_χ(g)⊗L_{χ_a}) = 1·(2−2g − #R) − 0 = −#R`, so **`|V(a;χ₂,g)| ≤ #R · √p`**, all `p`.

- `g = x`: divisor `= (0,+√7)+(0,−√7) − 2·(O)`; odd-order points `= (0,±√7)` (the pole at `O` has
  even order 2, `χ₂` unramified there) ⇒ `#R = 2` ⇒ **`|Σ_P χ₂(x_P) e_n(ad)| ≤ 2√p`**.
- `g = y`: divisor `= (r₁)+(r₂)+(r₃) − 3·(O)` where `rᵢ` are the 2-torsion points (`y=0`, `x³=−7`);
  all four points have odd order (1,1,1 and pole 3) ⇒ `#R = 4` ⇒ **`|Σ_P χ₂(y_P) e_n(ad)| ≤ 4√p`**.

This **closes the §XI.10 scope gap**: the χ₂-twisted single-coordinate sums are `O(√p)` by Weil–Deligne,
with an explicit cohomological constant `#R`, replacing the separate `‖F‖_A` argument the master
relied on for χ₂.

## 7. COMMITTED numerical predictions (pre-registration — verified in `weil_deligne_bound_verify_v1.py`)

Falsification: if any measured `max/√p` over nontrivial twists **exceeds** the committed constant
(beyond the `+1/√p` O-term and float noise), a step above is wrong and must be found. Both directions
are decidable.

| sum, over all `a≠0` and the stated coordinate twist | committed bound `max/√p ≤` | sharp? |
|---|---|---|
| additive `U(a,b,c)`, `c≠0` (`f=bx+cy`) | **4** (+1/√p) | expect max → ~4 |
| additive `U(a,b,0)` = `T(a,b)`, `c=0` (`f=bx`) | **3** (+1/√p) | expect `c=0 ≤ 3 < 4`; y strictly adds |
| χ₂ single-x: `Σ_P χ₂(x_P) e_n(ad)` | **2** | Kummer, tame |
| χ₂ single-y: `Σ_P χ₂(y_P) e_n(ad)` | **4** | Kummer, tame |
| degenerate `(b,c)=(0,0), a≠0` | **0** exactly | complete char sum |

## 8. SCOPE — what this does and does NOT establish (no overclaim)

**Does:** (i) derives the single-sum bound `|U|≤(1+pole)√p+1` from **Weil II** (a proved, foundational
theorem) via an explicit `H^1_c`-dimension count — the "unconditional Part V input", no longer resting
on *citing* KS; (ii) gives the **sharp** constant (`= 1+pole`, matching KS Thm 1, NOT sharper);
(iii) **extends to χ₂** (Kummer), which KS does not cover — closing §XI.10; (iv) holds for **all `p`,
including `2²⁵⁶`** (it is an identity-level bound, not a small-`p` measurement); (v) classifies the
degeneracies exactly (only `(a,b,c)=0`).

**Does NOT:** (a) eliminate **Deligne's Weil II** — that is the irreducible cited input (no one
reproves Weil II; "unconditional" means "resting on Weil II, not on KS's packaging"); (b) close the
**unbounded-degree** residual — the constant is `1+ord_O(f)` (additive) / `#R` (χ₂), which **grows
with the readout's pole/ramification degree**, so a readout of degree `≳ √p` has a vacuous bound (the
`k ≳ p^{1/4}` / unbounded-degree GAP from the C/F/E audit is untouched); (c) say anything about ECDLP
hardness — it bounds a **class of readouts** (bounded-degree, single-coordinate, one group-character
twist), exactly the class Theorem B multiplies. The `m=1` aligned readout (the DLP) is outside it.

**Deeper structure flagged (not claimed):** the eigenvalues of `Frob` on `H^1_c` are Weil numbers of
absolute value `√p`; their distribution under the `μ₆`/CM action on `H^1_c` (the GLM "μ₆ on H¹_ét"
idea) and the Kummer/`χ₂` ramification's link to the `FLD = ±6h(−p)` class-number thread (Part VIII)
are the two structural directions this framework opens. Both are OPEN; neither is asserted here.

---

## 9. VERIFICATION OUTCOME `[VERIFIED — weil_deligne_bound_verify_v1.py, 2026-07-19]`

Every §7 committed prediction holds; **no measured `max/√p` exceeds its cohomological constant.**

| twist | committed | measured `max/√p` (p range) | reading |
|---|---|---|---|
| additive, `c≠0` | ≤ 4 | 3.23 → 3.54 (p=61→433) | ≤4, climbing to the `dim H¹_c=4` ceiling |
| additive, `c=0` | ≤ 3 | 2.43 → 2.79 | ≤3, **strictly below `c≠0` every p** ⇒ y adds a channel (Swan 2→3, dim 3→4) |
| `χ₂(x)` | ≤ 2 | 1.64 → 2.00 (p≤2089) | ≤2, **saturates** the Kummer `#R=2` bound |
| `χ₂(y)` | ≤ 4 | 1.73 → 2.00 | ≤4, well under bound |
| degenerate `(0,0)` | = 0 | 2e-14, 6e-14 | complete character sum vanishes |

**One honest refinement (a magnitude below its bound, flagged not claimed):** `χ₂(y)` sits at
`≈2√p`, not its `≤4√p` ceiling. The cohomological bound (`dim H¹_c = #R = 4`) is an **upper** bound
and is correct; the gap to `≈2` is real extra structure — most likely the **y-parity** splitting
(`y_{−d}=−y_d` ⇒ `χ₂(y_{−d}) = χ₂(−1)χ₂(y_d)`), which halves the effective sum into d-even/odd blocks
so only `~2` of the 4 eigenvalues carry weight-1 mass. This is a *sharper* statement than the bound
and a candidate next probe (does the `H¹_c(χ₂(y))` Frobenius spectrum split 2+2 under `[−1]`?), **not**
a closure. Consistent with the negative-bias rule: the `≈2√p` is a bounded magnitude living in a
`[−1]`-isotypic subspace, not "nothing".

**Net:** the single-sum bound feeding `bilinear_closure_proof_v1.md` (Theorem B) is now derived from
**Weil II** (foundational, proved) rather than resting on *citing* KS, with the **same sharp constant**
(4), **extended to χ₂** (Kummer, verified) which KS did not cover (§XI.10), and it holds at **all p
including 2²⁵⁶** for bounded-degree readouts. The `[GAP]` narrows to: (a) **Weil II itself** (cited,
uneliminable) and (b) **unbounded/growing-degree readouts** (constant `= 1+ord_O(f)` / `#R` grows with
degree — untouched, = the audit's `k≳p^{1/4}` residual). No ECDLP-hardness claim.
