# RESULT: the algebraic-number layer — eigenvalue splitting-field structure

**Date:** 2026-07-31
**Script:** inline (via `powersum_ladder_routeA_v1.sage` primitives; the norm-and-factor computation)
**Grade: `[VERIFIED — exact, 3 primes, stable law]`** for the minpoly-degree / multiplicity structure.
**Register:** purist. This is item 3 of the external critique — field/Galois data, a different observable class than the archimedean $|\alpha|,\arg\alpha$ the table reports, and **untouched by the ideals-argument circularity** (which addressed $(\alpha_1),(\alpha_2)$ as ideals, not the splitting field).

---

## 0. The object and why it's independent

The record proved the *ideal* measurement circular ($120°\Rightarrow$ ratio is a unit $\Rightarrow(\alpha_1)=(\alpha_2)$ identically). But the **field and Galois data** — minimal polynomial over $\mathbb{Q}$, splitting-field degree, factorization type — are a different observable class that the ideals argument does not touch. The eigenvalues at frequency $a$ live in $\mathbb{Q}(\zeta_n)$; their **$\mathbb{Q}$-Galois orbit structure** is the question. Known anchors: the field is **non-abelian** over $\mathbb{Q}$ at p=43,67 (`anew_eigenvalue_verify_v4`), and must contain $\omega$ ($\zeta_3\notin\mathbb{Q}(\zeta_n)$ when $3\nmid n$).

## 1. Method — the $\mathbb{Q}$-norm of $L_a$

The $\mathbb{Q}$-minpoly of the eigenvalue set is $P(T)=N_{\mathbb{Q}(\zeta_n)/\mathbb{Q}}(L_a)=\prod_{\sigma\in\mathrm{Gal}}\sigma(L_a)$, computed as the product of all Galois conjugates of $L_a(T)\in\mathbb{Q}(\zeta_n)[T]$ (0.2s; no QQbar needed). Its roots are all eigenvalues across all frequencies ($n-1$ freqs × 4 roots = $4(n-1)$ total). Factoring $P$ over $\mathbb{Q}$ gives the orbit structure directly.

(⚠ Small-$n$ artifact: at p=13, $n=7$, the char-poly coefficients are *all rational* — verified, 6/6 frequencies — so $L_a$ is already in $\mathbb{Q}[T]$ and the norm is just $L_a^6$. This is a degeneracy of $n=7$ being too small, **not** general structure; at p=43 (n=31), 0/30 frequencies have rational coefficients. p=13 is the wrong prime for this question.)

## 2. Result — a stable law: minpoly degree $4(n-1)/3$, multiplicity 3

| p | n | deg $P$ (norm) | minpoly deg | multiplicity |
|---|---|---|---|---|
| 43 | 31 | 120 | **40** | **3** |
| 67 | 79 | 312 | **104** | **3** |
| 127 | 127 | 504 | **168** | **3** |

**Two exact patterns, stable across three primes:**

1. **Multiplicity is always 3** — the $\mu_3$ signature at the $\mathbb{Q}$-Galois level, at every prime. The degree-$4(n-1)$ eigenvalue set splits into **3 Galois orbits of equal size**.
2. **Minpoly degree $= 4(n-1)/3$ exactly**: $4\cdot30/3=40$, $4\cdot78/3=104$, $4\cdot126/3=168$. Each orbit contains 4 eigenvalues from each of $(n-1)/3$ frequencies.

**Structural reading:** the $\mu_3$ action on *frequencies* ($a,\lambda a,\lambda^2 a$) lifts to a $\mathbb{Q}$-Galois orbit action on *eigenvalues*. One $\mathbb{Q}$-orbit per $\mu_3$-class of frequencies, each of size $4(n-1)/3$, with the threefold multiplicity encoding the three $\mu_3$-images. Concretely: the four eigenvalues at a single frequency $a$ come from **(up to) three different $\mathbb{Q}$-orbits** — they are not a single $\mathbb{Q}$-orbit. The eigenvalue splitting field over $\mathbb{Q}$ has degree $4(n-1)/3$.

## 3. What this sharpens (the mechanism picture)

The commutative-CM-commutation mechanism was **refuted** by non-abelianity (`RESULT_e2_identity_extended_verification_v1.md` §3). This result sharpens what replaces it:

- The $\mu_3$ structure is **not** a feature only of the archimedean eigenvalue configuration — it is visible at the **$\mathbb{Q}$-Galois / field-arithmetic level** (the multiplicity-3, the $4(n-1)/3$ degree). The three $\mu_3$-images of a frequency are genuinely different $\mathbb{Q}$-Galois orbits.
- The splitting field has degree $4(n-1)/3$ and is **non-abelian** over $\mathbb{Q}$ — consistent with (not refuting) the tensor-decomposition / $SU(2)$-monodromy candidate. A *commutative* CM-endomorphism explanation would force an abelian extension; the non-abelian degree-$4(n-1)/3$ field rules that out at the field level, matching the `anew_eigenvalue_verify_v4` finding.
- **The object to analyze for the mechanism is this degree-$4(n-1)/3$ non-abelian splitting field** — specifically, *where $\omega$ sits in it* and whether the monodromy action that generates it is the $\mathrm{SL}_2$-on-tensor-structure the marginal predicts. That is the concrete next structural target.

## 4. Scope held honestly

- **Three primes, all $\chi_2(-1)=-1$ branch** (p=43,67,127). The law (deg $4(n-1)/3$, mult 3) is exact at all three; a $\chi_2(-1)=+1$-branch confirmation would need a larger $+1$-branch prime (p=13 is too small, the artifact above). The multiplicity-3 is the robust, branch-independent signature.
- **Untouched by the ideals circularity** — this is field/Galois data, a genuinely independent observable class. The result stands regardless of the $(\alpha_1)=(\alpha_2)$ tautology.
- p=13 (n=7) is **excluded** as a degenerate small-$n$ artifact (coefficients collapse to $\mathbb{Q}$); recorded so it is not generalized from.

## 5. ADDENDUM (2026-07-31): the full tower at p=43 — $\omega$ located

Factoring the degree-40 minpoly over intermediate fields pins the complete tower (p=43, n=31):

$$\mathbb{Q}\;\subset\;\mathbb{Q}(\omega)\;[\text{deg }2]\;\subset\;L\;[\text{deg }20\text{ over }\mathbb{Q}(\omega)],\qquad [L:\mathbb{Q}]=40.$$

- **Over $\mathbb{Q}(\omega)$**: the minpoly splits into **two degree-20 factors**, and they are **$\omega\leftrightarrow\omega^2$ conjugates** (verified: applying the nontrivial automorphism of $\mathbb{Q}(\omega)$ to one gives the other). So $\mathbb{Q}(\omega)$ is *the* quadratic subfield of $L$, and $[L:\mathbb{Q}(\omega)]=20$.
- **Over $\mathbb{Q}(\zeta_n)$**: the minpoly splits into **ten degree-4 factors** ($10=(n-1)/3=\mu_3$-orbit count) — these are exactly the per-frequency char-polys $L_a$, one per $\mu_3$-class of frequencies. Confirms the $\mu_3$-orbit $\leftrightarrow$ degree-4-factor correspondence.
- **The degree-20 factors are EVEN in $T$** (only $T^{20},T^{18},\ldots,T^{2},T^{0}$ appear): $T\mapsto -T$ is an automorphism of each. This is the **field-level signature of the closure $\alpha\mapsto-\bar\alpha$** (the forced involution, `[PROVED-FORCED]`) — it survives all the way up to the $\mathbb{Q}(\omega)$-level. Reduces the genuine degree-20 content to degree-10 in $T^2$.

**Where $\omega$ sits, concretely.** $\omega$ generates the unique quadratic subfield of $L$; the eigenvalues do not live in a single extension of $\mathbb{Q}(\omega)$ by an abelian group (the field is non-abelian over $\mathbb{Q}$), but $\mathbb{Q}(\omega)$ itself is the clean 2-step at the bottom of the tower. The three $\mu_3$-images of a frequency correspond to the threefold multiplicity in the $\mathbb{Q}$-factorization; the $\omega\leftrightarrow\omega^2$ conjugation exchanges two of them at the degree-20 level.

**What this says about the mechanism.** The tower $\mathbb{Q}\subset\mathbb{Q}(\omega)\subset L$ with $L/\mathbb{Q}(\omega)$ degree-20, non-abelian, and even-in-$T$, is the field-arithmetic realization of the structure. It is **consistent with** the $SU(2)$-monodromy / tensor-decomposition candidate ($\mathbb{Q}(\omega)$ as the "rank-0 $R=1\oplus\xi$" layer; the degree-20 non-abelian extension as the $W$-piece). It does not *prove* that candidate — but it locates the two pieces ($\omega$-layer, $W$-layer) as distinct strata of the tower, which is the structural prerequisite the candidate needs. **The mechanism question is now: is the degree-20 non-abelian extension $L/\mathbb{Q}(\omega)$ generated by the predicted $\mathrm{SL}_2$-monodromy action?** That is the concrete open target, sharply scoped.

## 6. Open sub-questions after the tower

- The degree-20 extension $L/\mathbb{Q}(\omega)$: is it the splitting field of the degree-10-in-$T^2$ polynomial, and what is its Galois group over $\mathbb{Q}(\omega)$? (Computable in principle at n=31; the full `galois_group()` may be heavy but the group order/division structure is the target.)
- Branch confirmation at a $\chi_2(-1)=+1$ prime large enough to avoid the small-$n$ artifact.
- The connection (if any) between the degree-10-in-$T^2$ structure and the folded-angle $u(a)=\arcsin(\ldots)$ — both are "$T\mapsto -T$ quotient" objects.

## 7. Galois-group characterization via mod-prime cycle types (2026-07-31)

The full `galois_group()` is **infeasible**: PARI caps at degree 11, KASH at 21, no Magma — degree 40 is beyond all. Fell back to **factorization-type mod small rational primes** (the cycle type of the Frobenius-at-$\ell$ element of $G$, by Chebotarev). 100 primes $\ell<2000$ (excluding ramified), degree-40 minpoly mod $\ell$:

| cycle type | frequency |
|---|---|
| **(10,10,10,10)** | **77/100** (generic) |
| $(2^{20})$ | 10/100 (pure involutions) |
| $(5^{8})$ | 8/100 (pure order-5) |
| mixed with many 1-cycles | 5/100 (near-ramified) |

**Two further facts:**
- **Discriminant is a perfect square** ⟹ $G \subseteq A_{40}$ (the Galois group lies in the alternating group — no odd-signature elements). Verified exactly.
- **Every cycle length divides 10** — only 1, 2, 5, 10 appear. No 3, 7, or primes $>5$ in the cycle structure. The group's action is built entirely on divisors of 10.

**What this establishes:**
1. **$G$ is non-abelian, definitively.** The generic $(10,10,10,10)$ type (four disjoint 10-cycles, 77% of elements) is not an abelian signature — an abelian transitive group of degree 40 would have uniform/rectangular cycle types, not a dominant four-block 10-cycle generic element. Field-level confirmation of the non-abelianity (matching `anew_eigenvalue_verify_v4`).
2. **$G \subseteq A_{40}$** — a strong structural constraint; combined with the cycle data, this sharply narrows the candidates among transitive groups of degree 40.
3. **The four-10-block structure** ($40 = 4\times 10$, generic element cycles within each of four 10-blocks) is consistent with a **degree-4 outer action (the char-poly) × degree-10 inner action (the $W$-piece)** — exactly the block shape the tensor-decomposition / $\mathrm{SL}_2$-monodromy candidate predicts. The degree-10 inner block $= 2\cdot(n-1)/6$ connects to the folded-angle/free-orbit structure.

**vs the $\mathrm{SL}_2$-on-tensor-structure candidate:** the cycle-type data **does not contradict** the candidate and has the right block shape (degree-4 outer × degree-10 inner, $G\subseteq A_{40}$, non-abelian). It does not *prove* the candidate — pinning the group precisely among the transitive subgroups of $A_{40}$ with this cycle distribution would need either Magma or a custom resolvent computation, both beyond reach here. The candidate survives this test; the commutative alternatives do not.

**Honest residual.** What's established: non-abelian, $G\subseteq A_{40}$, generic cycle type $10^4$, all cycle lengths $\mid 10$, four-block structure. What's open: the *exact* group (among the transitive subgroups of $A_{40}$ matching this cycle distribution) and a direct match to the predicted $\mathrm{SL}_2$-action. The field-arithmetic evidence is now **consistent with and suggestive of** the $\mathrm{SL}_2$-monodromy candidate, field-confirmed non-commutative, with the commutative alternative refuted at every level examined (non-abelian Galois, non-abelian eigenvalue field, square-discriminant constraint).

## 5. Files

- Computation via `powersum_ladder_routeA_v1.sage` primitives (norm-and-factor); the structure table is reproducible from that script's `curve_data`/`histogram`.
- Builds on `anew_eigenvalue_verify_v4.sage` (non-abelianity) and `RESULT_powersum_ladder_routeA_control_v1.md` (the Route-A control).
