# RESULT: the degree-10 W-piece cross-check at p=61 (+1 branch) — the W-piece is branch-dependent

**Date:** 2026-08-01
**Script:** `algebraic_galois_degree10_p61_v1.sage` (reuses the construction + census of `algebraic_galois_degree10_v1.sage`).
**Grade:** `[VERIFIED — exact gate-by-gate construction at one cross-branch prime; control reproduces the published 10T14 identification]`.
**Register:** purist. Item B of the 2026-08-01 plan; the open cross-check named in `RESULT_algebraic_galois_degree10_v1.md` §6 and `RESULT_algebraic_branch_confirmation_v1.md` §3.

---

## 0. What was open

The degree-10 W-piece Galois-group identification (`RESULT_algebraic_galois_degree10_v1.md`: $\mathrm{Gal}(g/\mathbb{Q}(\omega))\cong 10T14$, $|G|=160$, solvable, not in $A_{10}$) was **single-prime**: at $p=43$ ($-1$ branch) the degree-$(n-1)/3=10$ object is in identifiable range; at $p=67/127$ the analogous object has degree 26/42 (out of range). The coincidence: at $p=61$ ($+1$ branch, $\chi_2(-1)=+1$), the minpoly degree is $4(n-1)/6=40$, so a *degree-40 squarefree object* feeds the same pipeline — a candidate second witness. The question was whether the $+1$-branch degree-10 object is the same kind of object, i.e. whether the W-piece structure survives the branch change.

## 1. Control — p=43 (−1 branch) reproduces 10T14 exactly

Re-running the full construction at $p=43$ validates the machinery against the published result:

| step | value | gate |
|---|---|---|
| $\deg P=N_{\mathbb{Q}(\zeta_{31})/\mathbb{Q}}(L)$ | 120 $=4(n-1)$ | ✓ |
| $\deg\mathrm{rad}(P)$ over $\mathbb{Q}(\omega)$ | 40 $=4(n-1)/3$ | ✓ |
| $\mathbb{Q}(\omega)$-factorization | 2 conjugate degree-20 factors, $\tau(f_+)=f_-$ | ✓ |
| evenness $f_+(-T)=f_+(T)$ | **holds** | ✓ |
| $g(S)=f_+(\sqrt S)$ | degree 10, irreducible over $\mathbb{Q}(\omega)$ | ✓ |
| Chebotarev census (790 embeddings / 400 split primes) | all 8 cycle types match | ✓ |
| transitive match | **tn=14, $|G|=160$, $C_2\times((C_2)^4\rtimes C_5)$** | ✓ |

Control reproduces the published identification in every particular. The pipeline is sound.

## 2. Cross-check — p=61 (+1 branch): G1 passes, G2 fails

| step | value | outcome |
|---|---|---|
| $\deg P=N_{\mathbb{Q}(\zeta_{61})/\mathbb{Q}}(L)$ | 240 $=4(n-1)$ | ✓ |
| $\deg\mathrm{rad}(P)$ over $\mathbb{Q}(\omega)$ | 40 $=4(n-1)/6$ | ✓ (squarefree part of the mult-6 minpoly) |
| **G1:** $\mathbb{Q}(\omega)$-factorization into 2 conjugate factors | 2 conjugate degree-20 factors, $\tau(f_+)=f_-$ | **PASS** |
| **G2:** evenness $f_+(-T)=f_+(T)$ | **all odd powers of $T$ nonzero** (indices $1,3,5,\ldots,19$) | **FAIL** |
| G3: $T^2$-reduction | not reached (the quotient $f_+(\sqrt S)$ is ill-defined when $f_+$ has odd powers) | — |

The $+1$-branch $\mathbb{Q}(\omega)$-factor is a full degree-20 polynomial in $T$ (both parities present). The W-piece quotient by $\alpha\mapsto-\alpha$ — equivalently the $T^2$-reduction that *defines* $g(S)$ — has no meaning here. **There is no $+1$-branch degree-10 W-piece object of the same kind as at $p=43$.** The 10T14 census therefore does not run (it is gated on degree 10, and the reduction that would produce degree 10 fails).

## 3. The mechanism — why the W-piece is branch-dependent

The evenness in $T$ (G2) at $p=43$ comes from the eigenvalue closure in the $-1$ branch. With $\varepsilon=\chi_2(-1)=-1$ ($p\equiv3\bmod4$), the eigenvalues pair under $\alpha\mapsto-\bar\alpha$, giving the spectrum $\{\alpha,\zeta_3\alpha,-\bar\alpha,-\zeta_3\bar\alpha\}$; the $\alpha\leftrightarrow-\alpha$ involution forces $f_+$ to be a polynomial in $T^2$ (roots paired as $\pm$), hence even-in-$T$.

In the $+1$ branch ($\varepsilon=+1$, $p\equiv1\bmod4$) the closure is $\alpha\mapsto\bar\alpha$ (the $e_3=\varepsilon p\,e_1$ sign flips, $e_3=+p\,e_1$). There is no $\alpha\leftrightarrow-\alpha$ pairing of the roots; the spectrum is $\{\alpha,\zeta_3\alpha,\bar\alpha,\zeta_3\bar\alpha\}$. The quotient by the involution $\alpha\mapsto-\alpha$ — the construction that defines the W-piece — does not correspond to a symmetry of the $+1$-branch spectrum. This is consistent with the branch-dependence already established at the minpoly level (`RESULT_algebraic_branch_confirmation_v1.md`: mult 3 vs mult 6, finer orbit decomposition in the $+1$ branch): the $+1$ branch has the extra $d\mapsto-d$ symmetry at the *orbit* level, but the $T^2$-quotient that produces the W-piece lives at the *eigenvalue* level, where the $-1$ branch's $\alpha\mapsto-\bar\alpha$ closure is required.

## 4. What this closes, and the honest scope

- **Closes the open cross-check:** the $+1$ branch at $p=61$ does **not** provide a second witness for the 10T14 identification. The W-piece (the $T^2$-quotient by $\alpha\mapsto-\alpha$) is a feature of the $-1$ branch ($p\equiv3\bmod4$, the secp256k1 branch) specifically; it does not generalize across branches.
- **This is a measured structural fact, not a closure of the mechanism question** (counter-prior). What it says precisely: the W-piece quotient and its 10T14 group are $-1$-branch objects. It does **not** say there is no $+1$-branch analogue — only that it is not the same quotient. (A $+1$-branch degree-10 object, if one exists, would come from a different reduction; that is not pursued here.)
- **Single cross-prime.** The verdict is at $p=61$ only. A second $+1$-branch prime with $(n-1)/6\in\text{range}$ would corroborate, but $p=61$ is the unique such prime where the degree-40 radical is in range; the next would give degree 26+. The G2 failure is structural (parity of the eigenvalue closure), so it is expected to hold at every $+1$-branch prime, but this is inference from the mechanism, not a sweep.
- **Arithmetic vs geometric.** This concerns the *arithmetic* Galois group $\mathrm{Gal}(g/\mathbb{Q}(\omega))$ (a $-1$-branch object). It does not touch the *geometric* monodromy conjecture ($\mathrm{SL}_2$, verified $SU(2)$ on traces) — a different object, verified across both branches at the connected-component trace level.

## 5. Files

- `algebraic_galois_degree10_p61_v1.sage` — the gate-by-gate driver; `load()`s `algebraic_galois_degree10_v1.sage` for the construction + census.
- `RESULT_algebraic_galois_degree10_p61_v1.json` — raw output (`p43_control` reproduces 10T14; `p61_crosscheck` records the G2 failure and the nonzero odd-power indices).
