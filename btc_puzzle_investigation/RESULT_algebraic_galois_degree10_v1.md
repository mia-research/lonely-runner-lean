# RESULT: Galois group of the degree-10-in-$T^2$ object

**Date:** 2026-08-01
**Script:** `algebraic_galois_degree10_v1.sage` (committed; reuses `build_L` from `anew_eigenvalue_identify_v3.sage` and `audit_n1_vsign_v2_core.py`).
**Grade:** `[VERIFIED — exact construction + cycle-type/Chebotarev identification, single prime]`. The transitive-group identification is a single-prime match; it is **not** a proven group identity across the family (impossible to cross-check by exact-group methods at $n>31$; see §4).
**Register:** purist. Item 1 of the 2026-08-01 handoff (`untested_threads`).

---

## 0. What was open, and what this closes

`RESULT_algebraic_number_layer_v1.md` §6 left two things un-computed: (i) the committed construction of the degree-10-in-$T^2$ object (the "W-piece" modulo the forced involution $\alpha\mapsto-\alpha$), and (ii) its Galois group over $\mathbb{Q}(\omega)$. The degree-40 norm, the $\mathbb{Q}(\omega)$-factorization, and the Frobenius cycle-type census reported in §5/§7 of that RESULT were performed inline and **not committed as a script**; this document commits all of it and extends it with the in-range group identification.

The reason the group is now reachable: at $n=31$ ($p=43$), the degree-$(n-1)/3$ object has degree **10**, within the range where (a) the 45 transitive groups are cataloged and (b) a cycle-type census uniquely identifies one. At $p=67$ the analogous object has degree 26, at $p=127$ degree 42 — both beyond exact-group routines (PARI `polgalois` caps at 11, `galoisinit` at 21, no KASH/Magma). So **$p=43$ is the unique prime where the exact-group identification lives.**

## 1. The construction (all correctness gates passed)

At $p=43$, $n=31$, $a=1$: build $L_1(T)\in\mathbb{Q}(\zeta_{31})[T]$ (degree 4) via `build_L`. Then:

| step | object | computed value | gate |
|---|---|---|---|
| Q-norm | $P=N_{\mathbb{Q}(\zeta_{31})/\mathbb{Q}}(L_1)$ | degree 120 $=4(n-1)$ | ✓ |
| radical over $\mathbb{Q}$ | $\mathrm{rad}(P)$ | degree 40 $=4(n-1)/3$ | ✓ (the minpoly; $P=\mathrm{rad}^3$) |
| factor over $\mathbb{Q}(\omega)$ | $f_+, f_-$ | two degree-20 factors | ✓ |
| conjugacy | $\tau(f_+)=f_-$, $\tau:\omega\mapsto\omega^2$ | verified | ✓ |
| evenness | $f_+(-T)=f_+(T)$ | only even powers $\{0,2,\ldots,20\}$ | ✓ |
| $T^2$-reduction | $g(S)=f_+(\sqrt{S})\in\mathbb{Q}(\omega)[S]$ | degree 10, **irreducible** | ✓ |
| absolute poly | $g_{\mathrm{abs}}=g\cdot\tau(g)\in\mathbb{Q}[S]$ | degree 20, irreducible | ✓ |

All checks exact (cyclotomic-field / $\mathbb{Q}$ arithmetic; no floats in the signal path). The tower committed to script matches `RESULT_algebraic_number_layer_v1.md` §5 in every particular and now has a saved witness (the script).

## 2. The degree-10 Galois group — identification by cycle-type census

`galois_group()` on the relative extension $\mathbb{Q}(\omega)[S]/(g)$ is **infeasible**: it requires KASH (not installed) for the degree-20 absolute splitting field — the same obstruction the degree-40 RESULT hit. Fell back to the **Chebotarev cycle-type census** of $g$ over $\mathbb{Q}(\omega)$: factor $g$ mod the two primes of $\mathbb{Q}(\omega)$ above each rational prime $\ell\equiv1\pmod3$ and read the Frob cycle type.

**Census:** 790 embeddings across 400 split primes $\ell\equiv1\pmod3$ (10 ramified/skipped). Distribution:

| cycle type | count | density |
|---|---|---|
| $(10)$ | 330 | 41.8% |
| $(5,5)$ | 308 | 39.0% |
| $(2,2,2,1,1,1,1)$ | 52 | 6.6% |
| $(2,2,1,1,1,1,1,1)$ | 36 | 4.6% |
| $(2,2,2,2,1,1)$ | 32 | 4.1% |
| $(2,1,1,1,1,1,1,1,1)$ | 24 | 3.0% |
| $(2,2,2,2,2)$ | 6 | 0.8% |
| $(1^{10})$ | 2 | 0.3% |

**Parity (from cycle types, $\mathrm{sign}=(-1)^{10-\#\text{cycles}}$):** even $0.478$, odd $0.522$. Hence $\mathrm{disc}(g)$ is **not** a square in $\mathbb{Q}(\omega)$, and $\mathrm{Gal}(g/\mathbb{Q}(\omega))\not\subseteq A_{10}$.

### Identification

Among the 45 transitive groups of degree 10, the criterion "every element order divides 10" + "10-cycles present" + "the full set of observed cycle types matches" selects **exactly one group**:

$$\boxed{\;\mathrm{Gal}(g/\mathbb{Q}(\omega))\;\cong\; \text{transitive group }10T14,\qquad |G|=160,\qquad G\cong C_2\times\big((C_2)^4\rtimes C_5\big).\;}$$

- $|G|=160$ (computed element orders: $\{1,2,5,10\}$, all $\mid 10$).
- Structure: $C_2\times((C_2\times C_2\times C_2\times C_2)\rtimes C_5)$ — **solvable** (`is_solvable=True`; derived series $[160,16,1]$).
- Predicted vs observed densities agree across **all 8 cycle types**, including the rare $(2^5)$ (predicted $0.6\%$, observed $0.8\%$) and $(1^{10})$ (predicted $0.6\%$, observed $0.3\%$).
- Half the elements are odd permutations of the 10 roots (consistent with the non-square discriminant above).

The group is the unique transitive degree-10 group matching the cycle signature; no other candidate survives the cycle-type-set test.

## 3. What this says about the mechanism — honest reading

The handoff / spine conjectured the $W$-piece carries an $\mathrm{SL}_2$-type monodromy, with the icosahedral family ($A_5\cong\mathrm{PSL}_2(\mathbb{F}_5)$ or $2.A_5\cong\mathrm{SL}_2(\mathbb{F}_5)$) as the concrete guess (element orders $\mid 10$, $G\subseteq A$, 10-cycles dominant). **This conjecture is not supported by the identification.** The degree-10 group is $10T14$, which is:

- **solvable** ($C_2\times((C_2)^4\rtimes C_5)$), hence **not** $A_5$ / $2.A_5$ / any $\mathrm{SL}_2(\mathbb{F}_5)$-type group (those are non-solvable, perfect);
- **not contained in $A_{10}$**, whereas the icosahedral degree-10 action on 2-subsets is.

What survives from the structural picture:
- The cycle lengths still all divide 10 (the "$W$-piece on the $T^2$-quotient" qualitative shape survives).
- The non-commutativity survives ($10T14$ is non-abelian).
- The four-block $40=4\times10$ structure of the degree-40 census remains consistent with a degree-4 outer action times this degree-10 inner action.

What is **refuted** by this measurement: the *specific* $\mathrm{SL}_2(\mathbb{F}_5)$ / icosahedral identification of the $W$-piece's Galois group. Per the counter-prior, this is a measured refutation of one candidate, not a closure of the mechanism question — the $\mathrm{SL}_2$-monodromy conjecture lives at the level of the *geometric* monodromy group $G_{\mathrm{geom}}$ (a different object from the arithmetic Galois group $\mathrm{Gal}(g/\mathbb{Q}(\omega))$ identified here), and the two need not agree. The geometric-monodromy statement (verified $SU(2)$ at scale on the connected-component trace) is untouched.

## 4. Scope held honestly

- **Single prime.** The group identification is at $p=43$ only — the unique prime where the degree-10 object is in identifiable range. Cross-check by exact-group methods at a second prime is impossible (degree 26 at $p=67$, 42 at $p=127$). A cycle-*signature* consistency check (cycle lengths $\mid 10$) at higher $p$ is feasible but does not pin the group.
- **Identification, not proven identity.** The match is by cycle-type/Chebotarev density, which is highly discriminating at degree 10 (8-type agreement including rare types) but is, strictly, evidence rather than a certified isomorphism. A certified identity would need `galois_group()` to complete (requires KASH/Magma).
- **Arithmetic vs geometric group.** $\mathrm{Gal}(g/\mathbb{Q}(\omega))$ (arithmetic, identified here as $10T14$) is distinct from $G_{\mathrm{geom}}$ (geometric monodromy, conjecturally $\mathrm{SL}_2$, verified $SU(2)$ on traces). The refutation in §3 is of the arithmetic-group-level icosahedral guess; it does not touch the geometric-monodromy conjecture.
- **$A_{10}$ clarification.** The degree-40 census fact "$G\subseteq A_{40}$" and the degree-20 absolute-polynomial fact "$\mathrm{disc}(g_{\mathrm{abs}})$ is a square $\Rightarrow\mathrm{Gal}(g_{\mathrm{abs}}/\mathbb{Q})\subseteq A_{20}$" are about *different* permutation representations and do **not** force the degree-10 quotient $\mathrm{Gal}(g/\mathbb{Q}(\omega))$ into $A_{10}$. It is not in $A_{10}$ (§2 parity).

## 5. Files

- `algebraic_galois_degree10_v1.sage` — the committed construction + census + identification. `analyse(43)` reproduces §1–§2.
- Builds on `RESULT_algebraic_number_layer_v1.md` (§5 tower, §6 open question, §7 cycle data) and `anew_eigenvalue_identify_v3.sage` (`build_L`).

## 6. What this opens / closes

- **Closes:** the committed construction of the degree-10-in-$T^2$ object; the in-range Galois-group identification ($10T14$, order 160, solvable, not in $A_{10}$).
- **Refutes (one candidate):** the arithmetic-level icosahedral/$\mathrm{SL}_2(\mathbb{F}_5)$ identification of the $W$-piece.
- **Leaves open:** the geometric-monodromy $\mathrm{SL}_2$ conjecture (untouched — different object); a certified (non-Chebotarev) group identity (blocked on KASH/Magma); the connection to the folded-angle $u(a)=\arcsin(\ldots)$.
