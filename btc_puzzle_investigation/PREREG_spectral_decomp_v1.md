# PREREG — Spectral decomposition of the pairwise cubic-character matrix (v1)

**Status:** FROZEN before apply. Gate: `experiment-designer` (isolated). Date: 2026-07-30.
**Motivation.** The CM-vanishing test (`RESULT_diffset_cubic_cmvanishing_v1.md`) showed E3
on the non-CM curve $E'$ is null ($E_3'=3711$, $p\approx 0.66$). But E3 is a *single-number
aggregate* — it projects the pairwise structure onto the all-ones mode. **If coherent signal
exists in a singular mode orthogonal to all-ones, E3 cancels it (destructive interference in
the marginal sum) even though the matrix carries it.** This test asks: is E3's null on $E'$
a *true* null, or is it hiding coherent structure that the aggregate destroyed?

## Object

Let $X_1,\dots,X_{82}$ be the pubkey $x$-coordinates (on secp, or on $E'$). Define the
**pairwise cubic-character matrix**

```
C[i,j] = χ₃(X_i − X_j) ∈ {1, β, β²}   (i ≠ j),  C[i,i] = 0
```

where $\chi_3(z) = z^{(P-1)/3}\bmod P \in \{1,\beta,\beta^2\}$ ($z\ne 0$; diagonal forced 0).
$C$ is Hermitian-like: $C[j,i] = \overline{C[i,j]}$ since $\chi_3(-1)=1$ at $P\equiv1\bmod6$
$\Rightarrow$ $\chi_3(X_j-X_i)=\chi_3(-(X_i-X_j))=\chi_3(X_i-X_j)$. So **eigenvalues are real**.

**Identity (the whole point).** With $\omega = e^{2\pi i/3}$ and $a,b,c$ the cubic-class
counts,

```
E3 = |Σ_{i<j} χ₃(X_i−X_j)|²  =  ½² · |1ᵀ C 1|²
```

(up to the trivial bookkeeping of which cube-root label gets the unit phase). I.e. **E3 is
the power of $C$ projected onto the all-ones mode $\mathbf{1}$** — exactly one direction. If
coherent signal lives in a singular mode $v \perp \mathbf{1}$, E3 cancels it.

## Statistic (FROZEN before apply)

- **$\sigma_{\max} = $ largest singular value of $C$** (= largest $|$eigenvalue$|$ since $C$ is
  Hermitian-like). Single scalar; captures any coherent mode, all-ones or not.
- Also report $\|\mathbf{1}^\top C\|$ (the all-ones projection; ties to E3) and
  $\sigma_{\max}^{(\perp)} = $ largest singular value of $C$ restricted to the subspace
  orthogonal to $\mathbf{1}$ (i.e. SVD of $C$ after projecting out the all-ones mode).

## Falsification (FROZEN, per cell, empirical order statistics)

For **each cell** (secp, $E'$) independently: 10,000 resamples of 82 from that cell's
constructed pool (matched bit-lengths), compute $C$ and $\sigma_{\max}$ for each. Frozen
region $[L_\sigma, U_\sigma]$ = order-statistic tails at $\alpha\approx 0.05$ (lower/upper
0.025). Seed `20260730`.

```
reject-HIGH (coherent structure)   iff  σ_max(real) > U_σ
reject-LOW  (over-rigidity)        iff  σ_max(real) < L_σ
else FAIL-TO-REJECT
```
Apply rank-$p$: `min((#{null ≥ σ_real}+1)/(N+1), (#{null ≤ σ_real}+1)/(N+1))·2`. Empirical
order statistics only.

## The four-way decision (the payload)

| secp $\sigma_{\max}$ | $E'$ $\sigma_{\max}$ | reading |
|---|---|---|
| REJECT-HIGH | FAIL-TO-REJECT | **CM-driven coherent structure** (consistent with E3 result; lens holds; structure on secp, not on $E'$) |
| REJECT-HIGH | **REJECT-HIGH** | **hidden structure on $E'$** that E3 cancelled — destructive interference confirmed; chase the singular vector |
| FAIL-TO-REJECT | FAIL-TO-REJECT | E3's secp anomaly was a marginal fluke (not coherent); the whole diffset avenue on this surface is bounded |
| FAIL-TO-REJECT | REJECT-HIGH | (unexpected; coherent on $E'$ but not secp — characterize, don't interpret) |

**The decisive cell is $E'$ REJECT-HIGH.** That is the destructive-interference signature:
E3 on $E'$ is null ($p\approx 0.66$) but $\sigma_{\max}$ on $E'$ is elevated. If we see it,
the aggregate was lying and there is real structure to chase.

## Controls (must fire or test void)

1. **Planted-coherent control:** plant a coherent block — pick a subset of $k$ keys, set their
   mutual $\chi_3$ entries to a fixed cube root — must reject-high with power $\ge 0.9$ at
   block size $k=10$ in each cell. If it doesn't fire, the SVD instrument can't see coherent
   structure $\Rightarrow$ test void.
2. **Random-matrix sanity:** null $\sigma_{\max}$ should be $\approx 2\sqrt{82}\approx 18.1$
  (Marchenko–Pastur / iid root-of-unity prediction). Record the empirical null mean; flag if
  it deviates by $>2\times$.
3. **All-ones consistency:** $\|\mathbf{1}^\top C_{\text{secp}}\|^2 / E_3$ should be $O(1)$
  (a fixed factor); record the ratio, flag if it changes between cells.

## Scope

- Same 82 real puzzle keys (secp $d$'s) as `RESULT_diffset_cubic_v1.md` / `_cmvanishing_v1.md`.
- Both cells over secp's $P$; same $\chi_3$.
- $C$ is $82\times 82$ (3,321 unique off-diagonal pairs $\times$ 2 for symmetry).
- **SCALE BANNER / LANGUAGE RULES / ANOMALY-DRILL RULE** inherited. No security verdict.

## Artifacts

- `spectral_decomp_apply.py` (C matrix, SVD, both cells, controls, decision)
- `spectral_decomp_frozen_null_secp_v1.npy`, `spectral_decomp_frozen_null_Eprime_v1.npy`
- `spectral_decomp_meta_v1.json`
- `RESULT_spectral_decomp_v1.md`
