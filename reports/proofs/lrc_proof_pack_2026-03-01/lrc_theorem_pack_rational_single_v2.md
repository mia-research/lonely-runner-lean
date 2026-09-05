# LRC Theorem Pack (v2): Triple Overlap + Inclusion Bounds

## 1) Rational SINGLE target (stationary-runner reduction)
Fix runner `i` and move to its stationary frame.
Let reduced integer relative speeds be `e_1,...,e_m` where `m=n-1`, `gcd(e_j)=1`.
Set `L=lcm(e_j)`, `N=nL`, lattice points `k in Z_N`, `s_k=k/N`.

Define dangerous sets:

`D_e = {k in Z_N : {e*s_k} < 1/n or {e*s_k} > (n-1)/n}`.

SINGLE-safe points are exactly `Z_N \ U_e D_e`.
So the theorem reduces to proving:

`|U_e D_e| < N`.

---

## 2) Exact overlap formulas

### Lemma 2.1 (single-set size, exact)

`|D_e| = 2L - e`.

### Lemma 2.2 (pairwise overlap, exact CRT form)
For `a,b | L`, let `m_a=nL/a`, `m_b=nL/b`, `d=gcd(m_a,m_b)`, `g=gcd(a,b)`.
Using dangerous residue windows `R_a, R_b` and residue counts `c_a(r), c_b(r)` mod `d`:

`|D_a ∩ D_b| = g * Σ_{r=0}^{d-1} c_a(r)c_b(r)`.

### Lemma 2.3 (triple overlap, exact CRT-lift form)
For `a,b,c | L`, let `g=gcd(a,b,c)`, `M=nL/g`.
Let `I_e(x)` be indicator that `x mod (nL/e)` lies in the dangerous residue window for `e`.
Then

`|D_a ∩ D_b ∩ D_c| = g * Σ_{x=0}^{M-1} I_a(x) I_b(x) I_c(x)`.

This is exact (no approximation): count compatible classes mod `M`, then lift by factor `g=N/M`.

---

## 3) Inclusion/multiplicity checker built and run

I implemented a moment-based LP checker over multiplicity histogram `x_r` (number of points with dangerous multiplicity `r`):
- constraints from exact moments `(N,S1,S2)` and `(N,S1,S2,S3)`
- objective: minimize `x_0` (safe count lower bound)

If LP minimum `x_0 > 0`, that tuple is proven (`|U D_e| < N`) from those moments alone.

Artifacts:
- checker script: `/tmp/lrc_triple_overlap_inclusion_checker_v1.py`
- table: `/tmp/lrc_triple_overlap_inclusion_table_v1.csv`
- summary: `/tmp/lrc_triple_overlap_inclusion_summary_v1.md`

### Results (full bounded exhaustive grid)
Grid used: same as prior bounded exhaustive program (`n=3..8`, `max_e` by `n`).

| n | gcd1 tuples | proven by (S1,S2) | proven by (S1,S2,S3) |
|---:|---:|---:|---:|
| 3 | 91 | 91 (100%) | 91 (100%) |
| 4 | 637 | 589 (92.46%) | 637 (100%) |
| 5 | 2303 | 1463 (63.53%) | 2231 (96.87%) |
| 6 | 3091 | 1471 (47.59%) | 2731 (88.35%) |
| 7 | 4031 | 3761 (93.30%) | 4031 (100%) |
| 8 | 16255 | 15625 (96.12%) | 16255 (100%) |

Unresolved by moment-3 LP: 432 tuples total (`n=5`: 72, `n=6`: 360).
These are not counterexamples; they are just not forced by moments up to order 3.
(Their exact safe counts from direct computation remain positive.)

---

## 4) One-perturbation AP track (parallel proof path)
Already formalized in:
- `/tmp/lrc_one_perturbation_branch_v1.py`

Key equations retained:
- AP witnesses: `t_r = r/(nΔ)`, `gcd(r,n)=1`.
- Perturbation shift at witness: `delta_phi_r = eps * t_r`.
- Boundary branch law: `t_q^{±}(eps) = (q ± 1/n)/|dv(eps)|`, with explicit derivative.

This gives the constructive continuation framework from AP to perturbed regimes.

---

## 5) Current proof status
- Exact formulas now available through triple overlaps.
- Strong empirical and partial-analytic support: no disproof, broad positive certification.
- Remaining theorem gap: a universal argument beyond 3rd moment (e.g., 4th moment / structural congruence constraints) to force `x_0>0` for all tuples.
