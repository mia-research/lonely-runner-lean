# Gap 1 Open Problem Brief (Exact Frontier)
**Date:** 2026-03-03
**Audience:** collaborator ideation memo
**Canonical references:** `lrc_ap_grid_extremizer_theorem_sequence_v11.md` §§17.14, 17.16, 17.17, 17.18, 17.19

## 1) What is already proved (not open)

For prime one-divisible all-distinct Gap-1 scope:

- TM2 obstruction is eliminated on canonical bands: `O_tm2=empty`, `E_tm2=0` (`§17.16`).
- Canonical fixed-signature complexity is bounded: `m_tot<=3` (`§17.17`).
- Sharpened aggregate/tail constants are proved: `C_bad(I_tot)<=|I_tot|/n+6L0`, `M0^sh<=4n^2+1` (`§17.18`).
- Reduced transition formulation is exact (`§17.19`):
  - `Delta_tr^sh := |I_tot|/n + K_loc^sh - C_bad(I_tot)` with `K_loc^sh=2L0*m_tot`,
  - `Delta_tr^sh>=0`,
  - closure criterion is equivalent to `(G1.K.4)` / `Xi_tr=0`.

So the theorem-link chain is complete through G1.K.

## 2) What is still open (exactly)

The open Gap-1 step is now a single uniform statement:

`(forall n prime)(forall F in F_n)(forall M in U_n^* with gcd(M,L0(F))=1): Xi_tr(F,M)=0`.

with baseline strip

`U_n^* = {1 <= M < 3n^4+1, gcd(M,n)=1}`.

Equivalent form:

`Delta_tr^sh(F,M) >= K_loc^sh(F,M) - ( ((n-1)/n)|I_tot| - (n-1) )`.

Equivalent safe-mass form on canonical bands:

`B_safe(I_tot) >= n-1`.

This is the only remaining analytic bottleneck in the current G1 route.

## 3) Critical reality check for ideation

Current support artifact (`lrc_gap1_delta_tr_mtot3_validation_v1.md`) shows:

- prime rows checked: `36,847`
- `Delta_tr^sh>=0` failures: `0`
- criterion-equivalence mismatches: `0`
- but `Xi_tr>0` rows: `92` (max `Xi_tr=18`)

By n, residual counts are:

- `n=7`: 8 rows
- `n=11`: 11 rows
- `n=13`: 16 rows
- `n=17`: 26 rows
- `n=19`: 31 rows

Observed structural pattern in all residual rows:

- `m_tot=3` (maximal reduced geometry complexity)
- several rows have `B_safe(I_tot)=0` (canonical band contributes no safe fibers)

Therefore, **uniform `Xi_tr=0` on current canonical `I_tot` is not supported by existing certified windows**.
This means the current closure target must be strengthened/reframed, not just pushed harder.

## 4) Why this does not contradict certified correctness

Even rows with `Xi_tr>0` still satisfy full theorem checks (`x0>=phi(n)`) from existing certifiers.
Example residual rows (all certified with `x0>=phi`):

- `n=7`, `fixed=(2,3,4,6)`, `M=17`: `Xi_tr=6`, `B_safe(I_tot)=0`, but `x0=1686`, `phi(7)=6`.
- `n=11`, `fixed=(1,2,3,4,6,8,9,10)`, `M=89`: `Xi_tr=10`, `B_safe(I_tot)=0`, but `x0=394212`, `phi(11)=10`.
- `n=13`, `fixed=(1,2,3,4,5,6,7,9,11,12)`, `M=53`: `Xi_tr=12`, `B_safe(I_tot)=0`, but `x0=6117288`, `phi(13)=12`.
- `n=17`, `fixed=(1,2,3,4,5,6,7,8,9,10,13,14,15,16)`, `M=89`: `Xi_tr=16`, `B_safe(I_tot)=0`, but `x0=126629954`, `phi(17)=16`.
- `n=19`, `fixed=(1,2,3,4,5,6,7,8,9,10,11,12,13,15,17,18)`, `M=211`: `Xi_tr=18`, `B_safe(I_tot)=0`, but `x0=13964359488`, `phi(19)=18`.

Interpretation: the missing safe mass is coming from outside the current canonical `I_tot` route.

## 5) Exact open mathematical fork (for colleague ideation)

The project now needs one of these theorem moves:

### Route A (recommended): augment the criterion with outside-band safe mass
Prove a uniform lower bound `S_out(F,M)` for safe fibers outside canonical `I_tot`, and show

`B_safe(I_tot) + S_out(F,M) >= n-1`.

Equivalent residual target:

`Xi_tr(F,M) <= S_out(F,M)` uniformly.

### Route B: redesign band geometry
Replace current `I_tot=I_lo union I_hi` with a new analytically tractable region `I_tot'` that
retains TM/frozen control but captures the safe mass now missed by canonical bands.
Then prove `B_safe(I_tot')>=n-1`.

### Route C: bypass band sufficiency and prove `x0` directly
Use global event-cell occupancy on full `B_div` (or a larger structured partition) to prove
`x0>=phi(n)` without requiring canonical-band threshold as an intermediate target.

## 6) What not to spend time on

- More finite-window runs alone (support evidence only).
- Re-trying disproved anchor-only or lower/top-only shortcuts.
- Attempting to prove uniform `Xi_tr=0` on current canonical `I_tot` as if no residual rows exist.

## 7) Immediate ideation tasks

1. Characterize where the extra safe mass sits when `B_safe(I_tot)=0` (middle region profile).
2. Define a minimal extra region `J(F,M)` with tractable event-cell structure.
3. Try to prove `B_safe(J) >= Xi_tr` (or direct stronger inequality) uniformly.
4. If successful, insert as `§17.20` and rebind `G1.G.2` with no empirical dependency.
