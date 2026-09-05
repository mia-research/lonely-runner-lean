# Gap 1 De-enumeration Track (Post G1.K)
**Date:** 2026-03-03

## Canonical state

Inserted chain in `v11`:
- G1.B (`§17.7`): cell cap
- G1.C (`§17.8`): aggregate constant
- G1.D (`§17.9`): affine extraction
- G1.E (`§17.10`): finite small-`M` bridge
- G1.F (`§17.11`): template-free `M0` envelope
- G1.G (`§17.12`): bounded-strip reduction
- G1.I (`§17.17`): canonical fixed-signature complexity bound (`m_tot<=3`)
- G1.J (`§17.18`): sharpened aggregate constant and `M0` envelope (`M0^sh<=4n^2+1`)
- G1.K (`§17.19`): exact reduced `Delta_tr` criterion and explicit residual `Xi_tr`

## Remaining analytic target

Prove `(G1.G.2)` uniformly on all templates; in prime Gap-1 scope `§17.16` already removes TM2 obstruction (`E_tm2=0`), and `§17.19` makes the reduced criterion exact; the remaining burden is proving uniform `Xi_tr(F,M)=0` (equivalently the `Delta_tr` threshold inequality):

`(forall n prime)(forall F in F_n)(forall M in U_n^* with gcd(M,L0(F))=1): x0(F,M) >= phi(n)`

where baseline strip is

`U_n^* = {1 <= M < 3n^4+1, gcd(M,n)=1}`

and `§17.18` gives a sharper tail envelope target

`U_n^sh = {1 <= M < 4n^2+1, gcd(M,n)=1}`

for the large-`M` bridge constants.

## Why this matters

This is exactly the de-enumeration step: if proved, template-by-template finite certification is
no longer needed for Gap 1.

## Guardrail

Any additional per-`n` certification remains support evidence only and does not satisfy this
analytic target.
