# Gap 2: Sharpened Component-Wise D.2 Statement (Theorem-Track Draft)

## Status
- This document formalizes the target analytic statement used by the multi-divisible TCP pipeline.
- It is a theorem-track statement tied to existing artifacts; universal asymptotic closure is **not** claimed here.

## Setup
Fix a template family
- `F = (n, E_fix, E_div)` with `|E_div| >= 2`,
- `L0 = lcm(E_fix ∪ E_div)`, `L = L0*M`, `gcd(M, nL0)=1`.

Let `B_div(F,M)` be the divisible-feasible set in `b`-space, represented as disjoint integer components
`C_j=[u_j,v_j]` from exact interval-intersection geometry.

Define canonical lower/top frozen bands
- `I_lo = [ceil(L/n), floor(L/e_max)-1]`,
- `I_hi = [ceil((e_max-1)L/e_max), floor((n-1)L/n)]`,
where `e_max = max(E_fix)`.

For each component `C_j`, define band intersections:
- `J_{j,lo}=C_j∩I_lo`, `J_{j,hi}=C_j∩I_hi`.

Aggregate quantities:
- `S(F,M) = Σ_j ( |J_{j,lo}| + |J_{j,hi}| )`
- `nu(F,M) = # {j: |J_{j,lo}|>0} + # {j: |J_{j,hi}|>0}`
- `zeta(F,M) = Σ_{nonempty J} # {u in J : L0 | u}`

## Theorem Target (D.2-multidiv-sharp)
For every admissible `M`,

`B_safe(F,M) >= floor( ((n-1)/n) * S(F,M) - ( 2*L0*nu(F,M) + zeta(F,M) ) ).`

Equivalent notation in code/artifacts:
- RHS is `d2_lb_floor`.
- Additive constant is `C(F,M)=2*L0*nu(F,M)+zeta(F,M)`.

## Affine Corollary Target (TCP Bridge)
If for a template `F` one proves affine envelopes
- `S(F,M) >= s1_F*M + s0_F`,
- `C(F,M) <= c1_F*M + c0_F`,
with `a_F := ((n-1)/n)*s1_F - c1_F > 0`, `b_F := ((n-1)/n)*s0_F - c0_F`,
then

`B_safe(F,M) >= floor(a_F*M + b_F)`.

Hence define
- `M0(F)=ceil((phi(n)-b_F)/a_F)`,
- `T(F)={ M : 1<=M<M0(F), gcd(M,nL0)=1 }`,
and exact verification on `T(F)` yields TCP-style closure for template `F`.

## Artifact Binding (Current Evidence)
This statement is operationalized by these fields in
`lrc_case2_multidiv_boundary_certifier_v1.py` and downstream CSVs:
- `lo_total_len + hi_total_len`  -> `S(F,M)`
- `lo_component_hits + hi_component_hits` -> `nu(F,M)`
- `zeta_candidates` -> `zeta(F,M)`
- `d2_lb_floor` -> theorem RHS floor value
- `B_safe` -> theorem LHS

Empirical checks already recorded:
- `lrc_case2_multidiv_batch_checks_n13_d23_f123_m80_v1.csv`
- `lrc_case2_multidiv_tcp_checks_n13_d23_f123_tcp_affine_m340_v1.csv`
- `lrc_case2_multidiv_batch_checks_n13_d23_f1234_m100_v1.csv`
- `lrc_case2_multidiv_tcp_checks_n13_d23_f1234_tcp_affine_m420_v1.csv`

In those artifacts, every recorded check satisfies `B_safe >= d2_lb_floor`.

## Scope Guardrail
- This is the formal theorem target tied to artifacts.
- Remaining open: a proof that the stated bound holds uniformly (without finite-cap restriction) in full multi-divisible generality.
