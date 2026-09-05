# Gap 1 External Open-Problem Brief (Self-Contained)
**Date:** 2026-03-03
**Purpose:** Give an external collaborator everything needed to attack the remaining Gap-1 theorem step without requiring access to internal notes.

## 1) Problem statement (self-contained)

We study a normalized Lonely Runner counting model at threshold `1/n`.
For each integer speed tuple `E` (size `n-1`, gcd-1 normalized), define an exact safe-count quantity `x0(E)`.
The target inequality is

`x0(E) >= phi(n)`

where `phi` is Euler's totient.

Gap 1 is the prime, one-divisible, all-distinct Case-2 family:

- `n` prime,
- exactly one speed divisible by `n` (normalized as speed `n`),
- fixed non-divisible speeds are distinct mod `n` (`|E_fixed|=n-3`),
- one-parameter family form `E(M) = E_fixed union {M} union {n}` with `gcd(M, n*L0)=1`,
- admissible `M` is required to be non-divisible mod `n`; residue collision with `E_fixed` is allowed,
- `L = L0*M`, `L0 = lcm(E_fixed union {n})`.

## 2) Key objects and exact formulas

For each divisible-feasible fiber index `b`, define `A_b` = number of safe residues `a in Z_n`.
Then

`x0(E) = sum_{b in B_div} A_b`.

Define canonical bands

`I_lo = [ceil(L/n), floor(L/e_max)-1]`,
`I_hi = [ceil(L-L/e_max), floor((n-1)L/n)]`,
`I_tot = I_lo union I_hi`,

where `e_max = max(E_fixed)`.

Define band-safe count

`B_safe(I_tot) = #{b in I_tot : A_b > 0}`.

A sufficient closure condition is

`B_safe(I_tot) >= n-1`.

## 3) What is already proved (not open)

Within this Gap-1 scope, the following are established analytically:

1. TM2 obstruction vanishes on canonical bands:
   `O_tm2 = empty`, so no obstruction surcharge term remains.
2. Fixed-signature partition complexity on canonical bands is at most 3 cells:
   `m_tot <= 3`.
3. Cell aggregation yields
   `C_bad(I_tot) <= |I_tot|/n + 6L0`,
   where `C_bad(I_tot) = |I_tot| - B_safe(I_tot)`.
4. Exact reduced transition reserve can be defined by identity:

   `K_loc^sh := 2L0*m_tot`,
   `Delta_tr^sh := |I_tot|/n + K_loc^sh - C_bad(I_tot)`.

   This is exact (definition rearrangement), and `Delta_tr^sh >= 0` is proved.

5. Equivalent closure criterion on canonical bands:

   `B_safe(I_tot) >= n-1`

   iff

   `Delta_tr^sh >= K_loc^sh - ( ((n-1)/n)*|I_tot| - (n-1) )`.

6. Residual form:

   `Xi_tr := max(0, K_loc^sh - ( ((n-1)/n)*|I_tot| - (n-1) ) - Delta_tr^sh )`,

   then

   `B_safe(I_tot) >= n-1 - Xi_tr`.

So the only missing step in this route is a uniform proof that `Xi_tr=0`.

## 4) Exact open statement

Open target (current route):

`(forall prime n)(forall templates F in Gap-1 class)(forall M in U_n^* with gcd(M,L0(F))=1): Xi_tr(F,M)=0`.

with baseline strip

`U_n^* = {1 <= M < 3n^4+1, gcd(M,n)=1}`.

(Sharpened envelope from G1.J for tail constants: `M < 4n^2+1`.)

Equivalent:

`Delta_tr^sh(F,M) >= K_loc^sh(F,M) - ( ((n-1)/n)*|I_tot| - (n-1) )`.

Equivalent safe-band form:

`B_safe(I_tot) >= n-1`.

## 5) Critical empirical reality (support-only, not proof)

A support check over certified prime windows evaluated `36,847` rows and found:

- `Delta_tr^sh >= 0` failures: `0`
- criterion-equivalence mismatches: `0`
- rows with `Xi_tr > 0`: `92`
- max observed `Xi_tr`: `18`

By prime `n`:

- `n=7`: 8 residual rows
- `n=11`: 11 residual rows
- `n=13`: 16 residual rows
- `n=17`: 26 residual rows
- `n=19`: 31 residual rows

Observed structural pattern in all residual rows:

- `m_tot=3` (max complexity case),
- many rows have `B_safe(I_tot)=0`.

## 6) Why this does not break overall certification

Even when `Xi_tr>0`, full exact checks still satisfy `x0(E) >= phi(n)`.
Examples:

- `n=7`, fixed `(2,3,4,6)`, `M=17`: `Xi_tr=6`, `B_safe(I_tot)=0`, but `x0=1686 >= phi(7)=6`.
- `n=11`, fixed `(1,2,3,4,6,8,9,10)`, `M=89`: `Xi_tr=10`, `B_safe(I_tot)=0`, but `x0=394212 >= 10`.
- `n=13`, fixed `(1,2,3,4,5,6,7,9,11,12)`, `M=53`: `Xi_tr=12`, `B_safe(I_tot)=0`, but `x0=6117288 >= 12`.
- `n=17`, fixed `(1,2,3,4,5,6,7,8,9,10,13,14,15,16)`, `M=89`: `Xi_tr=16`, `B_safe(I_tot)=0`, but `x0=126629954 >= 16`.
- `n=19`, fixed `(1,2,3,4,5,6,7,8,9,10,11,12,13,15,17,18)`, `M=211`: `Xi_tr=18`, `B_safe(I_tot)=0`, but `x0=13964359488 >= 18`.

Interpretation: the current canonical-band sufficiency target misses safe mass that is contributing elsewhere.

## 7) What an external agent should actually try

At least one of these theorem moves is required:

1. **Outside-band compensation theorem (recommended first):**
   Define/prove a uniform lower bound `S_out(F,M)` outside canonical `I_tot` such that
   `B_safe(I_tot) + S_out(F,M) >= n-1`.
   Equivalent residual target: prove `Xi_tr <= S_out` uniformly.

2. **Band redesign theorem:**
   Replace `I_tot` with a larger analytically tractable region `I_tot'` (still event-cell manageable),
   then prove `B_safe(I_tot') >= n-1` directly.

3. **Direct global theorem:**
   Bypass band sufficiency and prove `x0(E) >= phi(n)` from a global event-cell occupancy inequality
   on all of `B_div`.

## 8) Non-productive directions (already screened)

- More finite-window certification alone (evidence only).
- Anchor-only mass arguments.
- Lower/top guaranteed-safe-only arguments.
- Assuming uniform `Xi_tr=0` on current canonical bands despite explicit residual rows.

## 9) Minimal deliverable that would close Gap 1 in this route

A theorem proving either:

- `Xi_tr(F,M)=0` uniformly, or
- `Xi_tr(F,M)<=S_out(F,M)` with a uniform theorem-grade `S_out` and
  `B_safe(I_tot)+S_out>=n-1`.

Either result is enough to complete the prime one-divisible all-distinct all-`n` analytic closure step.
