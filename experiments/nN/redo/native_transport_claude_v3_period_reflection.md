# Period-reflection economy for rational_reflection_data: findings

Scope: `PinchReflectionN.lean`, `IncomingWindowN.lean`, `WindowPinchN.lean`,
`GrandReturnN.lean`, `PathRouteN.lean`. Read-only review; no edits made.

## 1. The correct construction (keeps q, keeps hleft untouched)

Fix S, d : ι→ℚ with d_i>0, and H>0 with e_i := d_i*H ∈ ℤ for every i∈S
("current period" of the readings — same kind of object as
`PathRouteN.common_period`, but with no factor of 8 and no dependence on t).
Given the old witness time t and old labels q_i (q_i+1/8 ≤ d_i t ≤ q_i+7/8),
set m := ⌊t/H⌋, lam := (m+1)H/t − 1, P_i := (m+1)·e_i.

Then **lam > 0** (since t < (m+1)H by definition of floor, strictly, for
t ≠ (m+1)H's lower edge handled by m's definition), **P_i is an integer**, and
`(P_i:ℝ) = (lam+1)*d_i*t` holds exactly (d_i cancels: (lam+1)t=(m+1)H for
every i simultaneously, since lam does not depend on i). This is hP, verbatim
the hypothesis of `PinchReflection.reflected_band` / `reflected_right_windows`
— so **everything downstream (`reflected_slack`, `active_boundaries`,
`active_slope_reversal`, `active_slope_nonpos`, `reflected_right_inequalities`,
`reflected_right_windows`) applies with no new proof**, by instantiating the
existing lam,P. In particular `hleft` is the ORIGINAL hypothesis on q — nothing
about it is touched, so the incoming-direction condition transfers with zero
discrepancy.

Resulting label p_i := P_i − q_i − 1 satisfies p_i ∈ [0, e_i−1] = [0, d_i·H−1]:
this follows from the *same* general argument already in the file (`hq` in
`reflected_right_windows` gives p_i≥0 from lam,t>0; the matching upper bound
p_i≤e_i−1 follows from d_i·u≤e_i with u=lam·t=H−t0≤H). Reflected time
u = lam·t = (m+1)H − t = H − t0, where t0 = t − mH ∈ [0,H) is the ordinary
remainder of t mod H. **So p_i and u are bounded purely by H and d_i,
independent of q_i, m, or how many prior reflections produced t.** Exact
check (Fraction arithmetic, d_i=2/3, d_j=5/7, H=21, t=40.1, m=1): lam=19/401>0,
P_i=28, P_j=30 (integers), p_i=p_j=1 ∈ [0,e−1], u=H−t0=19/10, all four band
inequalities verified exactly.

## 2. Nonactive inequalities and ties — unaffected

`reflected_right_inequalities`'s proof of `hC` (nonactive/strict slack stays
≥0) and `hB` (active slack sign-reversal) is an identity in *any* lam,P
satisfying hP — `reflected_slack` and `active_slope_reversal` are proved for
arbitrary lam>0, P. Plugging in the (m,H)-built lam,P above changes nothing in
those proofs. Ties (`active_boundaries`'s hz = 0, simultaneous equality on two
runners) transfer exactly for the same reason — nothing in the derivation used
t or P individually, only the algebraic identity `reflected_slack`, which is
lam/P-agnostic. So the sign reversal `(... )*vj - (...)*vi = -lam*((qj+7/8)vi-
(qi+1/8)vj)` — i.e. every active derivative, proportional to t*(d_j v_i−d_i
v_j) in the untransformed picture, flips sign with factor −lam — holds for
every active pair and every tie, not merely "from periodicity."

## 3. Where the naive q→q′ relabeling actually breaks

A different-looking route — reduce t to t0=t mod H and ALSO relabel
q_i ↦ q_i′ := q_i − m·e_i (so the band holds at t0 with q′, exactly) — gives
the identical final p_i formula, but is the wrong hypothesis to carry hleft
through. If hleft is given in q-form (the real "feasible strictly before the
pinch" fact, about d_i−delta·v_i), the q′-form of the same statement is NOT
equivalent: algebraically,
`(q-form LHS−RHS) − (q′-form LHS−RHS) = m·H·delta·(d_j·v_i − d_i·v_j)`.
This was checked exactly (Fractions): with m=1, H=21, delta=1/100, v_i=3,
v_j=−2, the two sides of the identity both equal 73/100. The term is
generically nonzero, because H is a period of d_i, **not** of d_i−delta·v_i
(v_i is an arbitrary real direction; nothing makes v_i·H rational). So
relabeling q and asking the SAME time-shift to carry the incoming-direction
hypothesis is false in general — it is not merely unproved, it has an
explicit nonzero correction term. **This is why §1 keeps q and t exactly as
given**, varying only the (lam,P) choice used to name the reflected labels;
that version has no such term because hleft is never touched.

## 4. No uniform H along a deformation

H is a property of the *exact* rational d_i at one fixed arrangement (its
denominators). For h≠0, d_i+h·v_i is generically irrational or has an
unrelated denominator, so no single H serves two different points of a
one-parameter family. The (m,H) construction is per-arrangement only: each
rational pinch along a cascade needs its own H, recomputed, though H is
reusable for *repeated* pinches at the *same* fixed arrangement (h=0 held
fixed), where it keeps times bounded by H forever (t≤H after the first use,
so m=0 thereafter).

## 5. Six-fixed-readings one-mover resonance

In `PathRouteN.segment_lonely`'s `heq` branch (Fin 8, subject k, one mover i,
six others fixed), the period actually used is `common_period hallq t1`
(lines 187–204, called per-instant inside the proof). `hallq` is rationality
of ALL seven non-subject readings — the six truly fixed ones AND the mover's
CURRENT value u_i−u_k at the specific resonant instant t1 (obtained via
`reading_rat`/`instant_rat` from t1 itself being forced rational by the tie).
**No fixed, mover-independent H exists**: a period built from the six fixed
readings alone constrains nothing about the mover's reading, which varies
with h and is only pinned down at the specific resonance point. So the
existing per-instant `common_period` call is already the minimal construction
here; the (m,H) economy of §1 does not reduce further in this case, because
the "H" needed necessarily depends on the mover's current rational value, not
only on the six fixed ones.

## 6. On the "previous report"'s restricted (C)

I could not locate a document in `experiments/nN/redo` making the claim "all
ratios near 1 give nested blocked intervals." A grep for "restricted (C)" and
"nested blocked" in this directory turns up only `transport_priority_claude_v2_search.{py,out}`,
whose "restricted (C)" is an unrelated walker-residue-cover claim (fastest-
flank covers of size ≤5), not a ratio/scale statement. I therefore cannot
verify or refute the specific claim against its source and flag this rather
than guess at its content.

What the files actually in scope support: `WindowPinch.first_scale_pinch`
gives, for a **single fixed** lap assignment (S, beta, lo, hi), a genuine
global statement — `(∃ lam, windows hold) ↔ s ≤ tau` for ALL s (not just a
local neighbourhood), because the active slack is affine and an affine
function crosses zero at most once. So within one fixed lap assignment, once
blocked, blocked forever — no horizon bound is needed for *that* assignment.
But the theorem's own comment is explicit: "no conclusion that a different
lap assignment restores feasibility." A claim that nested blocked intervals
persist "for all ratios near 1" is only safe if it is read as holding **per
fixed lap assignment**; the moment a reflected/alternative assignment is
allowed to take over (exactly what §1's reflection produces), a horizon bound
on how many such reflections occur before the ratio leaves "near 1" is
needed and is not supplied by `first_scale_pinch` alone. Absent the source
document, the safest precise statement is:

> For one fixed (S,beta,lo,hi), feasibility is an interval s∈[0,tau] with no
> later recapture under that SAME assignment. Recapture under a DIFFERENT
> (e.g. reflected) assignment is not excluded by this lemma and requires an
> explicit bound on the number of lap reassignments before the deformation
> leaves the stated ratio range.

## 7. Explicit non-claims

No claim is made that this economy holds for all n=8, nor that off-lattice
(irrational) witnesses converge — H is defined only from rational d_i.
