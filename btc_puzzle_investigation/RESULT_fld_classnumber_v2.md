# FLD = ±6h(−p): reduction to one geometric lemma (L2 proven)

Date: 2026-07-19. Supersedes `RESULT_fld_classnumber_v1`. Scripts `_fld_interval_v1.py`,
`_fld_reduce_explore_v1.py`, verification loop over p∈[100,2500). The class-number law now has an
almost-complete proof chain; the single open step is isolated and verified 86/86.

## The reduction chain (status tagged)
`FLD(p) = Σ_{x∈F_p} σ(x)χ2(x)`. For p ≡ 1 mod 6:

**Step 0 [PROVEN].** p ≡ 1 mod 4 ⇒ FLD = 0 (x→−x: σ odd, χ2(−1)=+1 ⇒ summand odd).

**Step 1 [PROVEN].** p ≡ 3 mod 4 ⇒ `FLD = 2·Σ_{x∈T+} χ2(x)`, T+ = {x : u(x)−v(x) > ½} the positive
flap triangle (x→−x swaps T±, χ2(−1)=−1). Verified exactly all p.

**Step 2 [L1 — VERIFIED 86/86, NOT yet proven].** `|Σ_{x∈T+} χ2(x)| = F4`, where
`F4 := Σ_{p/4 < a < p/2} χ2(a)`. The hexagonal-triangle character sum equals, in magnitude, the
quarter-interval character sum. Checked exactly on all 86 primes p≡3 mod4, p≡1 mod6, p<2500.
(Sign of FLD at p≡19 mod24 is +/−, possibly σ-orientation-convention dependent; not in the
magnitude law.)

**Step 3 [PROVEN here].** `F4 = 0` at p≡7 mod8; `F4 = D` at p≡3 mod8, where `D := Σ_{0<a<p/2}χ2(a)`.
*Proof.* Let E4 = Σ_{0<a<p/4}χ2(a), so E4+F4 = D. Since χ2 is nontrivial, Σ_{0<b<p}χ2(b)=0.
The even residues: Σ_{even 0<b<p}χ2(b) = Σ_{a=1}^{(p−1)/2}χ2(2a) = χ2(2)·D. Split the even b at p/2:
(i) even b∈(0,p/2) are b=2a, 0<a<p/4, contributing χ2(2)·E4; (ii) even b∈(p/2,p) are b=p−c with c
odd, 0<c<p/2, contributing −Σ_{odd 0<c<p/2}χ2(c) = −(D − χ2(2)E4) [using χ2(−1)=−1, p≡3 mod4, and
(i)]. Summing: χ2(2)D = χ2(2)E4 − (D − χ2(2)E4) = 2χ2(2)E4 − D, so **E4 = D(1+χ2(2))/(2χ2(2))**.
Thus χ2(2)=+1 (p≡7 mod8) ⇒ E4=D, F4=0; χ2(2)=−1 (p≡3 mod8) ⇒ E4=0, F4=D. ∎

**Step 4 [CITED — Dirichlet].** `D = (2 − χ2(2))·h(−p)` for p≡3 mod4 (class number of ℚ(√−p)).
Verified exactly all p (`Dok=True`).

## Consequence
p≡1 mod6 splits mod 24 into {1,7,13,19}. FLD=0 at 1,13 (p≡1 mod4, Step 0) and at 7 (p≡7 mod8 ⇒
F4=0, Steps 1–3). At p≡19 mod24 (= p≡3 mod8 ∧ p≡1 mod3): F4=D=3h (Steps 3–4, χ2(2)=−1), so
**|FLD| = 2F4 = 6·h(−p)** (Steps 1–2). Matches the empirical law (34/34 nonzero, 103/103 zero, v1).

## What is now proven vs open
- PROVEN: Steps 0, 1, 3. CITED: Step 4 (Dirichlet).
- OPEN — exactly ONE lemma, **L1**: `|Σ_{T+}χ2| = F4`. A character-sum identity between the
  2D hexagonal flap triangle T+ (⊂ F_p via the Eisenstein lift, |T+|≈p/8) and the 1D quarter
  interval (p/4,p/2) (≈p/4 points). Different supports, equal magnitude — so it is a genuine
  identity, not a set bijection; likely both equal ±D through the μ3/lattice structure.

## L1 exploration (`_fld_L1_explore_v1.py`) — why it resists elementary reduction
- The flap coordinate `t(X) = p(u−v)` is an integer in (−p,p) with **t(X) ≡ M·X mod p, M constant**
  per prime (verified). But t = c(s₁X) − c(s₂X) is a DIFFERENCE of two centered sawtooths, so T+ =
  {t > p/2} ⊆ {X : MX mod p ∈ (p/2,p)} with an extra **branch condition** on the individual
  sawtooths — a genuinely 2D condition.
- The p points (c(s₁X), c(s₂X)) lie on a **line in the torus (Z/p)²**; T+ = those in the triangle
  {A−B > p/2}. So Σ_{T+}χ2 is a character sum over **(lattice-line ∩ triangle)** — a union of
  **6–33 scattered runs** in the MX-coordinate, the run count tracking the continued fraction of
  s₂/s₁. Not a single interval image.
- **The elementary levers fail (checked):** no multiplier c stabilizes T+ with χ2(c)=−1 (so the
  p≡7 mod8 zero is NOT an elementary multiplicative involution — the triangle's own symmetry
  (u,v)→(−v,−u) lifts to an X-map only if s₂≡±s₁); and no c maps T+ onto (p/4,p/2) (so the two equal
  sums are NOT a set correspondence — they meet through h).
- **The a→2a fold IS live on T+ (`_fld_L1_fold_v1.py`)** — RETRACTS the earlier "needs analytic
  machinery" verdict (that was three failed set-stabilizer/interval probes generalized into a regime
  claim). The centered residue obeys `c(2y)=2c(y)−p·e(y)`, e the p/4-crossing indicator, so the flap
  coordinate satisfies **`t(2X) = 2t(X) − p·D(X)`** exactly (verified), D(X)=e(au)+sgn·e(bv) the two
  quarter-crossings — the SAME p/4 thresholds F4=Σ_{(p/4,p/2)}χ2 counts. The fold self-consistency
  **`χ2(2)·S+ = Σ_X χ2(X)·1{t(2X)>p/2}`** holds exactly at every prime (S+=Σ_{T+}χ2). So L1 is in the
  SAME elementary regime as L2, not an analytic one.
- **First-moment thread — CHECKED, and it DISSOLVES (does not bridge to S+).** A prior draft here
  claimed the fold's first moment `T1=Σ_X χ2(X)t(X)` gave a new route via `Σχ2(a)c(a)=0` and
  `Σa·χ2(a)=−p(2−χ2(2))h`. Both were WRONG (unchecked, and generalized from four p≡3 mod8 primes).
  Corrected & verified: `Σa·χ2(a) = −p·h` (120/120, the standard formula); the fold carry `k = σ`
  exactly; so `Σχ2(a)c(a) = Σa·χ2(a)+pD = p(1−χ2(2))h`, and `T1 = χ2(M)·p(1−χ2(2))h + p·FLD`. The
  "carry sum" is therefore just FLD plus a Dirichlet term — **no independent handle on S+**. The
  relations `3T1=4pS+`, `T1/p=±4h` hold but are consequences of FLD+Dirichlet, not a new route.
- **Status of L1:** VERIFIED 86/86, NOT proven. No derivation of `S+=±F4` is currently in hand: the
  routes tried (single-interval image, multiplicative set-stabilizer, first-moment/carry fold) did
  not close it. No difficulty verdict either way — neither "needs analytic machinery" (retracted)
  nor "elementary and reachable" (retracted as unearned). It is an open lemma with a sharp statement
  and strong numerical support.

## The FLD sign (followed the lead; door did not open)
- **`T1 = χ2(M)·p(1−χ2(2))h + p·FLD`** verified 55/55 (M = the flap-coordinate slope, t(X)≡MX mod p).
  Confirms the first-moment "dissolution": T1 is FLD plus a Dirichlet term, no independent handle on S+.
- **`sign(FLD) = −χ2(M)`** verified 54/54 (p≡19 mod24, down to p=19). A sign-pinning consistency;
  convention-robust (orientation flip sends t→−t, M→−M, FLD→−FLD, both sides flip together).
- **But it does not reduce to an intrinsic invariant.** χ2(M) matches none of ~10 characters /
  π_p-component forms; sign(FLD) matches none of ~8 intrinsic cubic invariants (sign(L)/χ2(L) from
  4p=L²+27M², χ3(2), p mod48, …) — all ~coin-flip. So the sign-pinning is (so far) an internal
  consistency between two reduced-basis-dependent quantities, NOT a deeper arithmetic symmetry, and
  it does NOT refute the earlier "sign possibly convention-dependent" flag. Decisive open check: does
  sign(FLD) flip under a basis-chirality change (π_p ↔ π̄_p)? Not yet run. The **magnitude** |FLD|=6h
  is the intrinsic result; the sign is the murky, likely convention-internal part.

## Scope / exactness
Exact integers throughout (σ, χ2, h by reduced-form count). p∈[100,2500), p≡1 mod6, 86 primes at
p≡3 mod4. No float in the signal path. Steps 0/1/3 are exact algebra; Step 2 (L1) is empirical.
