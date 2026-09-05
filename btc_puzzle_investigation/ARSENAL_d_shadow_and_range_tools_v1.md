# ARSENAL — d-shadow & range-reduction tools (from the Downloads LBE/curve batch vetting)

**Purpose.** Collect every *conditional* tool that locates a **shadow of d** (a decomposition
component) or **reduces the range of d**, so that when a genuine leak channel from the **x/y curve
coordinates** appears, we can compose it into a real constraint. Each tool below is currently gated on
an input that needs the DLP — but a partial x/y hint on that input converts the tool into partial d.
Partial info is useful (puzzle): even a few bits / a range cut matters.

Related open threads: [[OPEN_lbe_isotypic_projection_v1]], [[OPEN_d2_congruence_law_v1]].

## Tools (verified structure; gate = what a future hint must supply)

1. **μ₃-orbit coordinate j (PUBLIC).** j = χ₃(x_P)-position in the GLV orbit; F(P)=χ₃(x_P)y_P obeys
   F(φP)=χ₃(β)F(P). ~1.58 bits, computable from P alone. *Gate: none — already public.* (docs 11/13)

2. **Isotypic projection Q_W ∈ A_new.** S=Q₀+β²Q₁+βQ₂ is a genuine ζ₃-eigenvector (σ(S)=[k]S,
   k³≡1, verified F₄₃, k=1849). dlog(S([d]G)) is injective but non-linear in d. *Gate: whether it
   narrows d at scale — OPEN.* (doc 11)

3. **mod-3 decomposition identity.** d ≡ (−1)^s λ^j d₀ − c·n (mod 3), exact (30/30, and 11/11 curves
   p≡7 mod12). Decomposes **d mod 3 = (orbit-rep shadow) − (carry shadow)**. *Gate: needs d₀ and
   c=((−1)^s d₀λ^j−d)/n (both need d). A hint giving partial d₀ or c → partial d mod 3.* (docs 13/14)

4. **GLV-lattice BDD geometry.** For j=1,2, knowing carry c pins d₀ to **1–3 candidates**
   (interval size n/λ^j ≈ 1.47, 3.1). = the known GLV/Babai half-lattice (~2¹²⁸, not a break by itself).
   *Gate: needs c. A hint on c (even a few high bits) → tight d₀ interval.* (doc 14 §3)

5. **Fractional-part identity.** {(−1)^s d₀λ^j / n} = d/n exactly ⇒ **upper bits of d = upper bits of
   the scaled-representative fractional part.** *Gate: needs d₀.* (doc 14 §3)

6. **μ₆ saturation boundary (a LIMIT to respect).** Aut(E)≅μ₆ (j-invariant 0) ⇒ no order-9
   automorphism ⇒ point-automorphism extraction caps at **mod 6** (j mod 3 × s mod 2 ≈ 2.58 bits).
   Bounds how much *this class* of method can ever give from automorphism structure alone. (doc 14 §2)

7. **Joint-carry boundary bit ε (~3-bit shadow of an unknown key).** For a known key d₁ + unknown d₂:
   c_sum = c₁+c₂+ε, ε=[r₁+r₂≥n] (identity, 6/6). ε is a boundary bit linking known r₁ to unknown
   r₂=d₂λ^j. *Ceiling measured:* all 6 (s,j) branches remove only ~1.4 bits (frac 0.389 of the range),
   and ε(s=1,·)=1−ε(s=0,·) ⇒ only **~3 independent bits**. *Gate: ε needs d₂ (c_sum contains d_sum);
   currently zero. If an x/y channel makes ε measurable → ≤3 bits on d₂.* (doc 16)

## Verified structural facts / corrections to earlier docs (doc 18, p=43 tested)

- **ζ₄ cover mechanism is CURVE-INDEPENDENT.** e₁=0 and e₃=0 (e₃=−p·e₁) on the cover w⁴=x³+Ax+B
  hold for CM *and* non-CM base curves at p≡3 mod 4 — driven by the order-4 automorphism ζ₄:(x,w)↦(x,iw),
  not CM. **Corrects doc 7's "perfect-square splitting uniquely mediated by μ₃/CM."**
- **Census sign is +p:** e₂=e₁²+p (doc 18, my c₂ proof) — **corrects doc 10's e₂=e₁²−p.** But NOT
  universal over a: in the vary-constant family e₂∈{+p,−2p,0,+2p}; census holds only for the a with
  e₂=+p (the non-residue a). Doc 18's "100% all a" is overclaimed.
- **The LBE attack channel is CM-gated.** GLV (βx,y) on-curve ⟺ A=0 (j-invariant 0). Cover symmetry is
  universal; the extraction gate (orbit j, carry c) needs the GLV endomorphism ⇒ needs CM. secp256k1
  qualifies (A=0); generic non-CM curves do not. Correct scoping of the attack surface.

## What is NOT yet in hand (the missing link)

Every tool above is gated on **d₀ or the carry c**, which currently require the DLP (circular).
The **range-constrained carry** thread (a known bit-range on d₀ ⇒ partial c) is the one non-circular
path; quantitatively weak for wide puzzle ranges (~2⁶⁸ carry values at k=70) but **not closed**.
The arsenal pays off the moment an x/y-coordinate channel supplies any of: reliable s, a partial
carry c, a partial d₀, or a raw bit of d — then tools 3–5 amplify it.

### ★ PRIORITY OPEN THREAD — a possible PUBLIC route to the correction bit ε (doc 19 §4A)

**The candidate missing link.** Doc 19 §4A ("Inradius Core Exclusion") claims: the Eisenstein lift
norm s = N(eis(X))/p ∈ [0, 3/4]; the flap-rate is **zero for s < 3/16**; therefore **if a public
point's lift norm s < 3/16, the correction bit ε is forced to 0**. IF (a) the lift norm s is genuinely
computable from the public x-coordinate, and (b) the "s<3/16 ⇒ ε=0" gate holds, this would supply ε —
or at least ε=0 for a fraction of points — **from public data alone**, which is exactly the input
tools 3, 5, 7 need (docs 13/16 required ε and could not get it without d). That would make the
circular pieces non-circular for the covered points.

**Why it is only a candidate:** the `eis(X)` (Eisenstein lift) construction is **not specified** in
doc 19, so the claim is UNTESTED. **To do:** obtain/recover the eis(X) map, then test — over a small
p — (1) is s=N(eis(X))/p computable from x alone? (2) does s<3/16 ⇒ ε=0 hold with a firing control?
(3) what fraction of points fall in the s<3/16 core (i.e. how often ε is pinned)? A scoped null here
is still a scoped null; a positive here is the amplifier that lights up the whole arsenal.

Also verified (doc 19 §2A): **V₁(a)=Σχ₂(y_d)e_n(ad) is purely imaginary on CM AND non-CM curves**
(= the doc 9 §2 object, now shown universal); census structure e₂=e₁²+p (imaginary e₁) is consistent.

## Bookkeeping honesty

None of these is a leak on its own; each is a **conditional amplifier**. The 82 solved keys all give
c=0, j=0, s=0 (small ⇒ own orbit min) ⇒ tools 3–5 give **no** constraint on them as-is. Keep the tools;
do not restate the conditional as an achieved reduction.
