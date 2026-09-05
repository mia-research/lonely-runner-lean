# Failure of the Bounded Persistence Theorem for k ≥ 3
## v1 — Session B (2026-03-10)

**Purpose:** Document why the attempt to close Tier 2 via
"TC fibres are within P(k) steps of a chamber entry sM" is wrong.
One correction, one mechanism, two numerical checks, one replacement target.

---

## 1. The Variable Error That Invalidates v1

In `lrc_transport_completeness_v1.md` §1, the floor state was written as
    t_e = ⌊b/e⌋.

**This is wrong.** The LRC framework (as used throughout the draft, e.g., §9.1,
CO-3 line 91) defines the floor as
    q_e(b) = ⌊eb/L⌋  (runner e's lap count at position b).

The two variables are related by q_e(b) ≈ e²/L at b ≈ e, NOT q_e ≈ 1.
All downstream definitions (ACS, P-SYNC, persistence bounds) in v1 are unreliable.

---

## 2. Consequence: Frozen Intervals Are Not Bounded

With q_e(b) = ⌊eb/L⌋:
- Runner e=1 has q_1(b) = ⌊b/L⌋ = 0 for ALL b ∈ B_div ⊂ (0,L). No floor
  changes. bad(1, 0, p^k) = {0, p^k-1} throughout B_div.
- Runner e=n-1 (fastest unit): floor changes every L/(n-1) steps. Total
  floor changes in B_div ≈ (n-1)(n-2)/n ≈ n-1 changes.

**Persistence mechanism:** A dangerous state at b=sM stays TC as long as no
floor change exposes an uncovered residue. A floor change of runner e removes
residue r = -(q_e+1)e^{-1} from e's bad set and adds r' = -(q_e+2)e^{-1}.
TC persists if r' is already covered by another runner and r = r'.

**Lower bound on dangerous interval length:** The first floor change after sM
is at distance δ_min = min_e (distance to e's next floor change). For the
fastest runner e = n-1 ≈ p^k: δ_min = L/(n-1) - sM mod L/(n-1) ≈ L/n.

**But TC need not break at the first floor change.** If n-1 runners change
floor before any residue is exposed, the dangerous interval has length >> L/n.

---

## 3. Numerical Verification of Failure

**n=27 (p=3, k=3):** L = lcm(units of Z_27) ≈ 3.2 × 10^9. M = L/3 ≈ 1.07 × 10^9.

Drop pair {3, 6}: 64 distinct dangerous intervals in B_div after the lower band.
Some intervals extend > 10^9 fibres from the nearest chamber entry sM.

Specifically: the interval starting near b ≈ 2M contains a dangerous stretch of
length ≈ M/2 ≈ 5 × 10^8. This is far from any single-point chamber entry and
extends for half a full period. The bounded persistence theorem
    |b - sM| ≤ P(3)  (for any fixed P independent of L)
is FALSIFIED: P would need to be Ω(L/n) = Ω(10^9), which grows with L.

**n=125 (p=5, k=3):** Same phenomenon at larger scale. Drop {5,10}: dangerous
intervals with length ≈ M/3 appear far from chamber entries.

**Conclusion:** The bounded persistence theorem is false for k≥3. The dangerous
geometry is NOT concentrated near chamber entries — it extends into the interior.

---

## 4. What Survives from v1

- **Prop 1 (F_p×-orbit):** Chamber entries b=sM (s≠0) are TC. Proved by scaling
  covariance. Not contradicted — it is still true that chamber entries are TC.
  The problem is that TC extends FAR BEYOND these entries.

- **Prop 2 (s=p-1, k=2 only):** For n=p², no non-unit runner reaches dangerous
  floor in the s=p-1 period (proved analytically in `lrc_prime_power_persistence_v1.md`).
  Still valid for k=2. Does not extend to k=3 (j=p+1 counter-example).

- **CO-3 (Tier 2 for n=p², p≥5):** Independently proved by the interval counting
  argument. Not affected by v1's variable error.

---

## 5. The Replacement Target

The correct theorem to prove is a **chamber density theorem**, not a persistence bound:

**Theorem (Chamber Density, to prove):**
For n=p^k (k≥3) under U-FORCE B3b:

    |{b ∈ B_div : τ(b) is TC}| / |B_div|  ≤  f(k, p) < 1

where f(k,p) → 0 as p → ∞ (holding k fixed), and 1 - f(k,p) ≥ 1/p > φ(n)/|B_div|.

Consequence: |safe fibres| ≥ |B_div| × (1 - f(k,p)) ≥ |B_div|/p >> φ(n). □

**Why this avoids the persistence problem:** The density bound does not require
TC to break quickly — only that TC fibres are sparse IN TOTAL. Even if TC persists
for Ω(L/n) consecutive fibres, as long as those dense dangerous blocks account for
≤ f(k,p) fraction of B_div, the bound follows.

**Key difficulty:** Proving the density bound requires understanding how TC fibres
are distributed across ALL s-periods, not just near chamber entries.
See `lrc_transport_completeness_v2.md` for the proof framework.
