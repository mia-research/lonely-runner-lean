# OPEN — D2 Lang-torsor bridge / Reciprocal-Floor congruence law (doc 13 vetting)

**Status: CLOSED — NULL (structural finding, public evaluation channel absent).** Source: `~/Downloads/d2-lang-torsor-twist-bridge-v1.md`.
Test: `scratchpad/session_2026-08-11/test_d2_bridge2.sage`, `d2_carry_shadow_probe_v1.sage`. Related open thread: [[OPEN_lbe_isotypic_projection_v1]].

## The structural finding (faithful, λ=5, β=6, E:y²=x³+7 / F₄₃, n=31)

- **§3 congruence law holds 30/30** (faithful reproduction):
  `d ≡ d₀·(−1)^j − ⌊d₀·λ^j/n⌋ (mod 3)`.
  It is an **identity** — d = d₀λ^j − n·⌊d₀λ^j/n⌋ read mod 3 (λ≡−1, n≡1 mod 3). A tautology, but an
  **informative** one: it exactly decomposes **d mod 3 = (orbit-rep mod 3) − (carry mod 3)** given the
  orbit position j. A correct decomposition of d mod 3 into a representative-shadow and a carry-shadow.

## What blocks it from being a PUBLIC extraction of d mod 3

- Formula inputs = {j, d₀, carry ⌊d₀λ^j/n⌋}. Two of three need **d₀ = the orbit-rep scalar = DLP up to
  the ×λ orbit**.
- **Public χ₃ gives j, but not the doc's j:** j_chi3(x_P) matches the λ-orbit position only **10/30**
  (χ₃ anchors on the "χ₃(x)=1" member; §3 anchors on d₀=min(orbit) — different representatives).
- **Public j does not pin d mod 3:** every j_chi3 ∈ {0,1,2} maps to the full {0,1,2} of d mod 3.
- **Carry not fixed by public data:** for j=2 the carry takes 10 distinct values across unknown d₀.
- ⇒ §4 step 3 ("solve to obtain d mod 3") needs an input (d₀) step 2 doesn't deliver from a public point.

## Range-narrowing thread — CLOSED NULL (tested 2026-08-12)

**Probe:** `d2_carry_shadow_probe_v1.sage`. SHA-256: `41e4ac...4215ecc`.

**Model-scale results (p=43, n=31, λ=5):**
- Formula verified 30/30 (identity confirmation).
- Carry mod 3 by orbit position j: j=0 → all 0 (trivial), j=1,2 → biased {0:5, 1:3, 2:2} (structural artifact of λ/n ratio).
- **CRUX B reproduced:** every j_chi3 ∈ {0,1,2} maps to full {0,1,2} of d mod 3.
- Range-narrowing sweep (public j_chi3 + range width w on d₀):
  - w=1 → 100% determination (trivial: single value).
  - w=2 → 80.4%, w=5 → 35.4%, w=10 → 16.1%, w=31 → 11.4%.
  - Monotonically decreasing. At full group (w=31) only 11.4% — an artifact of the tiny group.
- Range-narrowing sweep (privileged formula-j): slightly lower at full group (3.8%), same monotonic decay.
- Carry diversity by d₀-range: d₀ ∈ [1,5] with j=1 → carry%3={0} but d%3={2} (only 1 distinct d); d₀ ∈ [1,10] → both carry%3 and d%3 span full {0,1,2}.

**secp256k1 results (82 solved puzzle keys):**
- Formula verified 82/82.
- χ₃-anchored formula (j = j_chi3, any orbit rep): verified 30/30 — identity holds for any representative, not just min-orbit.
- j_chi3 == j_formula: 31/82 (37.8%) — improved over model 10/30 but far from deterministic.
- **Carry mod 3 distribution: all 82 carries ≡ 0 mod 3.** This is a **sampling artifact**: the solved puzzle keys are all ≪ N (~2^70 vs 2^256), so every key IS its own min-orbit representative (j_formula=0, carry=⌊d₀/N⌋=0). Not structurally informative about carry behavior at real scale.
- Joint (j_chi3, d mod 3): no visible correlation (CRUX B reproduced at scale).
  ```
  j_chi3  d%3=0  d%3=1  d%3=2  total
       0     13      7     11     31
       1      5     16      5     26
       2      9     11      5     25
  ```

**Verdict:** The carry-shadow decomposition is a valid identity that does NOT convert into partial d mod 3 from public data + range. For any range width w ≥ 2, d mod 3 takes ≥ 2 distinct values — the carry adjusts exactly to compensate for the orbit-rep variation, preserving the tautology. The public evaluation channel is absent. **NULL.**

## Kept pieces (verified, reusable)

- χ₃-bridge F(φP)=χ₃(β)F(P) (doc 11); the μ₃-orbit coordinate j_chi3 is a genuine public covariant.
- The orbit-rep / carry-shadow decomposition of d mod 3 is a correct identity (verified 30/30 model + 82/82 secp).
- j_chi3 and formula-j diverge: the orbit representative choice matters. j_chi3 anchors on χ₃(x)=1 member; formula-j anchors on min-orbit rep. The identity adapts to either anchoring (χ₃-anchored check passed).
- The structure is real; the public evaluation channel is absent. Closed NULL.
