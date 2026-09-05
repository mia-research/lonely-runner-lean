# PRE-REGISTRATION — construct and verify the dual 3-isogeny `φ̂`

*Filed 2026-07-24, **frozen before any fix code is written.** The previous attempt (`reduction.py`) had a
buggy `φ̂` and printed a false "efficiently invertible" conclusion; this pre-registers the fix with
explicit falsification and firing controls, per CLAUDE.md §3. Curve/CM arithmetic; no ECDLP or
key-recovery claim. Not to be recorded to memory until the user has viewed the result.*

## 0. Object and claim

`φ : E → E'` a 3-isogeny over `F_p` (`E : y²=x³+2`, `E' : y²=x³+12x+12`, `p=13`, kernel `x₀=7`). The dual
`φ̂ : E' → E` is the unique isogeny with **`φ̂ ∘ φ = [3]_E`** (`3 = deg φ`).

**Claim to be tested:** a correctly constructed `φ̂` satisfies `φ̂(φ(P)) = [3]P` for **every** `P ∈ E(F_p)`,
and `φ(φ̂(Q)) = [3]Q` for every `Q ∈ E'(F_p)`; consequently `φ^{-1} := [3^{-1} mod n] ∘ φ̂` satisfies
`φ^{-1}(φ(P)) = P` and `φ(φ^{-1}(Q)) = Q` for all points.

## 1. Pass conditions (all must hold)

- **P1** `φ̂(φ(P)) = [3]P` for **all** `P ∈ E(F_p)` (0 exceptions).
- **P2** it is specifically `[3]`, not another degree-9 endomorphism: on a generator `G`,
  `φ̂(φ(G)) = [3]G` **and** `≠ [k]G` for `k ∈ {1,2,4,-3,6,9}` (rules out `[±3]·unit`, identity-by-luck).
- **P3** `φ(φ̂(Q)) = [3]Q` for all `Q ∈ E'(F_p)` (dual composition, other side).
- **P4** `φ^{-1}(φ(P)) = P` and `φ(φ^{-1}(Q)) = Q` for all points.

## 2. Firing controls (pre-specified — each MUST fail, proving the checks have power)

The construction has a normalization step (`j(E)=0 ⇒ Aut(E)=μ₆`, so `φ̂_raw ∘ φ = [3]·α` for a single
`α ∈ μ₆`; the correct `φ̂` composes `φ̂_raw` with `α^{-1}`, calibrated on ONE point). To prove that
"calibrate on one point, verify on all" is not vacuous:

- **C1 — wrong kernel.** Build `φ̂'` from a **different** `ψ_3^{E'}` root (not the dual's kernel). For
  **none** of the 6 `μ₆` normalizations may P1 hold on all points. *(If some normalization rescues a wrong
  kernel, the test is vacuous — VOID.)*
- **C2 — wrong scalar.** `φ^{-1}` built with a **wrong** modular inverse `[k]·φ̂`, `k ≠ 3^{-1}`, must
  **fail** P4. *(Confirms P4 depends on the exact scalar.)*
- **C3 — identity check.** The map `Q ↦ Q` (identity `E'→E'`, not an isogeny to `E`) must **fail** P1
  (`φ̂` must actually change curves). Trivial guard against a no-op.

**If any control fails to fire, the run is VOID and no conclusion is drawn.**

## 3. Falsification

The construction is **wrong** if, after selecting the `μ₆` normalization by calibration on one point, P1
fails at **any** other point — because the true discrepancy `φ̂_raw∘φ / [3]` is a single point-independent
automorphism, so the correct normalization works everywhere or the kernel is wrong. A single surviving
counterexample falsifies.

## 4. Scope (fixed in advance)

- Verified at `p=13` (the `E'` above) **and** at a **second** independent small descending prime found by
  the same search (`3∤#E`, rational descending 3-isogeny, `j(E')∉{0,1728}`) — so the result is not a
  `p=13` fluke.
- All arithmetic exact `mod p` (Python `int`). The construction generalizes (Vélu + dual), but is
  **verified only at these small primes**; no secp-scale numerical claim.

## 5. Method, and the bug hypothesis (stated so the fix is not tuned to confirm it)

- `φ̂_raw : E' → E''` via Vélu from the dual kernel `x₁` (the `ψ_3^{E'}` root whose Vélu target has
  `j=0`). Then a twist isomorphism `E'' → E`, `(x,y) ↦ (u²x, u³y)`, sends `y²=x³+B''` to `y²=x³+u⁶B''`.
- **Bug hypothesis (my prior, to be tested — NOT assumed):** the previous code used `u⁶ = B''/2`; the
  correct normalization to reach `y²=x³+2` is **`u⁶ = 2/B''`** (`u⁶·B'' = 2`). Additionally, `μ₆` gives 6
  valid `u`; the one making `φ̂∘φ=[3]` must be selected by calibration (§2/§3).
- **The prereg tests whether the FIXED `φ̂` satisfies P1–P4, not whether my bug guess is right.** If the
  corrected `u⁶` still fails P1 at some point after trying all 6 normalizations, the fix is declared
  **failed** and the cause re-investigated — not patched to pass.

## 6. What this does and does not establish

- **Does:** `φ` is efficiently *invertible* (`φ̂` cheap + one scalar), completing the **other** direction
  `DLP(E') ≤_poly DLP(secp)` of the equivalence. (The lever direction `DLP(secp) ≤_poly DLP(E')` needs only
  forward `φ` and is a separate, already-run item — **not** re-claimed here.)
- **Does NOT:** say anything about secp's absolute ECDLP hardness; nor is it verified at secp scale (small
  `p` only); nor does it touch the frame-operator or any other result.

*Frozen. Any change after the first fix-run is logged as a deviation in
`PREREG_dual_isogeny_v1_DEVIATIONS.md`.*
