# RESULT — the Kummer-cover family carries **at most `log₂3` bits** about the curve constant

*2026-07-23. Runs `PREREG_kummer_family_b_capacity_v1.md`; deviations in
`PREREG_kummer_family_b_capacity_v1_DEVIATIONS.md` (**six — read them, two are defects in the spec and
one is a script bug that nearly produced a false falsification**). Scripts: `scratchpad/kummer_cap2.py`,
`cap_followup.py`. Exact integer / cyclotomic arithmetic; no float in the signal path.
**No leakage, key-recovery, or ECDLP claim is made or implied.***

---

# 1. The bound `[PROVED — UNREVIEWED]`

For `χ_d` of exact order `d | q−1` and `S_d(b) := Σ_{x∈F_q} χ_d(x³+b)`, substituting `x → cx`:
```
(★)   S_d(c³b) = χ_d(c)³ · S_d(b)          for every c ≠ 0
```
The orbits of `b ↦ c³b` are the cosets of the cubes — **exactly 3 of them**. So `S_d` is determined on
each orbit by its value at one representative, times an explicit factor.

Every isogeny-type invariant of every isotypic piece of every cover `w^k = x³+b` is a function of the
`S_d`, `d | k`. Therefore:

> **The entire Kummer family `{w^k = x³+b}` — every `k`, every piece — depends on `b` only through the
> cubic class of `b`, i.e. carries at most `log₂3 ≈ 1.585` bits about `b`.**

**Verification `[227016/227016 exact, zero violations]`** — all `b`, all `c`, `d ∈ {2,3,4,6,12}`,
`p ≡ 1 mod 6`, `11 ≤ p ≤ 120.`

⚠ **That 227016/227016 is an INSTRUMENT CHECK, not evidence** — `(★)` was derived and pre-registered as
derived precisely so a confirmation could not be miscounted (prereg §1). **The bound is carried by the
derivation; the count only says the code implements it.**

⚠ **Upper bound only, and not tight.** Control C2 shows the three cubic classes are *not* fully
separated at `d = 4, 6` (33.33% cross-class collision) — so at those `d` the real capacity is **lower**
than `log₂3`. By the spec's own §5 pre-commitment **those two arms are VOID** (D3). The bound's
direction is unaffected: void arms cannot raise capacity.

## 1.1 What this settles, and what it does not

**Settles:** the `28`-deflation of `RESULT_mu3_cover_jacobian_v2.md` was not a one-off. **No cover in
this family can encode anything about `b = 7` beyond `χ₃(7)`** — one of three values. The family is
closed as a source of curve-constant-specific structure, **by a proof rather than by exhaustion.**

**Does not settle:** the **`p`-dependence** — supersingularity of the `d=4` part at `p ≡ 3 mod 4`, the
`m`-law, the `p mod 12` splits — is untouched and is *not* bounded by this. The bound is about `b` only.

**No `d`-side content.** These are curve-side CM objects. Nothing here bears on leakage in either
direction.

---

# 2. `k = 12`: at secp's congruence class it reduces to the `μ₄` mechanism  `[EXPLORATORY — outside the registered scope, D6]`

`k = 12` was named as "the only place the `μ₄` and `μ₆` mechanisms can interact". At secp they do not
interact — **the `d = 12` part inherits the `d = 4` mechanism outright.**

- `C₁₂ : w¹² = x³+b` has genus **10**; the isotypic dimensions are `d=2 → 1`, `d=3 → 1`, `d=4 → 2`,
  `d=6 → 2`, **`d=12 → 4`**.
- secp has `p ≡ 7 mod 12`, so `12 ∤ p−1` and **`χ₁₂` does not exist over `F_p`** — exactly the situation
  that drives §A1.1 (`p ≡ 3 mod 4` ⇒ no `χ₄` over `F_p`).
- Frobenius permutes the four order-12 characters by `j ↦ 7j mod 12`: `{1,7}` and `{5,11}` — **two
  2-cycles, all blocks off-diagonal ⇒ trace 0 ⇒ `b₁ = 0` for the `d=12` part.**
- **Numerical confirmation:** `#affine(w¹² = x³+b) = #affine(w⁶ = x³+b)` for **every** tested `(p,b)`,
  `p ∈ {19,31,43,67,79,103,127,139}` (those `≡ 7 mod 12`) — i.e. the `d=12` part contributes exactly
  `0` to `a₁` over `F_p`.

> **At secp, both the `d = 4` and the `d = 12` parts are trace-free, by the same mechanism: their
> characters are not defined over `F_p` and Frobenius permutes them in 2-cycles.** `k = 12` is therefore
> not a new mechanism — it is the `μ₄` mechanism again, on a 4-dimensional piece.

---

# 3. Process record — what the rigorous frame actually bought

Three things, each of which would have been a false claim without it:

1. **A derived prediction caught a code bug that the pre-committed reading would have called a
   discovery.** The first run said P1 was violated 205 500 times; the pre-registered conclusion for that
   outcome was *"residual `b`-structure exists — a positive, the interesting outcome."* The violation was
   a wrong character index (D1). **Registering `(★)` as *derived* is what made a "positive" implausible
   enough to check the instrument first.**
2. **A control voided part of my own frozen spec.** C2 fails at `d = 4, 6` (D3), and the spec's own §5
   says that voids the arm. The bound survives only because it rests on the derivation, not on the arm.
3. **A post-hoc explanation was refuted by its own output.** I printed a "pigeonhole at small `d`" story
   before the per-`d` numbers existed; `d=2` came back 0.00% and the 33% sits at `d=4,6` (D4). **The
   33.33% is unexplained and stays open** — do not carry the story forward.

Also recorded: this is the **third** broken-instrument near-miss in this session (the others: a cube-root
routine valid only for `p ≡ 2 mod 3`; a first-pass audit that manufactured a false negative). In all
three the failure mode was identical — **a negative produced by my own code, one step from being written
up as a finding.**

---

# 4. What remains open

1. **The 33.33% cross-class collision at `d = 4, 6`** — unexplained; a mechanism, not a nuisance.
   Needs its own prereg.
2. **`k = 8`** (genus 7, new part dim 4) — untouched. `8 ∤ p−1` at secp (`p ≡ 7 mod 8`), so the same
   character-not-over-`F_p` mechanism is the prior; unverified.
3. **The `p`-dependence of the family** — explicitly outside this bound.
4. **Whether `ε` relates to the covers by anything beyond the shared argument `4b`** — carried forward
   from `RESULT_mu3_cover_jacobian_v2.md` §5, unaddressed.
5. **The conductor / volcano deformation family** (`RESULT_mu6_cover_and_conductor_v1.md` §2) — the one
   remaining direction in this area that is *not* bounded by §1, because it varies the endomorphism
   lattice rather than the curve constant.
6. **Priority checks** — none run on any of this.

---

*Grades: §1's `(★)` and the capacity bound `[PROVED — UNREVIEWED]` (my derivation, no adversarial pass);
its `227016/227016` `[VERIFIED — instrument check, not evidence]`. §2 `[DERIVED + VERIFIED, EXPLORATORY —
outside registered scope]`. C2 arms at `d = 4, 6` **VOID** per the spec's own pre-commitment. The scan
scope `p ≤ 120` is governed by frontier §XI.5's scale banner; §1's bound, being a derivation, is
scale-free.*
