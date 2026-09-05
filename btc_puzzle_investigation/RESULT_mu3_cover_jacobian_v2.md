# RESULT v2 — the μ₃ cover: the Jacobian stands; **the "28 link" is DEFLATED to an identity in `b`**

*2026-07-23. Supersedes `RESULT_mu3_cover_jacobian_v1.md`. §1 and §2 of v1 stand unchanged and are
restated only in summary; **v1 §3 is retracted and replaced by §3 below.** Scripts: `scratchpad/deflate.py`
(new), plus v1's. Exact integer arithmetic. No leakage, key-recovery or ECDLP claim.*

---

# 0. Verdict of the investigation

You asked whether the `28` link is really significant. **It is not.** Three independent deflations, each
verified:

1. **The link is an identity in the curve constant `b`** — it holds for *every* `y² = x³ + b`, at every
   `p ≡ 1 mod 6`. `10494/10494` `(p, b)` pairs. It carries **no secp-specific information**.
2. **All three "28"s are `4b` at `b = 7`.** The record's own source says so; the master's summary line had
   dropped the provenance, and I read the compressed form.
3. **The one free bit it does encode is a 1-in-3 coin with no consequence** — and its visible
   consequence (`Jac(C₃)` not prime order) had prior probability `5/6` anyway.

**What survives is the computation, not the interpretation.** §1–§2 below are unaffected.

---

# 1. What stands (from v1, unchanged)

- `C₃ : w³ = x³+7` is a smooth plane cubic, **genus 1**; `Jac(C₃) = Y² = X³ − 432·7² = X³ − 21168`,
  with `#C₃(F_p) = #Jac(F_p)` verified **106/106** primes `p < 600`.
- **At secp, by annihilation on 4 independent points, exactly one of the six sextic-twist orders fires
  and five do not** (discriminating control):
  ```
  #Jac(C₃)(F_p) = 115792089237316195423570985008687907852598652813156864395638497411212089444244
                = 2² · 3 · C253 ,    trace = 2a ,    closed form = (a−1)² + 3b² = N(π−1), π = a+b√−3
  ```
- `Jac(C₃)` is **not** secp, **not** isogenous to it (different trace), **not** prime order ⇒ **no
  amicable partner**. secp's own trace `a+3b` is odd ⇒ secp's Frobenius is half-integral in `ℤ[ω]`,
  `Jac(C₃)`'s is integral.

These remain `[VERIFIED — exact, full scale]` and are a genuinely new computed object.

---

# 2. Deflation 1 — the link is generic in `b` `[VERIFIED 10494/10494]`

Redo both derivations with a general constant `b`:

| object | condition | why |
|---|---|---|
| μ₆ cover `w⁶ = x³+b` | `N(S₁) = 4p ⟺ χ₃(4b) = 1` | ratio `r = χ₃(b)·χ₃(2)² = χ₃(4b)` |
| μ₃ cover `w³ = x³+b` | 2-torsion on `Y²=X³−432b² ⟺ χ₃(4b) = 1` | `432b² = 2⁴3³b² ≡ (4b)² mod cubes`; `gcd(2,3)=1` |

**Both sides are literally `χ₃(4b) = 1`, for every `b`.** Verified across **all `b ≠ 0` at every
`p ≡ 1 mod 6`, `11 ≤ p < 500` — 10494 `(p,b)` pairs, 0 failures**, on all three of: the measured μ₆
branch, the predicted `χ₃(4b)`, and the 2-torsion condition.

> **⇒ `28` is just `4b` at `b = 7`.** The "link" is a general fact about the family `y²=x³+b`, not a
> property of secp, of `7`, or of `28`. And because both sides *reduce to the same expression*, the
> equivalence is **trivially true once each side is derived** — the content lives in each derivation
> separately, and "one condition controls both covers" is a **restatement, not a finding**.

*(Unresolved and not claimed either way: whether the two `4`s have a common origin — Hasse–Davenport's
`χ̄(4)` factor on one side, `432 = 2⁴·3³` on the other. It may be one mechanism seen twice.)*

# 3. ★ Deflation 2 — RETRACTION: the "distinguished constant 28" was a compression artifact

**v1 §3 and `RESULT_mu6_cover_and_conductor_v2.md` §2 both claimed:** *"`28` was already a distinguished
constant here — Part IV's flap classifier `ε = ζ₆^{3−[28/π]₆}` and thread A's `χ(π) = −(28/π)₆⁻¹` — so
`28` now indexes two structures."* **Retracted.**

The record's own source, `aliquot_sextic.py:63`, states the rule with its provenance intact:
```
# exact rule (verified on all small primes):  epsilon = zeta6^(3 - [4D/pi]_6),  4D = 28
```
**`ε`'s `28` is `4D` — the same `4b`, at `D = b = 7`.** There is no coincidence and no second structure:
the μ₆ branch, the μ₃ 2-torsion, and `ε` all carry the identical argument `4b`.

**How the error happened, recorded because it is reusable.** `POSITIVE_FINDINGS_MASTER_v4.md:316` (and
v1/v2/v3 before it) summarise the rule as `ε=ζ₆^{3−[28/π]₆}` — **the `4D` is dropped and only the
evaluated `28` survives.** I read the master's compressed line, not the script, and a *parameter* looked
like a *constant*. This is exactly the failure mode named in my own provenance note two turns earlier
("one compression away from the object") and is the **fifth** time on this project that reading the
source dissolved something. **Fix at the record level: restore `4D` to the master's Part IV line in its
next version** — the bare `28` is an invitation to repeat this.

# 4. Deflation 3 — the free content is one 1-in-3 bit, with no consequence

Decompose `χ₃(28) = χ₃(7)·χ₃(2)²`:

| quantity | value at secp | status |
|---|---|---|
| `χ₃(7) = 1` ? | **no** | **FORCED — zero information.** `n` prime and odd ⇒ `E(F_p)` has no order-2 point ⇒ `x³+7` has no root ⇒ `−7` not a cube; `−1` is always a cube ⇒ `7` not a cube. |
| `χ₃(2) = 1` ? | no | free |
| `χ₃(28) = 1` ? | **yes** | ⟺ `χ₃(2) = χ₃(7)` — given the forced bit, a **1-in-3** event on the single free variable |

So the entire secp-specific content of §3 of v1 is: **one 1-in-3 coin landed.** And its stated
consequence — `Jac(C₃)` is not of prime order — was **already `5/6` likely**: of secp's six sextic
twists **exactly one** has prime order (verified). A non-prime twist is the default outcome, not a
finding.

---

# 5. What the investigation leaves

**Kept:** §1's computed object — `Jac(C₃)`'s identity, its exact 256-bit order, the closed form
`(a−1)²+3b²`, the integral-vs-half-integral Frobenius distinction, and the discriminating control. Also
kept: the μ₆ branch theorem `N(S₁) = 4p ⟺ χ₃(4b) = 1`, which is now stated in its correct generality
(v2 of that artifact says `χ₃(28)`; **read it as `χ₃(4b)`**).

**Dropped:** the "two covers link through 28" framing, the "`28` indexes two structures" claim, and any
suggestion that this says something about secp in particular.

**Still genuinely open, and untouched by this:**
1. `k = 8` (genus 7, new part dim 4) and **`k = 12`** — the only place the μ₄ and μ₆ mechanisms can
   interact.
2. Whether `ε` relates to the covers **by anything other than sharing the argument `4b`** — now a
   sharper question, since the shared constant is explained and is *not* evidence of a relation.
3. The conductor / volcano deformation family (`RESULT_mu6_cover_and_conductor_v1.md` §2) — untouched.
4. Priority check on any of it — not run.

---

*Grades: §1 `[VERIFIED — exact, control fired]`. §2 `[DERIVED + VERIFIED 10494/10494]`. §3 is a
**retraction** with a cited source line; do not re-claim the deflated form. §4 `[VERIFIED]`. Nothing in
this document is `[PROVED]` in the adversarially-reviewed sense.*
