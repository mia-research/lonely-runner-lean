# RESULT — the μ₃ cover `w³ = x³+7`: its Jacobian, computed at secp

*2026-07-23. Closes item (2) of `RESULT_mu6_cover_and_conductor_v2.md` §3. Scripts:
`scratchpad/c3_jac.py`, `c3_secp.py`, `c3_why.py`, `c3_tors.py`. Exact integer arithmetic; no float
anywhere. **No leakage, key-recovery, or ECDLP claim is made or implied** — this is a curve/CM object
with no `d`-side content.*

---

# 1. The curve and its Jacobian `[VERIFIED 106/106]`

`C₃ : w³ = x³ + 7`, projectively `W³ = X³ + 7Z³`. Smooth (the partials `−3X², 3W², −21Z²` vanish only at
`(0:0:0)`), so it is a **smooth plane cubic ⇒ genus 1**. It is the `k = 3` member of the Kummer family
that `POSITIVE_FINDINGS_ADDENDUM_1_v1.md:219` flags unmeasured. `Z = 0` gives `W³ = X³`, i.e. **3 points
at infinity** when `p ≡ 1 mod 3`.

Rewriting `w³ + (−x)³ = 7` puts it in Selmer/Fermat form `x³ + y³ = d z³` with `d = 7`, whose Jacobian is
classically `Y² = X³ − 432d²`. Here:
```
Jac(C₃)  =  E_J :  Y² = X³ − 432·7²  =  X³ − 21168
```
**Verified independently of the citation:** over a finite field a genus-1 curve always has a rational
point, so `#C₃(F_p) = #E_J(F_p)`. Direct point counts agree at **106/106 primes** `p < 600`,
`p ∉ {2,3,7}` (the bad primes of `21168 = 2⁴·3³·7²`). *The classical Jacobian formula is `[CITED — not
verified against source]`; the 106/106 identity is what this result rests on.*

**`E_J` is a sextic twist of secp's curve shape:** `b′/b = −21168/7 = −3024 = −(2⁴·3³·7)`, and at secp
`[−3024/π]₆ = ζ₆¹` — a **primitive** sextic class.

---

# 2. At secp — full 256-bit identification `[VERIFIED — exact, with a discriminating control]`

Method: `E_J` must be one of the six sextic twists, so its order is `p+1−t` for one of the six traces
`{±2a, ±(a+3b), ±(a−3b)}`, `p = a² + 3b²`. Tested by annihilation on **4 independent points** of
`E_J(F_p)`.

> **Exactly one candidate annihilates; the other five do not.** That five-way failure is the
> discriminating control — the identification is not a small-subgroup artifact. (Same method as
> §A1.2's amicable-pair verification.)

```
#Jac(C₃)(F_p) = 115792089237316195423570985008687907852598652813156864395638497411212089444244

trace(Jac C₃) = 2a  = 671331852483699643819086596696745227420
trace(secp)   = a+3b = 432420386565659656852420866390673177327
a = 335665926241849821909543298348372613710
b =  32251486774603278314292522680766854539            (p = a² + 3b², verified)
```

**Closed form `[VERIFIED]`:  `#Jac(C₃)(F_p) = (a−1)² + 3b²`** — i.e. `N(π − 1)` for `π = a + b√−3`,
exactly consistent with the measured trace `2a`.

**A clean structural distinction from secp.** `Jac(C₃)`'s Frobenius is `π = a + b√−3`, with **integral**
Eisenstein coordinates. secp's trace `a+3b` is **odd**, so secp's Frobenius is **half-integral** in
`ℤ[ω]` (`(m+n√−3)/2`, `m ≡ n mod 2`). The two covers' curves sit on opposite sides of that integrality
split.

**Not secp, and not isogenous to it.** Different trace ⇒ different isogeny class. And:
```
#Jac(C₃)(F_p) = 2² · 3 · C253          (C253 composite, 253 bits)
```
so it is **not of prime order**. ⇒ **`Jac(C₃)` has no amicable partner field** — `F_N` is not a field.
The amicability of §A1.2 is specific to secp's own twist, not a property of the `j=0` family.

---

# 3. ★ The two covers are linked, through `28`

`E_J : Y² = X³ + B`, `B = −21168`. A rational **2-torsion** point exists iff `X³ = −B = 21168` has a
root, i.e. iff `21168` is a cube mod `p`. And
```
21168 = 2⁴·3³·7²  ≡  2⁴·7² = 784 = 28²   (mod cubes, since 3³ is a cube)
```
so, as `gcd(2,3) = 1`,
```
21168 is a cube mod p   ⟺   28 is a cube mod p
```
— **which is exactly the μ₆-cover branch condition** of `RESULT_mu6_cover_and_conductor_v2.md`
(`N(S₁) = 4p ⟺ χ₃(28) = 1`). Both were computed independently and agree at secp.

**Verified at secp with explicit points:**

| | check |
|---|---|
| `28` a cube mod `p` | ✔ (μ₆ branch `= 4p`) |
| `21168` a cube mod `p` | ✔ (equivalent, confirmed both ways) |
| 2-torsion `T₂ = (x₀, 0)`, `x₀³ = 21168` | ✔ on curve, `2T₂ = O`, `T₂ ≠ O` |
| 3-torsion `T₃ = (0, √B)`, `B` a QR | ✔ on curve, `3T₃ = O`, `T₃ ≠ O` |
| ⇒ `6 | #Jac(C₃)(F_p)` | ✔ forced by torsion; `N mod 12 = 0` |

> **One cubic-residue condition on `28` controls both covers at once:** it puts the μ₆ cover in the
> `N(S₁) = 4p` branch **and** gives the μ₃ cover's Jacobian a rational 2-torsion point — hence
> non-prime order, hence `Jac(C₃) ≇ secp`.

⚠ **Scope.** The equivalence `28`-cube ⟺ 2-torsion is a **derivation** (immediate once seen); the
content is that a *single* arithmetic condition on secp's `p` governs two different geometric objects.
This is a **curve-side / CM statement**. It says nothing about `d`, and no leakage consequence follows.
`28` was already a distinguished constant here — Part IV's flap classifier `ε = ζ₆^{3−[28/π]₆}` and
thread A's `χ(π) = −(28/π)₆⁻¹` — but **no derivation links `ε` to either cover**; that remains the open
question named in v2 §3.1.

⚠ **A methodological note, recorded because the check caught it.** My first 2-torsion check **failed**,
and the failure was **my cube-root routine**, not the mathematics: `c^((2p−1)/3)` is a cube root only for
`p ≡ 2 mod 3`, and secp has `p ≡ 1 mod 3` (`v₃(p−1) = 1`). Re-run with a correct `nthroot_mod`, all four
torsion checks fire. **A negative from a broken instrument was one step from being reported as a
finding** — the same class as the nulls audited in §A3 and the `W1` non-primitive plant.

---

# 4. What this leaves

- **`k = 8`** (genus 7, new part dim 4) and **`k = 12`** — `k = 12` is the only place the μ₄ and μ₆
  mechanisms can interact. Untouched.
- **Any real relation between `ε` and the covers** beyond sharing the constant `28`. Open, well-posed.
- **Priority check** on §1–§3 — not run. The Selmer-curve Jacobian is textbook; the secp-specific
  identification and the `28` link are the parts that would need a search before any novelty claim.
- The conductor / volcano family of `RESULT_mu6_cover_and_conductor_v1.md` §2 — unchanged, open.

---

*Grades: §1's `106/106` and §2's identification `[VERIFIED — exact, discriminating control fired]`;
§2's closed form `[VERIFIED]`; §3's equivalence `[DERIVED]` with all four torsion checks
`[VERIFIED at secp]`; the classical Jacobian formula `[CITED — unverified]`, not load-bearing.
No claim here is `[PROVED]` in the sense of an adversarially reviewed argument.*
