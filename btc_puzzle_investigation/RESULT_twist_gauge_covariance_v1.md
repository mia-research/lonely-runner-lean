# The FLD sign law is gauge-invariant: a basis-dependent pair whose product is not

**Date 2026-07-19.** Pre-registered in `PREREG_twist_sum_B_closedform_v1.md` (written by
`experiment-designer` before any statistic was computed), Arm III. Two corrections to that spec are
declared in §0 below. Scripts: `twist_chirality_arm3_v1.py` (arm as specified),
`twist_chirality_arm3_v2/v3.py` (slope correction), **`twist_gauge_covariance_v1.py` (definitive)**.
Logs: `_arm3_IS_v1.log`, `_arm3_v3_IS.log`, `_twist_gauge_cov_v1.log`. Exact integers / `Fraction`
throughout; no float in the signal path.

**Protocol.** Output is a characterization. Every number carries its power and scope. No arm is
described as opened or shut.

---

## 0. What was pre-registered, and the three corrections

The prereg asked: does `sign(FLD)` flip under basis chirality `π_p ↔ π̄_p`? — the check named in
master §VIII.4/§X.9 as decisive and never run. Three things were wrong or incomplete in the spec,
each found by a control rather than by inspection:

**C1 — the `M` in the law was misidentified.** Prereg §7.1 takes `M` from `4p = L² + 27M²` (the CM
quantity) and derives that it is conjugation-odd. The record's `M` (`RESULT_fld_classnumber_v2.md`,
`_fld_L1_explore_v1.py:46`) is the **flap-coordinate slope**: `t(X) := p·s(X)` is an integer in
`(−p,p)` with `t(X) ≡ M·X mod p`, where `s` is the **orientation-carrying** combination — `u−v` at
`orient='-'`, `u+v` at `orient='+'`. Reproduction of the standing law is the discriminator:

| reading of `s` | `sign(FLD) = −χ₂(M)` |
|---|---|
| always `u−v` | 29/46 |
| always `u+v` | 38/46 |
| **orientation-carrying (the record's)** | **46/46** |

The CM `M` is a function of the ideal; the slope `M` is not. The prereg's chirality derivation
therefore does not apply to the law under test.

**C2 — the conjugation arm is degenerate, and there is a proof.** Every `X ∈ Z` is fixed by
conjugation, and the lift takes coordinates with respect to the **same basis that was conjugated**,
so `eis'(X) = conj(eis(X))` has **identical** coordinates `(u,v)`. Hence `σ' = σ` pointwise and every
`σ`-derived quantity is conjugation-invariant. `[PROVED; VERIFIED 99/99 primes]` — `σ` pointwise,
`FLD`, and `M` all invariant. So the pre-registered chirality question **dissolves**: conjugation is
not a nontrivial gauge on this complex. The live gauge group is the **presentation group** `G` of
prereg §3.2 (the 8 re-presentations `(±R1,±R2)`, `(±R2,±R1)` of the same lattice), and the rest of
this document is what that group does.

**C3 — a scope defect in the decomposition identity, exposed by a declared prereg deviation.**
`_twist_split_B_v1.py` computes `FLD` as `A + B`, partitioning `F_p` by `χ₂(x³+7) = ±1`. That drops
the abscissae with `x³ = −7` — the 2-torsion `x`-coordinates, present exactly when `−7` is a cube
mod `p`. The exact identity is

```
FLD  =  A + B + corr ,      corr := Σ_{x³ = −7} σ(x)·χ₂(x)          [VERIFIED 383/383]
```

`corr ≠ 0` at **38 of 383** primes `p ≡ 1 mod 6` in `[11,6000)`. The source scripts' `n`-prime filter
silently excluded these curves; prereg §6.1 deliberately **dropped** that filter, which is what
exposed the gap. This is the same shape as the documented `p=823` β-calibration trap: a convention
that is invisible while a filter hides it. **secp is unaffected** — `−7` is a non-cube mod secp's `p`
`[PROVED, on record]`, so `E(F_p)[2] = 0` and `corr = 0` identically. Every number below uses the
**true** `FLD = Σ_x σ(x)χ₂(x)`.

---

## 1. The object: neither side of the law is a function of the ideal

Scope: `p ≡ 19 mod 24` (where `FLD ≠ 0`), `p ∈ [11,2500)` in-sample (46 primes) and the **frozen**
`[2500,6000)` out-of-sample window (53 primes); 8 presentations each.

| | IS (46 primes, 368 instances) | OOS₁ (53 primes, 424 instances) |
|---|---|---|
| `sign(FLD)` takes **both** signs within the orbit | 46/46 | 53/53 |
| `χ₂(M)` takes **both** signs within the orbit | 46/46 | 53/53 |
| `\|FLD\|` constant over the orbit | 368/368 | 424/424 |

So the magnitude is an invariant of the lattice and **each sign separately is not** — which is
exactly the reading master §VIII.4 recorded when it called the sign law "an internal consistency
between two reduced-basis-dependent quantities."

## 2. The gauge acts by dilation, with no sign `[VERIFIED 792/792 instances]`

For every presentation `g`, with `c_g := M_g · M⁻¹ mod p`:

```
σ_g(x)  =  σ(c_g · x)          exactly, for all x        792/792 instances, 99 primes
```

measured as `σ_g(x) = ε·σ(c_g x)` with `ε` free: **`ε = +1` at 792/792**, no exceptions. The absence
of a sign is forced, not lucky: if `t_g(X) = ε·t(c′X)` then `M_g ≡ ε c′ M`, so `c_g = ε c′`, and `σ`'s
oddness (`σ(−x) = −σ(x)`, `[PROVED]` on record) absorbs `ε`:
`ε·σ(c′x) = ε·σ(ε c_g x) = σ(c_g x)`. The measured multiplier `c_g` is a **cube** at 1648/1648
instances.

## 3. The product is gauge-invariant `[PROVED given §2]`

For `p ≡ 3 mod 4`, substituting `y = c_g x` in the character sum (`χ₂(c⁻¹) = χ₂(c)`):

```
FLD_g = Σ_x σ(c_g x)χ₂(x) = χ₂(c_g)·FLD      ⇒   sign(FLD_g) = χ₂(c_g)·sign(FLD)
M_g   = c_g·M                                 ⇒   χ₂(M_g)     = χ₂(c_g)·χ₂(M)
⇒   sign(FLD_g)·χ₂(M_g) = χ₂(c_g)²·sign(FLD)·χ₂(M) = sign(FLD)·χ₂(M)        ∎
```

The two factors are gauge-**covariant with the same character**, so the product is a function of the
lattice although neither factor is. Measured:

| | IS | OOS₁ (frozen) |
|---|---|---|
| product `sign(FLD)·χ₂(M)` constant over all 8 presentations | **46/46** | **53/53** |
| its constant value | `−1` (46/46) | `−1` (53/53) |
| standing law `sign(FLD) = −χ₂(M)` in the canonical basis | 46/46 | 53/53 |

Power note: the derivation in this section makes the constancy a theorem given §2, so the counts are
a check on the implementation rather than the evidence. Taken purely as a null test — signs flipping
independently across the 7 non-base presentations — constancy at 99/99 primes has null probability
`2^{−693}`; that number is reported for completeness, not as the basis of the claim.

## 4. What this changes, stated exactly

**Retract (with an artifact, per the compile rule):** master §VIII.4's and §X.9's reading that the
sign-pinning "reduces to no intrinsic invariant … reads as an internal consistency between two
reduced-basis-dependent quantities, **not** shown to be a deeper arithmetic symmetry." The relation
**is** basis-independent — proved in §3, verified 99/99 including 53 out-of-sample. The earlier
finding that `χ₂(M)` alone matches none of ~25 intrinsic invariants stands and is **consistent**:
`χ₂(M)` alone is not intrinsic; only the product is.

**Consequence.** Combined with `|FLD| = 6·h(−p)` at `p ≡ 19 mod 24` (chain in
`RESULT_fld_classnumber_v2.md`, `[PROVED]` except the open lemma L1, `[CITED]` Dirichlet):

```
FLD  =  −6·χ₂(M)·h(−p)          at p ≡ 19 mod 24
```

is a **well-posed** identity — the right-hand side's sign combination does not depend on the basis
presentation. It inherits L1's open status; it does not resolve it.

**What is still not explained.** Why the invariant equals `−1` rather than `+1`. §3 proves the
product is a lattice invariant; it does **not** derive its value. That is the named next probe, and
it is now a well-posed question about the lattice rather than about a code convention.

## 5. Input to the main hunt (Arms I/II of the same prereg)

Measured over all `p ≡ 1 mod 6`, `p < 3000` (206 primes, 1648 gauge instances; `B = 0` at 26):

| quantity | constant over the gauge orbit |
|---|---|
| `\|A\|` | **206/206** |
| `\|B\|` | **206/206** |
| `sign(A)·χ₂(M)` | 119/206 |
| `sign(B)·χ₂(M)` | 122/206 |

So the **magnitudes** `|A|`, `|B|` are gauge-invariant — the Arm I closed-form target is well-posed
as stated — but the twist-side split does **not** inherit the field-side covariance of §3: the sign
of `B` is not tied to `χ₂(M)` by the same character. This is consistent with the mechanism, since the
dilation `x ↦ c_g x` does not preserve the `E`/twist partition (it carries `y² = x³+7` to
`y² = x³+7c_g³`, another sextic twist), so the substitution argument of §3 does not run for `A` or
`B` separately. **Actionable:** a *signed* closed form for `B` requires a stated gauge-fixing
convention; `|B|` does not. Arms I and II should be run against `|B|`, with `sign(B)` handled as a
separate object.

## 6. Scope and power, declared

1. **Scale.** `p ∈ [11,6000)`. Nothing here was measured at `p ≈ 2²⁵⁶`; the master's scale banner
   governs. §2 and §3 are algebra and carry to any `p ≡ 3 mod 4` where the stated inputs hold; the
   *value* `−1` is `[EMPIRICAL, 99/99 over the stated window]`.
2. **The gauge group tested is the 8-element presentation group**, plus conjugation (§C2). Other
   changes of construction — a different lattice reduction, a different fundamental domain, a
   different `σ` convention — are **not** probed and nothing here bounds them.
3. **`σ`'s oddness and μ₃-invariance** are inputs `[PROVED, on record]`, not re-derived.
4. **L1 is untouched.** `|FLD| = 6h(−p)` still rests on it (verified 86/86, not proved).
5. `corr ≠ 0` primes (§C3) are outside the `n`-prime scope of every prior result in this thread;
   this document does not re-grade any of those results, it only records that `A + B` is not `FLD`
   there.

## 7. Named next probes

1. **Derive the value `−1`** of the invariant `sign(FLD)·χ₂(M)` — now a well-posed lattice question.
2. **Gauge-fix `sign(B)`**: identify the character (if any) by which `sign(B)` transforms, given
   that `|B|` is invariant and the dilation moves `E` to `y² = x³+7c³`.
3. Arms I/II of the prereg, retargeted to `|B|` per §5, with the `n`-prime filter question settled
   by §C3 (either restore the filter or carry `corr` explicitly).
4. Re-audit any earlier result that used `FLD = A + B` on a window where the `n`-prime filter was
   dropped.
