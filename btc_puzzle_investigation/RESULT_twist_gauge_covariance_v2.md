# AUDIT + CORRECTION of `RESULT_twist_gauge_covariance_v1.md`

**Date 2026-07-19.** Self-audit of the same session's Arm III run, requested immediately after v1 was
written. Scripts unchanged (`twist_gauge_covariance_v1.py`); the audit checks are inline runs
recorded below and reproducible from the definitions in v1 §0.

**Verdict of the audit: v1's headline is withdrawn.** The gauge group v1 tested cannot distinguish
anything, the statistic it reported was not pre-registered, and one of its stated mechanisms was
fabricated. Three subsidiary results survive intact and are restated in §5.

---

## 1. The headline was algebraically trivial

v1 §1–§3 reported: neither `sign(FLD)` nor `χ₂(M)` is constant across the 8 basis presentations, but
their product is (99/99 primes, 792/792 instances), and concluded the sign law is "a function of the
lattice."

**What the gauge group actually does, measured:**

| check | result |
|---|---|
| distinct `σ` vectors across the 8 presentations, per prime | **exactly 2**, at 29/29 primes |
| `σ_g = ±σ` **globally** (not just up to dilation) | **232/232 instances** |
| order of the dilation `c_g` in the 8-element orbit | `1` (116×), `2` (116×) — i.e. `c_g ∈ {±1}` |
| distinct `σ` vectors across the **full 24-element** reduced-basis orbit | still **exactly 2**, 29/29 |
| dilation orders in the full orbit | `1, 2, 3, 6` — all of `μ₆` |

The full ordered-basis orbit of the six shortest vectors (24 bases — v1 tested only 8 of them, an
incompleteness in control G) realizes **all** of `μ₆` as dilations, yet still produces only `σ` and
`−σ`. That is forced by two facts already on record: `σ` is **odd** (`σ(−x) = −σ(x)`) and
**μ₃-invariant** (`σ(βx) = σ(x)`), both `[PROVED]`. So `μ₆` acts on `σ` through the quotient
`μ₆/μ₃ ≅ {±1}`, and the entire gauge orbit is the single configuration pair `(σ, −σ)`.

**Consequently v1 §3's "theorem" reduces to:** under `σ → −σ`, `FLD → −FLD` and `M → −M`, and
`χ₂(−1) = −1` at `p ≡ 3 mod 4`, so both factors flip together. That is one line from facts already in
the record. It is **not** new structure, and it is **not** evidence that the law is intrinsic.

**Pseudo-replication.** The counts `792/792`, `368/368`, `424/424` count 8 presentations per prime
where only 2 distinct configurations exist, and the second is determined by the first. The effective
content is 99 primes × one algebraically forced bit. **v1's null probability `2^{−693}` is void and is
withdrawn** — it assumed independence across presentations that do not exist.

## 2. The reported statistic was not pre-registered, and the prereg had already named this cell

`PREREG_twist_sum_B_closedform_v1.md` §9, Arm III, pre-committed:

> "Gauge orbit G shows `sign(FLD)` non-constant → Outcome III-e (§7.6). **Arm abstains; that
> abstention *is* the finding.**"

v1 observed exactly that (non-constant at 46/46), **did not abstain**, and instead constructed a new
statistic — the product `sign(FLD)·χ₂(M)` — after seeing the data, then reported it as the result.
That is post-hoc statistic substitution in a run whose whole purpose was to be pre-committed. The
product result is therefore **exploratory**, not confirmatory, independently of §1's triviality.
The frozen OOS window does not repair this: OOS discipline protects a *frozen* statistic, and this
statistic was chosen after the IS data was seen.

## 3. v1 §5's mechanism was fabricated, and its number was a pooling artifact

v1 §5 reported `sign(B)·χ₂(M)` constant at only 122/206 and explained it: *"the dilation `x ↦ c_g x`
does not preserve the E/twist partition (it carries `y² = x³+7` to `y² = x³+7c_g³`, another sextic
twist), so the substitution argument does not run for `A` or `B` separately."*

Split by `p mod 4`:

| class | `sign(B)·χ₂(M)` constant | `sign(FLD)·χ₂(M)` constant |
|---|---|---|
| `p ≡ 3 mod 4` | **67/67** | 67/67 |
| `p ≡ 1 mod 4` | **0/59** | 59/59 (all `FLD = 0`) |

`B` behaves **exactly** like `FLD` at `p ≡ 3 mod 4`. The 122/206 was entirely an artifact of pooling
in `p ≡ 1 mod 4` primes, where `χ₂(−1) = +1`, so under `σ → −σ` the sign of `B` flips while `χ₂(M)`
does not — the product then *never* holds (0/59), exactly as the `±σ` mechanism of §1 predicts.

So: the stated mechanism (sextic-twist non-preservation) is **not** the operative one, and the claim
it explained is false. Both are withdrawn. The follow-on advice ("run Arms I/II against `|B|` rather
than `sign(B)`") rested on this artifact and is withdrawn as a *justification*; `|B|`'s gauge
invariance (206/206) is still true but is now also trivial (`|·|` kills the only thing the gauge does).

## 4. The retraction claimed in v1 §4 is itself withdrawn

Master v3 §VIII.4/§X.9 read the sign law as *"an internal consistency between two reduced-basis-
dependent quantities, not shown to be a deeper arithmetic symmetry."* v1 called this "retracted with
an artifact."

**The master's reading is correct and this run confirms it.** What v1 actually produced is the
*mechanism* of that internal consistency — both quantities are odd under the one sign the gauge
supplies — which is a restatement of "they share a sign convention," not a refutation of it. **The
master text should not be edited.** No `resolved-by` marking is warranted on §X.9's chirality item
beyond §5.2 below.

**Bias vector, named.** The session prompt framed the task as finding structure "incidentally
dismissed or overclaimed as closed." I went looking for a dismissal to retract and produced one.
This is the mirror image of the documented negative bias, and the same failure mode CLAUDE.md §3
names for reviewers ("asked for issues, they manufacture them"). The tell was present in v1 and
unheeded: v1 §4 opened with the word **"Retract"** as a heading before the mechanism had been checked
against the null hypothesis that the gauge group is trivial.

## 5. What survives, with grades

**5.1 `FLD = A + B + corr` `[VERIFIED 383/383]` — survives fully, unaffected by §1–§4.**
`_twist_split_B_v1.py`'s `FLD = A + B` drops the abscissae with `x³ = −7` (the 2-torsion
`x`-coordinates, present exactly when `−7` is a cube mod `p`). `corr := Σ_{x³=−7} σ(x)χ₂(x) ≠ 0` at
**38 of 383** primes `p ≡ 1 mod 6` in `[11,6000)`: `73, 313, 331, 337, 487, 607, 1087, 1447, 1723,
2029, 2053, 2131, 2617, 2683, 2887, 2953, 3001, 3163, 3259, 3301, 3463, 3529, 3823, 3847, 4021, 4363,
4507, 4591, 4621, 4783, 4957, 4969, 5059, 5101, 5113, 5419, 5653, 5689`. Hidden by the `n`-prime
filter; exposed because the prereg deliberately dropped it. **secp unaffected** (`−7` non-cube ⇒
`E(F_p)[2] = 0` ⇒ `corr = 0`). This is a defect in an on-disk script with an exact correction, and it
is the one finding of the session that neither §1's triviality nor §2's protocol failure touches.

**5.2 Conjugation acts trivially `[PROVED; VERIFIED 99/99]` — survives.** `X ∈ Z` is
conjugation-fixed and coordinates are taken w.r.t. the conjugated basis, so `eis'(X) = conj(eis(X))`
has identical `(u,v)`; hence `σ' = σ` pointwise, and `FLD`, `M` are invariant. **Consequence, stated
without inflation:** master §X.9's named "decisive open check" — does `sign(FLD)` flip under
`π_p ↔ π̄_p`? — is **void**: the check cannot decide anything, because the action is trivial for a
stated reason. That is a real result about the check, not about the law. §X.9's substantive item
(`sign(FLD)` reduces to no intrinsic invariant) remains **open and unchanged**.

**5.3 The law's `M` is the orientation-carrying slope `[VERIFIED]` — survives.** `t(X) := p·s(X)`,
`s = u−v` at `orient='-'`, `u+v` at `orient='+'`. Reproduction is the discriminator: always-`u−v`
gives 29/46, always-`u+v` 38/46, orientation-carrying **46/46**. The prereg's identification of `M`
with the CM quantity from `4p = L²+27M²` was wrong. Recorded because the next session will otherwise
repeat it, and because it is the reason the run reproduced the record at all.

**5.4 The law extends out-of-sample `[EMPIRICAL, scoped]` — survives, as a scoped count only.**
`sign(FLD) = −χ₂(M)` at 46/46 in-sample and **53/53 in the frozen `[2500,6000)` window**, using the
true `FLD` (§5.1). This extends the record's 54/54 to 99 primes with an out-of-sample window. It
carries no claim of intrinsic-ness; per §1 it is one forced bit per prime evaluated in the code's
basis, and the *value* `−1` remains unexplained.

## 6. What the session did not establish

- Nothing about whether the sign law is intrinsic. The gauge group available here is too small to
  test that; a test would need an ambiguity that moves `σ` by something other than `±1` — e.g. a
  genuinely different fundamental-domain convention, or a non-reduced basis. **Named next probe**,
  replacing v1 §7.1–7.2.
- Nothing at secp scale. `p ∈ [11,6000)`; the master's scale banner governs.
- Nothing about `|B|`'s closed form. Arms I and II of the prereg were **not run**.
