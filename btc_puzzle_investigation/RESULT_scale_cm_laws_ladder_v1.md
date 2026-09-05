# RESULT — Scaling the positive findings across the scale banner (v1, 2026-07-29)

**Artifact:** `scale_cm_laws_ladder_v1.sage` (exact; passes `check_no_float.py`).
**Object:** the `POSITIVE_FINDINGS_MASTER_v4` **SCALE BANNER / N6** — *"everything in A.2 is at
`p ≤ 2¹⁷` or smaller; none of it has power at `2²⁵⁶`."*
**What this does:** pushes the subset of findings that **can** cross the banner to secp's actual
`p ≈ 2²⁵⁶`, and classifies **every** measured row by whether it can cross at all, and how far.
**What this does NOT do:** it does not touch the leakage / statistical layer. For those rows N6
**stands unchanged** (§4). This is a scope extension of already-graded laws, not a new claim.

---

## 1. FLAGSHIP — the CM / `π`-only laws hold **exactly at secp's own `p`** `[VERIFIED — exact, at secp]`

Every quantity here is a function of the Frobenius `π = a + bω ∈ ℤ[ω]` **alone**. `π` is derivable
in polylog time from `(p,t)` — `4p = t² + 3f²`, `a = (t±f)/2`, `b = 2a−t` — so the check runs at
`p = 2²⁵⁶ − 2³² − 977` directly, not by extrapolation. Prime ladder `p ≡ 1 mod 3`, **8 bits → 256
bits**, secp last:

| law (master ref) | 8b…253b | **secp (256b)** |
|---|---|---|
| Norm / purity `N(π)=p` ⇒ `|eigenvalue|=√p` (Hasse–Weil) | OK | **OK** |
| Trace `2a−b=t`, `#E=p+1−t`, **ordinary** (`t≢0 mod p`, P7) | OK | **OK** |
| CM discriminant `4p = t²+3f²` (Part I) | OK | **OK** |
| **Rhombus theorem** `N(π)=N(ωπ)=p`, 60° cell (Part II) | OK | **OK** |
| **Amicability arithmetic** `N(π−1)=p+1−t=#E` (Part IV) | OK | **OK** |
| `π²/p` a root of unity? (ordinary ⇒ **no**) — M6-flavoured | no | **no** |
| **Angle law** sextant `p₀=(¾)|cos2θ|/(2cos2θ+1)`, `cos2θ=(t²−2p)/2p` **exact ℚ** (Part II) | exact | **exact** |

**secp exact values** (reproducing Part II's on-file secp row, now with the full ladder behind it):
`cos2θ = t²/2p − 1` (exact rational), `p₀ = 44596787757037860205668370468758646601202757238619596622183826169044082478397 / 189854137280742227247740305439811363338845939805389246446063354236972672515376 ≈ 0.234900`, `3/8 − p₀ ≈ 0.140100`, pinned pair `= 1/8` (θ-independent), `θ ≈ 50.5515°` (display only).

**FIRING CONTROL (passes):** the ladder's *derived* secp constants equal the on-file Part I values
**exactly** — `a = 367917413016453100223835821029139468249`,
`b = 303414439467246543595250775667605759171`, `t = 432420386565659656852420866390673177327`,
`p+1−t = n_secp`. If the ℤ[ω] machinery were wrong, this would not match. It matches; the ladder is
validated by an independent constant.

**Grade move:** these rows were `[PROVED — continuum; VERIFIED at small p — banner]`. They are now
`[VERIFIED — exact, **at secp's actual p**]`. The PROVED/continuum status is unchanged; what moves
is that the empirical verification **reaches `2²⁵⁶`**, so **N6 no longer governs this subset.**
Nothing here is a leakage claim or an ECDLP consequence — a curve whose CM structure is confirmed at
secp is exactly what a generic ordinary `j=0` curve looks like at secp. It removes the *"we only ever
looked at toy `p`"* caveat for the CM/lift layer, nothing more.

---

## 2. THE SCALING LEDGER — every measured row, by how far it can cross the banner

Four tiers, by the **object** each row depends on (this is the drill's proxy guard: the reachable
scale is a property of the object, not of how hard we tried):

- **T1 `→ secp` (π-only).** Functions of the Frobenius `π` alone ⇒ polylog ⇒ secp. *Done in §1, or
  already on file.*
- **T2 `→ ~10⁶` (cover / field-lattice, `O(p)` enumerable).** Need a full `F_p` pass but no discrete
  log. Reachable to moderate `p`; **not** secp.
- **T3 `→ ~10⁴–10⁵` (`d`-labelled twisted sums, `O(p²)`).** Need the `d = dlog(P)` labelling. **Cannot
  reach secp *even in principle* — computing `V(a)` at secp *is* an ECDLP-scale enumeration.** The
  *law* may still be proved-for-all-`p`; only its numeric check is capped.
- **T4 `needs prereg` (statistical).** Scaling a null/saturation to new `p` is a **new statistical
  test** ⇒ `experiment-designer` sign-off first (memory: pre-registration is mandatory).

| row | statement (abbrev) | tier | current | reachable | note |
|---|---|---|---|---|---|
| Part II rhombus/angle/norm-band/cap; Part I constants | CM lattice geometry | **T1** | small p | **secp ✓ (§1)** | angle law now exact at secp |
| Part IV sextic identities `π_n=π−1`, `ε=ζ₆^{3−[28/π]₆}`, MOV `ord_n(p)` | π-only | **T1** | **already secp** | secp ✓ | `sextic_identities_verify.py`, P7′ |
| Jacobi sign law `J(χ₃,χ₄)=±p` | Jacobi/Stickelberger, π-only | **T1** | 28 primes | **secp reachable** | via Stickelberger closed form, not the `O(p)` sum |
| M4 `V` real/imag by `p mod 4` | proved-forced (`χ₂(−1)`) | **T1-proof** | every row | **holds at secp (proved)** | numeric check is T3 |
| M15 equipartition `1/6`; M16 μ₆-symmetry | proved-forced | **T1-proof** | exact | **holds at secp (proved)** | deficit = excluded `d=0` |
| M10 frame operator `λ_max/Tr = ½ / ¾` | field-lattice, exact | **T2** | tested p | ~10⁶ | continuum ⇒ holds at secp; numeric enumerable |
| M11 `|FLD| = 6·h(−p)` | field-lattice + class no. | **T2** | `p<2000` | ~10⁶ | not proved (mod L1); `h(−p)` free at any p |
| M12 `⟨σ,χ₂⟩_F = 0 ⟺ p≢3 mod8` | field | **T2** | 35/35 | ~10⁶ | extend prime count |
| M13 `(B2)=C`, `C²/p ≤ 3.7` | curve+field, Weil-scale | **T2** | 49/49, p→6000 | ~10⁶ | bound is proved (Weil); check enumerable |
| M1 `A_new` ordinary ⟺ `p≡1 mod4`; M2 `gcd(L_E,L_new)=1` | cover L-polys | **T2** | 24/18 | ~10⁶ | at secp = **N2 gap** (dim-2 unproved) |
| M6 `ord(α²/p)` CM `{1,3}`; M17 `k=ord_ℓ(p)=3` | cover / ss eigenvalues | **T2** | 6–7 primes | ~10⁶ (many primes) | at secp tied to N2; E-supersingular part is T1 |
| M9 Semaev first-fall/solving degree | Gröbner over `F_p` | **T2*** | `p≤307,m≤4` | modest | degrees ~p-independent; GB cost grows |
| M3 ½-saturation `χ₂(y) 0.470→½` | max-freq on twisted sums | **T3+T4** | 6 primes | ~10⁴–10⁵ | the **N1 anomaly**; d-labelled AND statistical |
| M5 no max/√p exceeds bound | twisted sums | **T3** | all rows | ~10⁴–10⁵ | bound (P6b) proved ∀p; check capped |
| 120° law `v=u²−¾`, `V₂=V₁²±2p`, `s₁²+s₁s₂+s₂²=¾` | twisted sums, exact | **T3** | ≤547, 357 cls | ~10⁴ | **exact identity**, no prereg; **cannot reach secp** |
| M14 joint `(x,y)` readout 0.93 | d-labelled statistic | **T3+T4** | 4 primes | ~10⁴–10⁵ | exact parts (even-in-d) proved ⇒ secp |
| M18 D1 no affine structure | d-labelled/geometric | **T3** | 3 primes | ~10⁴ | |
| M7 `C_T` coupling <1.6%; M8 `C_k` at floor | statistical | **T4** | `p≤2¹⁷` | enumerable + prereg | "zero power at 2²⁵⁶" is intrinsic |
| M19 coordinate-bit readouts; M20 μ₆ readouts | statistical | **T4** | 1 curve / 54 cells | enumerable + prereg | |
| twist-orbit spectrum null; `E[u⁴]~SU(2)` | statistical (nulls) | **T4** | `p≤2731` | enumerable + prereg | scaling a null = new test |

`*` M9's first-fall degree is **curve-independent** and largely `p`-independent — its scale story is
different (it is an algebraic-complexity statement, not an empirical `p`-scaling one).

---

## 3. THREE TIER BOUNDARIES THAT ARE THEMSELVES FINDINGS

1. **The `V(a)` / twisted-sum laws provably cannot reach secp.** `V(a) = Σ_P χ₂(y_P) e_n(a·d)` is
   indexed by `d = dlog_G(P)`. Evaluating it at secp is an `O(n)` walk over labelled points = the
   same enumeration ECDLP forbids at scale. So the 120° law, the `½`-saturation, and the joint-readout
   fidelity are **structurally banner-locked** — not for lack of compute, but because their defining
   object encodes the discrete log. *(This sharpens N6: for these rows "no power at `2²⁵⁶`" is not a
   sampling limitation, it is the ECDLP.)* Their proved-for-all-`p` *skeletons* (M4/M15/M16 parities,
   the P6b bound) do reach secp; the *magnitudes* do not.

2. **The N2 gap is the ceiling for the whole `A_new` tier.** M1/M2/M6/M17 and Part VII all inherit
   *"`A_new` supersingular at secp"*, which is `[VERIFIED 24/24 at small p]` but **unproved at dim 2**.
   Every one of these can be pushed to ~10⁶ in *sample*, but none crosses to secp until N2 is closed
   analytically. Scaling the sample does **not** close N2 — that is exactly the drill's "an empirical
   null/extrapolation is not a proof" rule, applied to a *positive* extrapolation.

3. **The continuum laws reach secp as continuum statements, verified numerically at moderate `p`.**
   Rhombus/angle/norm-band/cap are `p→∞` geometry with discretization error `→0` (on file:
   mean-`s` deviates from `1/6` by `7.7e-3 @211`, `1.2e-4 @1009`, `4e-7 @10⁶`). §1 supplies their
   **exact** secp observables (`p₀`, `cos2θ`); the enumerable checks (T2) confirm the finite-`p`
   convergence. Together these two put the CM/lift layer at secp with no extrapolation gap.

---

## 4. SCOPE — what N6 still governs (do not over-read §1)

§1 moves the **CM-algebraic / lift-geometry layer** across the banner. It says **nothing** about:
- the **leakage frontier** (Part VI) — every readout/concentration test is T3/T4, banner-locked or
  prereg-gated;
- the **`½`-saturation anomaly** (N1) — banner-locked (T3) *and* unexplained;
- **whether `A_new` is supersingular at secp** (N2) — untouched;
- any **statistical null** — unscaled here by design (needs prereg).

So the correct one-line summary is: *the parts of the structure map that are functions of `π` are now
confirmed at secp; the parts that are functions of the `d`-labelling are provably not, and the
statistical layer is unscaled.* N6, re-scoped to A.2's statistical/twisted-sum rows, **stands.**

---

## 5. RECOMMENDED master edit (for user approval — needs a v5 + `compile-diff`, not an in-place edit)

Do **not** delete N6. **Re-scope** it and add a companion positive row, e.g.:

- **N6 (re-scoped):** *"The **twisted-sum and statistical** rows of A.2 are at `p ≤ 2¹⁷`; the
  twisted-sum rows are **banner-locked by the DLP** (§3.1) and cannot reach `2²⁵⁶` even in principle;
  the statistical rows need prereg to scale. No power at `2²⁵⁶` for these."*
- **new P-row (Proved/Verified):** *"The CM/`π`-only laws (norm, trace, CM disc, rhombus, angle-law
  sextant `p₀`, amicability `N(π−1)=#E`, sextic identities, MOV degree) are **verified exact at secp's
  own `p`** — `RESULT_scale_cm_laws_ladder_v1`, firing control passes. `[VERIFIED — at secp]`."*

This keeps the honesty banner where it bites (the statistical/leakage layer) and stops it
over-claiming a gap on the CM layer that no longer exists.

---

*Method note:* run `sage scale_cm_laws_ladder_v1.sage`. Signal path is `ℤ / ℚ / ℤ[ω]` throughout
(the only floats are a display-only `θ` and Sage `QQ` exact-rational `/`, both `# noqa`-exempted with
justification; `check_no_float.py` passes). Trace at ladder primes via Sage CM point count; at secp
via the on-file `t`, cross-checked by reproducing the on-file `π`.
