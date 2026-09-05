# RESULT — group-law E3 on the real 82: a powered null; the "fires-harder" prediction is FALSIFIED, localizing the Brick A signal to x-coordinate field arithmetic

**Date 2026-08-19.** Executes FROZEN `PREREG_grouplaw_e3_real82_v1.md` (`experiment-designer` verdict
PROCEED, all five arms SOUND). Named next probe of `RESULT_e3_owed_measurement_v1.md` (Brick A). Script
`grouplaw_e3_real82_v1.py` (Curve/stats3/diffset_hist copied verbatim from validated
`c2_grouplaw_diffset_curve_v1.py`), log `grouplaw_e3_real82_v1.log`, summary
`grouplaw_e3_real82_v1_summary.json`, nulls `gl_e3_struct_null_{E2,E3,E6}_v1.npy`. Integer-exact signal +
decision path. No security / keyspace / extractability claim is made or reachable.

**Grade:** `[EMPIRICAL @ secp — POWERED, INFORMATIVE NULL. Group-law cubic energy on the real 82 is a
typical draw (two-sided p=0.261, 13.0th pctile), family-wise non-significant (p_FWER=0.585), NOT
set-specific (q_MT=0.854). The `_cmvanishing` §Next-2 "group-law fires harder" prediction is FALSIFIED;
the Brick A field-difference reject does NOT transfer to the CM-native group-law object.]`

---

## 0. Object and prediction
Group-law difference-set cubic energy `E3_gl = a²+b²+c²−ab−bc−ca` on the cube-class counts of
`{x(Pᵢ−Pⱼ)}` over the 82 real pubkey POINTS — the CM endomorphism's native operation (uses the
y-coordinates via curve addition), vs the x-only field difference `χ₃(x_i−x_j)` of Brick A.
`_cmvanishing` §Next-2 / `CORRECTION_e3_cmvanishing_interaction_reading_v1` §5.3 **predicted it would fire
harder** because the group law is where CM acts. This tests that prediction; it is not assumed.

## 1. Controls — both valid (this is a powered null, not a blind one)
- **A5 C-GLV (object identity):** a constructed φ-closed 81-point set gives `E2=12996, E3=0, E6=0` **exact**
  — the statistic is zeroed only by exact cubic (μ₃) symmetry, so a nonzero `E3_gl` reads genuine cubic
  imbalance. The real 82 is NOT φ-closed: `E3_gl(real)=489 > 0`, `T=3321`, `E3≡0 mod3` (bug-check). PASS.
- **A4 firing control (instrument power):** β²-count plant (E3=f(cube marginals), exactly matched). Δ=0
  FPR **0.012**; monotone; power **0.860** at Δ=100, **0.996** at Δ=150. A group-law cubic excess of
  magnitude Δ≳100 would have been detected — **none is present.** So the null is informative.

## 2. The result — a typical draw on every arm
| arm | statistic | value | reading |
|---|---|---|---|
| **A1** structural null (N=10000 uniform curve points), two-sided | `E3_gl(real)=489`, region `[93,12531]` | **13.0th pctile, p=0.261** | **FAIL-TO-REJECT** (neither high concentration nor low over-uniformity) |
| **A2** Westfall–Young FWER over {E2,E3,E6} | E2 p=0.540, E3 p=0.261, E6 p=0.902 | **p_FWER=0.585** | family-wise non-significant |
| **A3** OOS band-matched known-MT points | MT median 49.9th pctile; `q_MT=854/1000` | **q_MT=0.854** | **NOT set-specific** (real typical-to-below band-matched MT sets) |

The null E3_gl distribution is heavily right-skewed (mean 3345, median 2307, min 0, max 40041); 489 is a
routine low-ish draw. (An N=20 smoke had suggested "reject-low"; that was tail noise — at N=10000 489 sits
well above `L_struct=93`, the 2.5th pctile. The two-sided test was pre-registered, so the low tail is
covered; no over-uniformity is present.)

## 3. The finding — the prediction is falsified; the signal is localized (a brick, with power + scope)
Side-by-side with Brick A on the SAME 82 keys:

| object | E3(real) | pctile | two-sided p | q_MT | verdict |
|---|---|---|---|---|---|
| **field-difference** `χ₃(x_i−x_j)` (Brick A) | 13125 | 98.2nd | 0.035 | 0.015 | bounded set-specific **reject** |
| **group-law** `χ₃(x(Pᵢ−Pⱼ))` (this) | 489 | 13.0th | 0.261 | 0.854 | powered clean **null** |

**Direction of the result:** the CM-native group-law object was predicted to carry MORE structure and
carries LESS — a routine null. The bounded cubic concentration Brick A found is therefore **not** a
property of the elliptic-curve group law on the point set; it is a property of the **x-coordinate field
arithmetic** — the field subtraction `x_i−x_j` of the coordinate map `d↦x([d]G)`. This is a genuine
**refinement** of Brick A's reading: Brick A's "CM-mediated key-set×curve interaction" (it dissolves on
non-CM E′) is mediated through the **χ₃ character on field differences of x-coords**, and does NOT survive
into the group operation `Pᵢ−Pⱼ`. Consistent with `RESULT_c2_grouplaw_diffset_stageA_v1` (band-random arms'
group-law E3 was also bounded): the real 82's group-law E3 behaves like band-random/known-MT.

**Bound (power + scope), stated as a brick not a closure:** on the real 82, the marginal rank-1 all-ones
cubic-energy projection of the **group-law** difference set carries no detectable concentration OR
over-uniformity (two-sided p=0.261; family-wise 0.585), and is not set-specific (q_MT=0.854), at a firing
power that would have caught a β²-count excess of Δ≳100 (power 0.86). Scope: this bounds the **marginal
cubic projection of the group-law object**; it is blind by construction to orientation-odd, joint-triple,
and band-localized subspaces of that object. N=82 is the whole sample; raw p cannot strengthen.

## 4. What this does NOT close, and the redirect
Not a door shut. The group-law object's OTHER projections are untouched, and the redirect is now sharper:
because the Brick A concentration lives in the **x-coordinate field structure** (not the group law), the
productive next probe is to **characterize the field-difference β² excess itself** — which pairs / bit-bands
drive the +75 in class β² (Brick A §finding) — rather than the group-law joint object, which is now
bounded-null. The originally-listed triples `C(82,3)` and band-localized statistics remain open, but should
be built on the **field-difference** object, which is where the (bounded, set-specific) signal actually is.

## 5. Grade movement
No promotion elsewhere. This is a self-contained brick: a powered null on the group-law object + a falsified
prediction + a localization of the Brick A signal to x-coordinate field arithmetic. It sharpens, it does
not close.

*Predecessors: `RESULT_e3_owed_measurement_v1` (Brick A), `RESULT_diffset_cubic_cmvanishing_v1` (§Next-2
prediction, now falsified), `CORRECTION_e3_cmvanishing_interaction_reading_v1` (§5.3),
`RESULT_c2_grouplaw_diffset_stageA_v1` (band-arms group-law bound). Frozen spec:
`PREREG_grouplaw_e3_real82_v1.md`. Frontier #29.*
