# v37 — Deriving H1: the flap-parity law unified, sharpened, and reduced to a lattice-count lemma

**Date:** 2026-07-18 · **Scripts:** `_flap_count_formula_hunt_v1.py`, `_flap_parity_law_v1.py`
(+ v33–v36 machinery). Task: derive H1 (`flap ≡ 0 mod 12 ⟺ p≡7 mod 8`, v36 §3).

> ## ⚠ SCALE BANNER
> Measured `p ≤ 7000`. secp is `2²⁵⁶`. This is pure lift/lattice geometry — **no leakage bearing**
> (the flap count is an x-only object, inside the Part V bound). `y²=x³+7`, `p≡1 mod 6`, `n` prime.

---

## 1. The law, UNIFIED and SHARPENED  `[VERIFIED 61/61, incl. 38 out-of-sample]`

H1 (v36) was stated for `p≡3 mod 4` only. Computing `ORB = flap/6 mod 2` against `p mod 8` over all
`p≡1 mod 6` collapses it to a single clean statement:

```
(−1)^ORB  =  χ₂(2)  =  (−1)^((p²−1)/8) ,        ORB = flap/6
  ⟺  ORB even  ⟺  2 is a QR mod p  ⟺  p ≡ ±1 (mod 8).
```

Per `p mod 8`: `p≡1` → ORB even (all), `p≡7` → even (all), `p≡3` → odd (all), `p≡5` → odd (all).
**Verified 23/23 in-sample (`p<2500`) + 38/38 out-of-sample (`p∈[2500,7000)`) = 61/61.** This
**supersedes and unifies H1**: for `p≡3 mod 4`, `p mod 8 ∈ {3,7}` and the law gives ORB even ⟺
`p≡7 mod 8` — exactly v36's H1, now a special case.

**The `4·flap−p` hunt found no CM-invariant closed form** (`flap` is not `(p±t)/4` or any simple
function of `π_p=a+bω`, `t`, `f`). The arithmetic content is entirely in the **parity**, which is why
`p mod 8` (a `χ₂(2)` statement) and not the CM data governs it.

---

## 2. Exact reduction to a triangle lattice-count  `[PROVED]`

The flap `{x : |u−v| > ½}` (lattice coords of `eis(x)` in the reduced-basis rhombus) splits by `σ`:
`T⁺ = {σ=+1} = {u−v>½}`, `T⁻ = {σ=−1} = {v−u>½}`. From facts already `[PROVED]` on record:

- **`σ(−x) = −σ(x)`** (`[PROVED]`, v15 — field negation `x→−x` sends `(u,v)→(−u,−v)`). ⇒ negation maps
  `T⁺ ↔ T⁻`, and is **fixed-point-free on `F_p*`** (`p` odd) ⇒ **`|T⁺| = |T⁻| = flap/2`.**
- **`σ(βx) = σ(x)`** (`[PROVED]`, Cap Law Thm B). ⇒ μ₃`=⟨β⟩` preserves `T⁺`, and acts **freely** (its
  only fixed point is `x=0 ∉ flap`) ⇒ **`3 | |T⁺|`** and `T⁺` is `ORB` free μ₃-orbits.
- ⇒ **`ORB = flap/6 = |T⁺|/3`** `[PROVED]`.

All three verified 61/61 (`_flap_parity_law_v1.py` (b)). So the law becomes:

```
(−1)^(|T⁺|/3)  =  χ₂(2) ,     T⁺ = { x ∈ F_p : (u−v)(eis x) > ½ }  — a triangle in the rhombus.
```

**Finer exact fact** (what a proof must reproduce, `_flap_parity_law_v1.py` (c), 61/61):
`|T⁺| mod 6` is determined by `p mod 24` — `p≡1,7 mod 24 → |T⁺|≡0`, `p≡13,19 → |T⁺|≡3`. Since
`p≡1 mod 3` is fixed, this **is** the `p mod 8` law (`|T⁺|≡0 mod 6 ⟺ p≡±1 mod 8`).

---

## 3. The remaining lemma — Eisenstein/Dedekind lattice counting  `[named next step]`

What is left to prove is exactly:
```
|T⁺| ≡ 0 (mod 6)   ⟺   χ₂(2) = +1        (equivalently  (−1)^(|T⁺|/3) = χ₂(2)).
```
This is a **2D lattice-point count in a triangle, reduced mod 2** — the same setting in which
`χ₂(2) = (−1)^((p²−1)/8)` is proven classically (Eisenstein's lattice-point proof of the
supplementary law; Gauss's lemma). Structure established toward it:

- The map `x ↦ (u−v) mod 1` is an **additive isomorphism `ℤ[ω]/(π_p) ≅ (1/p)ℤ/ℤ`** (kernel `= {0}`,
  since the only in-domain rep with `u=v` is `0`). So `u−v ≡ c·x/p (mod 1)` for a fixed `c∈F_p*`, and
  `T⁺` selects the representatives whose **centered** `u−v` lands in `(½,1)` — a condition on the
  *joint* pair `(⟨αx⟩,⟨βx⟩)` of two centered sawtooths (the two lattice coordinates), i.e. a
  **Dedekind-sum-type** count, not a 1D residue count. This is why the mechanism is `χ₂(2)` (a
  boundary/`mod 8` effect) and not the CM data.

**Status: `[VERIFIED, reduced]` — not yet `[PROVED]` from scratch.** The empirical p-mod-8 coincidence
of v36 is now a unified exact law reduced by `[PROVED]` steps to one classical lattice lemma. The lemma
is the remaining step (a Dedekind-reciprocity / lattice-point count); the drill ends here, at a
named, self-contained, curve-arithmetic-free target — per the Anomaly-Drill rule.

---

## 4. What this settles

- **H1 is no longer an empirical coincidence.** It is `(−1)^{flap/6} = χ₂(2)`, unified over all `p`,
  out-of-sample verified, and `[PROVED]`-reduced to `(−1)^{|T⁺|/3}=χ₂(2)`, a triangle-lattice parity.
- This **completes the localization of the S law** (v36 §3): the `p mod 8` dependence of
  `⟨σ,χ₂⟩_FIELD` enters through this flap-count parity, which is now a pure `χ₂(2)` lattice statement
  with its remaining step named. (The *other* half of S — why, when parity permits, `S` actually
  *hits* 0 (35/35) — is still open and separate; see v36 §3.)
- **No leakage bearing** (banner). Positive: an empirical `p mod 8` law became an exact identity
  `(−1)^{flap/6}=χ₂(2)` with a proven reduction and a classical remaining lemma.

---

## 5. Reproduction
```
python3 _flap_count_formula_hunt_v1.py 100 2500     # no CM closed form; ORB parity = p mod 8 table
python3 _flap_parity_law_v1.py 100 2500 IN          # law + reduction steps (a)(b)(c), 23/23
python3 _flap_parity_law_v1.py 2500 7000 OOS        # out-of-sample, 38/38
```
Exact ints throughout (both scripts pass `check_no_float.py`). Prior: v36 §3 (H1), v34 §4 (the S law).
