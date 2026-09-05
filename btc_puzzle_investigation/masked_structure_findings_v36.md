# v36 — Following the S conservation to its symmetry (two mechanisms killed, one sector excluded)

**Date:** 2026-07-18 · **Scripts:** `_reflection_symmetry_hunt_v1.py`, `_odd_sector_conservation_v1.py`
(+ the v33–v35 machinery). Mantra: *hunt exact conservations; when found, follow to the deeper
symmetry; the leak/telling structure lives OUTSIDE the symmetry.*

> ## ⚠ SCALE BANNER
> All measured at `p ≤ 8000`. secp is `2²⁵⁶`. No power against a structure that switches on near
> `2²⁵⁶`. Everything here is `y²=x³+7`, `p≡1 mod 6`, `n=#E(F_p)` prime.

**The object being followed.** The open conservation from v34 §4: `⟨σ,χ₂⟩_FIELD = 0 ⟺ p ≢ 3 mod 8`
(the `p≡7 mod 8` regime, 35/35, unforced by the μ₆ selection rule). Last session killed the natural
multiplicative mechanism. This session follows it further and pins down *what kind of thing it is*.

---

## 1. The reflection mechanism — KILLED, with a structural reason  `[VERIFIED]`

**Candidate (rule 13: name it, kill it).** The hexagonal lattice `L=(π_p)` has symmetry group `D₆`
(order 12): 6 **rotations** `z↦ζ₆ᵏz` and 6 **reflections** `z↦ζ₆ᵏz̄`. The rotations descend to `F_p`
as multiplication by μ₆ — **these are the symmetry S lives outside of** (S is unforced *because* it
is a μ₆-matched pairing). The reflections were the next candidate: a `z̄`-type involution that flips
`σ` could pair the flap orbits with opposite sign and force `S=0`.

**Killed.** Constructing `τ(x) := eis⁻¹(conj(eis(x)))` and all six `R_k = β^k·(±1)·τ`
(`_reflection_symmetry_hunt_v1.py`, exact over all `x`, p=127→1249):
- **No `R_k` flips `σχ₂`** for all `x` (the `flips σ*χ₂` column is False at every prime).
- **`τ` is not even an involution** (`tau_inv=False`) and **not multiplicative** (`tau_mult=False`).

**The structural reason — this is the positive content.** The reflections **cannot** descend to `F_p`,
because `L̄ = (π̄_p) ≠ (π_p) = L`: `p` **splits** in `ℤ[ω]` (`p≡1 mod 3`), so the two primes above `p`
are distinct and conjugation is not a symmetry of the lattice. **The reflection maps E's coordinate
ring `ℤ[ω]/(π_p)` to the CONJUGATE `ℤ[ω]/(π̄_p)` — the amicable partner / the twist — not back to
itself.** So the involution that "should" enforce `S` points **outside `F_p`**, at the conjugate
object. *(This is the mantra's clause made precise: the structure is outside the symmetry
group — it is a map to a different object, not a self-symmetry.)*

**⇒ `S=0` is enforced by NO hexagonal-lattice symmetry of the `F_p` point set** — neither the μ₆
rotations (which it lives outside of) nor the reflections (which don't descend). Two mechanisms now
killed. The multiplicative-involution kill (v34) and this reflection kill together exhaust the `D₆`
lattice symmetries.

---

## 2. The S phenomenon does NOT extend to the odd/shadow sector  `[VERIFIED — a scoped null with a firing control]`

**Mantra probe.** S is an *even, x-only* conservation. The mantra says the leak/telling structure
lives outside that — in the **odd (y) sector**, the shadow half `x` is blind to (v16). Does the same
`p mod 8` conservation recur there?

**The odd analog** (`_odd_sector_conservation_v1.py`): `Sy := Σ_{P≠O} s_y(P)·χ₂(y_P)`, both factors
odd in `y`. Per `x`, the two points `(x,±y)` give `sign(y)χ₂(y)[1−χ₂(−1)]`:
```
Sy = 0                         at p ≡ 1 mod 4   (χ₂(−1)=+1)   — FORCED (the control), 19/19 exact
Sy = 2·Σ_{x:QR} sign(y)χ₂(y)   at p ≡ 3 mod 4                 — NOT forced
```

**Result: at `p≡3 mod 4`, `Sy` is generic** (p=127→5953, 30 primes): `Sy=0` in **1/30**, and by
`p mod 8`: **`p≡7 mod 8` gives `Sy=0` in 0/16** (generic ≈0.58), `p≡3 mod 8` in 1/14. **`Sy²/p`
bounded ≲ 20 (Weil scale).** No `p mod 8` conservation.

**⇒ The S law is FLAP-SPECIFIC — it does not extend to the y-coordinate.** It is not a generic
"even/odd + `p mod 8`" phenomenon (if it were, `Sy` would show it too). This is a clean exclusion:
the forced `p≡1 mod 4` zero fires as the control, and against it the `p≡7 mod 8` regime is flat.

---

## 3. Where that leaves S — localized to the flap boundary  `[the named next probe]`

Three sides now pin S:
1. **Not any `D₆` lattice symmetry** of `F_p` (§1).
2. **Not a generic even/odd + `p mod 8`** effect (§2, the y-analog is generic).
3. ⇒ it is tied specifically to **`σ` = the flap indicator**, whose boundary is `|u∓v| = ½`. **`2`
   enters through that boundary** (`2|u∓v| = 1`), which is why the law is a `χ₂(2)` = `p mod 8`
   statement.

**Restated as a pure lattice-count, verified 44/44:**
```
flap ≡ 0 (mod 12)   ⟺   p ≡ 7 (mod 8)          [p ≡ 3 mod 4, p≡1 mod 6, n prime]
flap ≡ 6 (mod 12)   ⟺   p ≡ 3 (mod 8)
```
(`flap = 6·ORB`; `ORB` even ⟺ `p≡7 mod 8`.) This is **H1** of v34, now isolated from all curve
arithmetic: it is a statement about `#{x∈F_p : eis(x) in the flap}` mod 12. **Deriving it is a
Gauss-circle-type boundary-lattice-point count with a `χ₂(2)` refinement** — the remaining named
probe. Not closed here; the drill ends in this sharper, self-contained lattice statement (per the
Anomaly-Drill rule: a named next probe, never a closure).

**Still, separately: when `ORB` is even, `S=0` (not merely allowed) — 35/35.** H1 explains *when
parity permits* `S=0`; it does not explain why `S` actually *hits* 0 rather than some even nonzero.
That second half remains the open core, and §1–§2 have removed every symmetry explanation
for it. It may be a Gauss/Jacobi-sum identity specific to the flap indicator against `χ₂`; that is
the next object.

---

## 4. Bearing on leakage, and what the mantra probe returned

**None on leakage.** All of this is `σ`/`χ₂`/`s_y` — x-only and y-parity readouts, inside the Part V
bounded-degree bound. The mantra said *look outside the symmetry, in the shadow sector, for the leak*;
§2 did exactly that (`Sy`, the odd sector) and found it **Weil-generic** — a scoped null (p≤5953)
with the forced `p≡1 mod 4` control firing. **No leak surfaced; the odd-sector conservation is only
the forced zero.**

**Positive returns:** (i) the S conservation is now known to be *non-symmetry* in origin — the two
lattice-symmetry classes are exhausted and both fail, for the precise reason that `p` splits and the
reflection lands on the conjugate prime; (ii) the phenomenon is flap-boundary-specific, isolated to
the self-contained lattice fact H1; (iii) the shadow sector was checked and is generic, so S is not a
gateway to the odd half.

---

## 5. Reproduction
```
python3 _reflection_symmetry_hunt_v1.py 100 1300     # D_6 reflection candidates: all fail to flip σχ₂
python3 _odd_sector_conservation_v1.py 100 6000      # Sy: forced 19/19 at p≡1 mod4, generic at p≡3
```
Signal paths exact int; float only in the generic-rate reference (`_odd_sector` line 89). The
`flap ≡ 0 mod 12 ⟺ p≡7 mod 8` restatement of H1 re-verified 44/44 (p≤8000).
Prior context: `masked_structure_findings_v34.md` §4 (the S law), `v35` §8–10 (session-2 follow-ups).
