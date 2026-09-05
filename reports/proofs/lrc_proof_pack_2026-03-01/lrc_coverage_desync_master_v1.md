# Coverage Desynchronization Master Note (v1)
Date: 2026-03-04
Status: Theorem-track framing note (not closure claim)

## 0) Executive verdict on the proposed mechanism
The proposed "rotating windows" mechanism is the right overarching geometry, with one necessary correction:

- It is exact as stated only in the **unit** regime (`gcd(e,n)=1`), where each runner contributes a 2-residue window.
- In composite/non-unit scope (`g=gcd(e,n)>1`), each runner contributes a **coset-union support** with size in `{0, g, 2g}` depending on divisibility of `-t` and `-(t+1)` by `g`.

So the unified object is not always "2-residue windows", but **rotating support sets** on `Z_n`.

This corrected geometry still supports the same master architecture.

---

## 1) Unified object (scope-safe)
For `alpha in I_div=[1/n,(n-1)/n]` and `t_e(alpha)=floor(e*alpha)`:

- `S_e(alpha) := bad_set(e, t_e(alpha), n)`
- `C_E(alpha) := union_{e in E_fix} S_e(alpha)`
- `R_E(alpha) := Z_n \ C_E(alpha)`

Case question (fixed-runner side): does `R_E(alpha)` become non-empty for some interior `alpha`?

Equivalent residue form:
- `Cov_e(r) := {alpha in I_div : r in S_e(alpha)}`
- `Miss(r) := I_div \ union_e Cov_e(r)`

Then `Miss(r) != empty` iff there are interior states where residue `r` is uncovered.

---

## 2) Why this unifies Y, Z, V, W
- Y-track (SL-1 style): existence/measure of `Miss(r)`.
- Z-track (run caps): transitions where `S_e` changes and `R_E` opens/closes.
- V-track (period sum): same object restricted to interior `t_div` periods.
- W-track (affine count): counting fibers with `R_E(alpha) != empty`.

So these are not competing methods; they are two coordinates on one arrangement.

---

## 3) Canonical master chain (M1-M3 aligned)

### M1 (Transition algebra)
Across a non-coincident boundary `alpha=m/e*`, only runner `e*` updates:
`S_{e*}` changes from `bad_set(e*,t,n)` to `bad_set(e*,t+1,n)`.
All other supports fixed.

This gives local update control for `C_E` and `R_E`.

### M2 (Existence blocker)
Case-iiib blocker is exactly:
`exists r with Miss(r) != empty`.

### M3 (Continuous->discrete bridge)
Any interval `I subset I_div` yields
`#{b in B_div : b/L in I} = |I|*L + O(1)`.
So positive-measure miss implies linear safe mass slope.

Once M2 is proved, M3 gives `Lambda_eff>0`; M1 feeds transition/run/period derivations.

---

## 4) What from the suggested theorem is usable now

### Usable immediately
1. Desynchronization as core interpretation (yes).
2. One master lemma + multiple corollaries architecture (yes).
3. Z.2/V.4 duality at mechanism level (yes).

### Needs correction before theorem use
1. "Every runner is 2-window" (false outside unit regime).
2. "Missing runner uniquely defends some (alpha,r) pair" is too strong as stated without extra hypotheses.
3. AP-extremal uniqueness language should remain conjectural unless formalized separately.

---

## 5) Strong empirical invariants already supporting this geometry
(From current in-pack probes)

1. Case-iiib extended sweep (composite `n=10..30`, 694 templates):
- `best_miss >= 1/(e_max*(e_max-1))` : zero violations.
- miss endpoints denominator `<= n` : zero violations.
- best miss interval boundary-touch: zero.
- integer witness at `M=1`: zero failures.

2. Additional structure clue:
- For all 694 templates, the best residue `r*` was coverable by at least one dropped runner (`a` or `b`).
This suggests a promising "dropped-runner witness" route for M2.

---

## 6) Recommended next analytic target (single blocker focus)

### M2 via dropped-runner witness lemma (candidate)
Let `E_fix={1,...,n-1}\{a,b}` in Case-iiib.
Prove there exists `r` in `Cover(a) union Cover(b)` with `Miss(r) != empty`,
where `Cover(e):=union_t bad_set(e,t,n)`.

If this lemma holds, then:
- M2 closes directly.
- Y.3 quantitative bound follows from Farey spacing/endpoint control already locked.
- Z/V/W corollaries become derivations, not separate engines.

---

## 7) Immediate operational rule for agents
When working any open item (`Y/Z/V/W`), first translate it into the common object:
- identify target statement in terms of `S_e(alpha)`, `C_E(alpha)`, `Miss(r)`, and state transitions,
- then prove in that language before mapping back to original notation.

This prevents piecemeal drift and keeps all open work coupled to the same mechanism.


## 8) Scoped Closure Addendum (Siiib-U)

This addendum records a closed sub-branch so the master geometry file can be cited one-hop.

**Locked sub-scope `Siiib-U`:**
- one-div near-complete Case-iiib branch,
- dropped runners `a,b` are units: `gcd(a,n)=gcd(b,n)=1`,
- `n>=10`, one-parameter family as in the canonical scope lock.

**Theorem M2.SU (closed in `Siiib-U`).**
There exists a residue with non-empty miss interval:
`exists r*: Miss(r*) != empty`.

Explicit witness (Sole Cover): for each dropped unit `d in {a,b}`,
- `r_d = -d^{-1} mod n`,
- `I_d = (1/n, 1/(n-1))`,
- `I_d subseteq Miss(r_d)`, so `meas(Miss(r_d)) >= 1/(n(n-1))`.

**One-hop source:**
`lrc_dropped_runner_witness_v1.md` §11.

**M3 consequence in `Siiib-U`:**
Positive miss measure implies positive discrete safe slope (`Lambda_eff>0`) by counting bridge.

**One-hop source:**
`lrc_master_geometry_m1_m3_v1.md` §5 and
`lrc_ap_grid_extremizer_theorem_sequence_v11.md` §17.33.

**Residual open boundary (unchanged):**
This does not close global Gap-4 / S3. Open work remains outside `Siiib-U`,
including non-unit dropped regimes and broader Case-B/general scope.
