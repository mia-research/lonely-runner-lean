# GATE REVIEW R2 (isolated) — QR-half domain adjudication for Brick E

**Input:** coordinator's structural facts (`brick_e_anew_Lpoly_v1.sage`) + the R1 review. **Question
adjudicated on the merits (not pre-decided):** is the μ₃-null MATCHED on the QR-half, i.e. was R1's
μ₆-bias an artifact of the full-group "primary domain"?

## DECIDABLE ANSWER: YES — the QR-half scalar / μ₃-null design is adequate; it resolves BOTH F1 and F2.

**F2 (well-posedness) resolved.** On the QR-half `y_P` is a QR ⇒ `√y_P ∈ F_p` ⇒ the fibre lift is
`F_p`-rational ⇒ `φ(P) ∈ A_new(F_p) = ⟨S(G)⟩`, cyclic of order `1893`. So `c⁺(d) = dlog_{S(G)}(S([d]G))
∈ Z/1893` is a genuine SCALAR, single-valued. (The full-group ill-posedness of R1-F2 was entirely the
non-QR half, whose images leave `⟨S(G)⟩`; excluding it removes the defect.)

**F1 (matched null) resolved — the ζ₄ relation genuinely exits the domain and does NOT fold back.**
Verified on three independent grounds:
1. **Only μ₃ preserves the domain.** Every covering automorphism realises an element of `Aut(E)=μ₆=⟨−λ⟩`;
   `λ` fixes `y` (GLV `(βx,y)`) so preserves QR-status, while every `μ₆∖μ₃` element carries the `−1`
   that flips it (`−1` a non-residue at `p≡3 mod4`). So the QR-half is a union of full `μ₃`-orbits and no
   larger symmetry acts in-domain. (Confirmed on the `p=43` set: `λ`-closed True, `−1`-closed False.)
2. **The ζ₄ intertwiner cannot even be stated among QR d's.** `(−λ)^6 = id` on the `d`-side, but the
   operator word `(ρσ)^6 = (ρ²)³ = [−1] ≠ id` on `A_new` (`ρ`=ζ₄ order 4, `σ`=GLV order 3). The
   factor-of-2 mismatch means the `ζ₄` relation `φ(−P)=ρφ(P)` is only defined up to the `±√y` sign — it
   is intrinsically a QR↔non-QR (cross-domain) statement and does not close within the QR-half.
3. **`ρ²=[−1]_{A_new}` forces no cross-orbit relation.** `ρ² =` deck involution `= identity on E`, so it
   relates `φ(P)` only to itself (as a Prym `−1`-eigenvector), never one QR `d` to another.

**Residual in-domain constraint beyond μ₃: NONE.** The sign convention for `√y_P` is itself μ₃-invariant
(`λ` fixes `y`), so it introduces no spurious cross-orbit relation. The μ₃-null over the `(n−1)/6`
QR-orbit representatives shares every forced in-domain symmetry and nothing more; `D_obs` below its
`D`-histogram is then genuine low-degree structure, not a null artifact.

---

## FINAL v2 DESIGN (defect-and-fix list to fold into PREREG v2)

**(a) Domain = QR-half scalar arm.** `d ∈ Q := {d∈[1,n): y_{[d]G} is a QR mod p}`; statistic
`c⁺(d)=dlog_{S(G)}(S([d]G)) ∈ Z/|A_new(F_p)|`. FREEZE the `√y_P` sign rule (e.g. the root in
`[1,(p−1)/2]`) — deterministic, μ₃-consistent. Full-group readout kept ONLY as control (d-iv).
*(Fix R1-F2; drop the "two arms agree on D" cross-check — the arms are structurally different objects.)*

**(b) Null (μ₃-matched).** Draw `c'⁺` uniform on ONE rep per `μ₃`-orbit of `Q` (the `(n−1)/6` reps);
propagate by `c'⁺(λd)=κ·c'⁺(d)`, `κ=1849` (verify `κ³≡1`, `κ≠1 mod 1893`, and that `κ` is GLOBAL not
per-orbit — the eigenvector structure says it is; confirm on the instrument). No other constraint. ≥2000
draws. Same domain `Q` for real and null (no selection bias). *(Fix R1-F1.)*
Read `D` per CRT factor (DEVIATIONS D1): headline `D = max` over the LARGE prime factor(s) of
`|A_new(F_p)|` (`631` at `p=43`, where the `Q`-values are distinct); the small factor (`3`) is a
consistency flag, not a degree.

**(c) Low-D threshold = null-histogram percentile, NOT a hard `N/3`.** Compute the μ₃-null `D`-histogram
(per large factor, over `Q`); declare "low D" iff `D_obs ≤` the null 1st-percentile (`π≤0.01`) AND `INV`
true (degree-`D` fit inverts uniquely for `d∈Q` given `c⁺(target)`). DROP the absolute `D≤N/3` gate
(uncalibrated for small #free-values). *(Fix R1-F3.)*

**(d) Firing controls — four, all must fire before the real read.** *(Fix R1-F4 + R1-F5 firing.)*
- (i) **Engine** (keep v1): planted `c*(d)=a₂d²+a₀ → D=2`, inversion recovers `d`. Mechanical.
- (ii) **Pipeline**: plant a μ₃-COVARIANT low-degree `c` (e.g. `c(d)=a·d^{i₀}`, `λ^{i₀}=κ`, degree `i₀`)
  and route it through the FULL null+π pipeline; require `π≤0.01` to FIRE. Exercises the null+permutation
  path that (i) does not.
- (iii) **Calibration**: draw `c⁺` FROM the μ₃-null; require `π ≈ Uniform[0,1]` (no systematic bias) —
  proves the p-value is calibrated (guards the R1-F1 failure mode empirically).
- (iv) **Structural (the coordinator's full-group readout)**: for each non-QR `d`, compute `φ([d]G)`
  directly in `A_new(F_{p²})` and independently `ρ·φ([−d]G)` (`−d∈Q`); assert EXACT equality in
  `A_new(F_{p²})`. Verifies the `F_{p²}`/`ρ` instrument AND that the non-QR half carries no independent
  content (the empirical warrant for the domain restriction). CAN fail (ρ/lift mis-built) ⇒ genuine
  control, not forced-trivial. Requires building the explicit order-4 ζ₄ endomorphism `ρ` on the
  instrument.

**(e) Ladder + per-rung power (orbit-rep counts).** *(Fix R1-F5 + scope defect below.)*
`#free values seen by the fit per rung = (n−1)/6` (the μ₃-orbit reps). Verified admissible rungs
(`p≡7 mod12`, `n=#E` prime, `6|(n−1)`):

| p | 43 | 67 | 79 | 163 | 211 | (547) |
|---|---|---|---|---|---|---|
| n=#E | 31 | 79 | 67 | 139 | 199 | 547 |
| μ₃-reps | 5 | 13 | 11 | 23 | 33 | 91 |

**SCOPE DEFECT — drop `p=331` from the frozen ladder.** `#E(F_331)=364` is COMPOSITE (`=4·7·13`),
`3∤(n−1)` ⇒ no order-3 `λ` ⇒ the μ₃ construction is UNDEFINED there, and it violates §0's "n prime".
§0's blanket "p≡7 mod12 ⇒ n prime" is false (also fails at 307, 367, 379, 439). Replace with an admissible
rung: `p=547` (n=547, reps=91) or `p=127` (n=127, reps=21); further verified options 823/907/967/991/
1051/1303. **Power:** `p=43` has ~5 free values ⇒ essentially no single-rung power (a low-degree fit to 5
values is unsurprising; the null histogram is broad) — a LEAD only. The powered claim is degree-STABILITY
across reps `{5,13,11,23,33,91}`; meaningful single-rung power begins at `p≥163` (reps≥23).

**Null-independent falsification arms (decisive, keep):** `D_obs ≥ max` over null draws (no reduction),
OR `D` not stable across the ladder ⇒ hypothesis refuted and `D_obs` becomes the cover-scramble degree
bound. These do not depend on the null being perfectly matched.

**Exactness:** all arithmetic mod `|A_new|` integer, no float (engine already exact). The `A_new(F_{p²})`
control (d-iv) is likewise exact-integer.

## Bottom line
The QR-half scalar / μ₃-null design is **adequate on the matched-null and well-posedness axes** — R1's
F1/F2 are dissolved by the domain restriction, with no residual in-domain symmetry. Remaining fixes
(c/d/e) are threshold calibration, two added controls, and the ladder scope correction (drop 331). With
those folded, PREREG v2 is interpretable.
