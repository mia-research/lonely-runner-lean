# DEVIATIONS — `PREREG_kummer_family_b_capacity_v1.md`

*Filed with `RESULT_kummer_family_b_capacity_v1.md`. Six deviations; two are defects in the
pre-registration itself, one is a script bug that nearly produced a false falsification.*

---

**D1 — ★ Script bug: a broken instrument almost falsified a derived identity.**
The first run reported **P1 = 21516/227016 (205 500 violations)** with counterexamples at `(p,d,b,c) =
(13,2,1,2)` etc. **This was a code defect, not a result.** The character was computed as
`χ_d(u) = ζ_d^{dlog(u)//m}` (`m = (p−1)/d`) — the **power-residue-symbol** index — where the multiplicative
character of order `d` requires `χ_d(u) = ζ_d^{dlog(u) mod d}`. Corrected run: **227016/227016, zero
violations.**
**What caught it was the derivation `(★)`, not a review**: a result contradicting an identity proved
before the run is an instrument failure until shown otherwise. Had `(★)` not been pre-registered as
*derived*, "P1 falsified — residual `b`-structure exists" was the pre-committed reading, and it would
have been reported as the interesting outcome. **Third broken-instrument near-miss this session** (cf.
the `p ≡ 2 mod 3` cube-root bug in `RESULT_mu3_cover_jacobian_v1`).

**D2 — Spec defect: C2's threshold was never quantified.** §3 says the cross-class relation "must fail"
and §5 voids the arm if C2 "fails to fire", but **no numeric threshold was fixed**. Unfalsifiable as
written. Resolved post hoc by breaking C2 out per `d` (D3). Recorded as a defect in my own frozen spec —
the same class as the uncentred `D_int` primary caught by its own control in
`PREREG_flap_a_invariance_v1`.

**D3 — ★ C2 FAILS at `d = 4` and `d = 6`; by §5's own pre-commitment those arms are VOID.**
Per-`d` cross-class "accidentally related" rates:

| `d` | rate | verdict |
|---|---|---|
| 2 | 0.00% (0/36624) | fires |
| 3 | 0.00% (0/36624) | fires |
| **4** | **33.33%** (6912/20736) | **VOID** |
| **6** | **33.33%** (12208/36624) | **VOID** |
| 12 | 0.00% (0/20736) | fires |

**Substantive note, kept separate from the verdict:** C2 tests whether the `log₂3` bound is **tight**,
not whether it is **valid**. The upper bound follows from the derivation `(★)` alone and does not depend
on C2. A C2 failure means the three cubic classes are *not* fully separated at that `d`, i.e. capacity
there is **lower** than `log₂3`, never higher. **The direction of the conclusion is unaffected; the arm
is nonetheless void as pre-committed, and §5's capacity figure is reported as an upper bound only.**

**D4 — ★ Post-hoc narration printed as if it were analysis.** The follow-up script contained, in a
`print` written **before** the per-`d` numbers existed, the explanation: *"high rate at small `d` is a
PIGEONHOLE artifact: at `d=2` the canonical form is a single integer … collisions are expected."*
**Refuted by its own output — `d = 2` came back 0.00%.** The 33% sits at `d = 4, 6`, which the
explanation does not cover. The mechanism of the 33.33% is **unexplained and remains open**; do not
carry the pigeonhole story forward.

**D5 — C1 not broken out per `d`.** Reported only in aggregate (71.2% of wrong-exponent tests fail).
The pass fraction is partly structural — at `d = 3`, `χ₃(c)³ ≡ 1` identically, so a wrong exponent
coincides with the right one whenever `3 | dlog(c)` — so the aggregate understates the control's power at
large `d` and overstates it at small `d`. **Not decomposed; C1 should be read as fired-in-aggregate
only.**

**D6 — Out-of-spec addition: the `k = 12` analysis.** §4 of the spec fixed `d ∈ {2,3,6}` plus `{4,12}`
where the characters exist. The `k = 12` structural result at `p ≡ 7 mod 12` (where `χ₁₂` does **not**
exist over `F_p`) is **outside the registered scope** and is filed as **EXPLORATORY** in the result. It
is a derivation with a numerical confirmation, not a registered arm.
