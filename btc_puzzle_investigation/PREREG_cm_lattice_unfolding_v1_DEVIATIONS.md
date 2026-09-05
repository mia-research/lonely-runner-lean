# DEVIATIONS — `PREREG_cm_lattice_unfolding_v1.md`

Run: `cm_lattice_unfolding_v1.py` (+ `cm_lattice_setup_v1.py` groundwork) → `cm_lattice_unfolding_run_v1.out`.

---

## D1 — transversal condition corrected (MATERIAL; the frozen `e=0∧s=0` does not quotient μ₃)

**Spec §3** defines the matched-null sample as the μ₆-transversal via `e=0 ∧ s=0`, claiming this
"quotients out" the μ₆ lockstep so a `Φ↔T` shuffle is a valid null (`N≈(n−1)/6`).

**Defect found at implementation.** `eps` and `s` are BOTH constant on the μ₃-suborbit `{φ^j P}`:
`φ(x,y)=(βx,y)` fixes `y` (so `s=[y>p/2]` is constant across `{φ^jP}`), and `eps` is μ₃-invariant
(function of `x`, `eps(βx)=eps(x)`). Therefore `e=0∧s=0` selects the **full μ₃-suborbit** `{φ^jP}` of
each core, `s=0` orbit — it removes the `[−1]` (μ₂) lockstep but **NOT** the `φ` (μ₃) lockstep. A
`Φ↔T` shuffle on that set would still manufacture μ₃-lockstep MI (the recorded 6–7σ soft-shadow
failure mode). It also does not give `N≈(n−1)/6` (it gives `≈(3/8)(n−1)`).

**Correction.** Use the TRUE μ₆-orbit transversal: exactly one canonical representative per scalar
orbit `{±λ^j d mod n}` (the min-`d` representative), `N=(n−1)/6` exactly. This quotients BOTH `φ` and
`[−1]`, so the `Φ↔T` shuffle is a valid matched null.

**Validated by the spec's own μ₆-witness.** Smoke (p=2089/2143): the full non-transversal set with a
plain `Φ↔T` shuffle shows inflation (`p_perm=0.066 / 0.002`) that the corrected transversal removes
(`p_perm=0.83 / 0.60`). The witness behaves exactly as §3 pre-committed (inflation present off-
transversal, gone on-transversal), so the corrected transversal is the admissible null.

## D2 — multiplicity: common pairing-shuffle max-T (not per-arm distinct nulls)

**Spec §2d** described one permutation loop recomputing all 8 statistics, with ARM N nulled by "permute
`Ψ` within `Φ` strata." **Taken:** a SINGLE common null — the `Φ↔T` pairing shuffle on the transversal
— applied to all 8 statistics (ARM P `MI(Φ_ℓ;T)` and ARM N `MI((Φ,Ψ)_ℓ;T)−MI(Φ_ℓ;T)`), family-wise
p = permutation rank of the max standardized statistic. Reason: (i) the within-strata Ψ-shuffle rebuilt
per draw made `B=9999` intractable (hours); (ii) the pairing shuffle is a valid common null for max-T —
it destroys `Φ–T` and `Ψ–T` together, so under it every statistic (including the ARM-N conditional
difference) is at its no-pairing null, which is exactly what family-wise max-T needs. Consequence: ARM
N here tests "does `(Φ,Ψ)` predict `T` beyond the no-pairing baseline," slightly weaker than the
"beyond `Φ` holding `Φ–T` fixed" conditional; disclosed. Each arm's single-test `p` is also reported.

## D3 — plant / hard-null at `B=1999` (not 9999)

**Spec §4** implies `B=9999`. **Taken:** the positive-plant ε-sweep and the 100-re-pairing hard null
use `B=1999` (min attainable `p=1/2000 < α=0.001`); the PRIMARY family-wise decision uses `B=9999`.
Cost only; no decision threshold affected.

## D4 — real-key witness: #135 only (#140 pubkey not on disk)

**Spec §6** names #135 and #140. Only #135's compressed pubkey is on disk
(`puzzle_kangaroo_pool.py:43`). The witness records #135's public secp feature `(eps, (u,v) mod 2)`.
Since `d_135` is unknown and (per the result) the channel is a bounded null, there is no actionable
`(a,b)` prediction to record — only the feature values, for the trail.

## D5 — power rung `p>10⁶` not run in the primary invocation

**Spec §6** includes one power rung `p>10⁶` per class. The primary run uses the three ladder rungs
`p>10⁴` per class (`N≈1700`, `I_min` reported per rung). The `p>10⁶` rung (`N≈1.6·10⁵`,
`I_min≈1.2·10⁻⁴`) is a tighter-power extension; runnable via `cm_lattice_unfolding_v1.py 9999 1000000`
but slower. Disclosed; the ladder rungs carry their own `I_min` so their bound is stated at their power.

---

## Not deviations
- Feature/target/partner objects exactly as §1 (Φ against `(π_p)` norm p; Ψ against `(π_n−1)` norm p,
  π_n the partner Frobenius with `N(π_n−1)=p`; T against `(π_p−1)` norm n). Frobenius/partner verified
  by exact norm identities `N(π_p−1)=n`, `N(π_n−1)=p` at every rung.
- Disjointness: `d` never in the Φ/Ψ path; `X` never in the T path (construction-by-inspection).
- Exact int/Fraction signal path; `math.log`/`log2` only inside the MI estimator, ranked vs the
  permutation null.
