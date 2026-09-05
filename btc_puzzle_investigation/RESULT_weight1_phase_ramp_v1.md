# RESULT — Brick C: the weight-1 phase channel is (a) NOT publicly per-point constructible, (b) parity-restricted to p≡3 mod4, (c) a bounded null where it exists (v1, 2026-08-21)

**Executes** `PREREG_weight1_phase_ramp_v1.md` (frozen). **Deviations:**
`PREREG_weight1_phase_ramp_v1_DEVIATIONS.md` (D1 covariant control = pure-(1,1); D2 p≡1 mod4
inadmissible; D3 ε_min analytic; D4 secondary/OOS). **Brick C** of `ROADMAP_REDIRECT_v3.md` — "phase on
the weight-1 eigenspace." Script `weight1_phase_ramp_v1.py`. Exact int/Fraction signal path; float only
in the phase carve-out. Model scale (p ≤ 1303); no `2²⁵⁶` claim; no ECDLP claim.

---

## 1. Three findings, in order of durability

**(a) `[STRUCTURAL]` The literal Brick-C object has no public per-point realization.** The A_new
weight-1 eigenspace is a **frequency-domain / cohomological** object (its per-point access is the
character sum `V(a)=Σ_d χ₂(y_d)e_n(ad)`, a sum over all `d` containing the target frequency). There is no
on-disk public map `single point P_d ↦ vector in H¹(A_new)` that is public, per-point, and linear for an
oblique projector to act on. The only public per-point lift (`eis(x)`) is **x-only ⇒ `[−1]`-invariant**,
so it cannot by itself break the `[−1]/μ₄` symmetry M16's no-go rests on. Brick C's phase-ramp idea is
therefore tested through a **proxy** (public per-point phase from `eis(x)` ⊕ `χ₂(y)`), with the coverage
gap below.

**(b) `[VERIFIED-exact + STRUCTURAL]` The weight-1 `[−1]`-odd phase channel exists ONLY at `p≡3 mod4`
(secp's class).** The `[−1]`-odd component needs `χ₂(y)` to be `[−1]`-odd, i.e. `χ₂(−1)=−1`, i.e.
`p≡3 mod4`. At `p≡1 mod4` (`χ₂(−1)=+1`), `φ₀` is `[−1]`-invariant and the `s=1` (`[−1]`-odd, weight-1)
isotypes are **identically zero** (`A_{j,1}=0`) — the readout is `arg(0)`, degenerate (gate `G=1.0` for
both the oblique and the pure-(1,1) control). So `p=349` (`≡1 mod12`) is **inadmissible**; the channel
lives only on the secp class. This mirrors the M4 parity law (`V(a)` real at `p≡1 mod4`, imaginary at
`p≡3 mod4`).

**Admissibility gate (secp class, p=163).** Oblique `M`: `G=0.0557 ≥ 0.05` → breaks μ₆ (PASS, but
marginal — the break is weak). Pure-(1,1) covariant control: `G=0.0000` (confirms the ramp and the
discriminator).

**(c) `[EMPIRICAL — bounded null, secp class, powered]` Where it exists, the channel does NOT align with
`a·d`.** Full-group phase-lock statistic `S_p=|R_p(1)|`, permutation null (B=2000) preserving `{Φ(d)}`,
secp-class ladder:

| p | n | S_p | p_perm |
|---|---|---|---|
| 163 | 139 | 0.068 | 0.534 |
| 823 | 829 | 0.019 | 0.738 |
| 907 | 967 | 0.020 | 0.678 |
| 991 | 1009 | 0.005 | 0.985 |
| 1051 | 1093 | 0.014 | 0.805 |
| 1303 | 1249 | 0.042 | 0.104 |

**Fisher `X = 7.62`, dof 12** (`χ²₀.₉₉ ≈ 26.2`) → **bounded null**. All `p_perm ≥ 0.10`. The **hard plant**
(a genuine d-linear ramp `Φ*(d)=2πd/n`) **fires** (`S=1.0`) at every prime — the test detects a real
ramp, so the null is not a power failure. Detectable amplitude `ε_min ≈ 2.6/√(n−1)` (≈0.20 at p=163,
≈0.07 at p≈1300; §5 analytic).

---

## 2. What this bounds, and what it does NOT (coverage gap — first-class output)

- **Bounds:** the **public per-point** weight-1 `[−1]`-odd phase (the `(j=1,s=1)` isotype of the
  `eis⊕χ₂` proxy) carries no d-linear alignment to `a·d` above `ε_min`, on the secp class, at model
  scale. This is the axis M14's forced-magnitude theorem left open (phase, not magnitude), in its
  publicly-realizable proxy form — a bounded phase channel with power + scope, **not a closure**.
- **Does NOT bound:** the true **frequency-domain** A_new weight-1 eigenspace phase. The identification
  "`eis`-isotype `(1,1)` ↔ A_new cohomological weight-1 subspace" is **unproven** (N9: the module `W`
  unidentified). The frequency-domain object is separately governed by M14/M16 and is not touched here.
- **Consistent with the redundancy barrier** (`ANALYSIS_public_gate_glv_carry_circularity`): a public
  function of `P_d` is redundant with `P_d`, so a d-linear public phase would be a DLP break — the
  bounded null is the expected outcome, now measured with power + scope rather than asserted.
- **Distinct from M28** (the proven k=3 `b`-phase that does not leak `d`): this is `d`-indexed,
  eigenspace-restricted, aimed at `a·d`; it uses no `b`-sweep and no `T`. A positive would have been a
  new channel; it is null.

---

## 3. Grade and the brick

| item | grade |
|---|---|
| literal weight-1 eigenspace phase not publicly per-point constructible | `[STRUCTURAL]` |
| channel `[−1]`-odd ⇒ exists only at `p≡3 mod4` (`A_{1,1}=0` at `p≡1 mod4`) | `[VERIFIED-exact + STRUCTURAL]` (mirrors M4) |
| public per-point weight-1 phase does not align with `a·d`, secp class | `[EMPIRICAL — bounded null, powered, scoped]` (Fisher X=7.62, plant fires) |

**Brick.** Brick C asked whether phase on the weight-1 eigenspace separates character from random (the
axis M14 left open). Answer at model scale: the **publicly-realizable** version of that phase (i) only
exists at `p≡3 mod4`, (ii) barely breaks μ₆ even there, and (iii) is a bounded null against the
`d`-linear target. The **frequency-domain** version — the object M14/M16 actually govern — is not
publicly per-point accessible at all (finding (a)), which is itself the reason the arsenal's phase route
is not a public leak. A durable redirect: the weight-1 phase, in every form reachable from public
per-point data, is bounded or non-existent, with the coverage gap to the frequency-domain object named
(N9) as the only thing left open on this axis.

**Scale banner.** `p ≤ 1303`; secp is `2²⁵⁶`. No claim about presence/size at secp. In-bounds
(number-theoretic key structure; uniform `d`; not the PRNG).

*Grade legend: STRUCTURAL · VERIFIED-exact · EMPIRICAL (bounded null, powered).*
