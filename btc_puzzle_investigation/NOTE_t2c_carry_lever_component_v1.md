# NOTE — T2c carry is a LIVE lever-COMPONENT (constant-factor half), kept available to join a scaling effect

**Date 2026-08-26.** Companion to `RESULT_t2c_carry_partition_kangaroo_bench_v1.md` (the measured no-lever).
Purpose: T2c is NOT closed — it is a **proved, exact, reusable partial resource** that gives no advantage
*alone* but is explicitly kept on the shelf to be **composed with a future partner effect** that supplies
the missing scaling. This NOTE is the interface: what T2c provides, the hump it hits alone, and exactly
what a partner must add to get over it. (Statement-of-intent: an empirical/measured null ≠ a closed
avenue; a bounded component stays live.)

## What T2c PROVIDES (a real, PROVED resource — not nothing)
- **An exact, PUBLIC, scale-free ~1-bit constraint on the secret's GLV coordinates.** For `d` in a known
  interval `[2^(k−1),2^k)`, the carry `ε_LBE(d)=[(a mod n)+(b mod n)≥n]` (where `(a,b)=glv(d)`) is a
  publicly-determined function on an EXACT partition of the range (`P_k` law, `RESULT_t2c_range_carry_skew_exact_v1`),
  and equivalently an `(a,b)` **sign-region** (`ε ⇔ a+b<0`, contiguous — no fragmentation in 2-D).
- Grade `[PROVED — exact integer counts + 3-line sign-law]`. It is a genuine constant-factor / one-bit
  handle on `d`, tied to secp's CM/GLV endomorphism ring — the exploitable-structure locus the project
  works toward.

## The HUMP (why it gives no advantage ALONE — measured + theorem)
1. **One bit ⇒ constant factor.** `ε` is a single bit; conditioning any search on one bit removes ≤1 bit
   → ≤√2 kangaroo/BSGS speedup, never exponent movement. (Info-theoretic; measured: carry oracle adds
   nothing, `2Dor≈2Dfull`.)
2. **The GLV box does not shrink with the interval.** The balanced halves `(a,b)` span ~`√n` for any
   genuinely-2-D key, so the 2-D box (~`n`) exceeds the interval (`2^k`) whenever `k<log₂n`; the interval
   bound beats the endomorphism structure (λ-fold 2⁵⁸× worse; joint-with-carry measured 1.6–20× worse).

## What a PARTNER EFFECT must supply to compose OVER the hump
A join with T2c yields a real lever ONLY if the partner provides **exponent scaling** on one of the two
obstacles. Two concrete openings — WATCH FOR EITHER and, when found, join it to T2c's exact ε-constraint
and re-run the composed op-count benchmark (`t2c_carry_composition_bench_v2.py` is the harness):

- **(Partner A — beat obstacle 1) A family of ~independent public constraints whose count grows with
  `log(interval)`.** T2c gives 1 bit; N15 showed the readout tuple `(e, s-class, y-parity)` totals only
  **3.65 constant bits** (independent, `TC≈0`) — still constant, not scaling. A partner that yields
  `Θ(log 2^k)=Θ(k)` roughly-independent public bits about `d` would, joined with the carry, cut the search
  super-constantly. (Where might scaling bits live? Not per-point readouts. Candidate: a multi-scale /
  recursive decomposition, or a CM/Hecke channel giving a bit per prime of `N`.)
- **(Partner B — beat obstacle 2) A mechanism that CONFINES the GLV halves `(a,b)` to a sub-box that
  shrinks with the interval.** The box is ~`√n` because the lattice basis is ~`√n`; a partner sublattice /
  torsion / second-endomorphism constraint that pins `(a,b)` into a region of area `≪ n` (ideally
  `~2^k`) would let T2c's contiguous ε sign-region compound into a real 2-D reduction. (Candidate:
  anything from the CM/Hecke route that constrains the Frobenius action on the point beyond the single
  GLV λ.)

## Join protocol (for the future session that finds a partner)
1. Confirm the partner is INDEPENDENT of the carry (not a re-encoding of the same 1 bit / same box) — else
   it adds nothing (N15's readouts were near-independent yet still constant; independence is necessary,
   not sufficient — the partner must also SCALE).
2. Join it to T2c's exact ε-constraint and measure the COMPOSED op-count vs the 1-D interval baseline on
   `t2c_carry_composition_bench_v2.py`'s harness (same fair baby+giant metric).
3. RETAINED only if the composed `R_k` shrinks super-constantly in `k` (exponent movement), surviving the
   §7 artifact checks of `PREREG_t2c_carry_partition_kangaroo_bench_v1.md`.

## Status
`[VERIFIED-scope — no advantage ALONE]`, **KEPT LIVE as a composition component.** The exact carry law and
the ε sign-region are on the shelf; the search is now for a partner effect that supplies scaling (A or B).
Cross-refs: `RESULT_t2c_carry_partition_kangaroo_bench_v1.md`, `RESULT_t2c_range_carry_skew_exact_v1.md`,
`NOTE_carry_readout_leak_nulls_v1.md` (readout class null), `RESULT_curve_island_lambda_folding_v1.md`
(λ-fold obstacle 2), `RESULT_n15_joint_readout_confinement_v1.md` (3.65 constant bits — obstacle-1 evidence).
