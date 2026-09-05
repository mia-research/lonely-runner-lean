# DEVIATIONS — `PREREG_mu3_diffset_control_repair_v1.md`

Mandatory per §11, filed even if empty. **7 deviations; D2 and D6 are material.**
Answers to the §11 checklist are in §8 below.

---

**D1 — `β` vs `β_GLV` conflated in the R2(vi) assertion (fixed; forcing unaffected).**
§8 says "β fixed once". There are two distinct order-3 constants: the χ₃ *labelling* reference
(`β`, smallest-`g` route) and the endomorphism's x-scaling (`β_GLV`, where `x([λ]P) = β_GLV·x(P)`).
Measured: `β_GLV == β²`. The first R2(vi) assertion tested `β` and **failed 0/40**, correctly
tripping F5. Replaced by the substantive assertion — `x([λ]P)/x(P)` is a *single* constant over all
P (1 distinct value / 40 points), it has order 3, it is recorded as `β` or `β²` rather than assumed,
and `χ₃(β_GLV)` is primitive. Since `⟨β⟩ = ⟨β²⟩`, orbit closure and the forcing are identical either
way; R2(iv) is now asserted for both. **No result changed.**

**D2 — PC-B's accept rule replaced (material; three iterations, each measured).**
§4.2 specifies `accept Q iff 3·c ≥ |S| + ⌈δ·|S|·3⌉`. That rule selects the **upper tail**, so it
overshoots its own target: measured `ε̂ = 0.077` at `δ = 0`, where the plant should be nil, and the
ladder saturated near `ε̂ ≈ 0.12` — never reaching the `ε ≈ 0.02–0.04` region where `ε₈₀` lives.
A band *centred* on the target fixed `δ = 0` (`ε̂ = 0.0008`) but undershot for `δ > 0` and saturated
at `ε̂ ≈ 0.026`, because candidate density is asymmetric across the band. Both are open-loop.
Adopted: a **closed-loop integer servo** — accept only if the candidate moves the *running* class-0
excess toward the target; `δ` carried as the exact rational `dnum/10000`; every comparison integer.
Result: `ε̂` hits every target within 2% (0.0003 / 0.0139 / 0.0211 / 0.0311 / 0.0413 / 0.0492 against
0 / 0.0141 / 0.0211 / 0.0311 / 0.0415 / 0.0500). **Consequence for interpretation:** the servo pins
`ε̂` with lower variance than a natural effect, so PC-B's power curve is optimistic; the reported
bound quotes PC-A/analytic `ε₈₀ = 0.0415`, not PC-B's 0.036 (RESULT §2, F7).

**D3 — `ε̂` initially computed on `max(nx)` instead of class 0 (fixed).**
§4.2 defines `ε̂ = (3n₀ − n_p)/(2n_p)` with `n₀` the *planted* class. `max()` carries a positive
bias (~+0.010 at `n_p = 3321`) even with no plant. Corrected to `nx[0]` before the run. For the
**studied** sets, where no class is planted, class 0 is not the right descriptor either; RESULT §1/§4
therefore quote the *dominant-class* excess, computed separately and labelled as such.

**D4 — the F2 gate was inverted (fixed before the run).**
§4.4 states "PC-B **inside** its surrogate ⇒ PC-B is defective". The gate initially passed when
PC-B's `E3` was *below* its surrogate — the reverse. Corrected: the gate passes when the planted
excess sits **above** the surrogate's 97.5% (measured 0.99 / 1.00).

**D5 — the frozen null arrays were not persisted (procedural).**
§11 asks for `mu3_diffset_frozen_null_v1.npz`. Only `mu3_diffset_meta_v1.json` was written
(region bounds, means, correlations, gate statuses, β, `g`, seeds, `m`, `n_pairs`, N). The empirical
order statistics are therefore not available for an exact rank-p, and the p-values in RESULT §4 use
the `Exp(n_p)` reference instead — defensible only because F4 passed (the reference matches the
measured region to 0.3–2.3%), but it is a weaker path than specified. The nulls are reproducible
from the recorded seeds.

**D6 — cell B is void: studied draw ≡ null draw (material; not a conclusion).**
`mu3_diffset_run_gates345_v1.py:361` `drawB` is used both for cell B's null (line 369) and for its
"studied" constructed-160 set (line 416), on the same RNG stream. The studied draw is a sample from
its own null, so the cell has no hypothesis. Its numbers are recorded and **not interpreted**
(RESULT §4). The ambiguity originates in §3.1, which gives cell B's null as "m = 160 drawn uniformly
from the whole pool" without assigning the studied draw a different provenance; the implementation
resolved it degenerately. Cell A is unaffected — its studied set is the actual 82 solved keys against
a bit-length-matched null from the 100k pool.

**D7 — gmpy2 and batch inversion (not a spec change).**
§8's exactness requirement is unchanged: `mpz` integers and `powmod` only, `E3` from exact integer
class counts, no `abs`/`sqrt`/`|M|/√pairs` in any decision path. Montgomery batch inversion computes
the `C(m,2)` group-law differences with one modular inverse per point set instead of `C(m,2)`;
it is an exact identity, not an approximation. Pure Python would have made the specified `N` values
infeasible (~3 h for cell A's null alone vs 11 min).

---

## 8. §11 checklist

| question | answer |
|---|---|
| statistic changed? | **No.** `E3 = n₀²+n₁²+n₂²−n₀n₁−n₁n₂−n₂n₀`, integer, as specified. |
| sample filtered? | **No** for the studied sets. The v32-era undisclosed 4000-row pool slice was *removed*; the whole 36,000-row pool is used for both draw and null. |
| subset chosen post-hoc? | **No.** Both cells and both readouts were computed and are reported; no max over cells. |
| control fired? | **Yes** — PC-B 1.00 at ε≈0.05 in both cells, margins 2.22 / 8.65, above its multiplicity surrogate. The retired λ̂-closed cell asserted `E3 = 0` exactly, as predicted. |
| power stated? | **Yes** — `ε₈₀ = 0.0415` (cell A), measured by PC-A within MC error of the analytic value. |
| scope on every number? | **Yes** — `p` = secp256k1's prime, `E: y²=x³+7`, `m = 82`, `n_p = 3321`, group-law difference multiset, weight-1 cubic character. Small-`p₀` R3 checks inherit no scope. |
| conclusion matches §9.2? | **Cell A: yes**, row 1 verbatim. **Cell B: no row applies** — §9.2 has no row for a cell whose studied draw and null share a distribution, so no conclusion is drawn (D6). |
| N as specified? | **Yes** — N = 10,000 (cell A), 2,000 (cell B); PC-A 10,000/rung; PC-B 200 (A) / 50 (B) per rung. |
