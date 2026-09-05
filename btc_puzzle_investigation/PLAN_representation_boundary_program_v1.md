# PLAN — the "invariant across a transformation boundary" principle, made operational

**Date:** 2026-08-13. Follows `ANALYSIS_public_gate_glv_carry_circularity_v1.md` (which failed the
principle's own gate). This is a **design menu**, not a result. No grade — nothing run yet.

The friend's principle, verbatim: *"The information, if recoverable, must arise from a relation between
representations. Construct an invariant/equivalence across the transformation boundary, then test whether
that equivalence determines the global branch independently. If evaluating it requires the original scalar
branch, the construction is circular."*

---

## 1. The principle as a 5-gate filter (every candidate must pass all five)

1. **Two genuinely different representations** of the same `d` (not two coordinates of one).
2. **An invariant** computable *across* the boundary.
3. **Circularity gate:** evaluating the invariant must NOT require `d` (or the canonical-orbit scalar `d₀`).
   — *the pasted pipeline died here: step 3 contained `d₀`.*
4. **Independence gate:** the invariant must pin the **global branch**, not merely a *relation between two
   unknowns*. — *χ₃ gave only `d = λ^j d₀`, a relation; it passed gate 3's public part but failed here.*
5. **Cost gate:** the representation the invariant lands in must be **no harder** than the source.
   — *the Weil/Tate pairing passes 1–4 but dies here: it lands `d` in `𝔽_{p^k}*` with k astronomical.*

## 2. The load-bearing constraint (a lever, not a wall)

**Any invariant that is a function of one public point `P=dG` alone is redundant with `P`,** hence carries
`d` only up-to-DLP. So: *non-circular + purely-public + single-point + determines-a-bit-of-`d`* ⟹ a DLP
distinguisher on one point ⟹ as hard as DLP. This does not close anything; it tells us **where a
non-circular win can come from** — exactly one of three:

- **(S) side-information on `d`** — short scalar (`N`-bit puzzle key), interval, or a known linear relation
  among several points. The extra constraint lives in one representation; the invariant couples it to the other.
- **(J) a joint invariant over a SET** whose relations are known (Semaev-type `ΣP_i = O`). Matches the
  standing memory: *the only signal surviving the ECDLP scramble is a joint property of the set, not a
  one-point readout.*
- **(T) a transfer** that lands `d` in a **genuinely easier** representation (anomalous lift, weak isogeny).

## 3. The faithful reading — the "carry" IS a p-adic digit

The archetype invariant-across-a-boundary that *does* determine the branch is the **SSSA anomalous attack**:
for `#E(𝔽_p)=p`, the reduction sequence `0→E₁(ℚ_p)→E(ℚ_p)→E(𝔽_p)→0` with `E₁ ≅ (p𝔽_p,+)` via the formal
log `λ` gives `d ≡ λ(pQ̃)/λ(pP̃) (mod p)` in **one p-adic digit** — the "carry." Poly-time. Class **(T)**.

**Why it fails for secp (`n≠p`), stated precisely** — and it is a clean instance of gate 3, not hand-waving:
lift `P,Q=dP` to `P̃,Q̃ ∈ E(ℚ_p)`. The lift of `Q` is only defined up to `K ∈ E₁` (the reduction kernel):
`Q̃ = dP̃ + K`. Multiplying by the order `n` (which kills reduction): `λ(nQ̃) = d·λ(nP̃) + n·λ(K)`.
- Anomalous (`p`): `λ(pP̃)` has valuation 1, `p·λ(K)` valuation ≥2 ⇒ error `≡0 (mod p)` ⇒ `d mod p` clean.
- secp (`n`): **`n` is a p-adic unit**, so `n·λ(K)` does NOT gain valuation. The unknown lift term `K` enters
  `d` at the **leading** digit. The branch re-enters through `K`. **Circular, via the lift ambiguity.**

This is the sharp restatement of the whole problem: *the missing carry is entangled with the free lift `K`,
and `n≠p` removes the valuation gap that suppressed it.* The principle now says something concrete: **find a
second representation that constrains `K`.** That is a well-posed, open question — not a wall.

## 4. Candidate boundaries (each with the gate that bites + a firing control)

| # | boundary (rep ↔ rep) | candidate invariant | which gate bites | small-curve firing control |
|---|---|---|---|---|
| A | `E(𝔽_p) ↔ E(ℚ_p)` formal group | p-adic elliptic log ratio (the carry) | 3 via lift `K` (§3) | anomalous curve `#E=p`: attack recovers `d` |
| B | `E/𝔽_p` (ord `n`) ↔ **amicable** `E'/𝔽_n` (ord `p`), via global CM lift | transport of a point across the aliquot 2-cycle | 3 (transport needs global lift) — **but** may constrain A's `K` | small Silverman–Stange amicable pair |
| C | point rep ↔ symmetric/resultant rep (Semaev) over a SET `ΣP_i=O` | branch-independent symmetric function + known sum (class **J**) | 5 (decomposition cost) | planted relation on small curve fires the sieve |
| D | short interval `d∈[0,2^N)` ↔ CM/GLV lattice rep (class **S**) | interval-restricted CM statistic vs full-group | must beat kangaroo `√`-cost | plant a short-`d` bias; kangaroo baseline |

The one that is *both* faithful to the "carry" language *and* has an unexploited second representation to try
is **A constrained by B**: use the amicable `n`-adic companion to pin the lift ambiguity `K` that kills A
alone. Neither A nor B alone passes; the open question is whether the **pair** does (an `{p-adic, n-adic}`
consistency condition on the same CM lift).

> **STATUS 2026-08-13 — A+B RESOLVED: closed by circularity (PROVED).** Pre-registered and rejected at
> Item 1: `PREREG_amicable_nadic_K_constraint_v1.md`. The companion `E'/𝔽_n` is a **real** anomalous SSSA
> oracle (fact 1), but its input port is `Q mod n = [d](G mod n)` — *applying the secret*. Exact witness
> (`b=3, p=199, n=211, G=(1,2)`, independently reproduced): `d=137` and `d=348` share the public p-state
> `(34,30)` but have distinct n-avatars — because `ord_p(G)=n ⟂ ord_n(G)=p`, the public p-side fixes only
> `d mod n` and leaves `d mod p` (what the n-oracle needs) CRT-free. Zero public bits; not an empirical null.
>
> **General lesson (redirects the program).** The CRT wall is not specific to this pair: **any single-point
> transport to a companion/transfer representation cannot manufacture `d mod p` from public p-side data.**
> So the faithful reading of the principle is now sharper — the "relation between representations" must be
> anchored by **class (S)** side-information that directly constrains `d` (boundary D, the `N`-bit puzzle
> interval) or **class (J)** a joint property of a *set* (boundary C), never a lone-point crossing. This is
> the standing memory restated from the p-adic side: *the only signal surviving the scramble is a joint
> property of the set, not a one-point readout.*

## 5. Recommended first test (needs `experiment-designer` pre-reg before running)

**Object:** the residual of the p-adic elliptic-log ratio on a **non-anomalous CM curve** `y²=x³+b`.
**Question:** does any public/second-representation constraint reduce the entropy of the lift term `K`
(equivalently: recover any digit of `d`) — tested against a matched null over random lifts `K`?
**Firing control (mandatory):** identical machinery on a small anomalous curve must recover `d` exactly.
**Exact arithmetic:** `ℤ_p` to fixed precision via `int`; no floats in the signal path.
**Falsification:** random-`K` scramble makes the recovered digit uniform ⇒ SCOPED NULL at that precision/curve
size; a surviving constraint from the `n`-adic companion ⇒ a real cross-representation lever to escalate.

Pre-register statistic + power + scope + matched control with `experiment-designer`, then run on the small
family before any claim.
