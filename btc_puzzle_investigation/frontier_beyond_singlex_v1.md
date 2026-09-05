# Beyond Single-x: the Two Frontiers — verified facts vs open questions (v1, 2026-07-13)

After the single-`x` chart (rhombus angle law + `χ₆`-uniform + GLV-orbit + norm-band),
the remaining structure lives off that axis. Neither frontier is closed. Frontier 1 rests
on a *citation* only; Frontier 2 is a short list of exact facts plus a *reduction* to the
(unproven-hard) DLP — not a proof of anything. Verification of Frontier 2's exact facts:
`frontier_beyond_singlex_v1.py`.

## Frontier 1 — joint / multi-point across keys (cited, not proved here)

The relevant analytical input is standard equidistribution: `d ↦ x([d]G)` is measure-
preserving, and for scalars drawn from ranges `≫ √p` the single-`x` coordinate
equidistributes with discrepancy `O(p^{-δ})` (Weil / Kohel–Shparlinski character-sum
bounds). For *independently* drawn such keys, the single-`x` marginals are jointly
near-uniform to the same order. That is the extent of the established statement.

What this does **not** establish, and what is therefore left open:
- it is a statement about **marginals up to `O(p^{-δ})`**, not a proof that the joint
  distribution carries no exploitable structure;
- it says nothing about keys from **short ranges** (`< √p`, the small puzzles), where
  `x([d]G)` does **not** equidistribute;
- whether scalar-selection dependence (e.g. a PRNG relation) leaves a **detectable**
  curve-side trace is **not** settled. No finite mutual-information check can prove
  undetectability — a null on a few coarse features and a bounded sample is a scoped
  observation, nothing more. This remains genuinely open.

## Frontier 2 — y / group-law: what is verified, and what is only a reduction

**Verified (exact integer computation):**
- `N(π_p) = p`; `N(π_p − 1) = n` (the secp group order); Frobenius trace `t = p+1−n`.
- GLV `[ω]` fixes `y`: `φ(x,y) = (βx, y)`, and `x³+7` is invariant (`β³=1`).
- `y`-parity flips under `d ↔ n−d` (with `x` unchanged).

That is the whole of what is proved here. Everything below is **cited or argued, not
proved**, and does not close anything:

- **Cited, not proved:** `E(𝔽_p) ≅ ℤ[ω]/(π_p − 1)` as `ℤ[ω]`-modules. I verified only
  that the *order* matches (`N(π_p−1) = n`), which is necessary but **not** sufficient;
  the isomorphism itself is standard CM theory (Deuring), taken on citation.
- **A reduction, not a characterisation:** if a "linear lift" `Λ` with `Λ([d]G)=d·Λ(G)`
  were efficiently computable, then `d = Λ([d]G)·Λ(G)^{-1}` in `ℤ[ω]/(π_p−1) ≅ ℤ/n`
  solves the discrete log. So computing `Λ` is **at least as hard as the DLP** — i.e.
  this reduces the `y`/group-law lift question to the DLP, **whose hardness is itself
  unproven**. This is a reduction to a conjecture, not a proof that the `y` side is
  closed, and not a "characterisation of ECDLP." No closure claim is warranted.

## Net position (what is and isn't proved)

- **Single-`x` axis:** each single-`x` marginal is shown scalar-independent by
  exact/symbolic argument (rhombus angle law; `χ₆` uniform; GLV shifts; norm band). These
  are the genuine positive results.
- **Joint across keys:** only the *cited* Weil equidistribution of single-`x` marginals
  (independent keys, ranges `≫√p`). Joint exploitability, short-range keys, and
  dependent-key detectability are **open**. Nothing proved.
- **`y` / group-law:** a handful of exact facts (above) plus a **reduction** of the lift
  question to the (unproven-hard) DLP. Not closed; not characterised.

No claim that the curve side is "closed," that a locus is "the only tractable one," or
that anything reduces to a *proved*-hard problem. Those would all be assertions, and are
not made.
