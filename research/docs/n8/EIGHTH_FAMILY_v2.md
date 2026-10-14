# The eighth-family, verified and formalised

2026-09-16. Successor to `~/ZCodeProject/lrc-n8/notes/EIGHTH_FAMILY_v1.md` (a parallel session's note,
relayed by the owner). Everything v1 claims was re-derived here from its own instruments; the theorem
stands, one paragraph of its proof does not, and the case v1 expected to need approximation theory
turns out to need nothing new at all.

Lean: `LonelyRunner/LRC/Cascade/EighthFamily.lean`. Cascade gate **177 theorems, axiom-clean, no `sorry`**.
Check script: `experiments/n8/eighth_family_check_v1.py`.

---

## 1. The family and the claim

Scale-normalised to `d_max = 8`, the set that shadows the largest flank is one-parameter:

    Δ(x) = {1, 3, 4, 5, 7, x, 8},   0 < x < 8.

At the `k`-th opening of the flank at difference `7` — `t = (k + 1/8)/7` — a difference `d` sits at
`d·(k + 1/8)/7` laps. Each fixed `d` is an integer, so its phase depends only on `k mod 7`.

## 2. What was verified  `[VERIFIED — exact rational arithmetic]`

- **The uncovered residues are exactly `k ≡ 1` and `k ≡ 3` (mod 7).** Confirmed by direct computation
  over all six fixed differences: `k ≡ 0` is blocked by `{1,3,4,5}`, `k ≡ 2` by `3`, `k ≡ 4` by `5`,
  `k ≡ 5` by `4`, `k ≡ 6` by `8`; `k ≡ 1` and `k ≡ 3` are clear on all six. This is v1's structural core
  and it holds.
- **Every integer `x ∈ {1,…,7}` has a clear opening** among `k ∈ {1, 3}`.
- **4000 random non-integer rationals in `(0,8)`** each found a fully clear opening; the largest index
  needed was `j = 9` (`x = 244/35`, `k = 64`).
- **The flank's own runner sits at exactly `1/8`** at every one of these openings. That is the boundary,
  and it is clear only because the zones are open (`inWay ⟺ circDist < 1/n`). The result depends on the
  manuscript's boundary discipline, §1.2 — the same discipline that decided the order-5 certificate.

## 3. The correction  `[CORRECTS v1]`

v1's proof paragraph reads: *"Integer x ∈ {1,…,7}: the phase is constant, and ‖9x/56‖ ≥ 1/8 for every x
… k = 1 is free outright."*

**That is false at `x = 6`**, where `‖9·6/56‖ = ‖54/56‖ = 2/56 = 1/28 < 1/8` — blocked, not free. The
theorem is unaffected, because `x = 6` is clear at `k = 3` (`‖150/56‖ = 18/56`), which v1's own *Anchors*
paragraph states: *"x = 6 … resolves at k = 3, t = 25/56."* So v1 contradicts itself within a page; the
statement to keep is the Anchors one. The Lean proof carries the split explicitly: `k = 1` for whole
`x ≠ 6`, `k = 3` for `x = 6`.

## 4. The irrational case needs no approximation theory  `[the substantive finding]`

v1 handles non-integer `x` in two pieces — a grid argument for rationals, and *"irrational x: the orbit
is dense"* for the rest. The relayed working session was accordingly preparing to import Kronecker's
theorem or a Dirichlet pigeonhole argument, and was uneasy about it (*"it's not a 'measure/density
argument' in the banned sense"*). That unease was warranted: the firewall's **No measure or density** row
is exactly this boundary, and a density claim is what it excludes.

**None of it is needed.** The artefact already contains the lemma, proved natively and axiom-clean:

> `Flanks.exists_clear_step (hn4 : 4 ≤ n) {f c : ℝ} (hf0 : 0 < f) (hf1 : f < 1) :`
> `    ∃ k : ℕ, (n : ℝ)⁻¹ ≤ circDist ((k : ℝ) * f + c)`

— *one step cannot stay in the way*, proved from consecutive nearest integers, with no density,
equidistribution or approximation input.

It applies directly. Along `k = 1 + 7j` the sixth difference's phase is `9x/56 + j·x`, which differs from
`9x/56 + j·(Int.fract x)` by the integer `j·⌊x⌋`, and `circDist` is invariant under integer shifts. So
with `f = Int.fract x` and `c = 9x/56`, `exists_clear_step` supplies the `j` — **for rational and
irrational `x` alike, in one case rather than two**. The rational/irrational split in v1 is unnecessary,
and so is the grid argument.

This is the difference between a result that needs a new import and one that does not.

## 5. The theorem  `[PROVED — Lean, axiom-clean]`

> **`eighth_family_lonely`.** For every `x` with `0 < x < 8`, the difference set `{1,3,4,5,7,x,8}` has a
> lonely instant, at an opening of the flank at difference `7`.
>
> **`eighth_family_lonely_scaled`.** For every `E > 0` and `0 < x < E`, the set
> `{E/8, 3E/8, E/2, 5E/8, 7E/8, x, E}` has a lonely instant. (Loneliness is read from the products `d·t`,
> so the normalised statement transports at `8/E` times the instant.)

Supporting: `clear_of_band` (the band `7 ≤ p ≤ 49` in fifty-sixths), `fixed_clear_one`, `fixed_clear_three`,
`int_clear_one`, `free_clear_of_not_int`.

## 6. What this does and does not do for Existence at order 8

**Does.** It closes the family that shadows the largest flank — per-runner Existence for every member,
at its own scale, with the instant explicit and early.

**Does not.** Existence at order 8 remains open, and the cascade gate still reports it unstated. v1's own
§"What this does to Existence" is correct that closing it outright requires **uniqueness of the eighth
pattern at all denominators** — that no other minimal largest-flank cover exists. That is unproved: the
`A = 0` census at `c > 8` is the instrument, the bounded-overhang lemma the structural form. Until it
lands, the disjunction "either a free largest flank or eighth-family" is established only within the
census range (denominators ≤ 8), which is a scoped statement, not the conjecture.

**Terminology.** `E = d_max`; the ratio to `d_min` is `S`, and the manuscript's **spread** is `W = v_8 − v_1`
— see `ORDER5_CERTIFICATE_v2.md` §Notation, where the same collision was corrected this session.
