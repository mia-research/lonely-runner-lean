# L3 — the reading is sound and complete

2026-09-15. Replaces `LEMMA_L3_v1.md`. Same result, shorter proof, and the proof here is the one
that is machine-checked.

**What changed from v1.** v1 proved completeness by showing the isolation set is closed, then
using compactness on a bounded range to get a minimum, then showing the minimum is an opening.
Steps (a) and (b) of that are **not needed**. The elementary argument below gives completeness
directly, and it does not require the minimum to exist. Formalising it needed no topology.

**Still corrected from `LEMMAS_v1` L3.** That text reads *"its first boundary point is the first
instant all seven others stand clear"*, which conflates the candidate list with the answer, and
its proof is a pointer — *"the chain construction is the proof"*. The statement that is true and
provable is soundness and completeness of the procedure.

---

## Setting

Runner `i` has differences `d_1, …, d_{n−1} > 0`; `m = min_j d_j`. Runner `j` stands clear of `i`
at `t` when `‖d_j t‖ ≥ 1/n`, so its clear set is

    C_j  =  ⋃_{k ≥ 0}  [ (nk+1)/(n d_j),  (nk+n−1)/(n d_j) ]

and `i` is isolated on `I = ⋂_j C_j`. Left endpoints are **openings**, right endpoints
**closings**. For a difference `d` and a time `t`, write

    opening(d, t)  =  ( ⌊d t⌋ + 1/n ) / d

— the opening of the stretch that `t` lies in, when `t` is clear for `d`.

## (a) The opening is no later than `t`  `[PROVED]`

If `‖d t‖ ≥ 1/n` then `Int.fract(d t) ≥ 1/n`, so `d t ≥ ⌊d t⌋ + 1/n`, so
`t ≥ (⌊d t⌋ + 1/n)/d = opening(d, t)`. ∎

Lean: `Construction8.opening_le`.

## (b) Clear back to the opening  `[PROVED]`

> If the runner at difference `d` stands clear at `t`, it stands clear at **every** `s` with
> `opening(d, t) ≤ s ≤ t`.

*Proof.* Write `q = ⌊d t⌋` and `f = Int.fract(d t)`. Clearance at `t` gives
`1/n ≤ f ≤ 1 − 1/n`. For `s` in the stated range, `q + 1/n ≤ d s ≤ d t = q + f`, so
`⌊d s⌋ = q` and `Int.fract(d s) = d s − q ∈ [1/n, f] ⊆ [1/n, 1 − 1/n]`. Hence
`‖d s‖ = min(d s − q, 1 − (d s − q)) ≥ 1/n`. ∎

Lean: `Construction8.clear_on_left`.

## (c) Completeness  `[PROVED]`

> If `i` is isolated at `t`, it is isolated at an **opening** no later than `t`.

*Proof.* Let `e` be a difference maximising `opening(d, t)` over the finitely many `d`. By (a),
`opening(e, t) ≤ t`. For each `d`, `opening(d, t) ≤ opening(e, t) ≤ t`, so by (b) the runner at
`d` stands clear at `opening(e, t)`. All of them do, so `i` is isolated there — and it is an
opening. ∎

Lean: `Construction8.reading_complete`.

**No minimum is assumed to exist.** (c) says the isolation openings sit cofinally below every
isolation instant. Two consequences, and only the second mentions a minimum:

- A reading that enumerates **only openings** cannot miss an isolation instant: if the range holds
  one at all, it holds one that is an opening.
- Hence if the earliest isolation instant in the range exists, it *is* an opening — because any
  isolation instant has an isolation opening at or below it.

## (d) The procedure  `[PROVED]`

    K(T)  =  { (nk+1)/(n d_j) : j, k ≥ 0 }  ∩  [1/(nm), T]

is finite: for each `j` at most `T·d_j + 1` values of `k`, and `I ⊆ [1/(nm), ∞)` because
`t < 1/(nm)` gives `‖m t‖ = m t < 1/n`. Enumerate `K(T)` in increasing order and return the
first member at which all `n−1` stand clear.

- **Sound** — what it returns lies in `I` by construction.
- **Complete** — by (c), if `I ∩ (0,T] ≠ ∅` then it contains an opening, which lies in `K(T)`;
  the first member of `K(T)` in `I` is therefore the earliest isolation instant in the range.
- **Honest on failure** — if no member of `K(T)` is in `I`, then `I ∩ (0,T] = ∅`.

Closings never need enumerating. `[VERIFIED — 3,200/3,200 runner-instances]` the openings-only
enumeration and the full endpoint enumeration return the same instant in every case.

## (e) The boundary separation is necessary, not stylistic  `[PROVED — by example]`

`I` can have empty interior. For the AP's end runner at `n = 8`, `d = (1,…,7)`,

    I ∩ [1/8, 7/8]  =  { 1/8, 3/8, 5/8, 7/8 }        exactly — four isolated points.

An implementation that evaluates cell midpoints, or merges touching closed zones, reports the
AP's own end runners as never isolated. The trap is recorded at `OWNER_PROCEDURE_v1` §1 and
`PROOF_CANDIDATE_v3` §5; (e) is why it is unavoidable rather than an implementation choice.

---

## Grade

`[PROVED]` (a)–(e), for arbitrary positive real differences and general `n`. No integrality, no
commensurability, nothing cited, and no topology.

**Machine-checked.** `LonelyRunner/LRC/Construction8/LemmaPass.lean` —
`opening`, `clear_on_left`, `opening_le`, `reading_complete`. Zero `sorry`, no `native_decide`,
`[propext, Classical.choice, Quot.sound]`.

**Not proved, and not claimed:** that `I` is nonempty. That is C1, and it is LRC(`n`) for runner
`i`.

**So the "within any searched range" qualifier is not a hedge — it is forced.** L3 says the
reading never lies and never misses. It does not say the search terminates. Only the first of
those is a lemma.
