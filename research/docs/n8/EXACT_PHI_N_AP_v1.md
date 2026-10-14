# The φ(n) AP law, verified exactly — and what it turns out to say

2026-09-07. The published verification of `lrc_ap_phi_n_law_v1` is IEEE-754 with
ulp-aware tolerances. Redone in exact rational arithmetic: no float is constructed and
no tolerance is used. Script: `experiments/n8/exact_phi_n_ap_v1.py`.

**The method is the paper's own.** The Boundary Set Method (§2.2, Lemmas 2.1–2.2,
Algorithm 2.1) says isolation status changes only at the boundary times
`t = (k ± 1/n)/v`, and the predicate is constant between consecutive boundary times —
event-complete, and exact by construction. Running it in floats discards the property
it was built to have. Nothing here is new method; it is the stated method executed
over `Fraction`.

---

## 1. Results, exact

**Theorem 3.1(a),(b),(d).** For AP relative speeds `(δ, 2δ, …, (n−1)δ)` at bound `1/n`,
the lonely set is **exactly** the `φ(n)` isolated points `r/n` with `gcd(r,n) = 1`, with
**zero positive-length components**. Verified for `n = 3,…,12`; `δ` only rescales `t`.

**§6, the "n = 8 computational anomaly".** At `n = 8` the lonely set is exactly
`{1/8, 3/8, 5/8, 7/8}` — `φ(8) = 4` points — and `min_j ‖j t‖ = 1/8` exactly at each.
No tolerance appears anywhere in that sentence. The anomaly was an artefact of float
inputs and does not exist in exact arithmetic.

**Theorem 3.1(c).** Positions at those instants are a translate of the uniform `n`-grid:
**0 failures** over all `n ≤ 10`, `v₀ ≤ 5`, `δ ≤ 5`, and every coprime `r`.

## 2. What the law actually says — a reframing the exact run forced

Running the non-AP control exactly turned up something the float study's pass/fail
framing hides.

**[PROVED, one line]** For *any* integer tuple `T` with `n ∤ v` for every `v ∈ T`, and
any `r` with `gcd(r,n) = 1`:

    ‖v·(r/n)‖ = |vr mod n|ₙ / n ≥ 1/n,

because `gcd(r,n) = 1` makes `vr ≡ 0 (mod n)` equivalent to `n | v`. Checked over 30 000
tuples at `n = 3..12` with zero violations, and the one-line proof is above.

So **the `φ(n)` times being lonely is not special to arithmetic progressions.** It holds
for every tuple avoiding `n | v` — which is close to the general-`n` manuscript's
Lemma 5.2-D (coprime-`n` explicit witness). What is special about APs is the *converse*
half: for an AP the lonely set is **nothing but** those points. APs are the rigid,
minimal-lonely-set case — which is exactly Proposition 4.1's zero stability radius,
and why `lrc_ap_worst_case_v1.md` treats the family as the worst case.

## 3. An open item the exact run surfaced — not dismissed

Of 400 non-AP tuples tested per `n`, essentially all have positive-length lonely
components. **Two do not**, and they are not APs and not AP after dividing by their gcd:

| `n` | `T` | lonely set |
|---|---|---|
| 5 | `{1,3,4,7}` | exactly `1/5, 2/5, 3/5, 4/5` |
| 8 | `{1,2,3,4,5,7,12}` | exactly `1/8, 3/8, 5/8, 7/8` |

Both achieve the same rigidity as the AP family — minimal lonely set, zero measure —
without being APs. `{1,3,4,7}` reduces mod 5 to `{1,3,4,2}`, a complete set of non-zero
residues; `{1,2,3,4,5,7,12}` reduces mod 8 to `{1,2,3,4,5,7,4}`, which is **not**
complete, so that is not the explanation.

**So the AP family is not the only extremal family, and the characterisation of the
rigid class is open.** This is recorded as a finding, not a footnote: a float run with a
pass/fail tolerance would have scored both of these as "non-AP, no φ(n) match" and moved
on. Scope: `n ∈ {4,…,8}`, first 400 non-AP tuples from `{1,…,4n−1}` in lexicographic
order — a biased sample by the project's own diverse-sampling rule, so the two are
existence witnesses and the counts are not a rate.

## 4. Status of the published paper

Not refuted — **re-verified, and at a stricter standard than it claimed.** Every result
of Theorem 3.1 and §6 that was checked here holds exactly. The reading note in
`lrc_ap_phi_n_law_v1.md` that excused the float basis ("the tolerance framework here is
the object of study rather than a contaminated measurement") is superseded: the
Boundary Set Method makes the exact computation available, so the tolerance framework
was never necessary for the verification, only for the fragility discussion it
illustrates.
