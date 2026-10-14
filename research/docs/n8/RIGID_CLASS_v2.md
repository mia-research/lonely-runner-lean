# The rigid class: four necessary conditions, and a correction to v1

2026-09-07. Supersedes `RIGID_CLASS_v1.md`. Two changes: **v1's Corollary A was stated
without a hypothesis its own Lemma A carries**, and the exhaustive sweep specified by
`PREREG_RIGID_CLASS_v1.md` turned up a second missing condition. Both are now proved.
Run and results: `RIGID_SWEEP_RESULTS_v1.md`.

## 0. Object

`L(T,n) = { t ∈ [0,1) : ‖v t‖ ≥ 1/n for every v ∈ T }`, `T` a set of `n−1` distinct
positive integers. `T` is **rigid** iff `L(T,n)` is exactly the `φ(n)` points `r/n`,
`gcd(r,n)=1` — all present, no other isolated point, no positive-length component.

- **(C0)** `n ∤ v` for every `v ∈ T`.
- **(C1)** `{ v mod n : v ∈ T }` contains every unit of `Z/nZ`.
- **(C2)** for every `q` with `2 ≤ q ≤ n−1`, some `v ∈ T` is divisible by `q`.
- **(C3)** `gcd(T) = 1`.

## 1. Lemma A — one-sided isolation  `[PROVED, unchanged from v1]`

*Let `gcd(r,n)=1` and `n ∤ v` for every `v ∈ T`. Then `r/n ∈ L(T,n)`, and it is isolated
on the right iff some `v ∈ T` has `v ≡ −r⁻¹ (mod n)`, on the left iff some `v ≡ +r⁻¹`.*

**Proof.** Write `vr ≡ s (mod n)`, `1 ≤ s ≤ n−1` (`s ≠ 0` needs both `gcd(r,n)=1` and
`n ∤ v`). For small `ε > 0` the fractional part of `v(r/n + ε)` is `s/n + vε`, so
`‖v(r/n+ε)‖ = min(s/n + vε, (n−s)/n − vε)`. For `s < n/2` the minimum is `s/n + vε ≥ 1/n`.
For `s = n/2` it is `1/2 − vε > 1/n` for `n ≥ 3` and small `ε`. For `s > n/2` it is
`(n−s)/n − vε ≥ 1/n` iff `vε ≤ (n−s−1)/n`, which holds for small `ε` when `s ≤ n−2` and
fails for every `ε > 0` when `s = n−1`. Since `n−1 > n/2` for `n ≥ 3`, that case sits in
the branch just treated. So a `v` cuts the point off on the right iff `vr ≡ −1`, i.e.
`v ≡ −r⁻¹`; `ε < 0` gives `vr ≡ +1`. ∎

### Corollary A′ — corrected  `[PROVED]`

*All `φ(n)` points `r/n` lie in `L(T,n)` and are isolated ⟺ **(C0) ∧ (C1)**.*

`(C0)` gives membership; without it some `v` has `n | v`, so `‖v·r/n‖ = 0` and no `r/n` is
lonely at all. `(C1)` then gives isolation, by Lemma A and the fact that `r ↦ r⁻¹` permutes
the units and the unit group is closed under negation. Hence **rigid ⟹ (C0) ∧ (C1)**.

**What v1 got wrong.** v1's Corollary A read "all `φ(n)` points isolated ⟺ (C1)", dropping
Lemma A's standing hypothesis `n ∤ v`. `(C1)` does not imply `(C0)`: `T` may carry the
units *and* an element `≡ 0 (mod n)`. The sweep located this mechanically — of the `C1∧C2`
tuples with **no** surviving `φ(n)` point, `46/46` at `n=4` and `3398/3398` at `n=6`
contain a multiple of `n`, and there are none at `n=5,7`. The prime cases are empty for a
reason worth recording: when `n` is prime, `φ(n) = n−1 = |T|`, so `(C1)` forces `T mod n`
to be a *bijection* onto the non-zero residues and leaves no slot for a zero. `(C0)` is a
consequence of `(C1)` at prime `n` and independent of it at composite `n`. The ten named
probes in v1 spanned `n ∈ {5,8,9,12}` but contained no tuple that satisfies `(C1)` *and*
carries a multiple of `n`, so they could not have exposed it.

## 2. Lemma B — denominator coverage  `[PROVED, unchanged from v1]`

*If some `q` with `2 ≤ q ≤ n−1` divides no element of `T`, then `L(T,n)` has a
positive-length component; so rigid ⟹ **(C2)**.*

**Proof.** For `a` coprime to `q`, `‖v·a/q‖ = s_v/q` with `s_v ≥ 1` since `q ∤ v`, so
`‖v·a/q‖ ≥ 1/q > 1/n` **strictly**, because `q ≤ n−1`. Finitely many strict inequalities
survive a small perturbation of `t` either way, so an interval around `a/q` lies in
`L(T,n)`. ∎

## 3. Lemma C — primitivity  `[PROVED, new]`

*Assume (C0). If `g = gcd(T) > 1` then `|L(T,n)| ≥ g·φ(n) > φ(n)`, so `T` is not rigid.
Hence rigid ⟹ **(C3)**.*

**Proof.** Put `S = T/g`. `(C0)` gives `n ∤ s` for every `s ∈ S`, since `n | s` would give
`n | gs`. For any `t`, `‖v t‖ = ‖s·(gt)‖`, so `t ∈ L(T,n) ⟺ frac(gt) ∈ L(S,n)`: the
lonely set of `T` is the **full preimage** of that of `S` under the `g`-to-1 map
`t ↦ frac(gt)`. By `EXACT_PHI_N_AP_v1.md` §2, `L(S,n)` contains all `φ(n)` points `r/n`,
so `L(T,n)` contains at least `g·φ(n)` points, which exceeds `φ(n)` for `g > 1`. ∎

The lonely set is then the `g`-fold refinement `{(k + r/n)/g}`, `0 ≤ k < g`. So the tuple
is still *measure*-rigid — zero-measure lonely set — but not rigid: it has too many points,
not too few. `T = 3·{1,2,3} = {3,6,9}` at `n=4` has lonely set `{1,3,5,7,9,11}/12`, six
points where `φ(4) = 2`. Note `(C3)` is independent of `(C1)`: multiplying by `g` coprime
to `n` permutes the units, so `g·S` satisfies `(C1)` exactly when `S` does.

## 4. Status

**`[PROVED]` rigid ⟹ (C0) ∧ (C1) ∧ (C2) ∧ (C3)**, unconditionally in `n` and `T`.

**Sufficiency is false**, and not marginally — see `RIGID_SWEEP_RESULTS_v1.md`. The four
conditions are arithmetic (residues and divisibility); what defeats them is a *covering*
failure with no evident arithmetic signature. The measure bookkeeping says why one should
expect the conditions to be weak: each speed `v` contributes a bad set `{t : ‖vt‖ < 1/n}`
of measure exactly `2/n`, so the `n−1` bad sets carry total measure `2 − 2/n` against a
target of `1`. Rigidity demands they cover `[0,1)` bar finitely many points with average
multiplicity at most `2 − 2/n` — an exact-covering condition, which is why solutions are
scarce and why conditions read off residues alone cannot capture it.
