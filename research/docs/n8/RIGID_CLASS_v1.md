# The rigid class: two necessary conditions, proved

2026-09-07. Follows `EXACT_PHI_N_AP_v1.md` §3, which surfaced an open item and did not
close it: two non-AP tuples — `{1,3,4,7}` at `n=5` and `{1,2,3,4,5,7,12}` at `n=8` —
have the same lonely set as the arithmetic progression, and the "complete set of non-zero
residues" explanation fits the first and fails the second. This file replaces that failed
explanation with two conditions, each with a proof of necessity. Sufficiency is **open**
and its test is pre-registered, not run.

## 0. Object

For `T` a set of `n−1` positive integers and `‖x‖` the distance to the nearest integer,

    L(T,n) = { t ∈ [0,1) : ‖v t‖ ≥ 1/n for every v ∈ T }.

`T` is **rigid** when `L(T,n)` is exactly the `φ(n)` points `r/n`, `gcd(r,n)=1` — those
points present, no other isolated points, no positive-length components.

Two candidate conditions:

- **(C1)** `{ v mod n : v ∈ T }` contains every unit of `Z/nZ`.
- **(C2)** for every `q` with `2 ≤ q ≤ n−1`, some `v ∈ T` is divisible by `q`.

## 1. Lemma A — one-sided isolation  `[PROVED]`

*Let `gcd(r,n)=1` and `n ∤ v` for every `v ∈ T`, so that `r/n ∈ L(T,n)` (that membership is
the one-line result of `EXACT_PHI_N_AP_v1.md` §2). Then `r/n` is isolated on the right iff
some `v ∈ T` satisfies `v ≡ −r⁻¹ (mod n)`, and on the left iff some `v ≡ +r⁻¹ (mod n)`.*

**Proof.** Write `vr ≡ s (mod n)` with `1 ≤ s ≤ n−1`; `s ≠ 0` because `gcd(r,n)=1` and
`n ∤ v`. For `ε > 0` small enough that no term wraps, the fractional part of `v(r/n + ε)`
is `s/n + vε`, so

    ‖v(r/n + ε)‖ = min( s/n + vε , (n−s)/n − vε ).

If `s < n/2` the minimum is `s/n + vε ≥ 1/n`, satisfied. If `s = n/2` (possible only for
even `n`) the minimum is `1/2 − vε`, which exceeds `1/n` for all small `ε` since `n ≥ 3`.
If `s > n/2` the minimum is
`(n−s)/n − vε`, and `(n−s)/n − vε ≥ 1/n` iff `vε ≤ (n−s−1)/n`. For `s ≤ n−2` the right
side is positive and the constraint survives all small `ε`. For `s = n−1` the right side
is `0`, so the constraint fails for every `ε > 0` — and `s = n−1 > n/2` whenever `n ≥ 3`, so
that case does fall in the branch just treated. Hence some `v` cuts the point off on
the right iff some `v` has `vr ≡ n−1 ≡ −1`, i.e. `v ≡ −r⁻¹`. The left side is the same
computation with `ε < 0`, giving `vr ≡ +1`. ∎

**Corollary A.** All `φ(n)` points `r/n` are isolated iff `T` satisfies **(C1)**. As `r`
runs over the units so does `r⁻¹`, and the unit group is closed under negation, so
requiring `r⁻¹` and `−r⁻¹` for every unit `r` is exactly requiring every unit. ∎

This is what the two witnesses have in common and what "complete non-zero residues" got
wrong. `{1,2,3,4,5,7,12}` reduces mod 8 to `{1,2,3,4,5,7}` — not complete, but it does
contain the units `{1,3,5,7}`.

## 2. Lemma B — denominator coverage  `[PROVED]`

*If some `q` with `2 ≤ q ≤ n−1` divides no element of `T`, then `L(T,n)` has a
positive-length component; so rigidity implies **(C2)**.*

**Proof.** Take `a` coprime to `q` and `t = a/q`. For `v ∈ T`, `‖v a/q‖ = s_v/q` where
`s_v = |va mod q|` reduced to `[0, q/2]`. Since `gcd(a,q)=1` and `q ∤ v`, `s_v ≥ 1`, so
`‖v a/q‖ ≥ 1/q > 1/n` — **strictly**, because `q ≤ n−1`. A finite set of strict
inequalities survives a small perturbation of `t` in either direction, so an interval
around `a/q` lies in `L(T,n)`. ∎

The strictness is the whole content: at `t = r/n` the inequality is met with equality,
which is why those points are isolated, and at `t = a/q` with `q < n` it is not.

## 3. What this does and does not settle

**Settled `[PROVED]`:** rigid ⟹ (C1) ∧ (C2). Both directions above are unconditional in
`n` and `T`; neither is a computation.

**Not settled:** the converse. (C1) alone is not sufficient — `T = {1,3,5,7,9,11,13}` at
`n=8` satisfies (C1), so all four points `1/8,3/8,5/8,7/8` are isolated exactly as
Corollary A predicts, and `L` nevertheless has five positive-length components, the one
around `1/2` being the `q = 2` failure of Lemma B. (C2) alone is not sufficient either —
`T = {2,…,8}` at `n=8` satisfies (C2) and loses every isolated point, since `8 ≡ 0`.
Whether (C1) ∧ (C2) is sufficient is **open**; a tuple could in principle carry a short
lonely interval containing no rational of denominator below `n`, which is precisely the
case neither lemma touches.

`[VERIFIED-INSTANCE]` Ten named tuples at `n ∈ {5,8,9,12}` — the two witnesses, three APs,
and five deliberate near-misses — all satisfy (C1) ∧ (C2) ⟺ rigid, computed exactly by the
Boundary Set Method. Ten hand-chosen tuples are a consistency check, not evidence of a
rate; the sweep that would bear on sufficiency is pre-registered separately and has not
been run.

## 4. The shape of the remaining question

(C1) ∧ (C2) turns "which tuples are rigid" into a covering problem: `n−1` integers must
hit every unit of `Z/nZ` under reduction **and** every modulus `2..n−1` under divisibility.
`T = {1,…,n−1}` satisfies both for the trivial reason that `q` covers `q` and the residues
are all of them. For prime `n` the two conditions bind hard together: `φ(n) = n−1` forces
`T mod n` to be a bijection onto the non-zero residues, so each residue is used exactly
once and the divisibility cover must be achieved within that constraint. Witness A is such
a solution at `n=5` distinct from the AP: residues `1,3,4,2` with `2|4`, `3|3`, `4|4`.

So the AP is not distinguished by being the only tuple meeting the conditions; it is
distinguished by meeting them in the cheapest way. That is a sharper statement of what
`EXACT_PHI_N_AP_v1.md` §2 found — the `φ(n)` points are generic, the absence of anything
else is the constraint — and it is why Proposition 4.1's zero stability radius is a
property of a *class*, not of the AP family alone.
