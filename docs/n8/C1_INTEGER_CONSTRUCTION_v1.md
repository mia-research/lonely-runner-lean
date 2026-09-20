# C1-integer — a construction for the residue-blocked case

2026-09-15. A swing at item 1 of `LEMMAS_v2`'s attack order: one-period nonemptiness for integer
readings, residue-blocked case. What follows is a **construction** — an explicit instant, no
search — with a proof, and the measured reach of each form.

Objects: the reading `s_j = d_j/d_min`, integral throughout (so `d_min | d_j`); the four
reference instants `u = p/8`, `p` a unit mod 8; **blocked** means `s_j ≡ 0 (mod 8)`, which by
`spine_all_or_nothing` kills all four instants at once and forever.

---

## 1. What moving off the reference instant costs  `[PROVED]`

At `u = p/8` an unblocked runner sits at phase `c_j/8` with `c_j = s_j p mod 8 ∈ {1,…,7}`, and a
blocked runner sits exactly on its lap line. Move right by `ε`:

- **unblocked `j` stays clear** while `s_j ε ≤ (7 − c_j)/8` — its phase must not pass `7/8`;
- **blocked `j` clears** when `‖8σ_j ε‖ ≥ 1/8`, where `s_j = 8σ_j`.

So, with `E = min_j (7 − c_j)/(8 s_j)` over the unblocked:

> **The residue-blocked case reduces to the same problem with only the blocked runners, on the
> bounded interval `(0, E]`.**

Seven constraints become the number of blocked runners — **1** in 71% of cases and **2** in 24%.

**The two directions are one.** Moving left instead gives `s_j ε ≤ (c_j − 1)/8`, and
`u ↦ 1 − u` maps the rightward solution at `p` to the leftward one at `8 − p`. Measured as an
exact bijection: right 16,712, left 16,712, both 16,712, left adds 0. That is the palindrome.

## 2. The theorem  `[PROVED]`

> Let `1 = s_1 ≤ … ≤ s_7` be integers. Suppose
> **(i)** exactly one `s_j ≡ 0 (mod 8)`, and it is the largest, `S`; and
> **(ii)** the residues `{s_j mod 8}` miss at least one of `{3, 5, 7}`.
> Then, with `p` the unit for which `7p⁻¹ ∉ {s_j mod 8}`,
>
>     u  =  p/8  +  1/(8S)
>
> is an isolation instant, and it lies in `[1/8, 7/8]`.

*Proof.* Each unit `p` is spoiled by exactly one residue class — `c_j = 7` happens iff
`s_j ≡ 7p⁻¹` — and `s_1 = 1` is always present, which spoils `p = 7`. So (ii) leaves a usable
`p ∈ {1,3,5}`, and for it every unblocked `c_j ≤ 6`.

At `u = p/8 + 1/(8S)` the unblocked runner `j` has phase `c_j/8 + s_j/(8S)`. Since `s_j ≤ S`, the
shift is at most `1/8`, so the phase lies in `[c_j/8, (c_j+1)/8] ⊆ [1/8, 7/8]`. The blocked
runner has phase `Sp/8 + 1/8 ≡ 1/8 (mod 1)`, since `8 ∣ S` makes `Sp/8` an integer — clear, at the
boundary. And `u ≤ 5/8 + 1/8 = 6/8`. ∎

`[VERIFIED — 16,117 / 16,117]`, no failures.

## 3. Reach

| form | population | solved | share |
|---|---|---|---|
| §2's theorem (one blocked, largest, residues miss one of 3/5/7) | — | 16,117 | **100%**, by proof |
| one blocked, largest | 8,815 | 7,806 | 88.6% |
| one blocked, condition `s_j ≤ S(7−c_j)` for some `p` | 58,049 | 31,215 | 53.8% |
| **any number blocked**, via §1's reduction | 65,071 | 33,278 | **51.1%** |

The 11.4% lost in row 2 is exactly the cases where all of `{3,5,7}` occur among the residues, so
no unit survives. The 48.9% lost in row 4 is where `E` is too short to hold an opening of the
blocked comb.

Every returned `u` was checked to be an isolation instant lying in `[1/8, 7/8]`; 0 verification
failures across all rows.

## 4. Status

`[PROVED]` §1's reduction and the two-directions bijection; §2's theorem.
`[VERIFIED]` §3's reach.
`[OPEN]` C1-integer. This closes a little over half of the residue-blocked population by
construction; it does not close the case.

**What it changes about the front line.** The residue-blocked case is no longer "find an instant";
it is "solve the same problem for the blocked runners alone, on a bounded interval". With one
blocked runner that is a single comb and §2 settles it whenever the reading leaves a unit
unspoiled. The remaining work is the short-interval case, and the two-or-more-blocked case, which
is the same reduction applied again.

**n = 8 is not proved here.** Neither is C1.
