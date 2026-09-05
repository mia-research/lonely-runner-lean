# Case-2 Counterexample Autopsy (C2-main(C))

## 1) Explicit violating tuple

- `n = 12`
- `E = (12, 10, 5, 4, 7, 3, 6, 1, 8, 3, 11)`
- `phi(12)=4`, yet `x0=9386` (so LRC-side target is very positive)

Computed invariants:

- `L=9240`, `N=110880`
- `|B_div|=7701`
- `C_bad=3919`, `B_safe=3782`
- `I_bad=85652`, `P_bad=78354`, `T_bad=91764`

So:

- `lhs3 := I_bad - P_bad + T_bad = 99062`
- `rhs := n(|B_div|-(n-1)) = 92280`
- `lhs3 > rhs` by `6782`

Hence **C2-main(C) is false universally**.

---

## 2) What causes the overshoot

Let `q_b(a)` be bad-speed multiplicity at residue `a` on bad fibers. For each residue:

`g3(q)=q-C(q,2)+C(q,3)`.

Since `1_{q>0} <= g3(q)`, we have

`lhs3 = n C_bad + Excess3`,

where

`Excess3 = sum_{bad b} sum_a (g3(q_b(a)) - 1)`.

For this tuple:

- `n C_bad = 47028`
- `Excess3 = 52034`
- `lhs3 = 47028 + 52034 = 99062`

Allowable slack from rhs over `nC_bad` is only

- `rhs - nC_bad = 45252`.

So failure is exactly: `Excess3` is too large (`+6782` over budget).

### q-spectrum on bad fibers (across `12 * C_bad` residues)

`{1:24736, 2:15362, 3:3542, 4:1232, 5:616, 6:440, 7:330, 8:462, 9:168, 10:140}`

Excess is concentrated in high-q tail (`q>=6`), especially `q=8,9,10`.

---

## 3) Why this also invalidates the current U_s^(bN) target

In Case-2 there is at least one divisible speed, so `|E_non| <= n-2`.
Thus for every residue, speed-level multiplicity satisfies:

`q(a) <= n-2`.

Also branch-level and speed-level multiplicities coincide (`q_branch=q_speed`) because the two branch congruences from a single speed are disjoint (`ea ≡ c` and `ea ≡ c-1 (mod n)` cannot both hold).

Therefore dynamic odd Bonferroni with `k_n=max odd <= n-1` is **exact cover** in Case-2:

- if `n` even: `k_n=n-1 >= q_max`
- if `n` odd: `k_n=n-2 = q_max`.

So `U_s^(bN)` collapses to exact obstruction (`U_s^cov`) in Case-2. It cannot rescue C2-main(C): if C2-main(C) fails, `U_s^(bN)` forcing fails too.

---

## 4) Immediate correction path

The issue is not occupancy detection; it is the **third-order polynomial weight** being too coarse under high multiplicity.

Next viable candidate is a higher odd-order aggregate:

`lhs5 := I_bad - P_bad + T_bad - Q4_bad + Q5_bad`,

with per-residue polynomial `g5(q)`.
For this counterexample:

- `lhs5 = 86198 <= rhs = 92280`.

So the autopsy points to upgrading C2-main(C) to a higher odd-order aggregate inequality (or another tail-controlled majorant), then proving that new bound universally.
