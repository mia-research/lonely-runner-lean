# First Dynamic Checkpoint Lemmas for the `p_j = 11m` Staircase

**Date:** 2026-03-24
**Status:** First staircase checkpoints proved analytically for `m >= 2`.

This note proves the first batch of **checkpoint-maximizer lemmas** for the
dynamic staircase program in the `p_j = 11m` Containment case.

The idea is uniform:

1. prove a generic large-runner bound

```text
tau_p(t) < t + 2/(11p),
```

for every blocking runner `p`;

2. use it to rule out all sufficiently large `p`;
3. check the finitely many small `p` exactly by modular arithmetic.

These lemmas do **not** yet solve the whole dynamic case, because additional
multiples of 11 still have to be handled at the pacemaker checkpoints
`2/11, 3/11, 4/11, ...`. But they rigorously establish the first staircase
segments.

---

## 1. Universal step-size bound

Let `tau_p(t)` be the next isolation-entry time of runner `p` after a blocking
time `t`.

> **Lemma U (step-size bound).**
> If runner `p` is blocking at time `t`, then
>
> ```text
> tau_p(t) < t + 2/(11p).
> ```

**Proof.**

Write `f = {p t}`.

- If `0 <= f < 1/11` (lower bad zone), then the next entry is when the
  fractional part reaches `1/11`, so

```text
tau_p(t) - t = (1/11 - f)/p < 1/(11p).
```

- If `10/11 < f < 1` (upper bad zone), the fractional part must first wrap and
  then reach `1/11`, so

```text
tau_p(t) - t = (12/11 - f)/p < 2/(11p).
```

In either case `tau_p(t) < t + 2/(11p)`. `square`

---

## 2. First checkpoint `a_1 = (11m+1)/(121m)`

Define

```text
a_1(m) = (11m+1)/(121m) = 1/11 + 1/(121m).
```

> **Lemma C1.**
> For `m >= 2`, among all blocking runners at `t = a_1(m)`, the largest
> next-entry time is
>
> ```text
> tau_max(a_1) = 6/55,
> ```
>
> attained by runner `10`.

**Proof.**

For `p >= 21`, Lemma U gives

```text
tau_p(a_1) < a_1 + 2/(11p) <= 23/242 + 2/231
```

because `a_1 <= 23/242` for `m >= 2`. Since

```text
6/55 - (23/242 + 2/231) = 137/25410 > 0,
```

no runner `p >= 21` can beat `6/55`.

So only `2 <= p <= 20` need be checked.

For such `p`, we have

```text
0 < p/(121m) <= 20/242 = 10/121 < 1/11.
```

Write `p = 11q + r`, `0 <= r <= 10`. Then

```text
{p a_1} = {r/11 + p/(121m)}.
```

- If `1 <= r <= 8`, then

```text
r/11 < {p a_1} < (r+1)/11,
```

so the fractional part lies strictly inside the safe region.

- If `r = 9`, then

```text
{p a_1} <= 9/11 + 20/242 = 109/121 < 10/11,
```

so still safe.

- If `r = 10`, then

```text
{p a_1} = 10/11 + p/(121m) > 10/11.
```

Among `2 <= p <= 20`, this gives only `p = 10`, and

```text
tau_10(a_1) = 6/55.
```

- If `r = 0`, the only possibility in `2 <= p <= 20` is `p = 11`, and

```text
{11 a_1} = 1/(11m) < 1/11,
```

so `11` is lower-bad with

```text
tau_11(a_1) = 12/121 < 6/55.
```

Thus runner `10` uniquely maximizes the next-entry time. `square`

---

## 3. Second checkpoint `s_1 = 6/55`

> **Lemma C2.**
> Among all blocking runners at `t = 6/55`, the largest next-entry time is
>
> ```text
> tau_max(6/55) = 4/33,
> ```
>
> attained by runner `9`.

**Proof.**

For `p >= 19`, Lemma U gives

```text
tau_p(6/55) < 6/55 + 2/(11p) <= 6/55 + 2/209.
```

Since

```text
4/33 - (6/55 + 2/209) = 8/3135 > 0,
```

no `p >= 19` can beat `4/33`.

For `2 <= p <= 18`, note that

```text
{p * 6/55} = (6p mod 55)/55.
```

Because `1/11 = 5/55`, blocking means

```text
6p mod 55 in {0,1,2,3,4,51,52,53,54}.
```

Listing `6p mod 55` for `p = 2,...,18` gives:

```text
12,18,24,30,36,42,48,54,5,11,17,23,29,35,41,47,53.
```

So the only blockers are:

```text
p = 9   (remainder 54),
p = 18  (remainder 53).
```

Their next-entry times are

```text
tau_9(6/55)  = 4/33,
tau_18(6/55) = 23/198,
```

and `4/33 > 23/198`. `square`

---

## 4. Third checkpoint `s_2 = 4/33`

> **Lemma C3.**
> Among all blocking runners at `t = 4/33`, the largest next-entry time is
>
> ```text
> tau_max(4/33) = 3/22,
> ```
>
> attained by runner `8`.

**Proof.**

For `p >= 17`,

```text
tau_p(4/33) < 4/33 + 2/(11p) <= 4/33 + 2/187.
```

Since

```text
3/22 - (4/33 + 2/187) = 5/1122 > 0,
```

no `p >= 17` can beat `3/22`.

For `2 <= p <= 16`,

```text
{p * 4/33} = (4p mod 33)/33.
```

Because `1/11 = 3/33`, blocking means

```text
4p mod 33 in {0,1,2,31,32}.
```

For `p = 2,...,16`, the residues are:

```text
8,12,16,20,24,28,32,3,7,11,15,19,23,27,31.
```

So the only blockers are:

```text
p = 8   (remainder 32),
p = 16  (remainder 31).
```

Their next-entry times are

```text
tau_8(4/33)  = 3/22,
tau_16(4/33) = 23/176,
```

and `3/22 > 23/176`. `square`

---

## 5. Fourth checkpoint `s_3 = 3/22`

> **Lemma C4.**
> Among all blocking runners at `t = 3/22`, the largest next-entry time is
>
> ```text
> tau_max(3/22) = 12/77,
> ```
>
> attained by runner `7`.

**Proof.**

For `p >= 15`,

```text
tau_p(3/22) < 3/22 + 2/(11p) <= 3/22 + 2/165.
```

Since

```text
12/77 - (3/22 + 2/165) = 17/2310 > 0,
```

no `p >= 15` can beat `12/77`.

For `2 <= p <= 14`,

```text
{p * 3/22} = (3p mod 22)/22.
```

Because `1/11 = 2/22`, blocking means

```text
3p mod 22 in {0,1,21}.
```

For `p = 2,...,14`, the residues are:

```text
6,9,12,15,18,21,2,5,8,11,14,17,20.
```

So the only blocker is

```text
p = 7   (remainder 21),
```

and

```text
tau_7(3/22) = 12/77.
```

`square`

---

## 6. Fifth checkpoint `s_4 = 12/77`

> **Lemma C5.**
> Among all blocking runners at `t = 12/77`, the largest next-entry time is
>
> ```text
> tau_max(12/77) = 2/11,
> ```
>
> attained by runner `6`.

**Proof.**

For `p >= 14`,

```text
tau_p(12/77) < 12/77 + 2/(11p) <= 12/77 + 2/154.
```

Since

```text
2/11 - (12/77 + 2/154) = 1/77 > 0,
```

no `p >= 14` can beat `2/11`.

For `2 <= p <= 13`,

```text
{p * 12/77} = (12p mod 77)/77.
```

Because `1/11 = 7/77`, blocking means

```text
12p mod 77 in {0,1,2,3,4,5,6,71,72,73,74,75,76}.
```

For `p = 2,...,13`, the residues are:

```text
24,36,48,60,72,7,19,31,43,55,67,2.
```

So the blockers are:

```text
p = 6   (remainder 72),
p = 13  (remainder 2).
```

Their next-entry times are

```text
tau_6(12/77)  = 2/11,
tau_13(12/77) = 23/143,
```

and `2/11 > 23/143`. `square`

---

## 7. Sixth checkpoint `a_2 = (22m+1)/(121m)`

Define

```text
a_2(m) = (22m+1)/(121m) = 2/11 + 1/(121m).
```

> **Lemma C6.**
> For `m >= 2`, among all blocking runners at `t = a_2(m)`, the largest
> next-entry time is
>
> ```text
> tau_max(a_2) = 12/55,
> ```
>
> attained by runner `5`.

**Proof.**

For `p >= 7`,

```text
tau_p(a_2) < a_2 + 2/(11p) <= 45/242 + 2/77.
```

Since

```text
12/55 - (45/242 + 2/77) = 53/8470 > 0,
```

no `p >= 7` can beat `12/55`.

For `2 <= p <= 6`, we have

```text
0 < p/(121m) <= 6/242 < 1/11,
```

so

```text
{p a_2} = {2p/11 + p/(121m)}.
```

Now:

- `p = 2,3,4`: fractional part lies strictly between `1/11` and `10/11`,
  so safe.
- `p = 5`: fractional part is `10/11 + 5/(121m) > 10/11`, so blocking.
- `p = 6`: fractional part is `1/11 + 6/(121m) > 1/11`, so safe.

Thus the only blocker with `p <= 6` is `p = 5`, and

```text
tau_5(a_2) = 12/55.
```

`square`

---

## 8. Seventh checkpoint `s_5 = 12/55`

> **Lemma C7.**
> Among all blocking runners at `t = 12/55`, the largest next-entry time is
>
> ```text
> tau_max(12/55) = 23/99,
> ```
>
> attained by runner `9`.

**Proof.**

For `p >= 16`,

```text
tau_p(12/55) < 12/55 + 2/(11p) <= 12/55 + 2/176.
```

Since

```text
23/99 - (12/55 + 2/176) = 1/360 > 0,
```

no `p >= 16` can beat `23/99`.

For `2 <= p <= 15`,

```text
{p * 12/55} = (12p mod 55)/55.
```

Blocking means

```text
12p mod 55 in {0,1,2,3,4,51,52,53,54}.
```

For `p = 2,...,15`, the residues are:

```text
24,36,48,5,17,29,41,53,10,22,34,46,3,15.
```

So the blockers are:

```text
p = 9   (remainder 53),
p = 14  (remainder 3).
```

Their next-entry times are

```text
tau_9(12/55)  = 23/99,
tau_14(12/55) = 17/77,
```

and `23/99 > 17/77`. `square`

---

## 9. Eighth checkpoint `s_6 = 23/99`

> **Lemma C8.**
> Among all blocking runners at `t = 23/99`, the largest next-entry time is
>
> ```text
> tau_max(23/99) = 3/11,
> ```
>
> attained by runner `4`.

**Proof.**

For `p >= 5`,

```text
tau_p(23/99) < 23/99 + 2/(11p) <= 23/99 + 2/55.
```

Since

```text
3/11 - (23/99 + 2/55) = 2/495 > 0,
```

no `p >= 5` can beat `3/11`.

For `p = 2,3,4`, the fractional parts are:

```text
2 * 23/99 = 46/99   (safe),
3 * 23/99 = 69/99   (safe),
4 * 23/99 = 92/99   (> 10/11, blocking).
```

So only `p = 4` blocks, and

```text
tau_4(23/99) = 3/11.
```

`square`

---

## 10. Ninth checkpoint `a_3 = (33m+1)/(121m)`

Define

```text
a_3(m) = (33m+1)/(121m) = 3/11 + 1/(121m).
```

> **Lemma C9.**
> For `m >= 2`, among all blocking runners at `t = a_3(m)`, the largest
> next-entry time is
>
> ```text
> tau_max(a_3) = 23/77,
> ```
>
> attained by runner `7`.

**Proof.**

For `p >= 9`,

```text
tau_p(a_3) < a_3 + 2/(11p) <= 67/242 + 2/99.
```

Since

```text
23/77 - (67/242 + 2/99) = 25/15246 > 0,
```

no `p >= 9` can beat `23/77`.

For `2 <= p <= 8`, we have

```text
0 < p/(121m) <= 8/242 < 1/11,
```

so

```text
{p a_3} = {3p/11 + p/(121m)}.
```

Now:

- `p = 2,3,4,5,6`: safe,
- `p = 7`: `10/11 + 7/(121m) > 10/11`, so blocking,
- `p = 8`: `2/11 + 8/(121m) > 1/11` and `< 10/11`, so safe.

Thus the only blocker with `p <= 8` is `p = 7`, and

```text
tau_7(a_3) = 23/77.
```

`square`

---

## 11. Tenth checkpoint `s_7 = 23/77`

> **Lemma C10.**
> Among all blocking runners at `t = 23/77`, the largest next-entry time is
>
> ```text
> tau_max(23/77) = 17/55,
> ```
>
> attained by runner `10`.

**Proof.**

For `p >= 21`,

```text
tau_p(23/77) < 23/77 + 2/(11p) <= 23/77 + 2/231.
```

Since

```text
17/55 - (23/77 + 2/231) = 2/1155 > 0,
```

no `p >= 21` can beat `17/55`.

For `2 <= p <= 20`,

```text
{p * 23/77} = (23p mod 77)/77.
```

Because `1/11 = 7/77`, blocking means

```text
23p mod 77 in {0,1,2,3,4,5,6,71,72,73,74,75,76}.
```

For `p = 2,...,20`, the residues are:

```text
46,69,15,38,61,7,30,53,76,22,45,68,14,37,60,6,29,52,75.
```

So the blockers are:

```text
p = 10  (remainder 76),
p = 17  (remainder 6),
p = 20  (remainder 75).
```

Their next-entry times are

```text
tau_10(23/77) = 17/55,
tau_17(23/77) = 56/187,
tau_20(23/77) = 67/220,
```

and `17/55` is the largest. `square`

---

## 12. Eleventh checkpoint `s_8 = 17/55`

> **Lemma C11.**
> Among all blocking runners at `t = 17/55`, the largest next-entry time is
>
> ```text
> tau_max(17/55) = 4/11,
> ```
>
> attained by runner `3`.

**Proof.**

For `p >= 17`,

```text
tau_p(17/55) < 17/55 + 2/(11p) <= 17/55 + 2/187.
```

Since

```text
4/11 - (17/55 + 2/187) = 41/935 > 0,
```

no `p >= 17` can beat `4/11`.

For `2 <= p <= 16`,

```text
{p * 17/55} = (17p mod 55)/55.
```

Because `1/11 = 5/55`, blocking means

```text
17p mod 55 in {0,1,2,3,4,51,52,53,54}.
```

For `p = 2,...,16`, the residues are:

```text
34,51,13,30,47,9,26,43,5,22,39,1,18,35,52.
```

So the blockers are:

```text
p = 3   (remainder 51),
p = 13  (remainder 1),
p = 16  (remainder 52).
```

Their next-entry times are

```text
tau_3(17/55)  = 4/11,
tau_13(17/55) = 45/143,
tau_16(17/55) = 7/22,
```

and `4/11` is the largest. `square`

> **Corollary C11.1 (First substitute step).**
> If runner `3` is absent, then among all blocking runners at `t = 17/55`,
> the largest next-entry time is
>
> ```text
> tau_max^(p != 3)(17/55) = 7/22,
> ```
>
> attained by runner `16`.

**Proof.**

The proof of Lemma C11 already identifies all blockers at `t = 17/55` with
`2 <= p <= 16`:

```text
p = 3, 13, 16,
```

with next-entry times

```text
tau_3(17/55)  = 4/11,
tau_13(17/55) = 45/143,
tau_16(17/55) = 7/22.
```

If runner `3` is excluded, the remaining candidates in this range are `13` and
`16`, and

```text
7/22 - 45/143 = 1/286 > 0.
```

For `p >= 21`, Lemma U gives

```text
tau_p(17/55) < 17/55 + 2/(11p) <= 17/55 + 2/231.
```

Since

```text
7/22 - (17/55 + 2/231) = 1/2310 > 0,
```

no `p >= 21` can beat `7/22`.

It remains to check `17 <= p <= 20` directly. Their fractional parts are:

```text
{17 * 17/55} = 14/55,
{18 * 17/55} = 31/55,
{19 * 17/55} = 48/55,
{20 * 17/55} = 10/55.
```

All lie in the safe region `[1/11, 10/11]`, so none of `17,18,19,20` is
blocking at `17/55`.

Therefore, once runner `3` is absent, the largest next-entry time among all
blocking runners is exactly `7/22`, attained by runner `16`. `square`

---

## 13. Pacemaker checkpoint obstruction

The real branching phenomenon now becomes visible: it occurs exactly at the
grid checkpoints `r/11`, not at the intermediate staircase checkpoints.

> **Lemma P0 (Pacemaker checkpoint rigidity).**
> Let `t = r/11` with `1 <= r <= 10`.
>
> 1. A runner `p` is blocking at `t` iff `11 | p`.
> 2. If the blocking multiples of `11` present in the speed set are
>
> ```text
> 11q_1 < 11q_2 < ... < 11q_s,
> ```
>
> then the maximal next-entry time at `t` is
>
> ```text
> tau_max(r/11) = r/11 + 1/(121 q_1),
> ```
>
> attained by the smallest present multiple `11q_1`.

**Proof.**

If `11` does not divide `p`, write `p ≡ a (mod 11)` with
`a in {1,...,10}`. Then

```text
{p * r/11} = {ar/11}.
```

Since `r` and `a` are nonzero mod `11`, the residue `ar mod 11` lies in
`{1,...,10}`. Hence

```text
{p * r/11} in {1/11, 2/11, ..., 10/11},
```

so `p` is not in the open blocking band.

If `p = 11q`, then

```text
{p * r/11} = {qr} = 0,
```

so `p` is lower-bad. Its next entry is when the fractional part reaches
`1/11`, namely

```text
tau_(11q)(r/11) = r/11 + (1/11)/(11q) = r/11 + 1/(121q).
```

This is strictly decreasing in `q`, so the smallest present multiple of `11`
gives the latest next-entry time. `square`

> **Corollary P0.1.**
> If the dangerous runner is `11m` and there is a smaller multiple `11q` with
> `q < m` in the configuration, then at every pacemaker checkpoint `r/11`,
>
> ```text
> tau_max(r/11) = r/11 + 1/(121q) > r/11 + 1/(121m).
> ```
>
> So the staircase step `r/11 -> (11rm+1)/(121m)` can only occur when `11m`
> is the smallest multiple of `11` present.

This is the exact obstruction that needs the separate slot-economy argument:
the only genuine competition with the dangerous runner occurs on the
`1/11`-grid itself.

---

## 14. Twelfth checkpoint `a_4 = (44m+1)/(121m)`

Define

```text
a_4(m) = (44m+1)/(121m) = 4/11 + 1/(121m).
```

> **Lemma C12.**
> For `m >= 2`, among all blocking runners at `t = a_4(m)`, the largest
> next-entry time is
>
> ```text
> tau_max(a_4) = 17/44,
> ```
>
> attained by runner `8`.

**Proof.**

For `p >= 10`,

```text
tau_p(a_4) < a_4 + 2/(11p) <= 89/242 + 2/110.
```

Since

```text
17/44 - (89/242 + 2/110) = 1/2420 > 0,
```

no `p >= 10` can beat `17/44`.

For `2 <= p <= 9`, we have

```text
0 < p/(121m) <= 9/242 < 1/11,
```

so

```text
{p a_4} = {4p/11 + p/(121m)}.
```

Now:

- `p = 2,3,4,5,6,7,9`: the fractional part lies strictly between `1/11`
  and `10/11`, so safe;
- `p = 8`: the fractional part is `10/11 + 8/(121m) > 10/11`, so blocking.

Thus the only blocker with `p <= 9` is `p = 8`, and

```text
tau_8(a_4) = 17/44.
```

`square`

---

## 15. Thirteenth checkpoint `s_9 = 17/44`

> **Lemma C13.**
> Among all blocking runners at `t = 17/44`, the largest next-entry time is
>
> ```text
> tau_max(17/44) = 23/55,
> ```
>
> attained by runner `5`.

**Proof.**

For `p >= 6`,

```text
tau_p(17/44) < 17/44 + 2/(11p) <= 17/44 + 2/66.
```

Since

```text
23/55 - (17/44 + 2/66) = 1/660 > 0,
```

no `p >= 6` can beat `23/55`.

For `2 <= p <= 5`,

```text
{p * 17/44} = (17p mod 44)/44.
```

Because `1/11 = 4/44`, blocking means

```text
17p mod 44 in {0,1,2,3,41,42,43}.
```

For `p = 2,3,4,5`, the residues are:

```text
34,7,24,41.
```

So the only blocker is

```text
p = 5   (remainder 41),
```

and

```text
tau_5(17/44) = 23/55.
```

`square`

---

## 16. Fourteenth checkpoint `s_10 = 23/55`

> **Lemma C14.**
> Among all blocking runners at `t = 23/55`, the largest next-entry time is
>
> ```text
> tau_max(23/55) = 34/77,
> ```
>
> attained by runner `7`.

**Proof.**

For `p >= 9`,

```text
tau_p(23/55) < 23/55 + 2/(11p) <= 23/55 + 2/99.
```

Since

```text
34/77 - (23/55 + 2/99) = 1/315 > 0,
```

no `p >= 9` can beat `34/77`.

For `2 <= p <= 8`,

```text
{p * 23/55} = (23p mod 55)/55.
```

Blocking means

```text
23p mod 55 in {0,1,2,3,4,51,52,53,54}.
```

For `p = 2,...,8`, the residues are:

```text
46,14,37,5,28,51,19.
```

So the only blocker is

```text
p = 7   (remainder 51),
```

and

```text
tau_7(23/55) = 34/77.
```

`square`

---

## 17. Fifteenth checkpoint `s_11 = 34/77`

> **Lemma C15.**
> Among all blocking runners at `t = 34/77`, the largest next-entry time is
>
> ```text
> tau_max(34/77) = 5/11,
> ```
>
> attained by runner `9`.

**Proof.**

For `p >= 15`,

```text
tau_p(34/77) < 34/77 + 2/(11p) <= 34/77 + 2/165.
```

Since

```text
5/11 - (34/77 + 2/165) = 1/1155 > 0,
```

no `p >= 15` can beat `5/11`.

For `2 <= p <= 14`,

```text
{p * 34/77} = (34p mod 77)/77.
```

Because `1/11 = 7/77`, blocking means

```text
34p mod 77 in {0,1,2,3,4,5,6,71,72,73,74,75,76}.
```

For `p = 2,...,14`, the residues are:

```text
68,25,59,16,50,7,41,75,32,66,23,57,14.
```

So the only blocker is

```text
p = 9   (remainder 75),
```

and

```text
tau_9(34/77) = 5/11.
```

`square`

---

## 18. What these lemmas accomplish

The lemmas above now prove the staircase envelope all the way through the next
pacemaker checkpoint:

```text
(11m+1)/(121m)  -> 6/55
6/55            -> 4/33
4/33            -> 3/22
3/22            -> 12/77
12/77           -> 2/11
(22m+1)/(121m)  -> 12/55
12/55           -> 23/99
23/99           -> 3/11
(33m+1)/(121m)  -> 23/77
23/77           -> 17/55
17/55           -> 4/11
(44m+1)/(121m)  -> 17/44
17/44           -> 23/55
23/55           -> 34/77
34/77           -> 5/11.
```

Together with Lemma P0, this isolates the exact remaining issue:

- away from the pacemaker gridpoints `r/11`, the staircase maximizer lemmas
  keep working by the same large-runner bound plus finite residue check;
- at the gridpoints `r/11`, the competition is rigid and purely among
  multiples of `11`;
- the dangerous runner `11m` follows the staircase only if it is the smallest
  present multiple of `11`.

So the dynamic proof frontier is now sharply reduced:

```text
prove the slot-economy statement that introducing a smaller 11-multiple
forces enough loss elsewhere that the final witness time cannot increase.
```

This is a much more precise obstruction than the older "dangerous windows near
10/11" formulation: the only genuine branching points are the pacemaker
checkpoints themselves.
