# The complete account of the cascade — Level C: the run as a function of the arrangement (v1)

2026-10-01. `CASCADE_DESIGN_v3` §8.4. Owner: *"Yes on to the next, if it not large then continue on to other too"*. Log
E223. No Lean (owner, E222).

**What Level C is.** How a whole chain depends on the speeds, derived from Levels A and B. Notation as in A.0 and B. An
arrangement is its speeds, up to scale (the proved symmetry). **Grades:** `[derived]` (on paper, checked in §C.8);
`[PROVED]` only through Level A's anchors.

**One flag for the owner.** C.4 and C.5 use A.1's `move_le_of_lonely` (the chain never passes a lonely instant), and so
its corollary A.9 (the landing is the first lonely instant at or after the bound). The owner ruled that the argument for
the conjecture does not rest on "first isolation" (E200). Here it is used only to describe what the oracle does when an
arrangement crosses a wall. It is not offered as part of a proof. This is said here so the owner can rule on it.

---

## C.1 The chain is decided by finitely many signs `[derived, for a chain of finite length]`

By B.1 and B.2, each move is decided by two kinds of comparison, all homogeneous and linear in the speeds:
- **edge forms:** at an exit of `a` on lap `k`, reading `b` against an edge `8j ± 1`: the sign of
  `b(8k + 1) − a(8j ± 1)`;
- **tie forms:** between two crowd members `c, c'` in slots `l_c, l_{c'}`: the sign of
  `c'(8l_c + 1) − c(8l_{c'} + 1)`, which decides which exits last (B.1). **A tie form is an edge form:** `c` and `c'` exit
  together exactly when `c` is on its leaving edge `8l_c + 1` at `c'`'s exit. So the edge forms alone decide the chain.
  (This was found by the check, §C.8; the first draft treated ties as a separate kind.)

The bound is the slowest reading's exit on lap 0, so it is covered by the edge forms with `a = m`, `k = 0`. Also needed is
the order of the speeds: the forms `s_i − s_j`.

So **if none of the forms used by a finite chain vanishes at an arrangement, every arrangement close enough has the same
chain**: the same setters (by rank), laps and landing certificate. The proof is by induction on the moves: each move's
outcome is a function of these signs alone. The zero sets of the forms are **walls**: hyperplanes through the origin.

## C.2 Two kinds of wall `[derived]`

- **Edge walls:** some reading exactly on an edge at some exit of the chain, `b(8k + 1) = a(8j ± 1)`.
- **Tie walls:** two crowd members' exits coincide, `c'(8l_c + 1) = c(8l_{c'} + 1)`. These are the edge walls on which
  a crowd member sits on its **leaving** edge at the setter's exit.
- Order walls (`s_i = s_j`) are the boundary of the arrangement space (two equal speeds, the lower orders).

## C.3 Crossing a tie wall: a relabelling, or the landing's leaving face `[derived]`

On a tie wall two crowd members exit together. Just either side, one exits a little later and sets the move; the other has
just left (clear, BSM). The new instant moves continuously across the wall, and the crowd at it is the same on both sides
(positions at a given instant do not depend on the chain, A.4).
- **At an intermediate move**, only the setter's name and lap at that move change; the rest of the chain and the landing
  are unchanged.
- **At the final move**, the tie wall is the landing's leaving face for the other member (C.5): **the landing hands off**
  from one to the other, with its instant continuous.

(A first draft said the landing never changes. The check found 54 crossings, all at the final move and all continuous
hand-offs, and the derivation was repaired: a tie is an edge on the leaving side, C.1.)

## C.4 Crossing an edge wall at an intermediate move: the route changes, the landing does not `[derived]`

The cascade's next move depends only on the current instant (A.1: `move` is a function of `t`). A chain never passes a
lonely instant (`move_le_of_lonely`), so a chain from the bound lands at the first lonely instant at or after the bound
(A.9). Take an edge wall at an intermediate exit `τ_j`: reading `b` exactly at an edge at `τ_j`. Crossing it changes `b`'s
speed by an infinitesimal amount:
- on one side `b` is in the way at `τ_j`, on the other it is not, so the chain's moves from `τ_j` on can differ (B.8: `b`
  joins the next crowd, or arrives one move later);
- the lonely instants change only near `b`'s own edge crossings. The landing `τ*` is not one of them unless `b` is also on
  an edge at `τ*` (then the wall is also a face of the landing's box, C.5), and no earlier instant becomes lonely unless
  `b` alone blocks it at an edge (then the wall is a face of an earlier certificate's box, C.6).

So **crossing a wall at an intermediate move changes the route between `τ_j` and the landing, never the landing, unless
the wall is also a face of the landing's box or of an earlier certificate's box.** This closes **gap C2** (where the
chain rejoins): the two routes meet again at the latest at the landing. Since the move depends only on the instant, they
coincide from the first instant both reach.

## C.5 The landing's own faces `[derived]` (E218 M4-3, M4-4, sharpened)

At the landing certificate `(h, K, (k_d))`, the faces are `d(8K + 1) = h(8k_d + 1)` (leaving) and `= h(8k_d + 7)`
(entering). Crossing one, with only `d` changing infinitesimally:
- **leaving face** (`d` just slower): `d` is in the way at `τ*` on the leaving side and exits just after. Every other
  reading had slack at `τ*` (generically), so it is clear at `d`'s exit. **The landing hands off to `d`'s opening on lap
  `k_d`, continuously, with no exception at an infinitesimal crossing.**
- **entering face** (`d` just faster): `d` is in the way at `τ*` on the entering side. The route to `τ*` is unchanged (C.4),
  so the next move is `d`'s exit on lap `k_d + 1`, at `(8k_d + 9)/(8d)`. The new landing is that exit if it is lonely, or
  the relay continues from there (Level B).
- **On both faces, no earlier instant becomes lonely at an infinitesimal crossing, unless the face is also a face of an
  earlier certificate's box**: two walls through one arrangement (C.6). Example: `(1, 3, 4, 5, 6, 7, 8)`, reading 4
  moved to its entering face `21/5` at the landing `25/56` is also on its leaving edge at the earlier instant `15/56`,
  where reading 7 is on its entering edge and every reading is clear. This condition was implicit in the first draft and
  is made explicit after the check found it (4 crossings in §C.8, all of this kind).
- **Gap C2a resolved:** E219 moved `d` a finite distance from its value to just past the face. The path crossed every
  wall involving `d` on the way: other readings' edges at other instants, order walls, and the faces of earlier
  certificates. That produced the 243 "other" and 106/153 "earlier" leaving-face cases and the 281 "earlier"
  entering-face cases. They are not exceptions to the local rule. §C.8 checks this with infinitesimal crossings.

## C.6 The landing's region `[derived]`

The landing certificate is constant on the arrangements inside its box (E218, M4-1) and outside the box of every
certificate with an earlier instant (E219). Its boundary is made of the box's own faces (C.5) and those earlier boxes'
faces, where an earlier instant becomes lonely and the landing jumps to it. Intermediate walls (C.4) and tie walls (C.3)
lie inside the region and change only the route.

## C.7 What Level C does not say

It does not say which certificate's region contains a given arrangement, or why the regions leave no arrangement out:
that is the obligation (map §5). Placement by grid plus deviation is Level D.

---

## C.8 The check (M8)

`LonelyRunner/experiments/nN/redo/cascade_level_c_check_v1.py`, exact rational speeds, `η = 10⁻⁹` relative.
- **C.1:** compute every form's margin along the chain (each reading's distance to its nearest edge at every exit, the
  setter's lead over the next exit at every move, and the gaps between speeds). Perturb every speed by a random
  multiple of a quarter of the safe size. The chain (setters by rank, laps, landing) must be identical. Arrangements on
  a wall (a margin of 0) are counted, not perturbed.
- **C.3:** at a move with another crowd member, place that member exactly on the tie wall with the setter. Both sides at
  `η` must have the same landing, with the chains differing only in that move's setter.
- **C.4:** at an intermediate exit, place a reading not in the next move's setters exactly on its nearest edge. Both
  sides at `η` must have the same landing, unless that reading is also on an edge at the landing (counted).
- **C.5:** at the landing, place each reading exactly on each face. The inside must land at the certificate (otherwise
  counted as a moved region). The outside must hand off to that reading's opening on lap `k_d` at an instant within
  `O(η)` (leaving face), or have its next move from the old landing at that reading's next exit with no earlier landing
  (entering face).

Populations: 300 seeded fine shapes (least reading 1,000, spread uniform in `[2, 20]`); 300 late band shapes drawn
uniformly; 300 sets drawn uniformly from the readings ≤ 16 family (many on walls, counted). Pass condition: 0 failures.
Result: log E223.
