# What the GLV Orbit Readout Enables — Capabilities Ledger (v2, CORRECTS v1)

**v2 retracts the √6 search-speedup claim of v1 as an error.** Date 2026-08-16.
Curve: secp256k1, `p = 2^256 − 2^32 − 977`, `n` prime, `y² = x³ + 7`.

## ⚠ Correction to v1 (self-audit)

v1 claimed the order-6 GLV+negation automorphism gives "up to `√6 ≈ 2.45×`" speedup
on #135, taking `~2^67.5 → ~2^66.2`. **This is wrong for the puzzle setting.** The
`√m` automorphism speedup is a **full-group Pollard-rho** result. The puzzles are
**interval DLP** (`d ∈ [2^134, 2^135)`), and the automorphism images leave the interval:

| image | fraction landing back in `[2^134,2^135)` (100k trials) |
|---|---|
| `φP = [λd]G` | **0 / 100000** |
| `φ²P` | **0 / 100000** |
| `−P = [n−d]G` | **0 / 100000** |

`λd mod n` and `n−d` are ~uniform in `[0,n)`; the interval is `2^-121` of the group,
so the images essentially never return. **A search folded on these images does not
stay in the interval, so the √6 does not apply.** v1 asserted it from rho literature
and never simulated it — the misapplication is the error.

## What the automorphism actually enables for interval DLP

- **GLV `φ`: no established interval-search speedup.** `φ` maps the interval elsewhere;
  there is no clean way to use it to accelerate a kangaroo on `[lo,hi)`.
- **Negation map: a real but modest factor.** Galbraith–Ruprai (2010) use the negation
  equivalence for short-interval DLP, up to `~√2`, with nontrivial implementation cost
  (fruitless-cycle handling). This is the *only* automorphism factor that applies here,
  and it is **not** what v1 claimed. Not simulated in this project; cite as literature.
- `ε=0` does **not** change any of this — `ε` concerns the coordinate lift, orthogonal
  to whether an image stays in the interval.

## What the readout genuinely IS (unchanged, and real)

- **Exact, public, O(1) orbit readout** `(e, s, y-parity)` per key — #135 `(1,0,0)`,
  #140 `(0,1,1)`. Real. (`CONFIRMED_glv_orbit_readout_puzzles_135_140_v1.md`.)
- **Exact, public, total ε-decision** `ε=0 ⟺ |u−v|≤½`, locus exactly 3/4, gate `s<3/16`
  = `π√3/8`. Real, proved. (`CONFIRMED_core_gate_carry_epsilon_zero_v2.md`.)

## What it does NOT enable (measured this session, controls fired)

- No `d mod 6 / d mod 3 / d mod 2` from public data (MI at shuffle floor; OOS predictor
  at chance on 82 solved keys and 400/800 secp keys).
- No a-priori exclusion of any `d`-region: the full 7.1-bit per-point signature has MI
  with `d mod k` at/below the shuffle floor. **Per-computed-point** the signature rules
  out 99.2% of candidates, **but this confers no search advantage** — it is a function
  of a point already computed and is strictly weaker than the exact point comparison the
  search performs anyway (self-audit correction: v1-era "table/memory cut" framing
  overstated this).
- No island exclusion: the target's Dirichlet island (5.14 bits) is not predicted by the
  public point (MI below shuffle floor); keys do not cluster at islands (matched null).

## Net (corrected)
The orbit readout and ε-decision are **real, exact, public** structural facts. They do
**not** deliver a search-space reduction on the puzzles: the √6 was a misapplied
full-group figure (retracted), the per-point filter is inert for search, and every
`d`-side exclusion tested is at the control floor. The one automorphism factor that
genuinely applies to interval DLP is the negation map (`≤√2`, Galbraith–Ruprai), which
is standard and not specific to this readout.
