# What the GLV Orbit Readout Enables — Factual Capabilities Ledger

**Scope:** what the confirmed public-key GLV/cubic readout (see
[CONFIRMED_glv_orbit_readout_puzzles_135_140_v1.md](CONFIRMED_glv_orbit_readout_puzzles_135_140_v1.md))
lets us do, combined with the other confirmed structure in this project.
Every row states the capability **and its measured magnitude/status**. Date 2026-08-16.
Curve: secp256k1, `p = 2^256 − 2^32 − 977`, `n` prime, `y² = x³ + 7`, `j = 0`, CM by `ℤ[ω]`.

---

## A. The primary capability — GLV order-6 automorphism, made explicit per key

**Fact.** From public `(x,y)` we read `e = cubic_exp(x) ∈ {0,1,2}` and sign `s`, which
place the point in its **order-6 automorphism orbit** under `⟨φ, [−1]⟩`
(`φ = [λ]`, order 3, `x→βx`; negation order 2). Confirmed exact for #135 `(e=1,s=0)`,
#140 `(e=0,s=1)`.

**What it enables — Pollard rho / kangaroo speedup.**
An automorphism group of order `m` acting freely speeds up collision-based DLP search
by up to `√m` (standard: Wiener–Zuccherato 1998; Duursma–Gaudry–Morain 1999;
Gallant–Lambert–Vanstone 2001; Bos–Kleinjung et al. on GLV rho). Here `m = 6`.

- **Realized factor: up to `√6 ≈ 2.449×`** (≈ **1.29 bits**).
- On #135's 134-bit interval, the ~`2^67`-scale kangaroo cost drops to the
  **`~2^65.7` group-operation scale**.
- Status for interval (kangaroo) search specifically: the negation part of the
  factor is implementation-dependent (interval is not `±`-symmetric; `φ` maps the
  interval to a shifted copy). Conservatively a **~2×–2.45× constant factor**.

**Magnitude in absolute terms:** `2^65.7 ≈ 6×10^19` group operations — the
best-known-algorithm cost with the order-6 automorphism factor applied. Genuine
constant-factor reduction of the search.

**What it does NOT enable (measured, not asserted).**
The orbit label `(e,s)` does **not** yield `d mod 6` / `d mod 3` / `d mod 2` as a
congruence that prunes the interval to an arithmetic progression:
- MI( public signature ; `d mod 6` ) ≈ 0.02–0.07 bits (at shuffle-noise floor).
- Out-of-sample learned predictor of `d mod 6` on 400 real secp keys in the
  `[2^134,2^135)` range: **16.25% = chance (1/6)**; same learner predicts a genuinely
  public quantity at 92% (control fires). Scope: the CM/GLV secp family, `d` in the
  puzzle interval.
So there is no `2.585-bit` interval-pruning and no arithmetic-progression restriction
of `d`. The real key-side effect is the `√6` search factor above, not a residue on `d`.

---

## B. Other confirmed structure — status toward key recovery

| Discovery | Verified? | Demonstrated key-side capability |
|---|---|---|
| Class-number law `\|FLD(p)\|=6·h(−p)`, `p≡19 mod 24` | Yes, 69/69; `h` cross-checked 3 ways | None demonstrated — identity about `ℚ(√−p)` |
| μ4 cover even-split `b₁=b₃=0` (universal over primes) | Yes, 12 primes × 3 curves | None demonstrated — property of `Jac(w⁴=f)` |
| μ4 "supersingular `b₂=p`, scale-free" | **No** — p=43 artifact; `b₂∈{0,±p,±2p}` | n/a (claim did not survive) |
| Eisenstein core-gate `s<3/16` for #135/#140 | Yes, exact rational | Confirms `x`-lift sits in rhombus core; no lever beyond GLV |
| μ3 CM pullback-invariance vs non-CM | Yes | Restates the `(x,y)→(ζ₃x,y)` automorphism = same GLV structure as A |

**Net:** the single confirmed discovery with a *demonstrated* effect on the search
cost of #135/#140 is the **GLV order-6 automorphism (§A) → up to `√6` search speedup**.
The remaining items are verified structural/arithmetic facts with **no key-recovery
pathway demonstrated to date**; that is their current status, not a claim they are
useless.

---

## C. Honest bottom line

- **Real and usable:** GLV order-6 automorphism structure, read exactly off each
  public key, giving up to a `√6 ≈ 2.45×` (`~1.3-bit`) constant-factor speedup to
  rho/kangaroo search — the best-known speedup for this curve family.
- **Real but key-inert (so far):** class-number law, μ4 even-split, core-gate norms.
- **Not established:** any `d mod 6` congruence, interval pruning, `2.585-bit`
  reduction, or sub-`2^65` pathway to #135/#140. Measured at chance with a firing control.

Open, if wanted: (1) exact realized kangaroo factor for the GLV+negation classes on
an interval (implementation study); (2) #145 readout once its public `(x,y)` is supplied.
