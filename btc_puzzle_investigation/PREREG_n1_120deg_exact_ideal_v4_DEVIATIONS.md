# Deviations log — PREREG_n1_120deg_exact_ideal_v4.md

*Filed as they occur, not retrospectively (prereg §8). Each entry: when, what, why, effect on the
frozen design.*

---

## D1 — 2026-07-26, PRE-DATA (at freeze construction; no `V₁` computed yet)

**What.** The prereg §3 parenthetical stated the 120° law was "measured at
`p ∈ {13,43,127,163,211,349,397,433,547}` — all ≤547 … those nine are IN-SAMPLE." On enumerating the
selection rule (`p ≡ 7 mod 12`, `p ≤ 547`, `n=#E` prime) the actual rule-based in-sample set is

> **IN-SAMPLE I = {43, 67, 79, 127, 163, 211, 547}** (7 primes),

which is exactly the set the in-session reviewer measured (43, 67, 79, 127, 163, 211). The quoted nine
were the *original mixed-strata* measurement set from `RESULT_n1_v_sign_mechanism_v1.md`: `13, 349, 397,
433` are `≡ 1 mod 12` (not `≡ 7`), i.e. they belong to stratum-C territory, and were selected by an
earlier sweep that did **not** stratify by `p mod 12`.

**Why it happened.** The prereg reused a prose list from the source RESULT doc as if it were the
`p ≡ 7` in-sample set; it is a superset drawn from a different (unstratified) sweep.

**Effect on the design — none load-bearing.**
- The freeze (`n1_120deg_FREEZE_v1.json`, SHA-256 `a964f246b87fbe302b4740c3123a40a25ff0376b60cc45f8c3ef14d3c23c9fdf`)
  implements the **rule** correctly: I = {43,67,79,127,163,211,547}.
- **Out-of-sample integrity of STRATUM S is intact.** Every S prime (823, 907, 967, 991, 1051, 1303,
  1831, 2143, 2251, 2503) is `> 547`; none appears in either the rule-based I or the original mixed set
  (union of "seen" primes = {13,43,67,79,127,163,211,349,397,433,547}, all ≤ 547). The primary claim is
  and remains a prediction on unseen primes.
- The in-sample primes are reported in their own row and **never pooled** with S (unchanged).

**Resolution.** Proceed with the rule-based I = {43,67,79,127,163,211,547} as the frozen in-sample set.
No re-freeze needed (the JSON already encodes the rule, not the erroneous prose). This entry is the
correction of record.

---

## D2 — 2026-07-26, PRE-DATA — `g`-statistic implementation is MULTI-MODULAR (exact, no float)

**What.** PREREG §2 item 5 specifies `g = deg gcd(L*(T), L*(ζ₃T))` "over `ℚ(ζ_n, ζ₃)`". Direct GCD in
that degree-`2(n−1)` field requires inverting cyclotomic elements over `ℚ` — heavy for `n` in the
hundreds/thousands. The run computes `g` **multi-modularly**: for several primes `ℓ ≡ 1 mod 3n`, embed
`ζ_n, ζ₃ ↦` fixed roots of unity in `F_ℓ`, reduce the `L*` coefficients, and compute `deg gcd` over
`F_ℓ` by the Euclidean algorithm. Reduction can only **raise** the gcd degree (extra common factors
mod a bad prime), never lower it, so **`true g = min over ℓ`**; sampling several `ℓ` and taking the
minimum is exact. All arithmetic is integer/modular — **no float** — so the folder OVERRIDE is honored
(and this mirrors the record's own `audit_n1_vsign_v2_multimod.py`).

**Why.** Same-verdict exact computation at feasible cost; the direct field GCD is not float-free-cheap
at these `n`.

**Effect.** None on the statistic's meaning; `g` is still exact. The `ℓ`-selection is deterministic
(first 5 primes `ℓ ≡ 1 mod 3n`) and therefore frozen, not p-hackable.

---

## D3 — 2026-07-26, PRE-DATA — C-CROSS scope note

**What.** The run reuses the record's exact `hist_k1`/`hist_k2` (`audit_n1_vsign_v2_core.py`) for the
`V₁`/`V₂` integer histograms. Reuse is not an independent second implementation, so C-CROSS as
"two independent `V` implementations" is **partially** met: (i) regression against the core script's
published `h1,h2,W` at `p=13,43` holds by construction; (ii) the **independent** sign/coefficient check
is carried by **C-COEFF** via the Sage `O(p⁴)` eigenvalue route (`n1_twisted_eigenvalues_v1.sage`,
Sage present), which does not share the `V₂` convention. A fully independent second `V₂` implementation
is deferred; C-COEFF is the operative sign guard.

**Effect.** The `V₂→e₂` sign is still guarded (by C-COEFF, the control the gate designed for exactly
this). Noted so the C-CROSS claim is not overstated.

---

## D4 — 2026-07-26, DURING RUN — the forced `e₃` sign is `p mod 4`-dependent; a first-pass stratum-C null was a BUG (caught by C-COEFF cross-check)

**What.** The first sweep imposed `e₃ = −p·e₁` (prereg A6) on **every** prime and reported
**stratum C (p≡1 mod12): 0/5, `g=0` at every cell** — which would have fired the pre-committed
"stratum-specific law" reading (§5). **That null is spurious.** The independent Sage `O(p⁴)` route
(C-COEFF) at `p=13` (a `p≡1 mod4` prime) returns eigenvalue phases `{±0.211π, ±0.8776π}`, and
`0.8776π − 0.211π = 0.6667π = 120°` **exactly** — the `ζ₃` ratio **is** present, so the true `g` is 2,
not 0.

**Root cause.** `e₃ = −p·e₁` is **not** universal; it follows from the `α ↦ −ᾱ` closure, which holds
only when `χ₂(−1) = −1`, i.e. `p ≡ 3 mod 4` (stratum S). For `p ≡ 1 mod 4` (stratum C), `χ₂(−1) = +1`,
`V(a)` is **real** (not imaginary), the closure is `α ↦ ᾱ`, and the forced relation is `e₃ = +p·e₁`
(`e₄ = p²` is universal — both closures give it). Imposing the stratum-S sign on stratum-C data built
the wrong `L*` and manufactured `g=0`. **A null on wrong-convention data is uninformative** — the
folder stance, exactly.

**Fix.** `e₃ := χ₂(−1)·p·e₁ = (leg)·p·e₁`, `leg = +1` if `p≡1 mod4` else `−1` (run_n1_120deg_v1.py,
`g_and_flags`). Re-verified: with the fix, `p=13,577,733` (all `p≡1 mod4`, previously `g=0`) now give
**`g=2` at every cell**; `p=43,67` (`p≡3 mod4`) are unchanged at `g=2`. Independent confirmation of the
sign itself (that `e₃/(p·e₁)=+1` for `p≡1 mod4`, `−1` for `p≡3 mod4`) is from the Sage `V₁..V₄` route
(`verify_e3_sign.sage`), which imposes nothing.

**Corrected finding.** The 120° law (the `ζ₃` ratio, `g=2`) holds in **both** strata; it is **not**
stratum-specific. What differs by stratum is the **pairing/closure sign** (`e₃ = χ₂(−1)·p·e₁`). This
**amends prereg A6**, which stated `e₃=−p·e₁` unconditionally (true only for `p≡3 mod4`).

**Lesson (for memory).** The forced relation used to avoid computing `V₃,V₄` was itself
convention-dependent; hard-coding one stratum's version produced a confident false null on the other.
The cross-check (C-COEFF, independent implementation) is what exposed it — a firing plant would not
have, since the plants are all `p≡3 mod4`-geometry Weil numbers.
