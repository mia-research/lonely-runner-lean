# φ(n)-native probe of the (n,k,D) decomposition — findings v1 (2026-07-10)

**Frame.** Re-open the (n,k,D) decomposition through the *φ(n)-residue* lens
(the user's RH-line framework), not generic ML. Prior "k has no structure" nulls
tested k as an integer **magnitude**; the framework says read k as a **unit in
(Z/n)ˣ** and read n through its reduced-residue / Ramanujan structure. All exact
(integer/Fraction, `check_no_float` clean). Sample: 63 solved keys with N≥20;
null = matched uniform-d draws in the same bit-band, same exact decomposition.
Scripts: `phi_n_native_knd_probe_v{1,2}.py`, `phi_n_native_D_coupling_v{1,2}.py`,
`phi_n_native_prime_content_v1.py`.

## Result 1 — ω(n) lean is REAL and confound-controlled ✅
Real keys' position-denominators n carry **more distinct prime factors** than the
matched Farey null. Exact two-sided sign-test **p = 0.002** (44/63 above null
median). The n-**magnitude** control comes back null (p = 0.207) — so this is
**not** the "big n has more factors" artifact; the ω excess is intrinsic. This
reconfirms R4 ("composite / low-φ(n) lean", `nk_reduction_spec_v1.md`) per-key,
framework-native, with the magnitude confound now ruled out. φ(n)/n leans low in
the same direction (p = 0.207 alone, consistent).

## Result 2 — the ω(n) lean is BASE-10 smoothness, not curve/χ₋₃ arithmetic ⚠
Per-prime over/under-representation vs null (share of factor incidences):
- prime **2**: 0.412 vs 0.337 (ratio **1.22**) — real n more often even (matches R4 "even ×1.27").
- prime **5**: 0.238 vs 0.167 (ratio **1.42**) — the strongest single enrichment.
- prime **3** (χ₋₃): 0.253 vs 0.253 (ratio **1.00**) — NO enrichment.
- prime **7** (curve b=7): 0.126 vs 0.123 (ratio 1.02) — none.
- {2,3,7} curve bad primes share: 0.438 vs 0.426 — null. {3} χ₋₃: 0.140 vs 0.151 — if anything low.

Read: the lean is carried by **2 and 5 (the decimal primes)** → denominators
divisible by 10 → hand-picked keys sit on decimal-round positions (k/10, k/20,
k/50…). This is a **creator-selection / base-10 smoothness** effect — exploitable
as a prior (as R4 already is), but it does **not** touch the curve's arithmetic or
the χ₋₃ / sextic structure. The position-decomposition φ(n) thread is real but shallow.

## Result 3 — k-as-unit predictions: clean NULLs (redirect) ○
- k ≡ ±1 mod n (the operator's surviving Fourier mode): real 0.047 vs null 0.066 — null.
- multiplicative order of k in (Z/n)ˣ ≤ 2: real 0.096 vs null 0.103 — null.
So the P_n "surviving ±1 mode" does **not** surface as k = ±1 in this
decomposition. Redirects the thread; does not close the framework.

## Result 4 — D↔n propagation (bidirectional idea, direct-divisibility form): NULL after ω-control ○
Raw: D shares a factor with n more than null (gcd(D,n)>1: 0.396 vs 0.305;
D≡0 mod some p|n: 0.396 vs 0.297). **But** conditioning the baseline on each key's
OWN n (exact p_hit = 1−∏_{p|n}(1−1/p)) gives expected 21.97 vs observed 25 →
(obs−E)/sd ≈ **1.0**. The raw gap was the ω(n) confound. So the residual does NOT
demonstrably remember n's primes beyond chance — **in this direct-divisibility
form, at n=63.** This is a conditional null on ONE surface form of propagation,
not a verdict on the user's (separate) propagation math. Untested forms: k↔D
coupling, residue-class (not divisibility) signatures, multiplicative-mod-n
coupling, and structure inside the D-term recursion.

## Two distinct φ(n) threads (for steering)
- **(A) φ(n) on key POSITIONS (n,k,D)** — this doc. Real but shallow (base-10 selection).
- **(B) φ(n) on the CURVE's L-function** — `secp256k1_Lfunction_intersections.md`.
  Genuinely at the frontier: κ(L) computed on the curve's CM Hecke L(s,ψ)/ℚ(√−3),
  the μ₆/sextic organizing principle, and the one case where the framework's C.1
  (Frobenius equidistribution) is a **theorem** (Hecke CM equidistribution).
  This is the thread that brushed contemporary curve papers. Open, falsifiable
  test: instantiate the φ(n)-residue operator on the curve's Hecke L (spectral
  answer = critical line = a Weil theorem) — a check the purely-classical RH
  target cannot provide.

## Honest scope
n=63 is small; single-feature p=0.002 survives ×6 Bonferroni (~0.01) and
corroborates an independent prior (R4), so ω(n) is trustworthy. Everything else
here is either a clean null (redirects) or a shallow-but-real selection effect.
Nothing is declared permanently dead; the propagation nulls are conditional on the
specific surface form tested.
