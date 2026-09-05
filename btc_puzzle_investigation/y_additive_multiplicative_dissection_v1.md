# y-coordinate: additive/multiplicative dissection + the RH-framework backdoor (v1, 2026-07-13)

Prompted by reviewing the ASSERTED "irreducible complexity" of `d ↦ y([d]G)` against the
user's RH programme (φ(n)-residue framework + spectral-rigidity / operator-arithmetic
duality preprint). Purpose: dissect the assertion and run the multiplicative-basis /
rigidity instruments the framework indicates. Tags: `PROVED` · `VERIFIED` ·
`VERIFIED-null (scoped)` · `CITED` · `CONJECTURAL` · `RETRACTED`.

## 1. Retraction of "irreducible complexity"

`[RETRACTED]` I asserted `d ↦ y(d)` has "irreducible complexity." That was an assertion,
and it conflated two things the additive/multiplicative lens cleanly separates:

- **Vertical (point-coordinate distribution) — PROVEN, tame.** `[CITED]` How `[d]G`'s
  coordinates distribute is square-root-cancelled by **Weil = RH for `E/𝔽_p`** (a theorem),
  so the pseudo-randomness of the *coordinates* is not asserted — it is a proven RH-analog.
  And it is the *tame* side: `ℤ[ω]` has class number 1, so its Epstein/lattice zeta
  **factors** `ζ_{ℤ[ω]}(s) = ζ(s)·L(s,χ₋₃)` `[VERIFIED numerically]` — no Davenport–Heilbronn
  off-line pathology exists in this CM field. The additive/lattice object is secretly
  multiplicative.
- **Horizontal (scalar recovery) — CONJECTURAL.** `[CONJECTURAL]` Recovering `d` is the
  sum over `d` weighted by characters at scale `~√n` — the DLP. Its hardness is an
  assumption, not a theorem. This is the *only* "irreducible" piece, and it is the same
  DLP wall as always.

So "irreducible complexity" = a proven tame theorem (Weil) + a named conjecture (DLP). Not
a vague irreducibility.

## 2. The framework's instruments, applied to `f(d) = χ₂(y([d]G))`

The framework's thesis: additive-basis analysis is the wrong instrument for a
multiplicative object; use the φ(n)-residue / Ramanujan projector (multiplicative modes).
My earlier `y`-null was **additive-basis only** (Fourier over `d↦d+k`). Two proved facts
sharpen the target: `f` is **odd under `−1`** (`p≡3 mod4`, deterministic) and **invariant
under `λ`** (`[λ]=φ` fixes `y`, deterministic) — so `f` transforms by the `μ₆` sign
character, and a multiplicative character `ψ` can correlate only if `ψ(−1)=−1, ψ(λ)=1`.
Since `n≡1 mod4` and `n−1 = 2⁶·3·149·631·(3 large primes)`, **every symmetry-allowed
character has order divisible by the full `2⁶=64`** — the smallest is order 64.

**Results (`y_multiplicative_rigidity_v1.py`, `y_order64_decisive_v1.py`):**
- Multiplicative characters order `{2,3,6,149,631}`: all `|c_m| <` floor — but all are
  *forced-zero by symmetry* (none odd), so uninformative. `[correct but not a test]`
- **Order-64 (smallest allowed): decisively NULL.** An apparent `~2.75σ` standout at
  `M=32k` **resolved to noise at `M=80k`**: `|c₁|=0.0023 <` floor, decaying `∝1/√M`; the
  full `ℤ/64` DFT gives `max_k|c_k|=0.0067` vs permutation-null max `0.0076±0.0011`,
  `z=−0.9`. `[VERIFIED-null]`
- **Rigidity Gram** (regress `f` on the residue dictionary `{d mod q}`, `q∈{3,5,7,11,13}`,
  jointly): `R²` tracks the permutation null with **no growth** (`0.0053→0.0022→0.0012`,
  `z≈0`) — **rigid**: no coherent mode across the dictionary predicts `χ₂(y)`. The
  multiplicative residue features (Legendre/cubic of `d mod q`) likewise null (`z=+1.5`).
  `[VERIFIED-null]`

## 3. Where this leaves the backdoor

The RH-framework lens genuinely reframed the problem (`x`=multiplicative/tame,
`y`=additive but—via class number 1—also tame; the DLP is the lone conjectural piece) and
directed the right instruments (multiplicative basis, symmetry-allowed characters,
residue-dictionary rigidity). Every one of them, at accessible scale, comes back **flat /
rigid** — consistent with `χ₂(y)` being the DLP hardcore bit, now tested in the additive
*and* multiplicative bases and via the rigidity operator, not just asserted.

**Honest scope and gaps (not closure):**
- All nulls are at accessible scale (chars up to order `9536`, moduli `≤13`, `M≤80k`,
  floor `~0.003–0.006`). **Nothing tests the `√n` scale**, which *is* the DLP — no
  instrument here can, without solving it.
- I built the *light* version of the rigidity instrument (`R²` regression = "does any
  coherent mode exist"). The **full operator-arithmetic-duality construction** — a
  prime-weighted Gram operator, coherent-subspace projection, spectral-floor certification
  (the preprint's actual machinery) — is **unbuilt**. For *us* the light version suffices
  to *detect* a mode (there is none); the full version is for *proving* rigidity (a
  theorem), which is the RH-side use and a larger undertaking.

Net: the backdoor was knocked on with the framework's own instruments; at accessible scale
it is as rigid as the front door. The one thing that would be genuinely new is the full
spectral-rigidity operator — a construction, not a scan — but it certifies rigidity (no
signal), it does not open one.
