# Twist-order n_t spectral analysis — corrected (2026-07-10)
Reworks the "Spectral Dilution / spectrally optimal n_t" claims. Script inline in
session; n_t = 2(p+1)−n = 3²·13²·3319·22639·P, P a 220-bit prime.

## 1. Frame bounds of the full S_{n_t} — LOOSE, not tight
Ramanujan sum c_{n_t}(k)=∏ c_{p^a}(k) is multiplicative; c_{p^a}∈{0,−p^{a−1},p^{a−1}(p−1)}.
Nonzero ⟺ 3|k and 13|k (squared primes); 3319,22639,P always contribute (−1 or ℓ−1).
- **min nonzero |c| = 39** (= 3·13, large primes in their −1 branch; exact at k=39, c=−39).
- **max over NONTRIVIAL modes |c| = φ(n_t)/2 = 3.56×10⁷⁶**, at **k = n_t/3** (3‖k drops the
  3²-factor 6→3, all else maximal; verified c_{n_t}(n_t/3)=−φ(n_t)/2). The DC mode k≡0 gives
  φ(n_t) but that's trivial — do NOT quote it as the max (self-correction, 2026-07-10 audit).
- **frame |λ|² ratio ≈ 2⁴⁹⁸** (nontrivial; 2⁵⁰⁰ incl. DC) — dominated by P. NOT tight; maximally loose.
The synthesis's **576** = ratio ONLY on the sub-family where 3319,22639,P ∤ k (factors=−1):
min 39, max 6·156=936, ratio²=576. That's the **typical-mode spread** (bulk density ≈1),
a legit statistic — but NOT a frame bound (a bound is sup/inf over ALL modes → 2⁵⁰⁰).
Drop "tightest possible frame / spectrally optimal."

## 2. μ(n_t)=0 — the squared primes ANNIHILATE the survival mode (liability, not asset)
Because 3²,13² | n_t, **μ(n_t)=0**, so the framework's survival value
**c_{n_t}(±1) = μ(n_t) = 0** — the k=±1 infinite-lifetime mode is killed on n_t.
Clean Ramanujan survival needs a SQUAREFREE modulus; n_t is the opposite. Small squared
primes HURT the φ-averaging here — the reverse of the "optimal" story. Qualitative correction.

## 3. CM support fraction — enhancement 1.5× is right; fractions are 1/2 & 1/3
CM data a_k ≠ 0 ⟺ split ⟺ k≡1 mod 3 (χ₋₃=+1). Split density among the coprime (surviving)
modes, by direct residue count:
- **3 | n_t**: coprime residues ⟹ k≡1 or 2 (mod 3) only → split density **1/2** (verified 216/432).
- **3 ∤ q** (random ≡1 mod3): coprime residues hit {0,1,2} (mod 3) equally → **1/3** (verified 432/1296).
- **Enhancement = (1/2)/(1/3) = 3/2 = 1.5×** — the synthesis's ratio is CORRECT, but the
  absolute fractions are **50% and 33%**, not 3/7 (43%) and 2/7 (29%). The "/7" was spurious
  (coincidentally preserves the 3:2 ratio, so 1.5× still came out).

## Honest bottom line on "how special is n_t"
Real, correct: (a) **n_t/φ(n_t)=1.6256** — elevated φ-ratio from the small factors 3,13²;
(b) **1.5× CM support density** among coprime modes (from 3|n_t). Both genuine.
Wrong: the **tight-frame / spectrally-optimal** claim — the full frame is loose (2⁵⁰⁰),
and the squared primes make **μ(n_t)=0**, annihilating the survival mode. So n_t is
"special" via small factors + mod-3 alignment, but the squared primes are a LIABILITY for
the survival/frame mechanism, not an optimization. Reframe the section accordingly.
