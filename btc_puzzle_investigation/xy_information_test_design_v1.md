# Does (X, Y) leak the private key? — a valid test design

**Scope.** Only the claim from `canonical_truth_v2` that the public point
`(X, Y) = d·G` carries recoverable information about the private key `d`. The
D-recursion and the (n, k, D) parameter machinery are out of scope by request.

---

## 1. The ideas, de-fluffed

Stripping the metaphors ("2-torus", "longitude/latitude", "thermodynamic
temperature", "φ(n) universal constant"), the source makes three concrete,
falsifiable claims about `(X, Y)`:

- **A — Residue channel.** `X` and `Y` reduced modulo something constrain a
  reduced coordinate of the key (the doc writes `a_X = X mod M_X`,
  `k ≡ a_X`). Generalized and made honest: *does any function of `X mod m`,
  `Y mod m` predict `d mod m'` above chance?*
- **B — Magnitude / position channel.** The size of a coordinate as a fraction
  of the field prime estimates where `d` sits in its band (`y_ratio = Y/p`,
  `d₀ ≈ y_ratio · range`). Made honest: *does the magnitude of `X` or `Y`
  predict the position `u = (d − 2^{N−1})/2^{N−1} ∈ [0,1)`?*
- **C — Joint / two-coordinate channel.** `X` and `Y` are "independent" and
  jointly localize `d`. Made honest: *do `X` and `Y` together predict a
  `d`-function better than either alone?*

## 2. Why the source's *form* is unsound (but the *idea* is testable)

- The formulas (`M_X = (n−1)/2`, `M_Y = (n+1)/2`, `d₀ ≈ (Y/p)·range`) have no
  derivation and are asserted, not measured.
- The "extractor" uses the **secret** `n` to reduce `X` — circular: you cannot
  compute `X mod n²` on an unsolved puzzle because you do not know `n`.
- The demo/solver had **no sensitivity control**, so a null result was
  indistinguishable from a dead detector — that is exactly how it fooled its
  author.

None of that kills the underlying question. "Does `(X, Y)` leak a *reduced
coordinate* of `d`?" is a well-posed information-theoretic question with a
clean null and a decisive control. That is what we test.

## 3. Two experiments the source conflates

| | E1 — Map property | E2 — Selection property |
|---|---|---|
| Data | Synthetic: uniform-random `d`, **real** secp256k1 arithmetic | The real solved puzzle keys |
| Question | Does the *curve map* `d ↦ (X,Y)` leak `d`? | Do the *creator's actual keys* leak more than uniform? |
| Power | Arbitrary (100k now, more on demand) | Bounded by ~82 keys |
| Independent of the puzzle PRNG? | Yes | No — this *is* the PRNG/selection question |
| Decisiveness | High — this is the real ECDLP-leak question | Low — a marginal prior at best |

E1 is the decisive first test. If the curve map does not leak `d` at high power,
no universal `(X,Y)`-extractor exists, regardless of metaphor. E2 is the
follow-up and can only ever yield a marginal prior (it never uses the secret at
attack time only if the leaked quantity is public — position/parity are, most
are not).

## 4. Targets (functions of the secret `d`, computed on solved/synthetic keys)

- Residue: `d mod 2, 3, 5, 7, 11, 13`.
- Positional bits: middle bit `(d >> ⌊N/2⌋) & 1`, second-from-top bit.
- Position bin: `⌊8·u⌋`, `u = (d − 2^{N−1})/2^{N−1}` (needs `N ≥ 8`).
- **Planted controls** (not `d`-functions — sensitivity calibration):
  - `PLANT_strong = X mod 7` (deterministic in `X`; detector MUST recover ~log₂7 bits).
  - `PLANT_weak = X mod 7` with 90 % of labels overwritten by uniform noise
    (a deliberately faint leak; the MI at which this fires = the sensitivity floor).

## 5. Features (from `X`, `Y`, and public `N` ONLY — never `d`, never a secret `n`)

- Residues `X mod m`, `Y mod m` for `m ∈ {2,3,4,5,7,8,9,11,13,16,25,32,64,256}`.
- Magnitudes: `⌊256·X/p⌋`, `⌊256·Y/p⌋` (top bits), Hamming weight of `X`, of `Y`.
- Parities: `X & 1`, `Y & 1` (`Y`'s is public — it is the compression prefix).
- Curve-aware views (still public — no secret used):
  - GLV endomorphism `φ(P) = (β·X mod p, Y)`, β the cube root of unity → its residues.
  - Negation `−P = (X, p−Y)` → its residues.

Feature hygiene rule: **every feature is a function of `(X, Y, N)` alone.** Any
feature that needs `d` or the secret `n` is disqualified (that was the source's
circularity).

## 6. Statistics, null, control, correction

- **Estimator 1 (per-feature):** mutual information `I(feature; target)` in bits
  via contingency table (features binned, targets discrete).
- **Estimator 2 (joint, Channel C):** `HistGradientBoosting` 5-fold CV accuracy
  on the *full* feature matrix vs a permutation null — catches structure no
  single feature carries.
- **Null:** permute target labels `R = 2000×`; empirical
  `p = (#null ≥ obs + 1)/(R+1)`.
- **Look-elsewhere:** track the max statistic over all (feature, target) cells
  per shuffle → corrected `p` from that max-null. (The source, and our own past
  F1, both died of look-elsewhere; it is mandatory.)
- **Sensitivity floor:** the MI at which `PLANT_weak` reaches corrected `p<0.05`.
  Report it. A null real target is then a *bound* ("no leak larger than X bits"),
  not "no information" — a conditional negative.

## 7. Out-of-sample confirmation (survivors only)

Any target with corrected `p < 0.01` is refit on a train split and confirmed on
a held-out split (held-out **confirms**, it does not discover). No OOS
confirmation → treat as look-elsewhere noise.

## 8. Attack-validity (translation, if E1/E2 ever fire)

A leakage test uses the secret as the *label* — that is a necessary condition,
not an attack. Residue channels translate to an attack only in **candidate-sweep**
form: compute the statistic at all candidate moduli `m'` and bet on the outlier;
a real attack never touches the secret. Stage 1 (leak with known `d`) is required
before any Stage 2 (public-only sweep) is worth building.

## 9. Pre-registered decision rule

1. **Control gate.** If `PLANT_strong` does not fire at `MI ≈ log₂7`, the run is
   void (dead detector) — fix and rerun.
2. **Signal.** Any real target at corrected `p < 0.01` **and** OOS-confirmed →
   SIGNAL; proceed to attack translation (§8).
3. **Null.** Otherwise → report the sensitivity floor as a bound. No "impossible",
   no "secp256k1 broken" — a bounded conditional negative tied to this feature
   set, sample size, and MI floor.

Run E1 first (decisive, high power). E2 second (selection, low power).
