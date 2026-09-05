# Exclusions / negative correlations of (X,Y) vs n,k,d — findings v1 (2026-07-10)

**Question (user):** beyond aggregate MI, "cross-reference against itself or any
negative correlation" — does any residue of (X,Y) *forbid/deplete* (rule out) a
value of n/k/d? Ruling candidates out is a search reduction that unsigned averaged
MI can miss. Tool: per-channel contingency standardized residuals — min residual
(most depleted cell = strongest exclusion / negative corr), empty cells with E≥5
(forbidden combos), signed 2×2 odds ratios — permutation-validated. N≥64 (64,020),
exact n,k,D. Script: `phi_n_exclusion_scan_v1.py` (+ discriminator check).

## Positive control ("against itself") — the method WORKS
n and k are coprime by construction, so `n≡0 mod q` forbids `k≡0 mod q`:
- n vs k mod 2/3/5/7: **min-resid = −84, −64, −42, −31; one empty (forbidden) cell
  each; perm p=0.002** (floor). The test detects a real exclusion overwhelmingly.

## (X,Y) → {n,k,D}: NO exclusion, NO negative correlation
- Most-depleted cell across 120 channels: **min-resid −3.80, ZERO forbidden
  (empty) cells** anywhere. Against the control's −84 with an empty cell, this is
  the noise floor. The flagged extreme ((X+Y)mod16 vs D, perm p=0.007) is the
  survey max over 120 channels (look-elsewhere ≈0.8).
- Signed 2×2 odds ratios (X&1, Y-parity, Legendre(X)) vs (n&1, k&1, sign D): all
  **0.978–1.013** — no positive or negative association.

## Recurring D-artifact confirmed inert (same as the MI finding)
The depleted cells that survive permutation are all **D-channels**, and the d-vs-D
discriminator settles them exactly as before:
- (X+Y)mod16: vs **D** min-resid −3.80 p=0.002 (halves −2.69,−3.22, replicates);
  vs **d** p=0.303 (NULL); vs **n** p=0.542 (NULL).
- Matches (X*Y)mod64 vs D (MI scan): tracks the construction residual D=d−base, not
  the key d. Cryptographically inert (predicting D mod m needs the unknown base to
  reach d; d mod m is directly null).

## Verdict (two independent lenses agree)
Aggregate MI AND exclusion/negative-correlation both find **no reduction of the
private key d (or n, k)** from any residue/resonance of (X,Y). Both methods are
positive-control-validated (MI: it would show; exclusion: n-vs-k fires at −84).
The only recurring non-null is a tiny artifact confined to the construction
residual D, which does not propagate to the key. This is a bounded, quantified,
twice-confirmed null — consistent with ECDLP one-wayness, now measured from two
directions rather than assumed.
