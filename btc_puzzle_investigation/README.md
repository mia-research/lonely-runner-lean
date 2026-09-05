# Bitcoin Puzzle Investigation — folder contents

Snapshot of a search in progress. See `btc_puzzle_findings_v1.md` for the full
record and the "how to read this" note (every negative result here is conditional
and re-testable, not a proof of impossibility).

## Documents
- **`btc_puzzle_findings_v1.md`** — the findings record (draft v1, for review).

## Data
- **`puzzles_verified.csv`** — 82 solved puzzles, independently rebuilt and
  on-chain verified (private key → our computed X → matches the public key
  recorded on-chain; 82/82). The canonical dataset. Columns: `puzzle, bits,
  private_key, X, Y, address, funding_block, reveal_block,
  onchain_pubkey_matches_our_X, u_position, n, k`.
- **`solved_puzzles_xy.csv`** — the earlier third-party CSV used only to bootstrap
  the verified rebuild; superseded by `puzzles_verified.csv`.

## Scripts (`scripts/`)
Note: scripts use absolute paths to this folder
(`~/Desktop/Math Ex/btc_puzzle_investigation/`). The v1 scripts are in
`scripts/`; this session's experiments are in `scripts/session_2026-07/`
(see `btc_puzzle_findings_v2.md`).

| script | what it does | findings §|
|---|---|---|
| `build_verified.py` | builds `puzzles_verified.csv`; cross-checks each computed X against the on-chain revealed pubkey | §1.1 |
| `leak_hunt.py` | broad single-feature (X,Y)→n / position-quarter leak hunt, validated detector + control-keypair null | §3.1 |
| `pos_confirm.py` | high-power confirmatory null for the one warm (position) feature | §3.1 |
| `curve_transforms.py` | curve-native transforms (GLV endomorphism, 2P/3P/P±G, field ops) → n | §3.1 |
| `mv_hunt.py` | multivariate random-forest interaction-leak hunt across several target framings | §3.2 |
| `mv_calib.py` | detection-floor calibration for the multivariate detector (documents the power wall) | §3.2 |
| `seed_brute.py` | guessable-seed brainwallet (`SHA256(seed‖i)`) + index-brainwallet brute | §3.4 |
| `ts_sweep.py` | time-seeded SHA256 / Mersenne-Twister sweep over the 2014–15 funding window | §3.4 |
| `wallet_brute.py` | Electrum-v1 + BIP32 (common mnemonics × standard paths) seed brute | §3.4 |
| `lowbits.py` | preserved-low-bit LCG / autocorrelation / uniformity structure test | §3.4 |
| `nonce_sweep.py` | r-value reuse sweep across sweep signatures | §3.5 |
| `nonce_recover.py` | recovers actual signing nonces from solved-puzzle sweeps; checks size/bias/gaps | §3.5 |

## Reproducing
Requires Python 3 with `ecdsa` and `base58`. Network-dependent scripts
(`build_verified.py`, `nonce_recover.py`, `nonce_sweep.py`) query a public block
explorer.
