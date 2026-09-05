# Bitcoin Puzzle Keys — secp256k1, the (n,k,d) Decomposition, and the Dataset

*Purpose: a self-contained description of the construction and the accompanying
dataset, so the mechanics can be studied without prior context. Descriptive only.*

## 1. The curve: secp256k1

Bitcoin keys live on the elliptic curve **y² = x³ + 7 (mod p)** (so a=0, b=7) over
the prime field with

- **field prime** `p = 2²⁵⁶ − 2³² − 977 = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F`
- **generator point** `G = (Gx, Gy)` with
  `Gx = 0x79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798`,
  `Gy = 0x483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8`
- **group order** `N_ord = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141`,
  **cofactor** 1.

A **private key** is an integer `d ∈ [1, N_ord−1]`. The **public key** is the point
`P = d·G = (X, Y)`, computed by scalar multiplication (repeated point
doubling/addition). X and Y are field elements (0 ≤ X,Y < p), and always satisfy
`Y² ≡ X³ + 7 (mod p)`. Because Y is determined by X up to sign, the point carries X
plus one parity bit of Y. The GLV endomorphism maps `(X,Y) → (β·X mod p, Y)` where
`β = 0x7AE96A2B657C07106E64479EAC3434E99CF0497512F58995C1396C28719501EE` (β³ ≡ 1).

## 2. From private key to WIF and address

- **priv_hex**: `d` as 32 bytes (64 hex chars, left-padded with zeros).
- **WIF (compressed)**: `Base58Check( 0x80 ‖ d(32 bytes) ‖ 0x01 )`.
- **compressed public key**: `(0x02 if Y even else 0x03) ‖ X(32 bytes)`.
- **address (P2PKH)**: `Base58Check( 0x00 ‖ RIPEMD160(SHA256(compressed_pubkey)) )`.
  (Base58Check appends the first 4 bytes of the double-SHA256 as checksum.)

## 3. Puzzle key construction (bit-length bands)

Puzzle number **N** uses a private key that is exactly N bits: `d ∈ [2^{N−1}, 2^N)`.
Equivalently, in 256-bit form it is `(256−N)` leading zero bits, then a 1 (bit
N−1), then N−1 lower bits. N is public (it is the puzzle number).

## 4. The (n, k, d) decomposition

Given `d` of bit-length N, define the **position** within the band:

> `u = (d − 2^{N−1}) / 2^{N−1}`  ∈ [0, 1)

Let **(n, k)** be the **best rational approximation of u with denominator n ≤ 256**
(a continued-fraction convergent; `k` = numerator, `gcd(k,n)=1`). Define

> `base = 2^{N−1} + ⌊ 2^{N−1} · k / n ⌋`  and  `D = d − base`.

`D` (the residual) is expressed by a **D-term recursion**: with `err₀ = d − base`,
each step takes `Dᵢ = ⌊ 2^{N−1} / |errᵢ₋₁| ⌋`, adds a correction
`termᵢ = sign(errᵢ₋₁) · ⌊ 2^{N−1} / Dᵢ ⌋`, and updates `errᵢ = d − (running sum)`,
until the error is 0. The full identity is

> **d = 2^{N−1} + ⌊ 2^{N−1} · k / n ⌋  ±  Σ 2^{N−1} / Dᵢ**

`(n, k, D)` reconstructs `d` exactly. `n, k` encode the coarse position (top of the
band); `D` (0–3 terms in practice) supplies the remainder. The map is invertible:
`d ↔ (X, Y)` via the curve, and `d ↔ (n, k, D)` via the decomposition.

## 5. The dataset — `constructed_keys_1to160_100k.csv`

100,023 rows. For each bit-length b = 1…160, `min(660, 2^{b−1})` distinct keys `d`
drawn from `[2^{b−1}, 2^b)` (all of them where fewer than 660 exist). Columns:

| column | meaning |
|---|---|
| `bits` | N, the bit-length (1–160) |
| `d` | private key, decimal integer |
| `priv_hex` | d as 64-char hex |
| `wif` | Wallet Import Format (compressed) |
| `X`, `Y` | public-key coordinates (hex), `P = d·G` |
| `address` | compressed P2PKH address |
| `n`, `k` | decomposition (best rational approx of u) |
| `D` | residual `d − base` |
| `D_terms` | number of terms in the D-recursion |

Every row is an independently computed real key: `d → (X,Y)` by scalar
multiplication, `d → address` by the hash chain above, and `(n,k,D) → d` by the
decomposition — all self-consistent.

## 6. Minimal reproduction (Python)

```python
p  = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F
Gx = 0x79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798
Gy = 0x483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8
# X,Y = d * G on y^2 = x^3 + 7 mod p   (standard EC scalar multiplication)
# u = (d - 2**(N-1)) / 2**(N-1);  n,k = best rational approx of u, n<=256
# base = 2**(N-1) + (2**(N-1)*k)//n;  D = d - base
```
