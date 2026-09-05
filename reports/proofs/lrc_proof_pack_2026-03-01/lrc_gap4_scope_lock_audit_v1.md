# Gap 4 Scope-Lock Audit (v1)
**Date:** 2026-03-04  
**Purpose:** Canonical record of the strict re-audit after session handoff; separates unconditional proofs from scoped/conditional claims.

---

## 1. Locked Scope (H1-H7)

- `n >= 6`, Case-2, `gcd(E)=1`, `L>2n`.
- One-parameter family with **one divisible speed only**: `E = E_fix union {M} union E_div`, `E_div={n}`.
- Near-complete one-div template: `|E_fix|=n-3`.
- `gcd(M,nL0)=1`, `L=L0*M`, `L0=lcm(E_fix union {n})`.
- Under this scope, `B_div = [L/n, (n-1)L/n] cap Z` is a single interval.

Outside this scope (multi-div or `f>1` divisible factor), interval geometry and tau=0 witness claims are not automatic.

---

## 2. Unconditional Core (within H1-H7)

- Two-level decomposition (`tau`-bands; `D_fix` constant on each band): **PROVED**.
- Unit free-runner facts (`|U_M|<=2`, `t_M=floor(b/L0)`): **PROVED**.
- Per-band bounds by miss size class:
  - `sz>=3 => C_bad=0`
  - `sz=2 => C_bad<=|I|/n + 2L0`
  - `sz=1 => C_bad<=2|I|/n + 4L0`
  - `sz=0 => C_bad=|I|`
  all **PROVED**.
- Global weighted lower bound from band summation: **PROVED**.
- Affine-in-`M` decomposition of `Sigma_s(M)`: **PROVED**.

---

## 3. Scoped Lambda Positivity Split

- **Case A** (`G_tot <= d + 2|E_nu|`, with `d=1` here):
  - `tau=0` band has positive width,
  - `sz(tau=0) >= 1`,
  - therefore `Lambda_eff>0`.
  - Status: **PROVED under H1-H7**.

- **Case B**, `n<=9`:
  - reducible to known small-runner closure (`k=n-2<=7`).
  - Status: **PROVED-UNDER-H** (depends on cited small-k result).

- **Case B**, `n>=10`:
  - key lemma still open:
    `exists tau in B_div path with U_fix(tau) != Z_n`.
  - Status: **OPEN**.

---

## 4. Consequence Status

- Large-`M` closure and finite-strip TCP reduction are **CONDITIONAL** on `Lambda_eff>0`.
- Therefore Gap 4 is **not globally closed**; remaining load-bearing blocker is Case-B (`n>=10`) positivity/existence.

---

## 5. Canonical Use

Use this audit as the status authority for:
- `S3-GENERAL` wording,
- `G4A/G4B/G4C` scope labels,
- any claim that says "only small-M remains" (must be marked conditional unless Case-B blocker is solved).

