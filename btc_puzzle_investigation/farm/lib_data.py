"""
Canonical data + secp256k1 arithmetic for the (n,k,D) farm.

ONE loader, ONE curve implementation, shared by every work package so results
are mergeable. Pure-Python integer arithmetic (arbitrary precision, exact) — no
float smoothing of curve values (methodology: exact integer/rational only).

Public-in-the-real-puzzle columns  = {bits, X, Y, address, wif*}  (*wif/priv_hex
are secret; listed only so the guard can reject them).  ATTACK-VALID features may
depend on (X, Y, bits) ONLY.  d, n, k, D, D_terms are LABELS — using them to
"predict" n is circular (the XY-mod-n^2 / F1 trap). `public_frame()` enforces this.
"""
from __future__ import annotations
import os
import pandas as pd

# ------------------------------------------------------------------ curve ----
P  = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F
N_ORD = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141
A_CURVE, B_CURVE = 0, 7
GX = 0x79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798
GY = 0x483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8
G  = (GX, GY)
BETA   = 0x7AE96A2B657C07106E64479EAC3434E99CF0497512F58995C1396C28719501EE
# lambda: eigenvalue of the GLV endomorphism (phi(x,y)=(beta*x,y) == [lambda]P)
LAMBDA = 0x5363AD4CC05C30E0A5261C028812645A122E22EA20816678DF02967C1B23BD72

INF = None  # point at infinity


def inv_mod(a: int, m: int = P) -> int:
    return pow(a % m, m - 2, m)


def ec_add(Pt, Qt):
    if Pt is INF:
        return Qt
    if Qt is INF:
        return Pt
    x1, y1 = Pt
    x2, y2 = Qt
    if x1 == x2 and (y1 + y2) % P == 0:
        return INF
    if x1 == x2 and y1 == y2:
        m = (3 * x1 * x1) * inv_mod(2 * y1) % P
    else:
        m = (y2 - y1) * inv_mod(x2 - x1) % P
    x3 = (m * m - x1 - x2) % P
    y3 = (m * (x1 - x3) - y1) % P
    return (x3, y3)


def ec_mul(k: int, Pt=G):
    """Scalar multiplication [k]Pt, double-and-add. k reduced mod N_ORD."""
    k %= N_ORD
    if k == 0 or Pt is INF:
        return INF
    R = INF
    Addend = Pt
    while k:
        if k & 1:
            R = ec_add(R, Addend)
        Addend = ec_add(Addend, Addend)
        k >>= 1
    return R


def ec_neg(Pt):
    return INF if Pt is INF else (Pt[0], (-Pt[1]) % P)


def on_curve(Pt) -> bool:
    if Pt is INF:
        return True
    x, y = Pt
    return (y * y - x * x * x - B_CURVE) % P == 0


# ---------------------------------------------------- (n,k,D) decomposition ---
def best_rational_approx(num: int, den: int, max_den: int = 256):
    """Best rational approx k/n of num/den with 0<=k<n<=max_den, gcd(k,n)=1.

    Standard bounded-denominator best approximation via continued-fraction
    convergents + the final semiconvergent. Returns (k, n). Used to (a) VERIFY
    the dataset's n,k column and (b) build the matched-multiset null.
    """
    from fractions import Fraction
    if den == 0:
        return (0, 1)
    target = Fraction(num, den)
    # continued fraction of target
    a, b = num, den
    cf = []
    while b:
        cf.append(a // b)
        a, b = b, a - (a // b) * b
    # build convergents, track best with denom <= max_den
    h_m2, h_m1 = 0, 1
    k_m2, k_m1 = 1, 0
    best = None  # (abs_err, k, n)
    for i, ai in enumerate(cf):
        # full convergent
        h = ai * h_m1 + h_m2
        kk = ai * k_m1 + k_m2
        # semiconvergents ai' = 0..ai (only those keeping denom <= max_den)
        lo = (ai // 2)
        for aj in range(lo, ai + 1):
            hh = aj * h_m1 + h_m2
            nn = aj * k_m1 + k_m2
            if nn == 0 or nn > max_den:
                continue
            err = abs(target - Fraction(hh, nn))
            cand = (err, hh, nn)
            if best is None or cand < best:
                best = cand
        h_m2, h_m1 = h_m1, h
        k_m2, k_m1 = k_m1, kk
        if k_m1 > max_den:
            break
    if best is None:
        return (0, 1)
    _, kbest, nbest = best
    from math import gcd
    g = gcd(kbest, nbest) or 1
    return (kbest // g, nbest // g)


def decompose(d: int, bits: int, max_den: int = 256):
    """(n,k,D,D_terms) for a private key d of the given bit-length.

    D_terms counts the reciprocal-correction steps of the D-recursion.
    """
    A = 1 << (bits - 1)
    # position u = (d - A)/A  in [0,1); best approx with denom <= max_den
    k, n = best_rational_approx(d - A, A, max_den)
    base = A + (A * k) // n
    D = d - base
    # D-term recursion (counts terms; value is exact by construction)
    err = d - base
    terms = 0
    running = base
    while err != 0 and terms < 8:
        Di = A // abs(err)
        if Di == 0:
            break
        term = (1 if err > 0 else -1) * (A // Di)
        running += term
        err = d - running
        terms += 1
    return n, k, D, terms


# ------------------------------------------------------------------ loader ---
DEFAULT_CSV = os.path.join(os.path.dirname(__file__), "..",
                           "constructed_keys_1to160_100k.csv")

# columns that reveal the label in the real puzzle -> forbidden as features
SECRET_COLS = {"d", "priv_hex", "wif", "n", "k", "D", "D_terms"}
PUBLIC_COLS = {"bits", "X", "Y", "address"}


def load(csv_path: str = DEFAULT_CSV, bits_min: int = 1, bits_max: int = 160,
         nrows: int | None = None) -> pd.DataFrame:
    """Load the 100k dataset with big-ints parsed. X,Y,d,D become Python ints."""
    df = pd.read_csv(
        csv_path,
        dtype={"d": "string", "X": "string", "Y": "string", "D": "string",
               "priv_hex": "string", "wif": "string", "address": "string"},
        nrows=nrows,
    )
    df = df[(df["bits"] >= bits_min) & (df["bits"] <= bits_max)].reset_index(drop=True)
    df["X"] = df["X"].map(lambda s: int(s, 16))
    df["Y"] = df["Y"].map(lambda s: int(s, 16))
    df["d"] = df["d"].map(int)
    df["D"] = df["D"].map(int)
    # u in Python-int space then float ratio (2**159 overflows int64 -> div0)
    df["u"] = [ (int(d) - (1 << (int(b) - 1))) / float(1 << (int(b) - 1))
                for d, b in zip(df["d"], df["bits"]) ]
    return df


def public_frame(df: pd.DataFrame) -> pd.DataFrame:
    """Return ONLY the columns an attacker sees. Guards against label leakage."""
    keep = [c for c in df.columns if c in PUBLIC_COLS]
    return df[keep].copy()


def assert_attack_valid(feature_cols) -> None:
    """Raise if any feature is derived from a secret label."""
    bad = SECRET_COLS.intersection(set(feature_cols))
    if bad:
        raise ValueError(f"CIRCULAR: features {bad} use secret labels (F1 trap). "
                         f"Attack features may use {PUBLIC_COLS} only.")


def band_anchor(bits: int):
    """[2^(bits-1)] * G — the band anchor, shared by all keys in a band."""
    return ec_mul(1 << (bits - 1))
