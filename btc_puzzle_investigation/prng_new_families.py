#!/usr/bin/env python3
"""
prng_new_families.py  —  seed sweep for RNG families NOT yet tested.

Already ruled out (mt_full32_results / extra_results): Python MT (full 2^32), PHP
mt_rand, Randstorm RC4 — at time-second + small-int seeds. Untouched families with an
enumerable integer/time seed: glibc rand(), Java java.util.Random (48-bit LCG), .NET
System.Random (subtractive). This adds them, with the SAME match discriminator
(longest consecutive-from-#1 run vs the known keys; coincidence floor ~7, hit=70) and
a mandatory positive-control SELFTEST: seed a family, emit the key sequence, confirm
run==full. A null sweep rules out "<family> from <seed space> with <model>", not the
family in general (info-theoretic ceiling: fingerprintable only if the seed was
enumerable).

Exact integer arithmetic (keys are ints). No float in the signal path.

Usage: python3 prng_new_families.py [--smallint 20] [--selftest-only]
"""
import argparse, csv, os, ctypes, ctypes.util

MASTER = os.path.join(os.path.dirname(__file__), "btc_puzzle_master.csv")

def load_known():
    K = {}
    with open(MASTER) as f:
        for r in csv.DictReader(f):
            if r["status"] == "SOLVED" and r["priv_dec"]:
                K[int(r["puzzle"])] = int(r["priv_dec"])
    CHECK, n = [], 1
    while n in K: CHECK.append(n); n += 1
    return CHECK, [K[n] for n in CHECK]

CHECK, KVAL = load_known()

# ----------------------------- Java java.util.Random -----------------------------
class JavaRandom:
    M = (1 << 48) - 1
    def __init__(self, seed): self.s = (seed ^ 0x5DEECE66D) & self.M
    def next(self, bits):
        self.s = (self.s * 0x5DEECE66D + 0xB) & self.M
        return self.s >> (48 - bits)
    def next_bytes(self, k):                     # faithful nextBytes
        out = bytearray()
        while len(out) < k:
            rnd = self.next(32)
            for _ in range(4):
                if len(out) >= k: break
                out.append(rnd & 0xFF); rnd >>= 8
        return bytes(out)

def _java_bits(rng, m):                          # BigInteger(numBits, rnd)-style m random bits
    if m == 0: return 0
    nbytes = (m + 7) // 8
    b = rng.next_bytes(nbytes)
    excess = 8 * nbytes - m
    v = int.from_bytes(b, "big") >> excess
    return v

def run_java(seed, model, check=None, kval=None):
    check = CHECK if check is None else check; kval = KVAL if kval is None else kval
    rng = JavaRandom(seed); run = 0
    for i, N in enumerate(check):
        if model == "topbit":
            k = (1 << (N - 1)) | _java_bits(rng, N - 1)
        elif model == "reject":
            while True:
                k = _java_bits(rng, N)
                if k >= (1 << (N - 1)): break
        else: raise ValueError(model)
        if k == kval[i]: run += 1
        else: break
    return run

# ------------------------------- .NET System.Random -------------------------------
class DotNetRandom:
    MBIG = 2147483647
    def __init__(self, seed):
        self.tbl = [0] * 56
        mj = 161803398 - (2147483647 if seed == -2147483648 else abs(seed))
        self.tbl[55] = mj; mk = 1
        for i in range(1, 55):
            ii = (21 * i) % 55
            self.tbl[ii] = mk; mk = mj - mk
            if mk < 0: mk += self.MBIG
            mj = self.tbl[ii]
        for _ in range(4):
            for i in range(1, 56):
                self.tbl[i] -= self.tbl[1 + (i + 30) % 55]
                if self.tbl[i] < 0: self.tbl[i] += self.MBIG
        self.i1, self.i2 = 0, 21
    def sample(self):
        self.i1 += 1; self.i2 += 1
        if self.i1 >= 56: self.i1 = 1
        if self.i2 >= 56: self.i2 = 1
        r = self.tbl[self.i1] - self.tbl[self.i2]
        if r < 0: r += self.MBIG
        self.tbl[self.i1] = r
        return r                                  # in [0, MBIG)
    def next_bits(self, m):                       # assemble m bits from 31-bit samples
        v, got = 0, 0
        while got < m:
            v = (v << 31) | self.sample(); got += 31
        return v >> (got - m)

def run_dotnet(seed, model, check=None, kval=None):
    check = CHECK if check is None else check; kval = KVAL if kval is None else kval
    rng = DotNetRandom(seed); run = 0
    for i, N in enumerate(check):
        if model == "topbit":
            k = (1 << (N - 1)) | rng.next_bits(N - 1)
        elif model == "reject":
            while True:
                k = rng.next_bits(N)
                if k >= (1 << (N - 1)): break
        else: raise ValueError(model)
        if k == kval[i]: run += 1
        else: break
    return run

# --------------------------------- glibc rand() ----------------------------------
_libc = ctypes.CDLL(ctypes.util.find_library("c"))
def run_glibc(seed, model, check=None, kval=None):
    check = CHECK if check is None else check; kval = KVAL if kval is None else kval
    _libc.srand(ctypes.c_uint(seed & 0xFFFFFFFF))
    run = 0
    for i, N in enumerate(check):
        if model == "topbit":
            v, got = 0, 0
            while got < N - 1:
                v = (v << 31) | (_libc.rand() & 0x7FFFFFFF); got += 31
            k = (1 << (N - 1)) | (v >> (got - (N - 1)) if N > 1 else 0)
        elif model == "reject":
            while True:
                v, got = 0, 0
                while got < N:
                    v = (v << 31) | (_libc.rand() & 0x7FFFFFFF); got += 31
                k = v >> (got - N)
                if k >= (1 << (N - 1)): break
        else: raise ValueError(model)
        if k == kval[i]: run += 1
        else: break
    return run

FAMILIES = {"java": (run_java, JavaRandom), "dotnet": (run_dotnet, DotNetRandom), "glibc": (run_glibc, None)}
MODELS = ["topbit", "reject"]

def _emit(fam, seed, model, genN):
    """Generate the first genN keys (bit-lengths = CHECK[:genN]) from a family+seed."""
    checkN = CHECK[:genN]; planted = []
    if fam in ("java", "dotnet"):
        rng = FAMILIES[fam][1](seed)
        draw = _java_bits if fam == "java" else (lambda r, m: r.next_bits(m))
        for N in checkN:
            if model == "topbit":
                planted.append((1 << (N - 1)) | draw(rng, N - 1))
            else:
                while True:
                    v = draw(rng, N)
                    if v >= (1 << (N - 1)): planted.append(v); break
    else:  # glibc
        _libc.srand(ctypes.c_uint(seed & 0xFFFFFFFF))
        for N in checkN:
            if model == "topbit":
                v, got = 0, 0
                while got < N - 1:
                    v = (v << 31) | (_libc.rand() & 0x7FFFFFFF); got += 31
                planted.append((1 << (N - 1)) | (v >> (got - (N - 1)) if N > 1 else 0))
            else:
                while True:
                    v, got = 0, 0
                    while got < N:
                        v = (v << 31) | (_libc.rand() & 0x7FFFFFFF); got += 31
                    k = v >> (got - N)
                    if k >= (1 << (N - 1)): planted.append(k); break
    return checkN, planted

def selftest():
    """Positive control: emit a key sequence from each family/model, confirm run==full."""
    print("SELFTEST (positive control — detector must reach full run on its own output):")
    ok = True
    for fam in FAMILIES:
        for model in MODELS:
            seed = 123456789
            genN = min(24, len(CHECK))
            checkN, planted = _emit(fam, seed, model, genN)
            r = FAMILIES[fam][0](seed, model, check=checkN, kval=planted)
            good = (r == genN); ok &= good
            print(f"  {fam:7s} {model:7s}: recovered run {r}/{genN}  {'PASS' if good else 'FAIL'}")
    return ok

def sweep(lo, hi, label):
    print(f"\nSWEEP [{label}]  seeds [{lo},{hi})  ({hi-lo} seeds) x {len(FAMILIES)} fam x {len(MODELS)} models")
    for fam, (fn, _) in FAMILIES.items():
        for model in MODELS:
            best, bs = 0, 0
            for s in range(lo, hi):
                r = fn(s, model)
                if r > best: best, bs = r, s
                if r >= len(CHECK): break
            flag = "HIT!!!" if best >= 15 else "coincidence"
            print(f"  {fam:7s} {model:7s}: best run {best:2d}/{len(CHECK)} (seed {bs})  {flag}")

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--smallint", type=int, default=20, help="sweep small-int seeds [0,2^k)")
    ap.add_argument("--time-window", type=int, default=0, help="seconds of time-seed window (from 2015-01-01) to sweep")
    ap.add_argument("--selftest-only", action="store_true")
    a = ap.parse_args()
    print(f"# PRNG NEW-FAMILIES sweep  known-key run length CHECK=1..{len(CHECK)}  (hit=full, floor~7)\n")
    if not selftest():
        print("\nSELFTEST FAILED — detector not trustworthy, aborting sweep."); return
    if a.selftest_only: return
    sweep(0, 1 << a.smallint, f"small-int 0..2^{a.smallint}")
    if a.time_window:
        base = 1420070400  # 2015-01-01 UTC
        sweep(base, base + a.time_window, f"time 2015-01-01 +{a.time_window}s")

if __name__ == "__main__":
    main()
