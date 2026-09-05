#!/usr/bin/env python3
"""
puzzle_kangaroo.py  —  the REAL technique: Pollard's kangaroo for interval ECDLP.

Brute force (puzzle135_bruteforce_toy.py) needs 2^134 key checks -> hopeless. Kangaroo
uses the exposed public key to find d in a KNOWN interval [a,b] in ~2*sqrt(b-a) group
operations -- a square-root speedup. For #135 that is ~2^67.5 (finite, but still huge).
This is how exposed-pubkey puzzles (#120/#125/#130) actually fell.

  --demo         : hide a key in a real interval and SOLVE it with kangaroo (proves it works,
                   and shows steps ~ sqrt(W) vs brute force's W).
  (no args)      : set up kangaroo on the real #135 pubkey, measure jump rate on a live
                   sample, and report the honest 2^67.5 cost + time. It does NOT finish.

Two tame/wild herds do pseudorandom jumps (jump size depends only on the current point,
so once they collide they merge); distinguished points detect the collision with little
memory. Pure-integer secp256k1, stdlib only.
"""
import argparse, os, sys, time, secrets

P     = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F
N_ORD = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141
Gx = 0x79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798
Gy = 0x483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8
G  = (Gx, Gy)

def inv(x): return pow(x % P, P - 2, P)
def add(A, B):
    if A is None: return B
    if B is None: return A
    x1, y1 = A; x2, y2 = B
    if x1 == x2 and (y1 + y2) % P == 0: return None
    m = (3 * x1 * x1) * inv(2 * y1) % P if A == B else (y2 - y1) * inv(x2 - x1) % P
    x3 = (m * m - x1 - x2) % P
    return (x3, (m * (x1 - x3) - y1) % P)
def mul(k, Pt=G):
    R = None; A = Pt
    while k:
        if k & 1: R = add(R, A)
        A = add(A, A); k >>= 1
    return R
def decompress(comp_hex):
    pre = int(comp_hex[:2], 16); x = int(comp_hex[2:], 16)
    y = pow((x * x * x + 7) % P, (P + 1) // 4, P)
    if (y & 1) != (pre & 1): y = P - y
    return (x, y)

def make_jumps(W):
    B = W.bit_length()
    K = max(8, B // 2 + 2)
    jumps = [1 << i for i in range(K)]
    return K, jumps, [mul(s) for s in jumps]        # precomputed s*G

def kangaroo(Q, a, b, max_mult=60, report=None):
    """Find d in [a,b] with d*G == Q. Returns (d, steps) or (None, steps)."""
    W = b - a; B = W.bit_length()
    K, jumps, jumpG = make_jumps(W)
    dp_bits = max(1, B // 2 - 5); dp_mask = (1 << dp_bits) - 1
    max_steps = max_mult * (1 << (B // 2)) + 5000
    tame_e0 = (a + b) // 2
    T = mul(tame_e0); td = 0
    Wp = Q; wd = 0
    table = {}; steps = 0; t0 = time.time()
    while steps < max_steps:
        i = T[0] % K; T = add(T, jumpG[i]); td += jumps[i]
        if (T[0] & dp_mask) == 0:
            e = table.get(T)
            if e and e[0] == "W":
                d = tame_e0 + td - e[1]
                if a <= d <= b and mul(d) == Q: return d, steps
            table[T] = ("T", td)
        i = Wp[0] % K; Wp = add(Wp, jumpG[i]); wd += jumps[i]
        if (Wp[0] & dp_mask) == 0:
            e = table.get(Wp)
            if e and e[0] == "T":
                d = tame_e0 + e[1] - wd
                if a <= d <= b and mul(d) == Q: return d, steps
            table[Wp] = ("W", wd)
        steps += 1
        if report and steps % report == 0:
            r = steps / (time.time() - t0)                          # noqa: float (display rate only; never touches keys)
            sys.stdout.write(f"\r  {steps:,} jumps  {r:,.0f} jumps/s  table {len(table):,}   ")
            sys.stdout.flush()
    return None, steps

def demo():
    width_bits = 36
    a = 1 << 50; b = a + (1 << width_bits)
    secret = a + secrets.randbelow(b - a)
    Q = mul(secret)
    print(f"DEMO: hid a key in an interval of width 2^{width_bits} = {b-a:,}")
    print(f"  brute force would need up to {b-a:,} checks (~2^{width_bits}).")
    print(f"  kangaroo expects ~2*sqrt(W) ~ 2^{width_bits//2 + 1} ~ {2*(1<<(width_bits//2)):,} steps.\n")
    t = time.time()
    d, steps = kangaroo(Q, a, b, report=20000)
    dt = time.time() - t
    print(f"\n\n  {'SOLVED' if d == secret else 'FAILED'}: d = {hex(d) if d else None}")
    print(f"  took {steps:,} jumps in {dt:.1f}s  ({steps/dt:,.0f}/s)")   # noqa: float (display only)
    print(f"  speedup vs brute force: ~{(b-a)//max(steps,1):,}x fewer operations")

TARGET_135 = "02145d2611c823a396ef6712ce0f712f09b9b4f3135e3e0aa3230fb9b6d08d1e16"

def hunt135(sample=100000):
    a, b = 1 << 134, 1 << 135; W = b - a
    Q = decompress(TARGET_135)
    assert (Q[1] * Q[1] - Q[0] ** 3 - 7) % P == 0, "pubkey not on curve"
    ops = 2 * (1 << 67)                                   # ~2*sqrt(2^134) = 2^68.5-ish
    print("=== Pollard kangaroo on Bitcoin Puzzle #135 (the real method) ===")
    print(f"interval : 2^134 .. 2^135   (width 2^134 = {W:.3e})")
    print(f"pubkey   : {TARGET_135}  (on curve: yes)")
    print(f"brute    : ~2^134 = {float(1<<134):.2e} key checks")   # noqa: float (display only)
    print(f"kangaroo : ~2*sqrt(W) = ~2^67.5 = {ops:.2e} group ops  ({(1<<134)//ops:,.0f}x fewer)\n")
    print(f"Measuring real jump rate on this machine ({sample:,} jumps)...")
    K, jumps, jumpG = make_jumps(W)
    Xt = mul((a + b) // 2); Xw = Q; t0 = time.time()
    for s in range(1, sample + 1):
        Xt = add(Xt, jumpG[Xt[0] % K]); Xw = add(Xw, jumpG[Xw[0] % K])
        if s % 20000 == 0:
            r = s / (time.time() - t0)                              # noqa: float (display only)
            sys.stdout.write(f"\r  {s:,} jumps  {r:,.0f} jumps/s   "); sys.stdout.flush()
    rate = sample / (time.time() - t0)                             # noqa: float (display/ETA only; never touches keys)
    yrs = ops / rate / (365.25 * 86400)                            # noqa: float (display ETA only)
    print(f"\n\n  this machine: {rate:,.0f} jumps/s (pure Python).")
    print(f"  => ~2^67.5 ops here would take ~{yrs:.2e} years.")
    print(f"  On a 1000-GPU cluster at ~1e12 ops/s: ~{ops/1e12/(365.25*86400):.1f} years -- finite, but real.")   # noqa: float (display only)
    print("  (This is the honest state of the art. It does NOT run to completion here.)")

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--demo", action="store_true")
    ap.add_argument("--sample", type=int, default=100000)
    a = ap.parse_args()
    if a.demo: demo()
    else: hunt135(a.sample)

if __name__ == "__main__":
    main()
