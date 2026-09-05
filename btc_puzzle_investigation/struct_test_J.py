#!/usr/bin/env python3
"""
struct_test_J.py  —  Plan v5 Test J: jump-selection mixing (constant-factor only).

Kangaroo picks its jump by  i = X % K.  Is that mixing optimally over the interval,
or does conditioning the jump index on a different cheap local statistic cut
steps-to-collision (a real constant-factor gain)? Cannot beat sqrt(W); this only
asks whether the standard rule leaves a constant on the table.

Compares steps-to-collision (fewer = better mixing) across jump-index rules at fixed
W, many solvable instances. Same jump SIZES, only the selector differs. Integer ops.

Usage: python3 struct_test_J.py
"""
import secrets, statistics
from puzzle_kangaroo import add, mul, G

GOLDEN = 0x9E3779B97F4A7C15F39CC0605CEDC835

def make_jumps(W):
    B = W.bit_length(); K = max(8, B // 2 + 2)
    jumps = [1 << i for i in range(K)]
    return K, jumps, [mul(s) for s in jumps]

def selector(rule, x, K, dp_bits):
    if rule == "R0 X%K":        return x % K
    if rule == "R1 highbits":   return (x >> dp_bits) % K
    if rule == "R2 popcount":   return bin(x & 0xFFFFFFFF).count("1") % K
    if rule == "R3 mulhash":    return ((x * GOLDEN) >> 200) % K
    return x % K

def run_once(a, b, rule, max_mult=80):
    W = b - a; B = W.bit_length()
    K, jumps, jumpG = make_jumps(W)
    dp_bits = max(1, B // 2 - 5); dp_mask = (1 << dp_bits) - 1
    max_steps = max_mult * (1 << (B // 2)) + 5000
    d_true = a + secrets.randbelow(W); Q = mul(d_true)
    tame_e0 = (a + b) // 2
    T = mul(tame_e0); td = 0; Wp = Q; wd = 0
    table = {}; steps = 0
    while steps < max_steps:
        i = selector(rule, T[0], K, dp_bits); T = add(T, jumpG[i]); td += jumps[i]
        if (T[0] & dp_mask) == 0:
            e = table.get(T)
            if e and e[0] == "W": return steps
            table[T] = ("T", td)
        i = selector(rule, Wp[0], K, dp_bits); Wp = add(Wp, jumpG[i]); wd += jumps[i]
        if (Wp[0] & dp_mask) == 0:
            e = table.get(Wp)
            if e and e[0] == "T": return steps
            table[Wp] = ("W", wd)
        steps += 1
    return None

def main():
    WBITS = 24
    a = 1 << 50; b = a + (1 << WBITS)
    M = 200
    print(f"# TEST J  jump-selection mixing   W=2^{WBITS}, {M} instances/rule")
    print(f"# metric: steps-to-collision (fewer=better). sqrt(W)=2^{WBITS//2}={1<<(WBITS//2)}.\n")
    for rule in ("R0 X%K", "R1 highbits", "R2 popcount", "R3 mulhash"):
        st = []; solved = 0
        for _ in range(M):
            s = run_once(a, b, rule)
            if s is not None: st.append(s); solved += 1
        if len(st) >= 3:
            mean = statistics.mean(st); sd = statistics.pstdev(st)
            se = sd / (len(st) ** 0.5)                            # noqa: float (reported diagnostic)
            print(f"  {rule:<13} solved {solved}/{M}  steps: mean={mean:8.1f} +/- SE {se:5.1f}  "
                  f"median={statistics.median(st):8.1f}")
        else:
            print(f"  {rule:<13} solved {solved}/{M}  (too few)")
    print("\n  read: means within noise of each other => X%K already mixes optimally; no")
    print("        constant-factor left on the table. A rule with clearly lower mean = a win.")

if __name__ == "__main__":
    main()
