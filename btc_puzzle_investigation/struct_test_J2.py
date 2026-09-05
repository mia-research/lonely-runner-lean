#!/usr/bin/env python3
"""
struct_test_J2.py  —  Plan v5 Test J confirmation (PAIRED, mechanism test).

J at M=200 hinted R1 (jump index from HIGH X bits) beats R0 (i=X%K, LOW bits) by
~2.2 sigma. Candidate mechanism: R0's low-bit selector OVERLAPS the DP mask
(dp_bits=7 > log2(K)=4), coupling jump choice to DP-ness and hurting mixing;
high-bit selectors are disjoint from the mask.

Confirm with a PAIRED design (same d,Q per instance across all rules -> per-instance
difficulty cancels -> high power) and a mechanism contrast:
  A_lowbits   i = X % K                 (bits 0..3  -> OVERLAP dp_mask bits 0..6)
  B_highbits  i = (X >> dp_bits) % K     (bits 7..10 -> DISJOINT)
  C_higher    i = (X >> (dp_bits+8)) % K (bits 15..18-> DISJOINT)
Prediction if mechanism is real: A slower than B ~= C. Paired mean diffs + SE.

Usage: python3 struct_test_J2.py [--M 400]
"""
import argparse, secrets, statistics
from puzzle_kangaroo import add, mul, G

def make_jumps(W):
    B = W.bit_length(); K = max(8, B // 2 + 2)
    return K, [1 << i for i in range(K)], [mul(1 << i) for i in range(K)]

def sel(rule, x, K, dpb):
    if rule == "A_lowbits":  return x % K
    if rule == "B_highbits": return (x >> dpb) % K
    if rule == "C_higher":   return (x >> (dpb + 8)) % K
    return x % K

def run_fixed(a, b, rule, d_true, Q, max_mult=80):
    W = b - a; B = W.bit_length()
    K, jumps, jumpG = make_jumps(W)
    dpb = max(1, B // 2 - 5); dp_mask = (1 << dpb) - 1
    max_steps = max_mult * (1 << (B // 2)) + 5000
    tame_e0 = (a + b) // 2
    T = mul(tame_e0); td = 0; Wp = Q; wd = 0
    table = {}; steps = 0
    while steps < max_steps:
        i = sel(rule, T[0], K, dpb); T = add(T, jumpG[i]); td += jumps[i]
        if (T[0] & dp_mask) == 0:
            e = table.get(T)
            if e and e[0] == "W": return steps
            table[T] = ("T", td)
        i = sel(rule, Wp[0], K, dpb); Wp = add(Wp, jumpG[i]); wd += jumps[i]
        if (Wp[0] & dp_mask) == 0:
            e = table.get(Wp)
            if e and e[0] == "T": return steps
            table[Wp] = ("W", wd)
        steps += 1
    return None

def main():
    ap = argparse.ArgumentParser(); ap.add_argument("--M", type=int, default=300)
    ap.add_argument("--wbits", type=int, default=22)
    a = ap.parse_args()
    WBITS = a.wbits; lo = 1 << 50; hi = lo + (1 << WBITS); M = a.M
    rules = ["A_lowbits", "B_highbits", "C_higher"]
    print(f"# TEST J2  PAIRED jump-selection   W=2^{WBITS}, {M} paired instances")
    print(f"#   dp_bits={max(1,WBITS//2-5)} (DP mask), K=max(8,B//2+2) -> selector ~4 bits.")
    print(f"#   A overlaps the DP mask; B,C are disjoint. sqrt(W)={1<<(WBITS//2)}.\n")
    steps = {r: [] for r in rules}
    for _ in range(M):
        d = lo + secrets.randbelow(hi - lo); Q = mul(d)
        for r in rules:
            steps[r].append(run_fixed(lo, hi, r, d, Q))
    for r in rules:
        v = [s for s in steps[r] if s is not None]; unsolved = M - len(v)
        mean = statistics.mean(v); se = statistics.pstdev(v) / len(v) ** 0.5              # noqa: float
        print(f"  {r:<11} solved {len(v)}/{M}  mean={mean:8.1f} +/- SE {se:5.1f}  "
              f"median={statistics.median(v):8.1f}  unsolved(hit cap)={unsolved}")
    # paired differences (same instances, both solved) -> per-instance variance cancels
    print("\n  paired differences (positive => second rule is FASTER):")
    for x, y in (("A_lowbits", "B_highbits"), ("A_lowbits", "C_higher"), ("B_highbits", "C_higher")):
        diffs = [steps[x][i] - steps[y][i] for i in range(M)
                 if steps[x][i] is not None and steps[y][i] is not None]
        md = statistics.mean(diffs); sd = statistics.pstdev(diffs) / len(diffs) ** 0.5    # noqa: float
        sig = md / sd if sd else 0.0                                                       # noqa: float
        print(f"    {x} - {y}:  {md:+8.1f} +/- {sd:5.1f}  (n={len(diffs)})  = {sig:+.2f} sigma")
    print("\n  read: A-B and A-C strongly positive (>3 sigma) AND B-C ~0  => confirmed:")
    print("        low-bit selector overlapping the DP mask costs a real constant factor;")
    print("        fix = pick jump index from bits disjoint from dp_mask. Else => noise.")

if __name__ == "__main__":
    main()
