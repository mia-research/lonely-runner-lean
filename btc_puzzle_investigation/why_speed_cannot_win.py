#!/usr/bin/env python3
"""
why_speed_cannot_win.py  —  the point of the toy, in numbers.

Puzzle #135 lives in a range of 2^134 keys. Brute force checks them one at a time,
so faster compute only multiplies the CHECK RATE by a constant. The search space is
exponential; no constant speedup dents an exponent. This prints the wall.
"""
N        = 1 << 134                       # keys in [2^134, 2^135)
AVG      = N // 2                         # expected keys to a hit (half the range)
SEC_YR   = 365.25 * 86400
UNIV_YR  = 13.8e9                         # age of the universe, years

def years(rate):                          # time to search the whole range at `rate` keys/s
    return N / rate / SEC_YR

RATES = [
    ("this laptop (pure-Python d*G)",      1e3),
    ("1 high-end GPU (optimized secp256k1)",1e9),
    ("a 1,000-GPU cluster",                 1e12),
    ("1,000,000 GPUs",                      1e15),
    ("~all computers on Earth (exascale)",  1e18),
    ("= the ENTIRE Bitcoin mining network", 1e21),
]

print(f"Search space (2^134): {N:.3e} keys   (expected to a hit: {AVG:.3e})\n")
print(f"{'compute rate':38s}{'keys/s':>10s}{'time to search':>22s}{'vs universe age':>20s}")
for label, r in RATES:
    y = years(r)
    print(f"{label:38s}{r:>10.0e}{y:>18.2e} yr{y/UNIV_YR:>17.1e}x")

need = N / (UNIV_YR * SEC_YR)             # rate to finish within one universe lifetime
print(f"\nTo finish in ONE age-of-the-universe you'd need {need:.2e} keys/s")
print(f"  = {need/1e21:.1e}x the entire Bitcoin network — for a SINGLE key.")

print("\nWhy speeding up compute is the wrong lever:")
print(f"  1 GPU:            {years(1e9):.1e} yr")
print(f"  x1,000,000 faster:{years(1e15):.1e} yr   (a MILLION-fold speedup, still 1e17 yr)")
print("  A constant speedup just shifts the exponent's coefficient. 2^134 wins.")

print("\nThe ONLY thing that helps is a smaller EXPONENT (a better algorithm, not faster HW):")
print(f"  brute force : 2^134 = {float(1<<134):.2e} ops   -> hopeless")
print(f"  Pollard kangaroo (exposed pubkey, sqrt speedup): 2^67 = {float(1<<67):.2e} ops")
print(f"    at 1 GPU (1e9/s): {(1<<67)/1e9/SEC_YR:.1f} yr;  at 1000 GPUs: {(1<<67)/1e12/SEC_YR:.2f} yr")
print("  That is how exposed-pubkey puzzles actually fall — the exponent halves, not the clock.")
