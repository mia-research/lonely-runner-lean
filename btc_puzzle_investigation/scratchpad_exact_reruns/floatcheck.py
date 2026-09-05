import math
from math import isqrt
print("Why a float 'distance-to-nearest-integer' cannot certify a perfect square")
print("(demonstrated at ~40 digits; the deg-23 disc is ~758 digits, far worse):\n")
base = 2889400000000000000003    # 22-digit odd
sq   = base*base                 # ~44-digit true perfect square
non  = sq + 2*base               # = (base+1)^2 - 1 : strictly between two squares, NOT a square
for name,x in [("true square", sq), ("non-square (sq+2base)", non)]:
    fs   = math.sqrt(x)                 # float64 sqrt: ~15-16 sig digits only
    frac = abs(fs - round(fs))
    print("  %-22s  float sqrt=%.4e  'dist to int'=%.6f  | EXACT isqrt^2==x: %s"
          %(name, fs, frac, isqrt(x)**2==x))
print("\n  Float reports 'distance 0.000000' for BOTH -> it cannot tell them apart.")
print("  math.sqrt on the actual ~758-digit deg-23 disc raises OverflowError (>1.8e308),")
print("  and the claimed root 2.8894e379 itself overflows float64 -- so the reported")
print("  'exact 0.0 distance' was never a float64 computation. Only isqrt(disc)**2==disc")
print("  is a valid perfect-square certificate at this scale.")
