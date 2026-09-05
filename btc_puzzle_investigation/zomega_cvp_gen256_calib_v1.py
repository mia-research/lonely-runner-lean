#!/usr/bin/env python3
"""
Calibrate the ZLomega GLV-short test (zomega_lattice_probe T1) in the NON-DEGENERATE
regime the real puzzle keys never reach: 81/82 real keys are < 2^128, so their
balanced GLV rep is ~(d,0) (b~0) -- the test is starved. Generated 256-bit keys
(the 'we can generate solved keys' unlock) give genuinely 2-D (a,b). Here we:
  (1) confirm uniform-d 256-bit keys are NOT GLV-short (calibrated null, P~0.5),
  (2) show the instrument FIRES on a planted GLV-short creator (a,b both < 2^120),
      i.e. it WOULD detect a creator who picked keys as short Z[omega] vectors,
  (3) quantify: a GLV-short creator = a real search reduction (maxbits well below
      the ~127 balanced expectation).
Exact integers. No float in the signal path.
"""
import random
N = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141
LAM = 0x5363AD4CC05C30E0A5261C028812645A122E22EA20816678DF02967C1B23BD72

def dot(u, v): return u[0]*v[0] + u[1]*v[1]
def round_div(num, den):
    # nearest integer to num/den for ANY sign, exact (matches zomega_lattice_probe)
    if den < 0: num, den = -num, -den
    q, r = divmod(num, den)   # den>0 => 0<=r<den
    if 2*r >= den: q += 1
    return q
def gauss_reduce(b1, b2):
    while True:
        if dot(b2, b2) < dot(b1, b1): b1, b2 = b2, b1
        mu = round_div(dot(b1, b2), dot(b1, b1))
        b2 = (b2[0]-mu*b1[0], b2[1]-mu*b1[1])
        if dot(b2, b2) >= dot(b1, b1): return b1, b2
B1, B2 = gauss_reduce((N, 0), (-LAM, 1))
DET = B1[0]*B2[1] - B1[1]*B2[0]
def glv(d):
    c1 = round_div(d*B2[1], DET); c2 = round_div(-d*B1[1], DET)
    a = d - (c1*B1[0]+c2*B2[0]); b = -(c1*B1[1]+c2*B2[1])
    assert (a + b*LAM - d) % N == 0
    return a, b
def maxbits(d):
    a, b = glv(d); return max(abs(a), abs(b)).bit_length()

rng = random.Random(2026)
NK = 3000

print(f"GLV reduced basis |b1|~2^{max(abs(B1[0]),abs(B1[1])).bit_length()-1}; "
      f"balanced maxbits ~127 expected for uniform 256-bit d\n")

# (1) uniform 256-bit d -> distribution of maxbits
uni = [maxbits(rng.randrange(1 << 255, 1 << 256)) for _ in range(NK)]
mean_uni = sum(uni) / len(uni)              # noqa: float (report only)
frac_short = sum(1 for x in uni if x < 120) / len(uni)   # noqa: float (report only)
print(f"(1) uniform 256-bit d: mean maxbits={mean_uni:.2f}, min={min(uni)}, "
      f"frac(maxbits<120)={frac_short:.4f}  (expect ~127, ~0 short)")

# (2) planted GLV-short creator: pick a,b < 2^120, form d=a+b*lambda mod n
short = []
for _ in range(NK):
    a = rng.randrange(1 << 120); b = rng.randrange(1 << 120)
    short.append((a + b*LAM) % N)
sh = [maxbits(d) for d in short]
mean_sh = sum(sh) / len(sh)  # noqa: float (report)
print(f"(2) planted GLV-short creator (a,b<2^120): mean maxbits={mean_sh:.2f}, "
      f"max={max(sh)}  -> instrument SEPARATES: short<<uniform")

# (3) rank test: sum(maxbits) of a sample vs matched uniform null
def rank_p(sample):
    S = sum(maxbits(d) for d in sample)
    worse = 0
    for _ in range(500):
        s = sum(maxbits(rng.randrange(1 << 255, 1 << 256)) for _ in sample)
        if s <= S: worse += 1
    return S, worse / 500  # noqa: float (rank p)

samp_uni = [rng.randrange(1 << 255, 1 << 256) for _ in range(60)]
samp_sh = [(rng.randrange(1 << 120) + rng.randrange(1 << 120)*LAM) % N for _ in range(60)]
Su, pu = rank_p(samp_uni); Ss, ps = rank_p(samp_sh)
print(f"\n(3) GLV-short rank test (n=60, the ~real-key sample size):")
print(f"    uniform-d sample : sum={Su}, P(sum<=obs)={pu:.3f}  (calibrated null ~0.5)")
print(f"    GLV-short creator: sum={Ss}, P(sum<=obs)={ps:.3f}  (fires ~0.000)")
print("\nConclusion: the GLV-short SELECTION test is well-calibrated and powerful in")
print("the 2-D regime, but the real puzzle keys (81/82 < 2^128) are degenerate for")
print("it -- only #130 (and the unsolved #135+) are genuinely 2-D. So a GLV-short")
print("creator-selection signal is UNTESTABLE on the available solved keys, not absent.")
