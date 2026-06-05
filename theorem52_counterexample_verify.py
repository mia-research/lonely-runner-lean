"""
Numerical verification: Theorem 5.2 (as stated in v11 manuscript) is FALSE
for arbitrary closed positive-measure A.

Setup:
  n = 5
  slow speeds = (1, 2)   --> L = lcm(1, 2) = 2
  p = 3                  --> 1 < p, gcd(3, 2) = 1 ✓
  A = [9/20, 11/20] = [0.45, 0.55]   (closed, μ(A) = 0.1 > 0)

jointGoodSet ∩ [0, 1) = goodSet(1,5) ∩ goodSet(2,5)
                     = [1/5, 4/5] ∩ ([1/10, 2/5] ∪ [3/5, 9/10])
                     = [1/5, 2/5] ∪ [3/5, 4/5]
                     (measure 2/5)

Claim: For every t in jointGoodSet, fract(3t) is NOT in [0.45, 0.55].

If true, Theorem 5.2 (as stated) is FALSE — it claims SOME t exists.
"""

import numpy as np

n = 5
threshold = 1.0 / n      # 0.2
speeds = [1, 2]
p = 3
A_lo, A_hi = 9 / 20, 11 / 20

def in_good(t: float, v: int, n: int) -> bool:
    """t ∈ goodSet v n: circDist(v·t) ≥ 1/n."""
    f = (v * t) % 1
    cd = min(f, 1 - f)
    return cd >= 1 / n - 1e-12

def in_joint(t: float) -> bool:
    return all(in_good(t, v, n) for v in speeds)

# Dense scan over [0, 1)
N = 10_000_000
ts = np.linspace(0, 1, N, endpoint=False)

hits = 0
joint_count = 0
example_violation = None

for t in ts:
    if in_joint(t):
        joint_count += 1
        f3t = (p * t) % 1
        if A_lo - 1e-12 <= f3t <= A_hi + 1e-12:
            hits += 1
            if example_violation is None:
                example_violation = (t, f3t)

print(f"Dense scan: {N:,} samples in [0, 1)")
print(f"  # samples in jointGoodSet: {joint_count:,} (fraction ≈ {joint_count/N:.4f}, theory: 0.4)")
print(f"  # samples with fract(3t) ∈ A: {hits:,}")
if hits == 0:
    print(f"  ✓ NO sample t ∈ jointGoodSet has fract(3t) ∈ A.")
    print(f"  ⇒ Theorem 5.2 (general A) FAILS for this counterexample.")
else:
    print(f"  Example violation: t = {example_violation[0]:.6f}, fract(3t) = {example_violation[1]:.6f}")
    print(f"  Counterexample DOES NOT hold — re-check the math.")

# Also compute fract(3t) over jointGoodSet to see the image set
print("\nImage of fract(3t) over jointGoodSet (sorted, deduplicated to 4 decimals):")
images = set()
for t in ts[::1000]:  # subsample for image
    if in_joint(t):
        f3t = round((p * t) % 1, 4)
        images.add(f3t)
sorted_imgs = sorted(images)
# Print just first/last few and detect the gap
print(f"  min: {min(sorted_imgs):.4f}, max: {max(sorted_imgs):.4f}")
# Detect gaps
gaps = []
for i in range(len(sorted_imgs) - 1):
    gap = sorted_imgs[i + 1] - sorted_imgs[i]
    if gap > 0.05:  # big gap
        gaps.append((sorted_imgs[i], sorted_imgs[i + 1], gap))
print(f"  Major gaps (>0.05) in image:")
for a, b, g in gaps:
    print(f"    ({a:.4f}, {b:.4f}) - width {g:.4f}")
print(f"  A = [{A_lo}, {A_hi}] should lie in one of these gaps if counterexample holds.")
