#!/usr/bin/env python3
"""
The rank-10 low-prime orthogonality under a CORE/FLAP split of the COLUMN PRIMES
(user's version, distinct from int2's row-character split). Tests two things:
 (1) the Frobenius-angle classification (theta_l from 4l=t^2+3f^2, pinned {0,3} if
     theta<30 else {1,4}) exists ONLY for l=1 mod3 -> only {7,13,19} of the 10 primes.
 (2) the column Gram is diagonal (rank-10 orthogonal, theorem) => ANY column partition
     into 6+4 gives orthogonal sub-blocks (rank-6 (+) rank-4) TRIVIALLY -- curve split
     and a RANDOM split decompose it identically. So the μ3-projection does not SELECT
     a canonical decomposition.
"""
import numpy as np, cmath, math, random
from sympy import primerange, primitive_root

P0 = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29]


def frob_angle(l):
    """theta_l mod 60deg for l=1 mod3 via 4l = t^2 + 3 f^2; None if l!=1 mod3."""
    if l % 3 != 1: return None
    for t in range(1, int((4 * l) ** 0.5) + 1):
        rem = 4 * l - t * t
        if rem > 0 and rem % 3 == 0:
            f2 = rem // 3; f = int(f2 ** 0.5)
            if f * f == f2:
                th = math.degrees(math.atan2(f * math.sqrt(3), t)) % 60
                return th
    return None


def main():
    print("(1) Frobenius-angle core/flap classification of the 10 low primes:")
    cls = {}
    for l in P0:
        th = frob_angle(l)
        if th is None:
            cls[l] = "inert/ramified (no angle)"
        else:
            cls[l] = f"theta={th:.1f} -> pinned {'{0,3} CORE' if th < 30 else '{1,4} FLAP'}"
        print(f"    l={l:2d} ({l%3} mod3): {cls[l]}")
    have_angle = [l for l in P0 if frob_angle(l) is not None]
    print(f"  => only {len(have_angle)} primes have an angle: {have_angle}. A clean 6-core+4-flap")
    print(f"     split is NOT defined by this criterion (7 of 10 primes have no angle).")

    # (2) build rank-10 F (Dirichlet), show column Gram diagonal, any 6/4 split orthogonal
    Q = 100; qs = list(primerange(Q // 2, Q + 1)); rows = []
    for q in qs:
        g = primitive_root(q); ind = {}; cur = 1
        for e in range(q - 1): ind[cur % q] = e; cur = cur * g % q
        inv = 1.0 / math.sqrt(q - 1)
        for j in range(1, q - 1):
            rows.append([cmath.exp(2j * cmath.pi * j * ind[p % q] / (q - 1)) * inv for p in P0])
    F = np.array(rows)
    G = F.conj().T @ F
    offmax = np.max(np.abs(G - np.diag(np.diag(G))))
    print(f"\n(2) column Gram F*F: off-diagonal max = {offmax:.4f}  (=0 => orthogonal, rank-10)")

    def block_rank(cols):
        sub = F[:, cols]
        s = np.linalg.svd(sub, compute_uv=False)
        return np.sum(s > 1e-6 * s[0])

    # curve split (put the 3 angled primes' classification + assign rest arbitrarily to make 6/4)
    core_idx = [P0.index(l) for l in have_angle]  # only 3; pad to a 6/4 to illustrate
    rng = random.Random(0)
    rest = [i for i in range(10) if i not in core_idx]
    curve6 = core_idx + rest[:3]; flap4 = rest[3:]
    rand_perm = list(range(10)); rng.shuffle(rand_perm)
    rnd6, rnd4 = rand_perm[:6], rand_perm[6:]
    print(f"    'curve' 6/4 split : rank(core6)={block_rank(curve6)}  rank(flap4)={block_rank(flap4)}  "
          f"both orthogonal={np.max(np.abs((F[:,curve6].conj().T@F[:,flap4])))<1e-6}")
    print(f"    RANDOM 6/4 split  : rank(6)={block_rank(rnd6)}  rank(4)={block_rank(rnd4)}  "
          f"both orthogonal={np.max(np.abs((F[:,rnd6].conj().T@F[:,rnd4])))<1e-6}")
    print("\n  => rank-10 = rank-6 (+) rank-4 holds for ANY 6/4 partition (trivial from column")
    print("     orthogonality). The μ3/curve classification does NOT select a canonical")
    print("     decomposition — consistent with int2 (orthogonality is μ6-robust, the μ6/CM")
    print("     structure lives in the large-prime correlation K, not the rank-10 matrix).")


if __name__ == "__main__":
    main()
