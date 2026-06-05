"""
Joint-good fine cell existence harness — search for counterexamples.

Goal: under the hard case (p < n*L_G), with gcd(p, L_G) = 1 and both
goodCellIdx sets non-empty, does a joint-good fine cell m'' < n*L_G*L_A*p
always exist?
"""

import itertools
import math
from functools import reduce


def lcm(a, b):
    return a * b // math.gcd(a, b)


def lcm_list(xs):
    return reduce(lcm, xs, 1)


def isprime(n):
    if n < 2:
        return False
    if n % 2 == 0:
        return n == 2
    i = 3
    while i * i <= n:
        if n % i == 0:
            return False
        i += 2
    return True


def good_cell_idx(speeds, n, L):
    """Returns list of m in [0, n*L) such that for every v in speeds,
    (m // (L // v)) % n is in [1, n-2] (closed interval, so 1..n-2)."""
    result = []
    for m in range(n * L):
        ok = True
        for v in speeds:
            assert L % v == 0, f"speed {v} does not divide L={L}"
            d = L // v
            r = (m // d) % n
            if not (1 <= r <= n - 2):
                ok = False
                break
        if ok:
            result.append(m)
    return result


def exists_joint(G_speeds, A_speeds, n, p):
    L_G = lcm_list(G_speeds)
    L_A = lcm_list(A_speeds)
    M_A = n * L_G * L_A
    G_idx = set(good_cell_idx(G_speeds, n, L_G))
    A_idx = set(good_cell_idx(A_speeds, n, L_A))
    if not G_idx or not A_idx:
        return False, (L_G, L_A, M_A, len(G_idx), len(A_idx), -1)
    L_Ap = L_A * p
    count = 0
    first = None
    for mpp in range(n * L_G * L_A * p):
        alpha = mpp // L_Ap
        beta = (mpp % M_A) // L_G
        if alpha in G_idx and beta in A_idx:
            count += 1
            if first is None:
                first = (mpp, alpha, beta)
    exists = count > 0
    return exists, (L_G, L_A, M_A, len(G_idx), len(A_idx), count)


def main():
    SPEED_POOL_G = list(range(1, 9))   # 1..8
    SPEED_POOL_A = list(range(1, 7))   # 1..6
    PRIMES = [p for p in range(2, 31) if isprime(p)]
    NS = [3, 4, 5, 6, 7]

    total = 0
    eligible = 0
    joint_zero = 0
    joint_pos = 0
    counterexamples = []

    for n in NS:
        for kG in [1, 2, 3]:
            for G_speeds in itertools.combinations(SPEED_POOL_G, kG):
                G_speeds = list(G_speeds)
                L_G = lcm_list(G_speeds)
                if L_G == 0:
                    continue
                G_idx = good_cell_idx(G_speeds, n, L_G)
                if not G_idx:
                    continue
                for kA in [1, 2]:
                    for A_speeds in itertools.combinations(SPEED_POOL_A, kA):
                        A_speeds = list(A_speeds)
                        L_A = lcm_list(A_speeds)
                        if L_A == 0:
                            continue
                        A_idx = good_cell_idx(A_speeds, n, L_A)
                        if not A_idx:
                            continue
                        for p in PRIMES:
                            total += 1
                            if not (1 < p):
                                continue
                            if math.gcd(p, L_G) != 1:
                                continue
                            if not (p < n * L_G):
                                continue  # not hard case
                            # Avoid expensive enumeration if M too large
                            M = n * L_G * L_A * p
                            if M > 5_000_000:
                                continue
                            eligible += 1
                            exists, info = exists_joint(G_speeds, A_speeds, n, p)
                            L_G_, L_A_, M_A, gG, gA, jc = info
                            if exists:
                                joint_pos += 1
                            else:
                                joint_zero += 1
                                counterexamples.append({
                                    "n": n,
                                    "G_speeds": G_speeds,
                                    "A_speeds": A_speeds,
                                    "p": p,
                                    "L_G": L_G_,
                                    "L_A": L_A_,
                                    "|G_idx|": gG,
                                    "|A_idx|": gA,
                                    "joint_count": jc,
                                    "M_A": M_A,
                                    "n*L_G": n * L_G_,
                                    "L_A*p": L_A_ * p,
                                })

    print("=" * 60)
    print("JOINT FINE CELL EXISTENCE HARNESS — RESULTS")
    print("=" * 60)
    print(f"Total configs tried:        {total}")
    print(f"Eligible (all hyps + hard): {eligible}")
    print(f"Joint count > 0:            {joint_pos}")
    print(f"Joint count = 0 (COUNTER):  {joint_zero}")
    print()
    if counterexamples:
        print(f"FOUND {len(counterexamples)} COUNTEREXAMPLE(S):")
        for ce in counterexamples[:20]:
            print(f"  {ce}")
        if len(counterexamples) > 20:
            print(f"  ... and {len(counterexamples) - 20} more")
    else:
        print("No counterexamples found in this range.")
        print("Conclusion: lemma appears to hold under the stated hypotheses for the searched range.")


if __name__ == "__main__":
    main()
