"""
Filtered counterexample search for joint_fine_cell_exists.

Adds LRC-realistic constraints:
- G_speeds ∩ A_speeds = ∅ (disjoint)
- All speeds together are distinct
- gcd(all speeds, including p) = 1 (LRC normalisation)
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
    result = []
    for m in range(n * L):
        ok = True
        for v in speeds:
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
    for mpp in range(n * L_G * L_A * p):
        alpha = mpp // L_Ap
        beta = (mpp % M_A) // L_G
        if alpha in G_idx and beta in A_idx:
            count += 1
    return count > 0, (L_G, L_A, M_A, len(G_idx), len(A_idx), count)


def main():
    SPEED_POOL = list(range(1, 9))
    PRIMES = [p for p in range(2, 20) if isprime(p)]
    NS = [3, 4, 5, 6, 7]

    total = 0
    eligible = 0
    joint_zero = 0
    counterexamples = []

    for n in NS:
        for kG in [1, 2, 3]:
            for G_speeds_tup in itertools.combinations(SPEED_POOL, kG):
                G_speeds = list(G_speeds_tup)
                L_G = lcm_list(G_speeds)
                G_idx = good_cell_idx(G_speeds, n, L_G)
                if not G_idx:
                    continue
                for kA in [1, 2]:
                    for A_speeds_tup in itertools.combinations(SPEED_POOL, kA):
                        A_speeds = list(A_speeds_tup)
                        # disjoint
                        if set(G_speeds) & set(A_speeds):
                            continue
                        L_A = lcm_list(A_speeds)
                        A_idx = good_cell_idx(A_speeds, n, L_A)
                        if not A_idx:
                            continue
                        for p in PRIMES:
                            total += 1
                            if math.gcd(p, L_G) != 1:
                                continue
                            # LRC: also exclude p in G_speeds or A_speeds (so we get
                            # a coherent "p is the prime being separated")
                            if p in G_speeds or p in A_speeds:
                                continue
                            if not (p < n * L_G):
                                continue  # hard case only
                            M = n * L_G * L_A * p
                            if M > 5_000_000:
                                continue
                            # gcd of all speeds incl. p must be 1 (LRC normalisation)
                            g_all = math.gcd(p, reduce(math.gcd, G_speeds + A_speeds, 0))
                            if g_all != 1:
                                continue
                            eligible += 1
                            exists, info = exists_joint(G_speeds, A_speeds, n, p)
                            L_G_, L_A_, M_A, gG, gA, jc = info
                            if not exists:
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
                                    "p<n": p < n,
                                    "p∣n": (n % p == 0),
                                })

    print("=" * 70)
    print("FILTERED HARNESS — LRC-LIKE COUNTEREXAMPLES")
    print("  (disjoint G/A, p not in speeds, gcd(p,G,A)=1, hard case p<n·L_G)")
    print("=" * 70)
    print(f"Total configs:         {total}")
    print(f"Eligible (all hyps):   {eligible}")
    print(f"Joint count = 0:       {joint_zero}")
    print()
    if counterexamples:
        print(f"FOUND {len(counterexamples)} LRC-LIKE COUNTEREXAMPLE(S):")
        for ce in counterexamples[:30]:
            print(f"  {ce}")
        if len(counterexamples) > 30:
            print(f"  ... and {len(counterexamples) - 30} more")
        # Patterns
        print("\nPattern analysis:")
        print(f"  All with p∣n:    {sum(1 for ce in counterexamples if ce['p∣n'])}")
        print(f"  All with p<n:    {sum(1 for ce in counterexamples if ce['p<n'])}")
        small_G = sum(1 for ce in counterexamples if ce['|G_idx|'] == 1)
        small_A = sum(1 for ce in counterexamples if ce['|A_idx|'] == 1)
        print(f"  |G_idx|=1:       {small_G}")
        print(f"  |A_idx|=1:       {small_A}")
    else:
        print("No LRC-like counterexamples found.")


if __name__ == "__main__":
    main()
