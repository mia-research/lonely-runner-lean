"""
Phase 3b — Filter joint_fine_cell counterexamples by LRC realisability.

For each counterexample (n, G_speeds, A_speeds, p), check if it corresponds to
a valid call from §10.1 (DI) or §11.1 (ModDI):

DI (Theorem 10.1):
  - A_speeds = [q]  (singleton)
  - slow = G_speeds (n-2 elements)
  - V = p*q, p prime, gcd(p, lcm(slow)) = 1
  - (n-1)*slow_min < V <= (n-1)*slow_max  (hard case)
  - All speeds (slow ∪ {V}) distinct, gcd = 1

ModDI (Theorem 11.1):
  - A_speeds = [w_1, ..., w_r, q]  (r+1 elements)
  - slow = G_speeds ∪ {p*w_k : k} = "all slow speeds, including p-divisible"
  - hindSpeeds = G_speeds (n-2-r elements, those NOT divisible by p)
  - p | each w_k (after re-scaling: original slow speeds are p*w_k for the divisible ones)
  - q = V/p
  - All slow ∪ {V} distinct, gcd = 1, hard case

Reports: of the 681 counterexamples, how many correspond to valid §10.1 or §11.1 inputs?
"""

import itertools
import math
from functools import reduce
from fractions import Fraction


def gcd_list(xs):
    return reduce(math.gcd, xs, 0)


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


def good_intervals(v, n):
    intervals = []
    for k in range(v):
        a = Fraction(k, v) + Fraction(1, n * v)
        b = Fraction(k, v) + Fraction(n - 1, n * v)
        intervals.append((a, b))
    return intervals


def intersect_unions(U1, U2):
    result = []
    i = j = 0
    while i < len(U1) and j < len(U2):
        a1, b1 = U1[i]
        a2, b2 = U2[j]
        lo = max(a1, a2)
        hi = min(b1, b2)
        if lo <= hi:
            result.append((lo, hi))
        if b1 < b2:
            i += 1
        else:
            j += 1
    return result


def joint_good_intervals(speeds, n):
    if not speeds:
        return [(Fraction(0), Fraction(1))]
    joint = good_intervals(speeds[0], n)
    for v in speeds[1:]:
        joint = intersect_unions(joint, good_intervals(v, n))
        if not joint:
            return []
    return joint


def classify_di(n, G_speeds, A_speeds, p):
    """Is (n, G_speeds, A_speeds=[q], p) a valid §10.1 input?
    Returns dict with details or None."""
    if len(A_speeds) != 1:
        return None
    q = A_speeds[0]
    if len(G_speeds) != n - 2:
        return None  # slow speeds must have n-2 elements
    if not all(0 < v for v in G_speeds):
        return None
    if not isprime(p):
        return None
    V = p * q
    if V <= 0:
        return None
    if V in G_speeds:
        return None
    slow_with_V = G_speeds + [V]
    if len(set(slow_with_V)) != len(slow_with_V):
        return None
    if gcd_list(slow_with_V) != 1:
        return None
    L = lcm_list(G_speeds)
    if math.gcd(p, L) != 1:
        return None
    slow_sorted = sorted(G_speeds)
    if not ((n - 1) * slow_sorted[0] < V <= (n - 1) * slow_sorted[-1]):
        return None
    return {"q": q, "V": V, "slow": slow_sorted}


def classify_moddi(n, G_speeds, A_speeds, p):
    """Is (n, G_speeds, A_speeds, p) a valid §11.1 input?
    A_speeds = [w_1, ..., w_r, q] (r+1 elements, r>=1).
    G_speeds = hindSpeeds = slow speeds NOT divisible by p.
    Full slow = G_speeds ∪ {p*w_k}.
    Returns dict or None."""
    if len(A_speeds) < 1:
        return None
    if not isprime(p):
        return None
    # Try all ways to split A_speeds into (w_1..w_r, q): try last element as q
    # (the manuscript convention is Fin.snoc w q so q is the last).
    # But we can also try other splits.
    for q_idx in range(len(A_speeds)):
        w = A_speeds[:q_idx] + A_speeds[q_idx+1:]
        q = A_speeds[q_idx]
        r = len(w)
        if r < 1:
            continue
        # ModDI requires r >= 1
        if r > n - 3:
            continue  # Lemma 9.3
        # Recover full slow speeds: hind (G_speeds) ∪ {p*w_k}
        slow_div = [p * wk for wk in w]
        if not all(0 < v for v in slow_div):
            continue
        slow_full = G_speeds + slow_div
        if len(slow_full) != n - 2:
            continue
        if len(set(slow_full)) != len(slow_full):
            continue
        # G_speeds (hind) must all be coprime to p
        if not all(math.gcd(v, p) == 1 for v in G_speeds):
            continue
        V = p * q
        if V in slow_full:
            continue
        speeds_all = slow_full + [V]
        if gcd_list(speeds_all) != 1:
            continue
        slow_sorted = sorted(slow_full)
        if not ((n - 1) * slow_sorted[0] < V <= (n - 1) * slow_sorted[-1]):
            continue
        return {"w": w, "q": q, "V": V, "slow_full": slow_sorted, "hind": list(G_speeds)}
    return None


def main():
    print("=" * 78)
    print("PHASE 3b — Filter counterexamples by LRC realisability")
    print("=" * 78)
    print()

    SPEED_POOL = list(range(1, 9))
    PRIMES = [p for p in range(2, 20) if isprime(p)]
    NS = [3, 4, 5, 6, 7]

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
                        if set(G_speeds) & set(A_speeds):
                            continue
                        L_A = lcm_list(A_speeds)
                        A_idx = good_cell_idx(A_speeds, n, L_A)
                        if not A_idx:
                            continue
                        for p in PRIMES:
                            if math.gcd(p, L_G) != 1:
                                continue
                            if p in G_speeds or p in A_speeds:
                                continue
                            if not (p < n * L_G):
                                continue
                            M = n * L_G * L_A * p
                            if M > 5_000_000:
                                continue
                            g_all = math.gcd(p, reduce(math.gcd, G_speeds + A_speeds, 0))
                            if g_all != 1:
                                continue
                            joint = 0
                            for mpp in range(M):
                                alpha = mpp // (L_A * p)
                                beta = (mpp % (n * L_G * L_A)) // L_G
                                if alpha in set(G_idx) and beta in set(A_idx):
                                    joint += 1
                                    break
                            if joint == 0:
                                counterexamples.append((n, G_speeds, A_speeds, p))

    print(f"Total counterexamples: {len(counterexamples)}")
    print()

    # Classify each
    n_di = 0
    n_moddi = 0
    n_neither = 0
    di_examples = []
    moddi_examples = []
    for n, G_speeds, A_speeds, p in counterexamples:
        is_di = classify_di(n, G_speeds, A_speeds, p)
        is_moddi = classify_moddi(n, G_speeds, A_speeds, p)
        if is_di:
            n_di += 1
            if len(di_examples) < 10:
                di_examples.append((n, G_speeds, A_speeds, p, is_di))
        if is_moddi:
            n_moddi += 1
            if len(moddi_examples) < 10:
                moddi_examples.append((n, G_speeds, A_speeds, p, is_moddi))
        if not is_di and not is_moddi:
            n_neither += 1

    print(f"Of {len(counterexamples)} counterexamples:")
    print(f"  Valid §10.1 (DI) inputs:     {n_di}")
    print(f"  Valid §11.1 (ModDI) inputs:  {n_moddi}")
    print(f"  Neither (abstract, not LRC): {n_neither}")
    print()

    if di_examples:
        print("§10.1 (DI) realisable counterexamples:")
        for n, G, A, p, info in di_examples:
            joint_speeds = G + [info["V"]]
            ints = joint_good_intervals(joint_speeds, n)
            print(f"  n={n} slow={info['slow']} V={info['V']}={p}*{info['q']} → joint good set: {[(str(a), str(b)) for a, b in ints] if ints else 'EMPTY'}")
    else:
        print("§10.1 (DI) realisable counterexamples: NONE")

    print()
    if moddi_examples:
        print("§11.1 (ModDI) realisable counterexamples:")
        for n, G, A, p, info in moddi_examples:
            joint_speeds = info["slow_full"] + [info["V"]]
            ints = joint_good_intervals(joint_speeds, n)
            print(f"  n={n} slow_full={info['slow_full']} V={info['V']}={p}*{info['q']} w={info['w']} → joint good set: {[(str(a), str(b)) for a, b in ints] if ints else 'EMPTY'}")
    else:
        print("§11.1 (ModDI) realisable counterexamples: NONE")


if __name__ == "__main__":
    main()
