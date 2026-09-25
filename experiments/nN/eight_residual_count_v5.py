"""v5: adds no_common_factor and no_six_seven_nine (v4 no_fifths, v3 no_thirds,
v2 no_rational_opening).  Count the sets in EightResidual (LonelyRunner/LRC/Spec/OrderEightCasesN.lean) among the
7-element subsets of [1, N], field by field as the structure states them.  Reports the count
without the two §15 fields and with them, and checks each residual set for a certificate
(Theorem 10: some flank e in S and index j < e with every d*(8j+1) mod 8e in [e, 7e])."""
import sys, itertools, time, math
N = int(sys.argv[1]) if len(sys.argv) > 1 else 30

def free_flank8(S, e):
    for d in S:
        if d != e and d % 8 == 0:
            r = d % (8 * e)
            if not (e <= r <= 7 * e): return False
    for k in range(8):
        if all((d * k + d // e) % 8 not in (0, 7) for d in S if d % 8): return True
    return False

def shifted(S):
    e = max(S)
    if e % 8: return False
    if any(d % 8 == 0 for d in S if d != e): return False
    return sum(1 for d in S if d != e and d % 2) <= 3

def first_lap(S):
    for e in S:
        others = [d for d in S if d != e]
        lo, hi = min(others), max(others)
        A = 1
        while hi * A <= 7 * e:
            if lo * A >= e: return True
            A += 8
    return False

def minus_seven(S):
    return any(all(e <= (-7 * d) % (8 * e) <= 7 * e for d in S) for e in S)

def certificate(S):
    for e in S:
        for j in range(e):
            A = 8 * j + 1
            if all(e <= (d * A) % (8 * e) <= 7 * e for d in S): return (e, j)
    return None


def rational_opening(S, N, M, i):
    """RationalOpening8 S N M i, as OrderEightCasesN states it."""
    for d in S:
        c = (8 * (i * d % N) + d // M) % (8 * N)
        if not (N <= c and (c < 7 * N or (c == 7 * N and d % M == 0))): return False
    return True

def has_rational_opening(S):
    """some e in S, N | 8, N | e, i: RationalOpening8 S N (e/N) i (i mod N suffices)."""
    return any(rational_opening(S, N, e // N, i)
               for e in S for N in (1, 2, 4, 8) if e % N == 0 for i in range(N))

def has_thirds(S):
    """some e in S with 3 | e and i: RationalOpening8 S 3 (e/3) i."""
    return any(rational_opening(S, 3, e // 3, i) for e in S if e % 3 == 0 for i in range(3))

def has_fifths(S):
    """some e in S with 5 | e and i: RationalOpening8 S 5 (e/5) i."""
    return any(rational_opening(S, 5, e // 5, i) for e in S if e % 5 == 0 for i in range(5))

def has_N(S, Nn):
    return any(rational_opening(S, Nn, e // Nn, i) for e in S if e % Nn == 0 for i in range(Nn))

def band_at(S, e, k):
    return all(e <= (d * (8 * k + 1)) % (8 * e) <= 7 * e for d in S)
t0 = time.time()
base = v2 = v3 = v4 = v4g = rem = 0; rest = []; nocert = []; mism = 0
for S in itertools.combinations(range(1, N + 1), 7):
    if not any(d % 2 for d in S): continue
    if not all(any(d % q == 0 for d in S) for q in (5, 6, 7, 8)): continue
    if not max(S) > 7 * min(S): continue
    if sum(4 if d % 8 == 4 else 2 for d in S if d % 8) < 8: continue
    if any(free_flank8(S, e) for e in S if e % 8 == 0): continue
    if shifted(S): continue
    srt = sorted(S)
    if srt[-1] > 7 * srt[-2]: continue
    if first_lap(S) or minus_seven(S): continue
    base += 1
    for e in S:                       # the class form agrees with Theorem 10 at k = i*(e/N)
        for Nn in (1, 2, 4, 8):
            if e % Nn: continue
            for i in range(Nn):
                if rational_opening(S, Nn, e // Nn, i) != band_at(S, e, i * (e // Nn)): mism += 1
    if has_rational_opening(S): continue
    v2 += 1
    if has_thirds(S): continue
    v3 += 1
    if has_fifths(S): continue
    v4 += 1
    if math.gcd(*S) > 1: continue
    v4g += 1
    if has_N(S, 6) or has_N(S, 7) or has_N(S, 9): continue
    rem += 1
    rest.append(S)
    if certificate(S) is None: nocert.append(S)
print(f"N = {N}: 7-subsets of [1,{N}]")
print(f"  EightResidual without no_rational_opening (v1): {base}")
print(f"  with no_rational_opening (v2): {v2}")
print(f"  with no_thirds (v3): {v3}")
print(f"  with no_fifths (v4): {v4}")
print(f"  with no_common_factor: {v4g}")
print(f"  EightResidual as stated (v5, with no_six_seven_nine): {rem}")
print(f"  first ten remaining: {rest[:10]}")
print(f"  class form vs Theorem 10 disagreements: {mism}")
print(f"  residual sets with NO certificate at any flank: {len(nocert)}  {nocert[:5]}")
print(f"  {time.time() - t0:.1f}s")
