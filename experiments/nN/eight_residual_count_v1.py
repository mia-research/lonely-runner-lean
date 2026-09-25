"""Count the sets in EightResidual (LonelyRunner/LRC/Spec/OrderEightCasesN.lean) among the
7-element subsets of [1, N], field by field as the structure states them.  Reports the count
without the two §15 fields and with them, and checks each residual set for a certificate
(Theorem 10: some flank e in S and index j < e with every d*(8j+1) mod 8e in [e, 7e])."""
import sys, itertools, time
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

t0 = time.time()
base = only_fl = only_m7 = both = 0; nocert = []
for S in itertools.combinations(range(1, N + 1), 7):
    if not any(d % 2 for d in S): continue                       # odd
    if not all(any(d % q == 0 for d in S) for q in (5, 6, 7, 8)): continue
    if not max(S) > 7 * min(S): continue                         # spread
    if sum(4 if d % 8 == 4 else 2 for d in S if d % 8) < 8: continue   # cost
    if any(free_flank8(S, e) for e in S if e % 8 == 0): continue  # no free flank
    if shifted(S): continue                                      # R4 fails
    srt = sorted(S)
    if srt[-1] > 7 * srt[-2]: continue                           # not fast
    base += 1
    fl, m7 = first_lap(S), minus_seven(S)
    if fl: only_fl += 1
    if m7: only_m7 += 1
    if fl or m7: continue
    both += 1
    if certificate(S) is None: nocert.append(S)
print(f"N = {N}: 7-subsets of [1,{N}]")
print(f"  residual before §15 (rules R6, R1, descent, free flank, R4, R8, halving): {base}")
print(f"  of those, first-lap clearance applies: {only_fl};  -7 opening applies: {only_m7}")
print(f"  residual after §15 (EightResidual as stated): {both}")
print(f"  residual sets with NO certificate at any flank: {len(nocert)}  {nocert[:5]}")
print(f"  {time.time() - t0:.1f}s")
