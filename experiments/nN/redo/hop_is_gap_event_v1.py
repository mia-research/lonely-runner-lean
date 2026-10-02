# Test: the isolation spot (the left end of the first component of the lonely set) moves continuously while its component persists,
# and jumps only when the first component DIES (length -> 0, a start-end tangency) or an earlier component is BORN.
import sys, random
sys.argv = [sys.argv[0]]
exec(open('effective_crossings_v1.py').read().split('\nif __name__ ==')[0])
RMAX = F(14)
def windows(rho):
    out = []; j = 0
    while F(8 * j + 1) / rho <= RMAX:
        out.append((F(8 * j + 1) / rho, min(F(8 * j + 7) / rho, RMAX))); j += 1
    return out
def inter(A, B):
    out = []; i = k = 0
    while i < len(A) and k < len(B):
        lo = max(A[i][0], B[k][0]); hi = min(A[i][1], B[k][1])
        if lo <= hi: out.append((lo, hi))
        if A[i][1] < B[k][1]: i += 1
        else: k += 1
    return out
def lonely_set(rhos):
    L = windows(rhos[0])
    for r in rhos[1:]:
        L = inter(L, windows(r))
        if not L: return []
    out = []
    for lo, hi in sorted(L):
        if out and lo <= out[-1][1]: out[-1] = (out[-1][0], max(out[-1][1], hi))
        else: out.append((lo, hi))
    return out
from collections import Counter
rnd = random.Random(318)
EPS = F(1, 10**9); TINY = F(1, 10**6)
bases = [("AP", [F(x) for x in range(1, 8)]), ("g15", [F(x) for x in (1, 2, 3, 4, 5, 6, 15)]), ("wide", [F(1), F(2), F(5), F(11), F(23), F(47), F(95)]),
         ("clump", [F(1), F(30), F(31), F(33), F(36), F(40), F(45)])]
for i in range(6): bases.append(("rand%d" % i, [F(x) for x in sorted(rnd.sample(range(10, 400), 7))]))
bases = [(n, [F(x) / b[0] for x in b]) for n, b in bases]
cnt = Counter(); bad = []
for name, base in bases:
    for r in range(30):
        k = rnd.choice((1, 2, 3, 4)); movers = tuple(sorted(rnd.sample(range(7), k)))
        p = list(base); q = [F(0)] * 7
        for m in movers:
            span = max(F(1), base[m] / 3); q[m] = max(F(3, 10) * base[0], base[m] + F(rnd.randint(-150, 300), 100) * span) - base[m]
        s0 = F(1, 1000)
        for _ in range(12):
            pred, steps = predicted_next(p, q, s0)
            if pred is None or pred[0] >= 1: break
            s = pred[0]
            La = lonely_set(rho_at(p, q, s - EPS)); Lb = lonely_set(rho_at(p, q, s + EPS))
            if La and Lb:
                Ra, Rb = La[0][0], Lb[0][0]
                if abs(Rb - Ra) < TINY: cnt["landing continuous"] += 1
                else:
                    first_a = La[0][1] - La[0][0]; first_b = Lb[0][1] - Lb[0][0]
                    if Rb > Ra and first_a < TINY and Lb[0][0] >= La[0][1] - TINY: cnt["forward hop = first component dies"] += 1
                    elif Rb < Ra and first_b < TINY and Lb[0][1] <= La[0][0] + TINY: cnt["backward hop = earlier component born"] += 1
                    elif Rb > Ra: cnt["forward hop, other"] += 1; bad.append(("fwd", name, movers, float(s), float(Ra), float(Rb), float(first_a), float(first_b)))
                    else: cnt["backward hop, other"] += 1; bad.append(("bwd", name, movers, float(s), float(Ra), float(Rb), float(first_a), float(first_b)))
            else: cnt["lonely set empty in (0,14]"] += 1
            s0 = s + F(1, 10**6)
for k_, v in sorted(cnt.items()): print("  %-42s %d" % (k_, v))
for b in bad[:12]: print("   exception:", b)
