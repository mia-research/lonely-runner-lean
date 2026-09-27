"""Named instants for the DEVIATED doubled-slot family (E40/E41): speeds 100 + i + e_i for slot i != r, and
100 + s + 8m + e_r for the moved runner; |e_i| <= rho(m) = 1/(512(m+1)).  Every runner, exact, random + corner deviations.
  outside the pair: class p = 3 if the pair's residue offset is +-1, else p = 1 (mirror 8 - p); neighbours = residue
     offsets +-p^{-1} = +-p (one of them may be the empty slot); gridT's rule at class p.
  home member: the undeviated instant's flank (partner, or the AP far-end runner at distance d), at its ACTUAL opening:
     t = (8L + 1)/(8 * delta_flank), L the flank's lap in the undeviated instant.
  far member: 1/(8 * delta_nearest) (R1) when 49 <= 48m + 6s, else the seven named instants."""
import random, itertools
from fractions import Fraction as F
from math import floor
def nd(x): x = x % 1; return min(x, 1 - x)
END = {1: (2, 0), 2: (7, 3), 3: (7, 2), 4: (5, 1), 5: (6, 1), 6: (7, 1)}
FARFL = {1: (0, 1), 2: (1, 1), 3: (2, 1), 4: (3, 1), 5: (1, 2), 6: (1, 3), 7: (6, 0)}
FAR = {1: F(9, 64), 2: F(9, 56), 3: F(3, 16), 4: F(9, 40), 5: F(17, 56), 6: F(25, 56), 7: F(1, 16)}
def speeds(s, r, m, e):
    u = [i for i in range(8)]; u[r] = s + 8 * m
    return [100 + u[i] + e[i] for i in range(8)], u
def class_rule(v, u, k, p):
    """gridT at class p for runner k; neighbours = residue offsets p (X side, pD = 1 mod 8) and 8-p (pD = 7)."""
    D = [u[j] - u[k] for j in range(8)]; dl = [v[j] - v[k] for j in range(8)]
    A = [j for j in range(8) if j != k and (p * D[j]) % 8 == 1]; B = [j for j in range(8) if j != k and (p * D[j]) % 8 == 7]
    q = 8 - p
    if len(A) != 1 and len(B) != 1: return None
    if not A:   # only B: B clear on one side of its class-p opening; its class-q opening works on the other
        b = B[0]; tB = F(p * D[b], 8) / dl[b]; return tB
    if not B:
        a = A[0]; tA = F(p * D[a], 8) / dl[a]; return tA
    a, b = A[0], B[0]; tA = F(p * D[a], 8) / dl[a]; tB = F(p * D[b], 8) / dl[b]
    if D[a] > 0 and D[b] > 0: return tA if tA <= tB else F(q, p) * tB
    if D[a] > 0 and D[b] < 0: return max(tA, tB)
    if D[a] < 0 and D[b] > 0: return min(tA, tB)
    return tB if tB <= tA else F(q, p) * tA
def home_rule(v, u, s, r, m):
    if 1 <= s <= 6 or (s, r) in ((0, 7), (7, 0)):
        fl, L = r, m                                  # the partner, lap m
    else:
        cc = (r if s == 0 else 7 - r); d, N = END[cc]
        t0 = F(8 * N + 1, 8 * d)
        if (8 * m * t0) % 1 == 0: fl, L = r, floor(8 * m * (t0 + F(1, 64 * m)))
        else:
            fl = [j for j in range(8) if j != s and abs(u[j] - u[s]) == d][0]; L = N
    return F(8 * L + 1, 8) / abs(v[fl] - v[s])
def far_rule(v, u, s, r, m):
    if 49 <= 48 * m + 6 * s:
        near = min((j for j in range(8) if j != r), key=lambda j: abs(u[j] - u[r]))
        return F(1, 8) / abs(v[near] - v[r])
    j, L = FARFL[r]                                   # the single runner pinning the undeviated instant
    return F(8 * L + 1, 8) / abs(v[j] - v[r])
def instant(v, u, s, r, m, k):
    if k == r: return far_rule(v, u, s, r, m)
    if k == s: return home_rule(v, u, s, r, m)
    ds = (s - k) % 8
    return class_rule(v, u, k, 3 if ds in (1, 7) else 1)
rnd = random.Random(51); fails = []; n = 0
for m in list(range(1, 13)) + [20, 40]:
    rho = F(1, 512 * (m + 1))
    for s in range(8):
        for r in range(8):
            if r == s: continue
            devs = [[rho * F(rnd.randint(-100, 100), 100) for _ in range(8)] for _ in range(6)]
            devs += [[rho * c for c in cs] for cs in [[rnd.choice((-1, 1)) for _ in range(8)] for _ in range(6)]]
            for e in devs:
                v, u = speeds(s, r, m, e)
                for k in range(8):
                    t = instant(v, u, s, r, m, k); n += 1
                    ok = t is not None and t > 0 and all(nd((v[j] - v[k]) * t) >= F(1, 8) for j in range(8) if j != k)
                    if not ok: fails.append((m, s, r, k, e[:3]))
print(f"checked {n} (runner, deviated arrangement) cases, m in 1..12, 20, 40; failures {len(fails)}")
from collections import Counter
print(Counter((f[1], f[2], 'home' if f[3] == f[1] else 'far' if f[3] == f[2] else 'other') for f in fails).most_common(12))
