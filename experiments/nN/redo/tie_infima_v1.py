# tie_infima_v1.py -- exact infimum of rho_7 over arrangements having a single-point window at a given instant R0, by class; exact witnesses.
# Derivation (tie_structure_v1.md section 3): with R0=u/v fixed, reading rho is allowed iff R0*rho mod 8 in [1,7], i.e. rho in I_m=[(8m+1)/R0,(8m+7)/R0];
# an exit reading sits at a left endpoint l_m, an entry reading at a right endpoint r_m. Reading 1 (=1) must be allowed. A seven-set S contains 1, an exit
# endpoint L (L may be 1 itself if R0 = 1 mod 8), an entry endpoint R (R may be 1 itself if R0 = 7 mod 8), and free points of the allowed set.
# Search description: R0 = u/v lowest terms, u odd, 1 < R0 <= 23, v <= 12.
import sys
from fractions import Fraction as F
from math import gcd, floor
exec(open('win_lib_v1.py').read())
def allowed_intervals(R0, top):
    out = []; m = 0
    while True:
        lo = F(8 * m + 1) / R0; hi = F(8 * m + 7) / R0
        if lo > top: break
        out.append((m, lo, hi)); m += 1
    return out
def crit(R0, rh):
    ps = [(R0 * r) % 8 for r in rh]
    return all(1 <= p <= 7 for p in ps) and (R0 == 1 or 1 in ps) and 7 in ps
def best_for(R0, cls):
    """cls: 'neither' (L,R > 1), 'r1_enters' (reading 1 is the entry, R0 = 7 mod 8), 'r1_exits' (reading 1 is the exit, R0 = 1 mod 8). Endpoints searched up to 12."""
    top = F(12)
    ivs = [(m, max(lo, F(1)), hi) for m, lo, hi in allowed_intervals(R0, top) if hi >= 1]
    if not any(lo <= 1 <= hi for m, lo, hi in ivs): return None
    r1_exit = (R0 % 8 == 1); r1_enter = (R0 % 8 == 7)
    Ls = [F(8 * m + 1) / R0 for m, lo, hi in ivs if F(8 * m + 1) / R0 >= 1]
    Rs = [F(8 * m + 7) / R0 for m, lo, hi in ivs if F(8 * m + 7) / R0 >= 1]
    if cls == 'r1_exits':
        if not r1_exit: return None
        Ls = [F(1)]; Rs = [r for r in Rs if r > 1]
    elif cls == 'r1_enters':
        if not r1_enter: return None
        Rs = [F(1)]; Ls = [l for l in Ls if l > 1]
    else:
        Ls = [l for l in Ls if l > 1]; Rs = [r for r in Rs if r > 1]
    pairs = sorted(((max(F(1), L, Rr), L, Rr) for L in Ls for Rr in Rs if L != Rr))
    best = None
    for M0, L, Rr in pairs:
        if best is not None and M0 > best[0]: break
        nd = any(min(hi, M0) > lo for m, lo, hi in ivs)
        if nd: cand = (M0, True, L, Rr)
        else:
            nxt = [lo for m, lo, hi in ivs if hi > lo and lo >= M0]
            if not nxt: continue
            cand = (min(nxt), False, L, Rr)
        if best is None or cand[0] < best[0] or (cand[0] == best[0] and cand[1] and not best[1]): best = cand
    return best
def witness(R0, cls, best):
    inf, att, L, Rr = best
    S = {F(1), L, Rr}
    top = F(60)
    ivs = [(max(lo, F(1)), hi) for m, lo, hi in allowed_intervals(R0, top) if hi >= 1]
    pieces = [(lo, min(hi, inf) if att else hi) for lo, hi in ivs if (min(hi, inf) > lo if att else (hi > lo and lo >= inf))]
    lo, hi = pieces[0]; k = 1
    while len(S) < 7:
        width = (hi - lo)
        for t in range(1, 9):
            x = lo + width * F(t, 9) if att else lo + width * F(t, 90 * k)
            if len(S) < 7 and x not in S and (R0 * x) % 8 not in (0,) and 1 <= (R0 * x) % 8 <= 7: S.add(x)
        k += 1
    return sorted(S)
print('class | R0 with smallest infimum | inf rho_7 | attained | witness (exact) | single-point window at R0 by windows(): | crit')
for cls in ('r1_exits', 'r1_enters', 'neither'):
    for kind in ('R0 integer', 'R0 non-integer'):
        res = []
        for v in range(1, 13):
            for u in range(v + 1, 23 * v + 1):
                if u % 2 == 0 or gcd(u, v) != 1: continue
                R0 = F(u, v)
                if (kind == 'R0 integer') != (v == 1): continue
                b = best_for(R0, cls)
                if b: res.append((b[0], not b[1], R0, b))
        if not res: print(cls, kind, 'none reached'); continue
        res.sort(key=lambda x: (x[0], x[1], x[2]))
        inf, na, R0, b = res[0]
        S = witness(R0, cls, b)
        ws = windows(S, 23)
        ok = (R0, R0) in ws and crit(R0, S) and verify(S, ws, 23)
        print(cls, kind, '| R0 =', R0, '| inf rho_7 =', inf, '=%.6f' % float(inf), '| attained' if b[1] else '| not attained', '| exit endpoint', b[2], 'entry endpoint', b[3], '| witness', [str(x) for x in S], '| point window at R0 and verify():', ok)
        # runner-up R0 values with the same inf
        same = [r[2] for r in res if r[0] == inf][:6]
        print('      R0 values attaining the same infimum (first 6):', [str(x) for x in same])
