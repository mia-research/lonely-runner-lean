import math, itertools

from fractions import Fraction as F

E = F(1, 8)

Rs = sorted({(a, b) for b in range(1, 13) for a in range(1, 8 * b + 1)})



def dist(x): f = x - math.floor(x); return min(f, 1 - f)

def fixedR(S):
    m = S[0]
    for a, b in Rs:
        q = b * m; ok = True
        for d in S:
            rem = (a * d) % q
            if 8 * rem < q or 8 * rem > 7 * q: ok = False; break
        if ok: return True
    return False

def chain2(r):
    n = len(r)
    for m in range(0, 7):
        for k in (1, 2):
            if m + k > n: continue
            rungs = r[m:n - k]; T = r[n - k:]
            LT = F(1, 4) / T[0] if k == 1 else F(1, 2) / T[0]
            gaps = [LT]
            for x in reversed(rungs): gaps.append(F(1, 4) / x + 2 * gaps[-1])
            gaps.reverse()
            if not all(gaps[i + 1] <= F(3, 4) / rungs[i] for i in range(len(rungs))): continue
            if m == 0: return True
            M = r[m - 1]; gam = F(1, m + 1)
            if gaps[0] * M <= 2 * (gam - E): return True
    return False

def count_split(od, a, b):
    return all((od + 2*a2 + 4*b2 < 4) or (od + 2*(a-a2) + 4*(b-b2) < 4) for a2 in range(a+1) for b2 in range(b+1))

def settled1(m, o, t, f):
    return ((count_split(o, t, f) and m <= 6) or (t == 0 and o <= 3 and m + f <= 6) or (m <= 3 and f <= 1 and o + t <= 3) or
            (o <= 3 and m + f <= 3 and t <= 1) or (count_split(o, t, 0) and m + f <= 3) or (o <= 3 and m + f <= 2 and t <= 2) or
            (count_split(o, t, 0) and m <= 2 and f <= 2))

def settled2(m, o, t, f):
    return settled1(m, o, t, f) or (o <= 3 and m + f <= 1 and t <= 3) or (count_split(o, t, 0) and m <= 1 and f <= 3)

def oott(S):
    odds = [e for e in S if e % 2]; ts = [e for e in S if e % 4 == 2]
    m = sum(1 for e in S if e % 8 == 0); f = sum(1 for e in S if e % 8 == 4)
    if len(odds) > 2 or len(ts) > 2 or m + f > 3: return False
    if len(odds) == 2 and not (odds[0] % 8 != odds[1] % 8 and (odds[0] + odds[1]) % 8 != 0): return False
    return True

def residue_settled(S):
    m = sum(1 for e in S if e % 8 == 0); o = sum(1 for e in S if e % 2); t = sum(1 for e in S if e % 4 == 2); f = sum(1 for e in S if e % 8 == 4)
    return settled2(m, o, t, f) or oott(S)

def simple_fields(S):
    if len(S) != 7: return False
    g = 0
    for d in S: g = math.gcd(g, d)
    if g != 1: return False
    if all(d % 2 == 0 for d in S): return False
    for q in (5, 6, 7, 8):
        if not any(d % q == 0 for d in S): return False
    if not any(7 * a < b for a in S for b in S): return False
    if sum(max(2, math.gcd(e, 8)) for e in S if e % 8) < 8: return False
    for V in S:
        if not any(s != V and V <= 7 * s for s in S): return False
    for e in S:
        for k in range(0, 7 * e // 8 + 1):
            if all(e <= d * (8 * k + 1) <= 7 * e for d in S if d != e): return False
    return True

def slow_gate(S):
    """best gate for the slow set S (list of Fractions): returns max of 1/(len+1) and the q-gates."""
    best = F(1, len(S) + 1)
    den = 1
    for d in S: den = den * d.denominator // math.gcd(den, d.denominator)
    a = [int(d * den) for d in S]; g = 0
    for x in a: g = math.gcd(g, x)
    for j in range(1, 9):
        if any((x * j) % g for x in a): continue
        ns = [x * j // g for x in a]
        for q in range(2, 8):
            if all(n % q for n in ns): best = max(best, F(1, q))
    return best

def chain2q(r):
    n = len(r)
    for m in range(0, 7):
        for k in (1, 2):
            if m + k > n: continue
            rungs = r[m:n - k]; T = r[n - k:]
            LT = F(1, 4) / T[0] if k == 1 else F(1, 2) / T[0]
            gaps = [LT]
            for x in reversed(rungs): gaps.append(F(1, 4) / x + 2 * gaps[-1])
            gaps.reverse()
            if not all(gaps[i + 1] <= F(3, 4) / rungs[i] for i in range(len(rungs))): continue
            if m == 0: return True
            M = r[m - 1]; gam = slow_gate(r[:m])
            if gam > E and gaps[0] * M <= 2 * (gam - E): return True
    return False

def clear_iv(x, T):
    out = []; n = 0
    while True:
        lo = F(8 * n + 1, 8) / x; hi = F(8 * n + 7, 8) / x
        if lo > T: break
        out.append((lo, min(hi, T))); n += 1
    return out

def meet(A, B):
    out = []; i = j = 0
    while i < len(A) and j < len(B):
        lo = max(A[i][0], B[j][0]); hi = min(A[i][1], B[j][1])
        if lo <= hi: out.append((lo, hi))
        if A[i][1] < B[j][1]: i += 1
        else: j += 1
    return out

def max_window(S):
    g = 0
    for d in S: g = math.gcd(g, d)
    T = F(2, g)
    J = clear_iv(F(S[0]), T)
    for s in S[1:]: J = meet(J, clear_iv(F(s), T))
    return max((hi - lo for lo, hi in J), default=F(0))

def chain_window(S):
    r = [F(d) for d in S]; n = len(r)
    for m in range(1, 7):
        for k in (1, 2):
            if m + k > n: continue
            rungs = r[m:n - k]; T = r[n - k:]
            LT = F(1, 4) / T[0] if k == 1 else F(1, 2) / T[0]
            gaps = [LT]
            for x in reversed(rungs): gaps.append(F(1, 4) / x + 2 * gaps[-1])
            gaps.reverse()
            if not all(gaps[i + 1] <= F(3, 4) / rungs[i] for i in range(len(rungs))): continue
            if max_window(S[:m]) >= gaps[0]: return True
    return False
