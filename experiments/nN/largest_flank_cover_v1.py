"""The sets whose largest flank is fully covered, and what the covering forces.
On the v1 EightResidual of [1,40]: the largest flank e = max S fails when no opening j < e has every
reading d*(8j+1) mod 8e in [e, 7e] (Theorem 10).  For each failure: every other runner's
g_d = gcd(d, e), q_d = e/g_d and the openings it blocks b_d (by exact count; §15J says
b_d = c_d * g_d with c_d the blocked classes mod q_d); the total sum(b_d)/e and the overlap
sum(b_d) - e; and which q <= 8 certifies the set by rung_selection_v1's rule (least multiple of q
as flank), with how that q relates to e and to the g_d."""
import itertools, sys
_ARGV = list(sys.argv)
from collections import Counter
from math import gcd
_rs = __file__.replace('largest_flank_cover_v1.py', 'rung_selection_v1.py')
_s = open(_rs).read(); __file__ = _rs; exec(_s[:_s.index("for top in (30, 40):")])

def blocks(d, e, j):
    r = d * (8 * j + 1) % (8 * e); return not (e <= r <= 7 * e)
TOP = int(_ARGV[1]) if len(_ARGV) > 1 else 40
n = 0; fails = []
for S in itertools.combinations(range(1, TOP + 1), 7):
    if not eight_residual(S): continue
    n += 1
    e = max(S)
    if not any(all(not blocks(d, e, j) for d in S if d != e) for j in range(e)): fails.append(S)
print(f"[1,{TOP}]: v1 residual {n}; largest flank fails on {len(fails)}")
qs = Counter(); rel = Counter(); ratio = []; gshape = Counter(); smallq = Counter(); rows = []
for S in fails:
    e = max(S); others = [d for d in S if d != e]
    b = {d: sum(blocks(d, e, j) for j in range(e)) for d in others}
    g = {d: gcd(d, e) for d in others}; q = {d: e // g[d] for d in others}
    ratio.append(sum(b.values()) / e)
    smallq[sum(1 for d in others if q[d] <= 7)] += 1
    gshape[tuple(sorted((g[d] > 1) for d in others))] += 1
    cert = [qq for qq in range(2, 9) if rule(S, qq, free_exact)]
    q0 = cert[0] if cert else None; qs[q0] += 1
    if q0:
        rel['q | e' if e % q0 == 0 else 'q does not divide e'] += 1
        rel['q | gcd(d,e) for some d' if any(g[d] % q0 == 0 for d in others) else 'q divides no g_d'] += 1
        rel['q = some q_d' if q0 in q.values() else 'q is no q_d'] += 1
    rows.append((S, e, {d: (g[d], q[d], b[d]) for d in others}, round(sum(b.values()) / e, 2), q0))
print("sum of blocked openings / e over the failures: min %.2f, mean %.2f, max %.2f" % (min(ratio), sum(ratio) / len(ratio), max(ratio)))
print("runners sharing a factor with e (g_d > 1), as a sorted pattern:", sorted(gshape.items(), key=lambda x: -x[1])[:6])
print("number of runners with small denominator q_d <= 7:", sorted(smallq.items()))
print("least certifying q (rung rule):", sorted(qs.items(), key=str))
print("relation of that q to the covering:", dict(rel))
print("first eight failures (S, e, {d: (g_d, q_d, b_d)}, sum b/e, q):")
for r in rows[:8]: print("  ", r)

# resonance of the largest flank: gcd(e, 8), failures against the whole residual
allg = Counter(); failg = Counter(); failm = Counter()
fs = set(fails)
for S in itertools.combinations(range(1, TOP + 1), 7):
    if not eight_residual(S): continue
    g8 = gcd(max(S), 8); allg[g8] += 1
    if S in fs: failg[g8] += 1; failm[max(S) % 8] += 1
print("gcd(largest, 8): residual", dict(sorted(allg.items())), " failures", dict(sorted(failg.items())))
print("largest mod 8 among failures:", dict(sorted(failm.items())))
allm = Counter()
for S in itertools.combinations(range(1, TOP + 1), 7):
    if eight_residual(S): allm[max(S) % 8] += 1
print("largest mod 8 over the residual:", dict(sorted(allm.items())))
print("odd-flank failures:", [S for S in fails if max(S) % 2])
from sympy import totient
bt = Counter(); bf = Counter()
for S in itertools.combinations(range(1, TOP + 1), 7):
    if not eight_residual(S): continue
    e = max(S); r = int(totient(e)) / e
    key = '<0.40' if r < 0.40 else '0.40-0.50' if r < 0.5 else '0.50-0.60' if r < 0.6 else '0.60-0.70' if r < 0.7 else '0.70-0.80' if r < 0.8 else '>=0.80'
    bt[key] += 1; bf[key] += S in fs
print("failure rate of the largest flank by phi(e)/e:")
for k in ['<0.40', '0.40-0.50', '0.50-0.60', '0.60-0.70', '0.70-0.80', '>=0.80']:
    print(f"   {k}: {bf[k]} of {bt[k]}  = {100 * bf[k] / max(bt[k], 1):.3f}%")
print("failing largest elements:", sorted(Counter(max(S) for S in fails).items()))
