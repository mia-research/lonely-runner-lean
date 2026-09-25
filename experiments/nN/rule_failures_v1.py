"""Where the rung-selection rule fails at q = 2 and q = 3, in closed form.

q = 2, e the least even disparity, instant 1/2 + 1/(8e): it fails exactly when an even d has
d mod 8e outside [e, 7e], or an odd d has d mod 8e in (3e, 5e).
q = 3, e the least multiple of 3, instants i/3 + 1/(8e), i = 1, 2: a multiple of 3 needs
d mod 8e in [e, 7e]; a non-multiple with s = i*d mod 3 spoils the unit i exactly when d mod 8e is in
(13e/3, 19e/3) for s = 1 or (5e/3, 11e/3) for s = 2; it fails when a multiple is out of band or
both units are spoiled.

Reports, on the v1 residual of [1,40]: agreement of these closed forms with the rule; the sets that
fail both q = 2 and q = 3 and how; the least q >= 4 that rescues them; where the blockers sit.
"""
import itertools, time
from collections import Counter
_lb = __file__.replace('rule_failures_v1.py', 'rung_selection_v1.py')
_s = open(_lb).read(); __file__ = _lb; exec(_s[:_s.index("for top in (30, 40):")])
def q2(S):
    ev = [d for d in S if d % 2 == 0]
    if not ev: return None
    e = min(ev); m = 8 * e
    A = [d for d in ev if not (e <= d % m <= 7 * e)]
    B = [d for d in S if d % 2 and 3 * e < d % m < 5 * e]
    return A, B
def q3(S):
    th = [d for d in S if d % 3 == 0]
    if not th: return None
    e = min(th); m = 8 * e
    A = [d for d in th if not (e <= d % m <= 7 * e)]
    def spoil(i):
        out = []
        for d in S:
            if d % 3 == 0: continue
            s = (i * d) % 3; r = 3 * (d % m)          # compare 3*(d mod 8e) with 13e..19e or 5e..11e
            if (s == 1 and 13 * e < r < 19 * e) or (s == 2 and 5 * e < r < 11 * e): out.append(d)
        return out
    return A, spoil(1), spoil(2)
t0 = time.time(); n = 0; agree = 0; fail = []; how = Counter()
for S in itertools.combinations(range(1, 41), 7):
    if not eight_residual(S): continue
    n += 1
    A2, B2 = q2(S); r2 = not A2 and not B2
    A3, U1, U2 = q3(S); r3 = not A3 and (not U1 or not U2)
    agree += (r2 == rule(S, 2, free_exact)) and (r3 == rule(S, 3, free_exact))
    if not r2 and not r3:
        fail.append(S)
        how[("A2" if A2 else "") + ("B2" if B2 else ""), ("A3" if A3 else "") + ("U" if (U1 and U2) else "")] += 1
print(f"[1,40] residual v1 {n}: closed forms agree with the rule at q = 2 and 3 on {agree}")
print(f"  fail both q = 2 and q = 3: {len(fail)}   ({time.time()-t0:.0f}s)")
print("  how they fail (q=2 part, q=3 part):", sorted(how.items(), key=lambda x: -x[1]))

resc = Counter(); pos2 = Counter(); pos3 = Counter(); b2count = Counter()
for S in fail:
    qs = [q for q in range(4, 41) if rule(S, q, free_exact)]
    resc[min(qs) if qs else None] += 1
    A2, B2 = q2(S)
    e2 = min(d for d in S if d % 2 == 0)
    b2count[len(B2)] += 1
    for d in B2: pos2[round((d % (8 * e2)) / e2, 1)] += 1
    A3, U1, U2 = q3(S)
    e3 = min(d for d in S if d % 3 == 0)
    for d in set(U1) | set(U2): pos3[(d % 3, round(3 * (d % (8 * e3)) / e3))] += 1
print("rescuing q (least q >= 4 where the rule holds):", sorted(resc.items(), key=lambda x: (x[0] is None, x[0])))
print("odd blockers of q = 2: count per set", dict(b2count), "; position (d mod 8e2)/e2:", sorted(pos2.items())[:25])
print("blockers of q = 3 units: (d mod 3, 3(d mod 8e3)/e3 rounded):", sorted(pos3.items(), key=lambda x: -x[1])[:16])
