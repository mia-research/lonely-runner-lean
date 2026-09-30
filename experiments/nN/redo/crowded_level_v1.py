"""E193 (2026-09-30): the crowded level at order eight, read with our order-seven proof's instant form. A MAP run.

Owner: "Ok that sounds good, just remember to keep to our own framework, boundaries, isolation events, cascade not
density or other frames."  Map: MECHANISM_MAP_v2, Q6 and Q5; M2 (d).

Our order-seven proof (Spec/OrderSeven*N.lean; docs/n8/Q6_ORDER_SEVEN_READ_v1.md) ends its hard branch at an instant
lambda/7^{m+1}, lambda = j + k*7^m: a fine instant j/7^{m+1} (a small dilation, where the crowded level's readings
leave two adjacent sevenths empty, `four_band` phase 1) and a grid rotation k/7 (which turns each residue class at its
own speed, 1, 2 or 4, until every class's arc misses the subject's slot, `phase2`, `lemma5`).  At m = 1 (§7) the modulus
49 can fail and 98 is used.

Order eight, readings <= 24: every set with a multiple of 8 has m = 1, N = 64: the instants (j + 8k)/64, j = 1..7,
k = 0..7 (every a/64 with 8 not dividing a).  Derived (M4): whether a/64 is lonely depends only on each reading mod 64
(a*d mod 64 in [8, 56]); a multiple 8u of 8 reads j*u/8, clear iff 8 does not divide j*u; a non-multiple reads its top
octal digit q(j*d) plus k*(d mod 8), rotating with its residue class.

Class (the translated hard branch, E192): 7-sets in 1..24 with a multiple of 8, the non-multiples' cost
sum max(2, gcd(d, 8)) >= 8, and no common factor.  Recorded per set, exactly:
  * the sign-normalised classes of the non-multiples (r = d mod 8: 1,7 -> 1; 3,5 -> 3; 2,6 -> 2; 4 -> 4);
  * which (j, k) make a/64 lonely;
  * the EXCEPTIONS (no a/64 lonely), each listed, with: the least P for which some a/(8P) is lonely (order seven's §7
    moved from 49 to 98 = 7*14); the cascade's landing t* and its host.
NOT reported as a finding: how many sets some a/64 isolates (56 instants: v21 §17E's density premise).  The content is
the finite reduction (derived above), the exceptions, and the structure of the (j, k) used.
Oracle check: the cascade's landing is lonely and no a/64 below it is lonely (the landing is the first lonely instant).
"""
import itertools, math
from fractions import Fraction as F
from collections import Counter
from multiprocessing import Pool
from place_incidents_v1 import cascade

CLS = {1: 1, 7: 1, 3: 3, 5: 3, 2: 2, 6: 2, 4: 4}


def lonely_at(S, a, N):
    lo, hi = N // 8, 7 * N // 8
    return all(lo <= (a * d) % N <= hi for d in S)


def study(first):
    out = []
    for rest in itertools.combinations(range(first + 1, 25), 6):
        S = (first,) + rest
        mult = [d for d in S if d % 8 == 0]
        if not mult:
            continue
        nonm = [d for d in S if d % 8]
        if sum(max(2, math.gcd(d, 8)) for d in nonm) < 8:
            continue
        if math.gcd(*S) > 1:
            continue
        good = [a for a in range(1, 64) if a % 8 and lonely_at(S, a, 64)]
        cls = tuple(sorted(CLS[d % 8] for d in nonm))
        rec = dict(S=S, cls=cls, nmult=len(mult), good=good, js=sorted({a % 8 for a in good}))
        ts, n = cascade(S)
        rec['ts'] = ts
        rec['oracle'] = all(not (F(a, 64) < ts) for a in good)
        if not good:
            P = next(P for P in range(1, 400) if P != 8 and any(lonely_at(S, a, 8 * P) for a in range(1, 8 * P)))
            hosts = [h for h in S if (h * ts - math.floor(h * ts)) == F(1, 8)]
            rec.update(P=P, aP=[a for a in range(1, 8 * P) if lonely_at(S, a, 8 * P)][:6], hosts=hosts)
        out.append(rec)
    return out


if __name__ == '__main__':
    with Pool(8) as pool:
        recs = [r for part in pool.map(study, range(1, 19)) for r in part]
    o = open('crowded_level_v1.out', 'w'); o.write(__doc__ + "\n"); w = lambda s: o.write(s + "\n")
    w("sets in the class: %d" % len(recs))
    w("CHECK oracle (no lonely a/64 before the cascade's landing): %d violations" % sum(not r['oracle'] for r in recs))
    w("multiples of 8 per set: %s" % dict(sorted(Counter(r['nmult'] for r in recs).items())))
    w("class patterns of the crowded level (normalised residues of the non-multiples): %d distinct" %
      len(Counter(r['cls'] for r in recs)))
    exc = [r for r in recs if not r['good']]
    w("\nEXCEPTIONS: no instant a/64 is lonely: %d sets" % len(exc))
    w("  by class pattern: %s" % dict(Counter(r['cls'] for r in exc).most_common()))
    w("  by number of multiples of 8: %s" % dict(sorted(Counter(r['nmult'] for r in exc).items())))
    w("  least P with a lonely a/(8P): %s" % dict(sorted(Counter(r['P'] for r in exc).items())))
    for r in exc[:60]:
        w("  %s cls %s  least P %d (a: %s)  cascade t* %s host %s" % (r['S'], r['cls'], r['P'], r['aP'], r['ts'], r['hosts']))
    w("\nstructure among the rest (coordinates, not evidence): which dilations j carry a lonely a/64")
    w("  least j: %s" % dict(sorted(Counter(min(r['js']) for r in recs if r['good']).items())))
    w("  j used, as sets: %s" % dict(Counter(tuple(r['js']) for r in recs if r['good']).most_common(12)))
    o.close()
    print(open('crowded_level_v1.out').read()[len(__doc__):])
