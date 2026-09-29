"""E188 (2026-09-30): the cascade's landings read in rung coordinates, against v21 section 17E's rung-selection rule.
A MAP: no pass condition except the derivation checks and the oracle check.

Owner: "yes run the landings through the cascade in residue form", with: "are we mapping things so we understand before
proposing a the mechanisim".  The residue form d(8k+1) mod 8e in [e, 7e] is v21 section 15's bridge
(lonely_eight_of_opening), already proved; read on a landing it only restates that the landing is lonely.  The
coordinates that tie the cascade to the case list (v21 section 17C-E) are the RUNG ones:

  rung (q, i, e): the instant i/q + 1/(8e), gcd(i, q) = 1, e the least reading divisible by q.  A multiple d of q reads
  as at e's first opening (clear iff d mod 8e in [e, 7e]: R1 on the multiples); a non-multiple reads d*i/q + d/(8e).
  q = 1 is the bound 1/(8 d_min) (R1); no multiple of q is R6 at the unit i/q.  (rung_selection_v1.py, section 17E.)

Derived (checked, must hold): the landing t* is an opening (K + 1/8)/h of a host h; with i/q = K/h reduced,
  (D1) h is the least reading divisible by q  (a slower multiple d would read d/(8h) < 1/8 at t*);
  (D2) so t* is the rung (q, i, h), and every reading is clear there in the rung's own terms.
Recorded, per set (exact, integer arithmetic for the rule):
  q_c   the cascade's own rung denominator, h/gcd(h, K); its class: 1 (the bound), q_c = h (gcd 1: the full resolution,
        where section 17D says the list "is the obligation again"), 2..8, other;
  q_min the least q for which the rung-selection rule certifies the set (some unit i clear), with R6 included;
  whether the cascade's landing is the earliest certified instant at q_min's rung.
"""
import itertools, math, json
from math import gcd
from fractions import Fraction as F
from collections import Counter
from multiprocessing import Pool
from quantity_tests_v1 import cd, E8
from place_incidents_v1 import cascade


def units(q):
    return [i for i in range(q)] if q == 1 else [i for i in range(1, q) if gcd(i, q) == 1]


def rung_instants(S, q):
    """Certified instants i/q + 1/(8e) (or i/q for R6) of the rung-selection rule at q, exact integer test."""
    mult = [d for d in S if d % q == 0]
    out = []
    if mult:
        e = min(mult)
        if any(not (e <= d % (8 * e) <= 7 * e) for d in mult):
            return out
        N = 8 * e * q
        for i in units(q):
            if all(e * q <= (d * (8 * e * i + q)) % N <= 7 * e * q for d in S if d % q):
                out.append(F(8 * e * i + q, N))
    else:
        for i in units(q):
            if all(q <= 8 * ((d * i) % q) <= 7 * q for d in S):
                out.append(F(i, q))
    return out


def one(S):
    ts, n = cascade(S)
    hosts = [h for h in S if (h * ts - math.floor(h * ts)) == E8]
    rec = dict(S=S, ts=ts, nh=len(hosts))
    h = max(hosts)                                   # D1 holds for every host; record the fastest
    K = math.floor(h * ts); g = gcd(h, K); q, i = h // g, K // g
    D = [d for d in S if d % q == 0]
    rec.update(h=S.index(h), K=K, qc=q, ic=i, nD=len(D), d1=(h == min(D)),
               d2=(ts == F(8 * h * i + q, 8 * h * q)))
    rec['qc_class'] = '1 (bound)' if q == 1 else ('q = h' if q == h else ('2..8' if q <= 8 else 'other'))
    qmin = None; first = None
    for qq in range(1, max(S) + 1):
        inst = rung_instants(S, qq)
        if inst:
            qmin, first = qq, min(inst); break
    rec.update(qmin=qmin, at_qmin=(first == ts), first_qmin=first, R=8 * S[0] * ts)
    return rec


def chunk(first):
    return [one((first,) + rest) for rest in itertools.combinations(range(first + 1, 25), 6)]


if __name__ == '__main__':
    with Pool(8) as pool:
        recs = [r for part in pool.map(chunk, range(1, 19)) for r in part]
    o = open('rung_map_v1.out', 'w'); o.write(__doc__ + "\n"); w = lambda s: o.write(s + "\n")
    w("sets: %d" % len(recs))
    w("CHECK D1 host is the least reading divisible by q_c: %d violations" % sum(not r['d1'] for r in recs))
    w("CHECK D2 t* is the rung instant i/q + 1/(8h): %d violations" % sum(not r['d2'] for r in recs))
    w("CHECK some rung certifies every set (the landing is one, D2): %d without" % sum(r['qmin'] is None for r in recs))
    w("hosts at t*: %s" % dict(sorted(Counter(r['nh'] for r in recs).items())))
    w("\nthe cascade's own rung, class of q_c: %s" % dict(Counter(r['qc_class'] for r in recs).most_common()))
    w("q_c = h (full resolution): by K: %s" % dict(sorted(Counter(r['K'] for r in recs if r['qc_class'] == 'q = h').items())))
    w("q_c other (> 8, < h): %s" % dict(sorted(Counter(r['qc'] for r in recs if r['qc_class'] == 'other').items())))
    w("readings divisible by q_c, count: %s" % dict(sorted(Counter(r['nD'] for r in recs).items())))
    w("\nq_min (least certifying rung, R6 included): %s" % dict(sorted(Counter(r['qmin'] for r in recs).items())))
    w("the landing IS the earliest certified instant of q_min's rung: %d of %d" % (sum(r['at_qmin'] for r in recs), len(recs)))
    w("q_c class x q_min: %s" % dict(sorted(Counter((r['qc_class'], r['qmin']) for r in recs).items(), key=lambda kv: -kv[1])))
    w("landing earlier than q_min's first certified instant: %d; later: %d" %
      (sum(r['ts'] < r['first_qmin'] for r in recs), sum(r['ts'] > r['first_qmin'] for r in recs)))
    big = [r for r in recs if r['qmin'] >= 7]
    w("\nsets with q_min >= 7: %d; by q_min %s" % (len(big), dict(sorted(Counter(r['qmin'] for r in big).items()))))
    for r in sorted(big, key=lambda r: -r['qmin'])[:40]:
        w("  %s  q_min %d first %s  | cascade t* %s = rung %d/%d + 1/(8*%d), q_c class %s, R* %s" %
          (r['S'], r['qmin'], r['first_qmin'], r['ts'], r['ic'], r['qc'], r['S'][r['h']], r['qc_class'], r['R']))
    json.dump([[list(r['S']), r['qc'], r['ic'], r['S'][r['h']], r['qmin']] for r in recs], open('rung_map_v1.json', 'w'))
    o.close()
    print(open('rung_map_v1.out').read()[len(__doc__):])
