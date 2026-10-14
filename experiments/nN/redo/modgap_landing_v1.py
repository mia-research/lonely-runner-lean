"""modgap_landing_v1 (2026-10-06): the cascade's first lonely instant t* read on the q-grids of its convergents and
intermediate fractions (the Stern-Brocot path of t*), for the stored residual members and for small sets.  Exact
(integers and Fractions); helpers in modgap_lib_v1; the statements P1-P7 are in modgap_map_v1.

Populations (built on; the rules of modgap_rule_v1 are tested on other sets):
  C    ../residual_members_C_list_v1.json, filtered by full_residual (all 22 fields)
  BS   both_shadowed_members_v1.json, filtered by full_residual
  DA   divisible_members_v2.json key A, DB key B (each also checked against full_residual)
  S1   every 7-subset of [1, 24] containing 1 (d_min = 1): 100,947 sets
  S2   every 7-subset of [1, 40] whose residues mod 8 are exactly {0, 0, 1, 2, 3, 5, 7}, gcd 1 (residual type
       (2; o,o,o,o,t) of E406)
For each set and each fraction a/q on the Stern-Brocot path of t* (every convergent; every intermediate fraction,
families with more than 50 members represented by their first 25 and last 25): the residue gap at a/q, the
displacement d*(t* - a/q) of every reading, the per-reading classes H/Z/N/W, the flags A_seg, A_tri, A_uni (lib
docstring); derivation check: each flag equals membership of a/q in [t*, t_X] (P2).  The least q with each flag is
the least denominator in [t*, t_X] (simplest(), exact); it is checked to lie on the Stern-Brocot path.
Catalogue: by the least A_seg modulus q_A (with a_A), by the case U (a unit fraction in the landing component,
P6) / M (the least-denominator rational is the opener-closer mediant of P4) / X (neither), and by the residue
pattern of the readings mod q_A.  Descent coordinates (P7) at q = 2..64 (members) or 2..16 (small sets): K_q,
whether tau_q = rho_q, i.e. whether t* is the descent instant (rho_q + K_q)/q with the quotients at their own
first lonely instant; for K_q = 0 that is t* = t*(multiples of q) (the multiples of q carry the landing).
Members only: the least modulus q <= 200 with any residue isolation a/q, and floor(q t*).
Per-member records are written to modgap_landing_v1_members.out.
"""
import sys, json, itertools, math, collections, time
from fractions import Fraction as F
from math import gcd
from functools import reduce
sys.path.insert(0, '.')
from modgap_lib_v1 import (load, full_residual, cascade, lonely, cd, frac, cascade_path, openers, component, tri_end,
                           uni_end, simplest, convergents, semiconvergent_families, stern_brocot_path, positions,
                           residue_gap, is_iso, left_end, classify, descent_coords, typ8, E8)

T0 = time.time()


def on_sb_path(x, r):
    conv, a = convergents(x)
    if (r.numerator, r.denominator) in conv:
        return 'conv'
    for (k, pp, qp, pk, qk, ak1) in semiconvergent_families(x):
        if (r.denominator - qp) % qk == 0:
            i = (r.denominator - qp) // qk
            if 0 < i < ak1 and pp + i * pk == r.numerator:
                return 'semi'
    return None


def small_q_iso(S, Q=200):
    for q in range(2, Q + 1):
        for a in range(1, q):
            if gcd(a, q) == 1 and is_iso(S, a, q):
                return a, q
    return None


def analyse(S, qd, member=False):
    t = cascade(S); path = cascade_path(S); tR, cl = component(S, t); op = openers(S, t)
    ttri = tri_end(S, t, tR); tuni = uni_end(S, t, tR)
    sA = simplest(t, tR); sT = simplest(t, ttri); sU = simplest(t, tuni)
    rec = dict(S=S, t=t, moves=len(path) - 1, tR=tR, op=op, cl=cl, sA=sA, sT=sT, sU=sU, qstar=t.denominator)
    # case U / M / X
    Js = {e: int(e * t - E8) for e in op}; Ms = {f: int(f * tR - F(7, 8)) for f in cl}
    meds = {F(Js[e] + Ms[f] + 1, e + f) for e in op for f in cl}
    rec['meds'] = meds
    if t < 1 and F(1, math.ceil(1 / tR)) >= t:
        rec['case'] = 'U'
    elif sA in meds:
        rec['case'] = 'M'
    else:
        rec['case'] = 'X'
    # Stern-Brocot path records
    sb = stern_brocot_path(t, cap=50)
    stats = collections.Counter(); dchk = []; ex = []
    for p, q, kind, k in sb:
        s = F(p, q)
        cls, seg, tri, uni = classify(S, p, q, t)
        side = 'below' if s < t else ('at' if s == t else 'above')
        g = residue_gap(S, p, q)
        stats[(side, 'iso' if g >= E8 else 'not iso')] += 1
        stats[('seg', seg)] += 1
        ok = (seg == (t <= s <= tR)) and (tri == (t <= s <= ttri)) and (uni == (t <= s <= tuni))
        if side == 'below':
            ok = ok and g < E8
        if not ok:
            dchk.append((p, q))
        if len(ex) < 6 and q > 1:
            ex.append((p, q, kind, g, {d: d * (t - s) for d in S}, cls, seg, tri, uni))
    rec['sbstats'] = stats; rec['dchk'] = dchk; rec['sbex'] = ex
    rec['onpath'] = tuple(on_sb_path(t, r) or ('t*' if r == t else None) for r in (sA, sT, sU))
    # residue pattern at q_A
    a, q = sA.numerator, sA.denominator
    rec['respat'] = tuple(sorted(d % q for d in S)); rec['pospat'] = tuple(sorted(a * d % q for d in S))
    rec['reduced'] = sum(1 for d in S if d >= q)
    rec['leftok'] = (left_end(S, a, q) == t)
    # descent coordinates
    dc = {}
    for qq in range(2, qd + 1):
        K, tau, rho = descent_coords(S, t, qq)
        if rho is not None:
            dc[qq] = (K, tau == rho)
    rec['dc'] = dc
    if member:
        rec['q0'] = small_q_iso(S)
    return rec


def s1():
    for r in itertools.combinations(range(2, 25), 6):
        yield (1,) + r


def s2():
    pools = {r: [d for d in range(1, 41) if d % 8 == r] for r in range(8)}
    for m in itertools.combinations(pools[0], 2):
        for p in itertools.product(pools[1], pools[2], pools[3], pools[5], pools[7]):
            S = tuple(sorted(m + p))
            if reduce(gcd, S) == 1:
                yield S


store = json.load(open('divisible_members_v2.json'))
pops = [('C', [S for S in dict.fromkeys(load('../residual_members_C_list_v1.json')) if full_residual(S)], 64, True),
        ('BS', [S for S in dict.fromkeys(load('both_shadowed_members_v1.json')) if full_residual(S)], 64, True),
        ('DA', list(dict.fromkeys(tuple(sorted(S)) for S in store['A'])), 64, True),
        ('DB', list(dict.fromkeys(tuple(sorted(S)) for S in store['B'])), 64, True),
        ('S1', list(s1()), 16, False),
        ('S2', list(s2()), 16, False)]

out = open('modgap_landing_v1.out', 'w'); out.write(__doc__ + "\n")
mout = open('modgap_landing_v1_members.out', 'w')
mout.write("modgap_landing_v1 per-member records (exact).  Fields: population, index, readings' digit count (max), "
           "CF of t* as digit counts of the partial quotients, case, q_A (digits) and a_A, q_tri (digits), q_uni "
           "(digits), q* = denominator of t* (digits), opener classes mod 8 (m/o/t/f), carriers q <= 64 with "
           "t* = rho_q/q, least residue isolation a0/q0 with q0 <= 200 and floor(q0 t*), moves.\n")


def w(s):
    out.write(s + "\n"); out.flush()


for name, sets, qd, member in pops:
    if name in ('DA', 'DB'):
        nfr = sum(1 for S in sets if full_residual(S))
    else:
        nfr = len(sets)
    recs = [analyse(S, qd, member) for S in sets]
    w("\n==== %s: %d sets (full_residual %d)   [elapsed %ds]" % (name, len(sets), nfr, time.time() - T0))
    # derivation checks
    nd = sum(1 for r in recs if r['dchk']); nsb = sum(sum(v for (kk, vv), v in r['sbstats'].items() if kk == 'seg') for r in recs)
    w("  derivation check, flags = interval membership (P2) and no residue isolation below t* (P1), over %d "
      "Stern-Brocot fractions: sets with a failure %d" % (nsb, nd))
    w("  least-q rationals on the Stern-Brocot path of t* (A_seg, A_tri, A_uni): %s" %
      dict(collections.Counter(r['onpath'] for r in recs)))
    w("  left end of the q_A component = t* (P3): [T %d/%d]" % (sum(r['leftok'] for r in recs), len(recs)))
    side = collections.Counter()
    for r in recs:
        side.update({k: v for k, v in r['sbstats'].items() if k[0] != 'seg'})
    w("  Stern-Brocot fractions by side of t* and residue isolation: %s" % dict(sorted(side.items())))
    cases = collections.Counter(r['case'] for r in recs)
    w("  cases: U (unit fraction in the landing component) %d, M (opener-closer mediant) %d, X (neither) %d" %
      (cases['U'], cases['M'], cases['X']))
    eqA = collections.Counter((r['sA'] == r['t'], r['sT'] == r['t'], r['sU'] == r['t']) for r in recs)
    w("  least accounting rational equal to t* itself (A_seg, A_tri, A_uni): %s" % dict(eqA))
    uo = collections.Counter((r['sU'] != r['t'], tuple(r['op']) == (max(r['S']),)) for r in recs)
    w("  (A_uni least rational != t*, unique opener = d_max): %s" % dict(uo))
    if not member:
        cA = collections.Counter((r['sA'].numerator, r['sA'].denominator) for r in recs)
        w("  catalogue by the least A_seg rational a_A/q_A (count): %s" %
          ', '.join('%d/%d:%d' % (a, q, c) for (a, q), c in sorted(cA.items(), key=lambda x: (x[0][1], x[0][0]))))
        cq = collections.Counter((r['sA'].denominator, r['case']) for r in recs)
        w("  by q_A and case: %s" % ', '.join('%d%s:%d' % (q, c, n) for (q, c), n in sorted(cq.items())))
        cT = collections.Counter(r['sT'].denominator for r in recs); cU = collections.Counter(r['sU'].denominator for r in recs)
        w("  least A_tri modulus (count): %s" % dict(sorted(cT.items())))
        w("  least A_uni modulus (count): %s" % dict(sorted(cU.items())))
        rq = collections.Counter((r['sA'].denominator, r['reduced'], len(set(r['pospat']))) for r in recs)
        w("  by (q_A, readings >= q_A [reduced by D_max at modulus q_A], distinct positions at a_A/q_A): %s" %
          ', '.join('%s:%d' % (k, v) for k, v in sorted(rq.items())))
        pats = collections.defaultdict(collections.Counter)
        for r in recs:
            pats[r['sA'].denominator][r['respat']] += 1
        w("  residue patterns mod q_A: number of distinct patterns per q_A, and the three most frequent:")
        for q in sorted(pats):
            top = pats[q].most_common(3)
            w("    q_A = %d: %d sets, %d patterns; %s" % (q, sum(pats[q].values()), len(pats[q]), top))
        rat = collections.Counter()
        for r in recs:
            mq = min(m.denominator for m in r['meds'])
            rat[('q_A = q*' if r['sA'].denominator == r['qstar'] else 'q_A < q*',
                 'q_A = min mediant modulus' if r['sA'].denominator == mq else 'q_A < min mediant modulus')] += 1
        w("  q_A against q* (denominator of t*) and the mediant modulus: %s" % dict(rat))
    # descent coordinates
    dk = collections.Counter(); deq = collections.Counter(); anyeq = 0
    for r in recs:
        hit = False
        for qq, (K, eq) in r['dc'].items():
            dk[(qq, K)] += 1
            if eq:
                deq[(qq, K)] += 1; hit = True
        anyeq += hit
    qs = sorted({qq for qq, K in dk})
    w("  descent coordinates (P7), per q: [sets with a multiple of q, {K_q: sets}, {K_q: sets with tau_q = rho_q}]:")
    line = []
    for qq in qs:
        tot = {K: n for (q2, K), n in dk.items() if q2 == qq}; eqs = {K: n for (q2, K), n in deq.items() if q2 == qq}
        line.append("q=%d:[%d,%s,%s]" % (qq, sum(tot.values()), dict(sorted(tot.items())), dict(sorted(eqs.items()))))
    for i in range(0, len(line), 6):
        w("    " + "  ".join(line[i:i + 6]))
    w("  sets with tau_q = rho_q for some q in [2, %d]: %d of %d" % (qd, anyeq, len(recs)))
    if member:
        q0 = collections.Counter(r['q0'][1] if r['q0'] else None for r in recs)
        k0 = collections.Counter(math.floor(r['q0'][1] * r['t']) if r['q0'] else None for r in recs)
        w("  least modulus q0 <= 200 with a residue isolation: %s; floor(q0 t*): %s" % (dict(sorted(q0.items(), key=str)), dict(k0)))
        cfs = collections.Counter(len(convergents(r['t'])[1]) for r in recs)
        a1 = collections.Counter((convergents(r['t'])[1][0], len(str(convergents(r['t'])[1][1]))) for r in recs)
        w("  CF length of t*: %s; (a_0, digits of a_1): %s" % (dict(sorted(cfs.items())), dict(sorted(a1.items()))))
        aA = collections.Counter((r['sA'].numerator, r['case']) for r in recs)
        pk = collections.Counter()
        for r in recs:
            eps = 1 - (r['sA'] - r['t']) / (r['tR'] - r['t'])     # 0 when 1/q_A sits at the right end t_R
            k = 0
            while eps * 10 ** (k + 1) < 1 and k < 60: k += 1
            pk[k] += 1
        w("  position of 1/q_A in the landing component: (t_R - 1/q_A)/(t_R - t*) < 10^-k, sets by k: %s" % dict(sorted(pk.items())))
        w("  (a_A, case): %s" % dict(aA))
        dig = collections.Counter((len(str(r['sA'].denominator)), len(str(max(r['S'])))) for r in recs)
        w("  (digits of q_A, digits of d_max): %s" % dict(sorted(dig.items())))
        car = collections.Counter(tuple(q for q, (K, eq) in r['dc'].items() if eq)[:1] for r in recs)
        w("  least carrier q (t* = rho_q/q) in [2, 64] (count): %s" % dict(sorted(car.items(), key=str)))
        ocl = collections.Counter((tuple(typ8(e) for e in r['op']), bool(tuple(q for q, (K, eq) in r['dc'].items() if eq))) for r in recs)
        w("  (opener class mod 8, some carrier q in [2,64]): %s" % dict(ocl))
        for i, r in enumerate(recs):
            pq = convergents(r['t'])[1]
            car = [q for q, (K, eq) in r['dc'].items() if eq]
            mout.write("%s %d dmax_digits=%d cf=%s case=%s qA=%dd/a=%d qtri=%dd/a=%d quni=%dd/a=%d qstar=%dd op=%s carriers=%s "
                       "q0=%s floor(q0 t*)=%s moves=%d\n" %
                       (name, i, len(str(max(r['S']))), [len(str(x)) for x in pq], r['case'], len(str(r['sA'].denominator)),
                        r['sA'].numerator, len(str(r['sT'].denominator)), r['sT'].numerator, len(str(r['sU'].denominator)),
                        r['sU'].numerator, len(str(r['qstar'])), ''.join(typ8(e) for e in r['op']), car,
                        ('%d/%d' % r['q0']) if r['q0'] else None, math.floor(r['q0'][1] * r['t']) if r['q0'] else None,
                        r['moves']))
    # examples with every displacement written out
    W = (lambda x: mout.write(x + "\n")) if member else w
    W("  %s examples (first two sets): t*, t_R, openers, closers, and the first Stern-Brocot fractions with q > 1, "
      "with every displacement d(t* - a/q):" % name)
    for r in recs[:2]:
        W("    S = %s" % (r['S'],))
        W("      t* = %s, t_R = %s, openers %s, closers %s, q_A rational %s, case %s" % (r['t'], r['tR'], r['op'], r['cl'], r['sA'], r['case']))
        for p, q, kind, g, disp, cls, seg, tri, uni in r['sbex'][:4]:
            W("      %s %d/%d: residue gap %s; displacements %s; classes %s; A_seg %s A_tri %s A_uni %s" %
              (kind, p, q, g, {d: str(v) for d, v in disp.items()}, ''.join(cls[d] for d in r['S']), seg, tri, uni))
mout.close()
w("\ntotal elapsed %ds" % (time.time() - T0))
out.close()
print(open('modgap_landing_v1.out').read()[len(__doc__):])
