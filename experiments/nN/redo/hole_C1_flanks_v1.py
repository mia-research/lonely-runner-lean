"""E259/E260 (2026-10-02): phase 3c's flank reading (E253, E258) on the open configurations: E118's C1 members of
EightResidual (residual_members_C_list_v1.json; mode A collider least, mode B collider in the cluster).  Design: log E259.

c = the least reading; the six others are the cluster's flanks.  At each flank e, c's band run u = 8k + 1 in [e/c, 7e/c];
a walker x_j is in the way at u iff x_j u mod 8e is outside [e, 7e] (Theorem 6.14).  Per flank: first clear opening, or
shadowed across the run; a shadowed flank is one walker throughout (A, A mod 8, eps with x_j/e = A + eps; |x_j - A e|/c)
or a hand-off (least number s of consecutive segments with one walker each; occupants' (A, eps)); alternating occupants'
nearest q <= 8 fraction against the exact uniform null of E258.  The fastest flank's state.
Checks: c never in the way inside its run; the earliest first-clear cluster-flank opening is the cascade's landing (any
member whose landing is not at a cluster flank is listed); lonely there.
"""
import sys, json, math
from fractions import Fraction as F
from collections import Counter
from multiprocessing import Pool
sys.path.insert(0, '../band_cert_v1')
from e151_block_v1 import trace
from quantity_tests_v1 import cd, E8
from hole6_handoff_v2 import nearest, null_by_q


def inway(x, u, e):
    r = (x * u) % (8 * e)
    return r < e or r > 7 * e


def lonely(S, t):
    return all(cd(d * t) >= E8 for d in S)


def flank(c, cl, e):
    k0 = -((-(e - c)) // (8 * c)); k1 = (7 * e - c) // (8 * c)   # u = 8k+1 in [e/c, 7e/c]
    us = [8 * k + 1 for k in range(k0, k1 + 1)]
    sets = []
    for i, u in enumerate(us):
        if inway(c, u, e):
            return dict(err='c in the way inside its run')
        ins = [x for x in cl if x != e and inway(x, u, e)]
        if not ins:
            return dict(state='free', idx=i, t=F(u, 8 * e), n=len(us))
        sets.append(set(ins))
    common = set.intersection(*sets)
    if common:
        x = min(common); A = round(F(x, e)); eps = F(x, e) - A
        return dict(state='alone', n=len(us), walker=(cl.index(x) + 1, A, A % 8, float(eps), float(abs(x - A * e)) / c))
    segs = []; cur = set(sets[0]); start = 0
    for i in range(1, len(sets)):
        nxt = cur & sets[i]
        if nxt:
            cur = nxt
        else:
            segs.append((start, i - 1, min(cur))); start = i; cur = set(sets[i])
    segs.append((start, len(sets) - 1, min(cur)))
    occ = []
    for a, b, x in segs:
        A = round(F(x, e)); eps = F(x, e) - A
        f = F(x, e) - math.floor(F(x, e))
        occ.append((b - a + 1, cl.index(x) + 1, A, A % 8, float(eps), nearest(f)[1]))
    return dict(state='handoff', n=len(us), s=len(segs), occ=occ)


def study(S):
    S = tuple(sorted(S)); c = S[0]; cl = list(S[1:]); chk = Counter()
    fl = {}
    for e in cl:
        r = flank(c, cl, e)
        if 'err' in r:
            chk[r['err']] += 1; r = dict(state='err')
        fl[e] = r
    ts, _ = trace(S)
    clear = [r['t'] for r in fl.values() if r.get('state') == 'free']
    land_ok = bool(clear) and min(clear) == ts
    if land_ok and not lonely(S, ts):
        chk['not lonely at the landing'] += 1
    return dict(S=S, chk=chk, land_ok=land_ok, R=float(8 * c * ts), fl=fl, ratio_min=float(F(cl[0], c)),
                fast=fl[cl[-1]]['state'], fast_detail=fl[cl[-1]])


if __name__ == '__main__':
    M = json.load(open('../residual_members_C_list_v1.json'))
    out = open('hole_C1_flanks_v1.out', 'w'); out.write(__doc__ + "\n"); w = lambda s: (out.write(s + "\n"), out.flush())
    meas, near = null_by_q()
    for mode in 'AB':
        with Pool(8) as pool:
            res = pool.map(study, [tuple(S) for S in M[mode]])
        ck = Counter()
        for r in res:
            ck.update(r['chk'])
        w("\n== mode %s (%s): %d members ==" % (mode, 'collider = least reading' if mode == 'A' else 'collider inside the cluster', len(res)))
        w("  CHECKS: %s" % (dict(ck) if ck else '0 failures'))
        nl = [r for r in res if not r['land_ok']]
        w("  landing not at the earliest first-clear cluster-flank opening (listed, not forced): %d %s" % (len(nl), [(r['S'][:3], round(r['R'], 3)) for r in nl[:5]]))
        w("  least cluster reading / c: min %.2f, max %.2f" % (min(r['ratio_min'] for r in res), max(r['ratio_min'] for r in res)))
        w("  shadowed cluster flanks per member (of 6): %s" % dict(sorted(Counter(sum(1 for v in r['fl'].values() if v['state'] in ('alone', 'handoff')) for r in res).items())))
        w("  shadowed flanks by rank (1 = slowest of the cluster): %s" % dict(sorted(Counter(sorted(r['S'][1:]).index(e) + 1 for r in res for e, v in r['fl'].items() if v['state'] in ('alone', 'handoff')).items())))
        al = [v['walker'] for r in res for v in r['fl'].values() if v['state'] == 'alone']
        w("  one walker throughout: %d; (A mod 8, sign of eps): %s; |x_j - A e| / c (tenths): %s" % (
            len(al), dict(Counter((a8, '+' if eps > 0 else '-') for rk, A, a8, eps, d in al)), dict(sorted(Counter(int(10 * d) / 10 for rk, A, a8, eps, d in al).items()))))
        ho = [v for r in res for v in r['fl'].values() if v['state'] == 'handoff']
        w("  hand-offs: %d; segments s: %s" % (len(ho), dict(sorted(Counter(v['s'] for v in ho).items()))))
        alt = [o for v in ho for o in v['occ'] if o[0] <= 2]
        if alt:
            qc = Counter(o[5] for o in alt)
            w("  alternating occupants (segments of 1-2): %d; nearest q: %s; uniform expectation: %s" % (
                len(alt), dict(sorted(qc.items())), {q: round(float(m) * len(alt), 1) for q, m in sorted(meas.items())}))
        w("  the fastest flank: %s" % dict(Counter(r['fast'] for r in res)))
        for r in res:
            if r['fast'] != 'free':
                w("    fastest flank not free: %s  %s" % (r['S'], r['fast_detail']))
    out.close()
    print(open('hole_C1_flanks_v1.out').read()[len(__doc__):])
