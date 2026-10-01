"""E240/E241 (2026-10-01): the record of every isolation, not only the cascade's.  Design: log E240.

Owner: "Maybe we should be keeping a record of what other isolations there are other than the one cascade points to".
Whole-number readings: the lonely set has period 1 and is symmetric about 1/2, so (0, 1/2] holds every isolation up to
those two maps (GrandReturnN.exists_lonely_iff_half).  Populations: the hole configurations of E233 (f = 3, 2,000) and
E235 (f = 4, 5, 6, 1,000 each).
Per configuration, written to hole_isolations_f<f>_v1.jsonl.gz (one JSON object per line; readings by rank in S,
0-based; an instant is named by [rank, lap]: an exit (8K+1)/(8d) on the left, an entering edge (8K+7)/(8d) on the right,
[-1, -1] for the cut at 1/2 or none):
  'st' rows [left rank, left lap, right rank, right lap, holds, g rank, g lap] for every core stretch in (0, 1/2];
  'iso10' for each of the first ten stretches, its isolations as [left rank, left lap, right rank, right lap];
  'cascade' [stretch index, rank, lap].  In words:
  - every core lonely stretch S_k in (0, 1/2]: its ends, each named by its certificate (reading, lap, edge: 'x' exit
    8K+1, 'e' entering edge 8K+7, or 'half' for the cut at 1/2);
  - for every stretch, the block's relay landing from the stretch's start, g_k, named by (reading, lap), and whether it
    lies in S_k (then S_k holds an isolation and g_k is its first; otherwise S_k holds none: g_k is the first block-clear
    instant at or after the start);
  - for the first ten stretches, every isolation in the stretch, each named by its left end (an exit) and right end;
  - the cascade's isolation (its stretch index and certificate).
The full files (about 45 MB) regenerate exactly from this seeded script and are kept on disk, not committed; the committed
record is hole_isolations_subset_v1.jsonl.gz: the first 100 configurations of each f and every configuration whose
cascade lands beyond S_0.
Checks: I1 the cascade's isolation is the first recorded one (A.9); I2 in the first ten stretches the first isolation
found by the clear set (no cascade) is g_k, and the stretch holds none exactly when g_k lies past its end; I3 every
recorded isolation is lonely at its left end (exact).  The .out reports places and lists, not totals of time or shares.
"""
import sys, json, gzip
from fractions import Fraction as F
from collections import Counter
from multiprocessing import Pool
sys.path.insert(0, '../band_cert_v1'); from core import clear_set
from e151_block_v1 import trace
from quantity_tests_v1 import cd, E8
import hole3_cascade_v1 as H3, holef_cascade_v1 as HF
from hole_perturb_v2 import relay

HALF = F(1, 2)


def cert(S, t, kind):
    """Name instant t as an exit ('x', 8K+1) or entering edge ('e', 8K+7) of a reading of S."""
    for d in S:
        p = 8 * d * t
        if p.denominator == 1:
            r = int(p) % 8
            if kind == 'x' and r == 1:
                return [int(d), (int(p) - 1) // 8, 'x']
            if kind == 'e' and r == 7:
                return [int(d), (int(p) - 7) // 8, 'e']
    return None


def lonely(S, t):
    return all(cd(d * t) >= E8 for d in S)


def study(args):
    f, core, block = args
    core = tuple(sorted(core)); block = tuple(sorted(block)); S = tuple(sorted(core + block))
    ix = {d: i for i, d in enumerate(S)}
    enc = lambda c: [ix[c[0]], c[1]] if isinstance(c, list) else [-1, -1]
    tc, _ = trace(core); ts, _ = trace(S)
    chk = Counter()
    stretches = [(a / 8, b / 8) for a, b in clear_set(list(core), 8 * tc, 8 * HALF)]
    st = []; iso10 = []; first_iso = None
    for k, (a, b) in enumerate(stretches):
        ca = cert(core, a, 'x'); cb = cert(core, b, 'e') if b < HALF else 'half'
        g, gm = relay(block, a)
        holds = g <= b
        gc = (cert(S, g, 'x') if g > a else ca) if holds else None
        if ca is None or (cb != 'half' and cb is None) or (holds and gc is None):
            chk['certificate not found'] += 1
        st.append(enc(ca) + enc(cb) + [1 if holds else 0] + enc(gc))
        if holds and first_iso is None:
            first_iso = (k, g, gc)
        if holds and not lonely(S, g):
            chk['I3'] += 1
        if k < 10:
            isos = [(lo / 8, hi / 8) for lo, hi in clear_set(list(block), 8 * a, 8 * b)]
            if (len(isos) > 0) != holds or (holds and isos[0][0] != g):
                chk['I2'] += 1
            iso10.append([enc(cert(S, lo, 'x') if lo > a else ca) + enc(cert(S, hi, 'e') if hi < b else cb) for lo, hi in isos])
            for lo, hi in isos:
                if not lonely(S, lo):
                    chk['I3'] += 1
    if first_iso is None or first_iso[1] != ts:
        chk['I1'] += 1
    return dict(f=f, S=[int(d) for d in S], ncore=len(core), cascade=[first_iso[0]] + enc(first_iso[2]) if first_iso else None,
                st=st, iso10=iso10), chk


if __name__ == '__main__':
    pops = {3: H3.gen(232, 2000)}
    for f in (4, 5, 6):
        pops[f] = HF.gen(f, 234 + f, 1000)[0]
    out = open('hole_isolations_v1.out', 'w'); out.write(__doc__ + "\n"); w = lambda s: (out.write(s + "\n"), out.flush())
    sub = gzip.open('hole_isolations_subset_v1.jsonl.gz', 'wt')
    for f in (3, 4, 5, 6):
        with Pool(8) as pool:
            res = pool.map(study, [(f, c, b) for c, b in pops[f]], chunksize=10)
        ck = Counter()
        with gzip.open('hole_isolations_f%d_v1.jsonl.gz' % f, 'wt') as z:
            for i, (r, c) in enumerate(res):
                ck.update(c); z.write(json.dumps(r) + "\n")
                if i < 100 or (r['cascade'] and r['cascade'][0] > 0):
                    sub.write(json.dumps(r) + "\n")
        w("\n== f = %d: %d configurations ==" % (f, len(res)))
        w("  CHECKS I1, I2, I3: %s" % (dict(ck) if ck else '0 failures'))
        w("  core stretches in (0, 1/2] per configuration, least and greatest: %d, %d" % (
            min(len(r['st']) for r, c in res), max(len(r['st']) for r, c in res)))
        w("  stretch index of the cascade's isolation: %s" % dict(sorted(Counter(r['cascade'][0] for r, c in res).items())))
        nohold = Counter(sum(1 for s in r['st'] if not s[4]) for r, c in res)
        w("  configurations by the number of core stretches in (0, 1/2] holding no isolation: %s" % dict(sorted(nohold.items())))
        w("  the first ten stretches, holding (1) or not (0): configurations by pattern, most common 12: %s" % Counter(
            ''.join(str(s[4]) for s in r['st'][:10]) for r, c in res).most_common(12))
        w("  isolations in each of the first ten stretches (configurations by count, stretch 0 .. 9): %s" % [
            dict(sorted(Counter(len(r['iso10'][k]) for r, c in res if k < len(r['iso10'])).items())) for k in range(10)])
    sub.close()
    out.close()
    print(open('hole_isolations_v1.out').read()[len(__doc__):])
