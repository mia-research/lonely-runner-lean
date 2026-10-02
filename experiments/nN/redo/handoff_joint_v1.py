"""E267/E268 (2026-10-02): Test 2 of log E267.  (a) hand-off occupants by |eps| weighted by openings covered; (b) state patterns over the
six flanks; (c) clusters built with twin chains at the top: flank patterns, and whether rank 1 is free when flanks 2..6 are all shadowed."""
import sys, os, json, random
from collections import Counter
from multiprocessing import Pool
HERE = os.path.dirname(os.path.abspath(__file__)); os.chdir(HERE); sys.path.insert(0, '../band_cert_v1'); sys.path.insert(0, HERE)
from hole_C1_flanks_v1 import flank
from slow_flank_mech_v1 import rand_cluster, run_us
from slow_flank_mech_v2 import valid
BINS = [(0, .05), (.05, .15), (.15, .35), (.35, .45), (.45, .5001)]
def binof(a):
    for i, (lo, hi) in enumerate(BINS):
        if lo <= a < hi: return i


def read(item):
    c, cl = item; cl = list(cl); pat = []; hist = Counter(); nho = 0; seg = Counter()
    for i, e in enumerate(cl):
        r = flank(c, cl, e)
        if r.get('state') == 'err': return None
        pat.append({'free': 'F', 'alone': 'A', 'handoff': 'H'}[r['state']])
        if r['state'] == 'handoff':
            nho += 1
            for (ln, idx, A, A8, eps, q) in r['occ']:
                hist[binof(abs(eps))] += ln; hist[('seg', binof(abs(eps)))] += 1
    return ''.join(pat), hist, nho


def chain_cluster(rnd, k):
    c = rnd.randrange(10**6, 10**7); lo = 25 * c; span = rnd.choice((1.5, 2, 3, 5, 8))
    top = rnd.randrange(lo, int(lo * span)) + 6 * c
    chain = [top]
    for _ in range(k): chain.append(chain[-1] - int(rnd.uniform(0.02, 0.30) * c))
    rest = [rnd.randrange(lo, max(lo + 1, min(chain))) for _ in range(5 - k)]
    cl = sorted(chain + rest)
    return c, cl


def chain_job(args):
    k, seed = args; rnd = random.Random(seed); rows = []
    for _ in range(4000):
        c, cl = chain_cluster(rnd, k)
        if len(set(cl)) < 6 or min(cl) < 25 * c or not valid(c, cl): continue
        rows.append((k, ''.join({'free': 'F', 'alone': 'A', 'handoff': 'H'}[flank(c, cl, e)['state']] for e in cl)))
    return rows


def rjob(seed):
    rnd = random.Random(seed); rows = []
    for _ in range(300):
        c, cl = rand_cluster(rnd)
        if len(set(cl)) < 6 or not valid(c, cl): continue
        rows.append((c, tuple(cl)))
    return rows


if __name__ == '__main__':
    items = [tuple(i[:2]) + (tuple(i[2]),) for i in json.load(open('members_5978_v1.json'))]
    out = open('handoff_joint_v1.out', 'w'); out.write(__doc__ + "\n")
    def w(s): out.write(s + "\n"); out.flush()
    with Pool(10) as pool:
        M = pool.map(read, [(S[0], S[1:]) for _, _, S in items], chunksize=40)
        R_ = [x for part in pool.map(rjob, range(40)) for x in part]
        RR = pool.map(read, R_, chunksize=40)
        for name, res in (('members', M), ('random clusters', RR)):
            res = [r for r in res if r]
            h = Counter()
            for _, hh, _ in res: h.update(hh)
            segs = {"%.2f-%.2f" % BINS[i]: h[('seg', i)] for i in range(5)}
            w("(a') %s: hand-off segments by |eps| bin of the occupant: %s" % (name, segs))
            tot = sum(v for k, v in h.items() if not isinstance(k, tuple))
            w("(a) %s: %d; hand-off flanks %d; openings covered by occupants, by |eps| bin: %s" % (name, len(res), sum(n for _, _, n in res),
              {"%.2f-%.2f" % BINS[i]: (h[i], round(h[i] / tot, 3)) for i in range(5)} if tot else {}))
            pc = Counter(p for p, _, _ in res)
            w("(b) %s: shadowed flanks per set: %s; patterns (F free, A one walker, H hand-off; rank 1..6), most common 14: %s" % (
                name, dict(sorted(Counter(sum(1 for ch in p if ch != 'F') for p in pc.elements()).items())), pc.most_common(14)))
            w("    sets with the most shadowed flanks: %s" % [(p, n) for p, n in sorted(pc.items(), key=lambda kv: -sum(1 for ch in kv[0] if ch != 'F'))[:6]])
        rows = [r for part in pool.map(chain_job, [(k, 900 + 10 * k + s) for k in range(1, 6) for s in range(10)]) for r in part]
    w("\n(c) clusters with a twin chain of k links at the top (gaps 0.02c..0.30c), c never in the way")
    for k in range(1, 6):
        X = [p for kk, p in rows if kk == k]
        pc = Counter(X)
        w("  k=%d: %d sets; shadowed flanks per set %s; rank 1 free in %d; flanks 2..6 all shadowed in %d (rank 1 free in %d of those); patterns %s" % (
            k, len(X), dict(sorted(Counter(sum(1 for ch in p if ch != 'F') for p in X).items())), sum(1 for p in X if p[0] == 'F'),
            sum(1 for p in X if all(ch != 'F' for ch in p[1:])), sum(1 for p in X if all(ch != 'F' for ch in p[1:]) and p[0] == 'F'), pc.most_common(6)))
    out.close(); print(open('handoff_joint_v1.out').read()[len(__doc__):])
