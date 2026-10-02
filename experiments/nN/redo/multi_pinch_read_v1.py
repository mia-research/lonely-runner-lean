"""E277/E278 (2026-10-02): the multi-pinches of E178 read.  Design and derivation: log E277.

Same path (WindowPinchN's deformation from the AP 1..7), same populations and event location as deform_pinch_v1.  At each
event with a MULTI pinch (not exactly one reading on +1/8 and one on -1/8): Lambda (leaving, position k_i + 1/8), E (entering,
k_j + 7/8), relative rates u_i = e_i / d_i (e_i = x_i - i).  First-order criterion (derived, E277), for a step sigma = +-1 in s:
  original window non-empty  iff  sigma=+1: min_L u >= max_E u ;  sigma=-1: max_L u <= min_E u
  mirror window (t -> P - t, laps k~_i = d_i P - k_i - 1) non-empty iff  sigma=+1: min_E u >= max_L u ;  sigma=-1: max_E u <= min_L u
CHECK: the criterion against the exact test (feasible() at s0 + sigma*delta, delta = 1e-9) for the pinching and the mirror
assignment, every non-tied event (ties listed).  Then, per event, the lost side (death: sigma=+1; birth: sigma=-1): does the
mirror reopen; if neither reopens, the protecting windows (positive width at tau): AP-origin, earlier/later than t0 in R, contains
P - t0, at a recurrence time t0 + j/(d_a - d_b) of a doubled pair on one edge, otherwise (listed)."""
import sys, math, random, itertools
from fractions import Fraction as F
from collections import Counter
from multiprocessing import Pool
import deform_pinch_v1 as D
from deform_pinch_v1 import readings_at, components, laps, feasible, first_window, classify, NGRID, EPS, cascade_landing

DEL = F(1, 10 ** 9)


def ext(x, sa, ka, sb, kb):
    rec = classify(x, sa, ka, sb, kb)
    if rec.get('tau') is None or rec['simple']:
        return rec
    kind = rec['kind']; k = ka if kind == 'death' else kb
    tau = rec['tau']; t0 = rec['t0']; ds = readings_at(x, tau)
    pos = [d * t0 - math.floor(d * t0) for d in ds]
    L = [i for i, p in enumerate(pos) if p == F(1, 8)]; Ee = [i for i, p in enumerate(pos) if p == F(7, 8)]
    e = [x[i - 1] - i for i in range(1, 8)]
    u = [e[i] / ds[i] for i in range(7)]
    q = 1
    for d in ds: q = q * d.denominator // math.gcd(q, d.denominator)
    g = 0
    for d in ds: g = math.gcd(g, int(d * q))
    P = F(q, g)
    kt = tuple(int(d * P) - ki - 1 for d, ki in zip(ds, k))
    def pred(sig):
        if sig == 1: a = (min(u[i] for i in L), max(u[j] for j in Ee)); m = (min(u[j] for j in Ee), max(u[i] for i in L))
        else: a = (max(u[j] for j in Ee), min(u[i] for i in L)); m = (max(u[i] for i in L), min(u[j] for j in Ee))
        # original: sig=+1 min_L >= max_E ; sig=-1 max_L <= min_E.  recompute properly below
        return None
    uL = [u[i] for i in L]; uE = [u[j] for j in Ee]
    def pr(sig):
        if sig == 1:
            o = (min(uL), max(uE), 'ge'); m = (min(uE), max(uL), 'ge')
        else:
            o = (max(uL), min(uE), 'le'); m = (max(uE), min(uL), 'le')
        res = []
        for lhs, rhs, op in (o, m):
            if lhs == rhs: res.append(None)
            else: res.append(lhs > rhs if op == 'ge' else lhs < rhs)
        return res
    out = dict(rec); out.update(k=k, L=L, E=Ee, u=[float(v) for v in u], uL=[float(v) for v in uL], uE=[float(v) for v in uE])
    ex = {}
    for sig in (1, -1):
        s = tau + sig * DEL
        dsx = readings_at(x, s)
        ex[sig] = (feasible(dsx, k)[0], feasible(dsx, kt)[0], pr(sig))
    out['ex'] = ex
    lost = 1 if kind == 'death' else -1
    out['lost'] = lost
    out['mirror_reopens'] = ex[lost][1]
    # interleaving on the lost side: neither reopens
    if not out['mirror_reopens']:
        comps = components(ds, need=4)
        wide = [c for c in comps if c[1] > c[0]]
        ap = readings_at(x, F(0))
        pairs = [(a, b) for a, b in itertools.combinations(L, 2)] + [(a, b) for a, b in itertools.combinations(Ee, 2)]
        prot = []
        for lo, hi in wide:
            kp = laps(ds, (lo + hi) / 2)
            cls = []
            if feasible(ap, kp)[0]: cls.append('AP-origin')
            cls.append('earlier' if lo < t0 else 'later')
            if lo <= P - t0 <= hi: cls.append('mirror')
            for a, b in pairs:
                gg = ds[a] - ds[b]
                if gg != 0:
                    gg = abs(gg); j = math.ceil((lo - t0) * gg)
                    if j != 0 and t0 + F(j) / gg <= hi: cls.append('recurrence'); break
            prot.append((float(8 * min(ds) * lo), float(8 * min(ds) * hi), tuple(cls)))
        out['prot'] = prot
        out['R0'] = float(8 * min(ds) * t0)
    return out


def events(x, sa, ka, sb, kb, out, depth=0):
    if ka == kb: return
    if sb - sa < EPS or depth > 60:
        out.append(ext(x, sa, ka, sb, kb)); return
    sm = (sa + sb) / 2; km = first_window(x, sm)
    events(x, sa, ka, sm, km, out, depth + 1); events(x, sm, km, sb, kb, out, depth + 1)


def follow(S):
    S = sorted(S); x = [F(7 * d, S[-1]) for d in S]
    grid = [F(j, NGRID) for j in range(NGRID + 1)]; ks = []
    for s in grid:
        ds = readings_at(x, s); comps = components(ds, need=1); ks.append(laps(ds, comps[0][0]))
    ev = []
    for j in range(NGRID): events(x, grid[j], ks[j], grid[j + 1], ks[j + 1], ev)
    return dict(S=tuple(S), events=ev)


def work(sets): return [follow(S) for S in sets]


if __name__ == '__main__':
    sys.path.insert(0, '../band_cert_v1')
    from coverB_fine_v1 import late_shapes
    out = open('multi_pinch_read_v1.out', 'w'); out.write(__doc__ + "\n")
    def w(s): out.write(s + "\n"); out.flush()
    caseB = [T for T in itertools.combinations(range(1, 25), 7) if 7 * T[0] < T[-1]][::100]
    rng = random.Random(13); caseC = []
    while len(caseC) < 500:
        T = tuple(sorted(rng.sample(range(1, 201), 7)))
        if T[-1] > 24 * T[0]: caseC.append(T)
    late = late_shapes()[::10]
    with Pool(10) as pool:
        for name, sets in [('Case B to 24, every 100th', caseB), ('late band shapes, every 10th', late), ('Case C sample (500)', caseC)]:
            res = [r for part in pool.map(work, [sets[i::64] for i in range(64)]) for r in part]
            ev = [(r['S'], e) for r in res for e in r['events'] if e.get('tau') is not None]
            multi = [(S, e) for S, e in ev if not e['simple']]
            w("\n== %s == paths %d, events %d, simple %d, multi %d" % (name, len(res), len(ev), len(ev) - len(multi), len(multi)))
            w("  multi by (|Lambda|, |E|): %s" % dict(Counter((len(e['L']), len(e['E'])) for S, e in multi)))
            mism = 0; tied = 0; chk = 0
            for S, e in multi:
                for sig in (1, -1):
                    oex, mex, (po, pm) = e['ex'][sig]
                    for ex_, p_ in ((oex, po), (mex, pm)):
                        if p_ is None: tied += 1
                        else:
                            chk += 1
                            if bool(ex_) != bool(p_): mism += 1
            w("  CHECK first-order criterion vs exact feasible at s0 +- 1e-9: %d comparisons, %d mismatches; tied (not decided at first order): %d" % (chk, mism, tied))
            lostside = Counter()
            for S, e in multi:
                lostside[(e['kind'], 'mirror reopens' if e['mirror_reopens'] else 'neither reopens')] += 1
            w("  lost side: %s" % dict(lostside))
            nr = [(S, e) for S, e in multi if not e['mirror_reopens']]
            w("  events where neither the instant nor its mirror reopens (interleaving): %d" % len(nr))
            pc = Counter(); unprot = 0; classes = Counter()
            for S, e in nr:
                if not e.get('prot'): unprot += 1
                for p in e.get('prot', []): classes[p[2]] += 1
            w("  of these with no positive-width window at tau: %d; protector windows by class: %s" % (unprot, dict(classes.most_common(12))))
            for S, e in nr[:40]:
                w("    %s %s |L|=%d |E|=%d uL=%s uE=%s R0=%.3f protectors: %s" % (S, e['kind'], len(e['L']), len(e['E']), [round(v, 4) for v in e['uL']], [round(v, 4) for v in e['uE']], e['R0'], e.get('prot', [])[:4]))
    out.close(); print(open('multi_pinch_read_v1.out').read()[len(__doc__):])
