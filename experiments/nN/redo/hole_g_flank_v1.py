"""E238/E239 (2026-10-01): g, the block's relay landing from the entry instant t0, read in the block's readings.
Design: log E238.

Flanks: each block reading h, openings (8K+1)/(8h), K >= K0(h) = the first lap whose opening is at or after t0; index
j = K - K0.  Derived (A.9 from t0; Corollary 6.24): g = t0 if the block is clear at t0, else the least clear flank
opening at or after t0 over the block's readings.
Checks: G1 g (relay) = least clear flank opening found by scanning flanks with Theorem 6.19's criterion (no cascade);
G2 the winning flank is the relay's last setter; G3 every relay instant after t0 is an opening of its setter's flank.
Populations: the hole configurations of E233 (f = 3, 2,000) and E235 (f = 4, 5, 6, 1,000 each) at t0 = tau_C, and the
30 overruns at t0 = the start of S1.
"""
import sys, math
from fractions import Fraction as F
from collections import Counter
from multiprocessing import Pool
sys.path.insert(0, '../band_cert_v1'); from core import clear_set
from e151_block_v1 import trace
from quantity_tests_v1 import cd, E8, next_opening
import hole3_cascade_v1 as H3, holef_cascade_v1 as HF
from hole_perturb_v2 import relay


def k0(h, t0):
    return math.ceil((8 * h * t0 - 1) / 8)


def blockers(block, h, K):
    out = []
    for d in block:
        r = (d * (8 * K + 1) / h) % 8
        if r < 1 or r > 7:
            out.append((d, float(r)))
    return out


def first_clear(block, h, t0, cap=20000):
    K = k0(h, t0)
    for j in range(cap):
        if not blockers(block, h, K + j):
            return F(8 * (K + j) + 1, 8) / h, j
    return None, None


def study(args):
    f, core, block, entry = args
    block = tuple(sorted(block)); core = tuple(sorted(core))
    tc, _ = trace(core)
    if entry == 'tau_C':
        t0 = tc
    else:
        cells = clear_set(list(core), 8 * tc, 8 * tc + F(400) / core[0])
        t0 = cells[1][0] / 8
    g, gm = relay(block, t0)
    chk = Counter()
    clear0 = all(cd(d * t0) >= E8 for d in block)
    fc = {h: first_clear(block, h, t0) for h in block}
    if clear0:
        gs = t0
    else:
        gs = min(v[0] for v in fc.values() if v[0] is not None)
    if gs != g:
        chk['G1'] += 1
    rec = dict(f=f, core=core, block=block, entry=entry, t0=t0, g=g, clear0=clear0, moves=len(gm), chk=chk)
    if clear0:
        return rec
    win = [h for h in block if fc[h][0] == g]
    h = win[0]; j = fc[h][1]
    last = gm[-1][2]
    if h not in last:
        chk['G2'] += 1
    for t, way, st, nx in gm:
        a = min(st)
        if (8 * a * nx - 1) % 8 != 0:
            chk['G3'] += 1
    C0 = [d for d in block if cd(d * t0) < E8]
    first_exit = max(next_opening(d, t0) for d in C0)
    passed = 0
    visited = set(mv[3] for mv in gm)
    for x in block:
        K = k0(x, t0)
        while F(8 * K + 1, 8) / x < g:
            if F(8 * K + 1, 8) / x not in visited and F(8 * K + 1, 8) / x != t0:
                passed += 1
            K += 1
    scan = []
    K = k0(h, t0)
    for jj in range(j + 1):
        scan.append((jj, [(blk, round(r, 3)) for blk, r in blockers(block, h, K + jj)]))
    rec.update(h=h, rank=block.index(h) + 1, j=j, nwin=len(win), h_in_C0=(h in C0), one_move=(g == first_exit),
               C0=tuple(C0), passed=passed, scan=scan,
               phases=tuple(round(float((8 * d * t0) % 8), 3) for d in block),
               setters=[(block.index(min(st)) + 1, int((8 * min(st) * nx - 1) / 8) - k0(min(st), t0)) for t, way, st, nx in gm])
    return rec


if __name__ == '__main__':
    pops = [(3, c, b) for c, b in H3.gen(232, 2000)] + [(f, c, b) for f in (4, 5, 6) for c, b in HF.gen(f, 234 + f, 1000)[0]]
    with Pool(8) as pool:
        base = pool.map(HF.study, [(c, b) for f, c, b in pops], chunksize=25)
    jobs = [(f, c, b, 'tau_C') for f, c, b in pops] + [(f, c, b, 'S1') for (f, c, b), r in zip(pops, base) if r['k_land'] != 'S0']
    with Pool(8) as pool:
        res = pool.map(study, jobs, chunksize=20)
    out = open('hole_g_flank_v1.out', 'w'); out.write(__doc__ + "\n"); w = lambda s: (out.write(s + "\n"), out.flush())
    for f in (3, 4, 5, 6):
        for entry in ('tau_C', 'S1'):
            grp = [r for r in res if r['f'] == f and r['entry'] == entry]
            if not grp:
                continue
            ck = Counter()
            for r in grp:
                ck.update(r['chk'])
            nz = [r for r in grp if not r['clear0']]
            w("\n== f = %d, t0 = %s: %d relays ==" % (f, entry, len(grp)))
            w("  CHECKS G1, G2, G3: %s" % (dict(ck) if ck else '0 failures'))
            w("  block clear at t0 (g = t0): %d" % sum(r['clear0'] for r in grp))
            w("  winning flank by rank (1 = slowest block reading): %s" % dict(sorted(Counter(r['rank'] for r in nz).items())))
            w("  winning flank's index j: %s" % dict(sorted(Counter(r['j'] for r in nz).items())))
            w("  ties (two flanks open at g): %d" % sum(1 for r in nz if r['nwin'] > 1))
            w("  winner in the way at t0: %d of %d" % (sum(r['h_in_C0'] for r in nz), len(nz)))
            w("  g = the latest exit of the readings in the way at t0 (one move): %d of %d" % (sum(r['one_move'] for r in nz), len(nz)))
            w("  readings in the way at t0: %s" % dict(sorted(Counter(len(r['C0']) for r in nz).items())))
            w("  moves: %s" % dict(sorted(Counter(r['moves'] for r in nz).items())))
            w("  flank openings in (t0, g) passed without a visit: %s" % dict(sorted(Counter(r['passed'] for r in nz).items())))
            w("  (rank, j) of the winner: %s" % dict(sorted(Counter((r['rank'], r['j']) for r in nz).items())))
            odd = [r for r in nz if r['j'] > 0]
            w("  paths with j > 0 (%d), first 15 read:" % len(odd))
            for r in odd[:15]:
                w("    core %s block %s  phases at t0 (eighths) %s  in the way %s  setters (rank, j) %s  winner rank %d j %d" % (
                    r['core'], r['block'], r['phases'], r['C0'], r['setters'], r['rank'], r['j']))
                for jj, bl in r['scan']:
                    w("        flank opening j=%d: %s" % (jj, 'clear' if not bl else 'blocked by ' + str(bl)))
    out.close()
    print(open('hole_g_flank_v1.out').read()[len(__doc__):][:12000])
