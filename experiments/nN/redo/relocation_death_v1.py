"""E182 (2026-09-29), relocation_death_v1: where the isolation goes when its window dies along the deformation from the AP.

Owner: "yes run the three-case relocation test if you tell me why it matters.  We are trying to determine how the
cascade is forced to show n=8."

Why: lonely_iff_run_ends makes n = 8 the statement that the cascade always stops.  Along the deformation from the AP
(isolated) to a target, the cascade's landing changes only at pinches (E178); a birth moves it to a newborn window at the
pinch instant; a DEATH is the only moment the isolation could be lost.  So the step to be forced is the relocation at a
death.

Derived from the definitions (reasoned): at a death the dying window is a single instant t0 where runner a sits on +1/8
(leaving the subject's slot, lap k_a) and b on -1/8 (entering, lap k_b).  Just after, b's closing precedes a's opening,
so a's window and b's window overlap and together cover everything from a's entry to b's exit
T_b = (k_b + 1 + 1/8)/d_b.  Hence the new first isolation is exactly one of:
  CASE 1  at T_b, b's exit (its separation, E158; SeparationN.move_eq_separation) -- exactly when the other readings are
          clear at T_b;
  CASE 2  earlier than t0: a window born at the same instant (the partial reflection, E181);
  CASE 3  later than T_b: some reading is in the way at T_b (carried into the slot by the shift, E161's transport).
CHECK (derived, must be 0): no new first isolation strictly between a's opening and T_b.
Everything is evaluated exactly at s = tau + delta, delta = 1/10^15, just after the death.
Case 3 records the readings in the way at T_b (faster or slower than b), and the cascade's moves from T_b to the landing.
Populations: E178's (Case B to 24 every 100th, late band shapes every 10th, Case C sample 500).  Simple pinches only;
multi-pinch deaths are counted.
"""
import sys, math, random, itertools
from fractions import Fraction as F
from collections import Counter
from multiprocessing import Pool
import deform_pinch_v1 as D
from quantity_tests_v1 import cd, E8, next_opening

DELTA = F(1, 10 ** 15)
_orig = D.classify


def classify_k(x, sa, ka, sb, kb):
    rec = _orig(x, sa, ka, sb, kb)
    rec['ka'], rec['kb'] = ka, kb
    return rec


D.classify = classify_k


def study(S):
    S = tuple(sorted(S)); x = [F(7 * d, S[-1]) for d in S]
    r = D.follow(S)
    rows = []
    for e in r['events']:
        if e.get('kind') != 'death' or e.get('tau') is None or e['tau'] == 0:
            continue
        if not e['simple']:
            rows.append(dict(simple=False)); continue
        tau, t0, k = e['tau'], e['t0'], e['ka']
        d0 = D.readings_at(x, tau)
        pos = [d * t0 - math.floor(d * t0) for d in d0]
        a = pos.index(E8); b = pos.index(F(7, 8))
        ds = D.readings_at(x, tau + DELTA)
        ta = F(8 * k[a] + 1, 8) / ds[a]                      # a's opening, just after the death
        Tb = F(8 * (k[b] + 1) + 1, 8) / ds[b]                # b's exit
        comps = D.components(ds, need=1)
        land = comps[0][0]
        rec = dict(simple=True, R0=float(8 * min(d0) * t0))
        if land < ta:
            rec['case'] = 2
        elif land < Tb:
            rec['case'] = 'between'                          # must not happen
        elif land == Tb:
            rec['case'] = 1
        else:
            rec['case'] = 3
            way = [i for i, d in enumerate(ds) if cd(d * Tb) < E8]
            rec['way'] = tuple(way)
            rec['faster'] = sum(1 for i in way if ds[i] > ds[b])
            rec['slower'] = sum(1 for i in way if ds[i] < ds[b])
            t, n = Tb, 0
            while n < 1000:
                w = [d for d in ds if cd(d * t) < E8]
                if not w:
                    break
                t = max(next_opening(d, t) for d in w); n += 1
            rec['moves'] = n
            rec['cascade_ok'] = (t == land)
            rec['R_jump'] = float(8 * min(ds) * (land - Tb))
        rows.append(rec)
    return S, rows


def report(name, res, out):
    rows = [x for S, rs in res for x in rs]
    simp = [x for x in rows if x['simple']]
    c = Counter(x['case'] for x in simp)
    out.write("\n== %s: deaths after s = 0: %d (simple %d, multi %d) ==\n" % (name, len(rows), len(simp), len(rows) - len(simp)))
    out.write("  CASE 1 (b's exit): %d   CASE 2 (earlier, born at the same instant): %d   CASE 3 (later than b's exit): %d\n" %
              (c[1], c[2], c[3]))
    out.write("  CHECK, a new first isolation between a's opening and b's exit (derived impossible): %d\n" % c['between'])
    c3 = [x for x in simp if x['case'] == 3]
    if c3:
        out.write("  case 3: readings in the way at b's exit: %s\n" % dict(sorted(Counter(len(x['way']) for x in c3).items())))
        out.write("  case 3: those faster than b / slower than b: faster-only %d, slower-only %d, both %d\n" % (
            sum(1 for x in c3 if x['faster'] and not x['slower']), sum(1 for x in c3 if x['slower'] and not x['faster']),
            sum(1 for x in c3 if x['faster'] and x['slower'])))
        out.write("  case 3: cascade moves from b's exit to the landing: %s; cascade reaches the landing: %d of %d\n" % (
            dict(sorted(Counter(x['moves'] for x in c3).items())), sum(x['cascade_ok'] for x in c3), len(c3)))
        out.write("  case 3: jump in R beyond b's exit: max %.3f, median %.3f\n" % (
            max(x['R_jump'] for x in c3), sorted(x['R_jump'] for x in c3)[len(c3) // 2]))
    paths1 = sum(1 for S, rs in res if all(x.get('case') in (1, 2) for x in rs if x['simple']))
    out.write("  paths in which every simple death relocates by case 1 or 2: %d of %d\n" % (paths1, len(res)))
    out.flush()


if __name__ == '__main__':
    sys.path.insert(0, '../band_cert_v1')
    from coverB_fine_v1 import late_shapes
    out = open('relocation_death_v1.out', 'w'); out.write(__doc__ + "\n")
    caseB = [T for T in itertools.combinations(range(1, 25), 7) if 7 * T[0] < T[-1]][::100]
    rng = random.Random(13); caseC = []
    while len(caseC) < 500:
        T = tuple(sorted(rng.sample(range(1, 201), 7)))
        if T[-1] > 24 * T[0]:
            caseC.append(T)
    with Pool(8) as pool:
        for name, sets in [('Case B to 24, every 100th', caseB), ('late band shapes, every 10th', late_shapes()[::10]),
                           ('Case C sample (500)', caseC)]:
            res = pool.map(study, sets)
            report(name, res, out)
    out.close()
    print(open('relocation_death_v1.out').read()[len(__doc__):])
