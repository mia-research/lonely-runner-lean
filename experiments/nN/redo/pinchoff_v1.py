"""Owner: the isolation exists (the progression, phi(n) law) and a speed deformation displaces it; locate every
pinch-off along deformation paths through the cascade.  Exact throughout (Fraction), BSM (the band test closed at 1/8).

Path: v(s) = (1 - s) v_AP + s v_target, s in [0, 1], where v_AP is the progression with the target's slowest speed and
spread (every speed positive, order kept, so the readings of the slowest runner are linear in s and keep their ranks).
Subject: the slowest runner (EndRunnerN).  Event: the cascade's fixed point from the bound 1/(8 d_min), the left end of a
lonely component [t, r]; t is the exit (k + 1/8)/d_a of runner a (or the bound, a = rank 0, k = 0) and r the next entry
(m - 1/8)/d_b of runner b.  A pinch-off is r = t: (8k + 1) d_b(s) = (8m - 1) d_a(s), linear in s, solved exactly.
At the pinch-off s*, the landing is computed at s* itself: from t* the entering runner b is in the way until its exit
(m + 1/8)/d_b, and the cascade from there gives the first lonely instant after the pinched point.
Recorded: pinchers (ranks a, b; laps), R = 8 d_min t before and at the landing, the handover chain (setters' ranks), the
landing component's length at s* (positive = it already existed in the geometry), and the event just after s* agreeing
with the landing (a check)."""
import sys, random
from fractions import Fraction as F
from math import floor
from arrangement_lib import nd

EIGHTH = F(1, 8)

def readings_at(D0, D1, s):
    return [d0 + s * (d1 - d0) for d0, d1 in zip(D0, D1)]

def cascade_from(ds, t, cap=100000):
    ch = []
    for _ in range(cap):
        way = [i for i, d in enumerate(ds) if nd(d * t) < EIGHTH]
        if not way: return t, ch
        cand = {i: (F(floor(ds[i] * t - EIGHTH) + 1) + EIGHTH) / ds[i] for i in way}
        i = max(cand, key=lambda x: cand[x]); ch.append(i); t = cand[i]
    return None, ch

def event(ds):
    """(t, pin (a, k), right end (b, m), r): event, its pinning exit, and the component's right end"""
    t0 = EIGHTH / ds[0]
    t, ch = cascade_from(ds, t0)
    if ch: a = ch[-1]; k = floor(ds[a] * t - EIGHTH + F(1, 10**12))  # t = (k + 1/8)/d_a
    else: a, k = 0, 0
    best = None
    for i, d in enumerate(ds):
        m = floor(d * t + EIGHTH) + 1; e = (m - EIGHTH) / d
        if best is None or e < best[2]: best = (i, m, e)
    return t, (a, k), (best[0], best[1]), best[2]

def form(ds):
    t, pin, rb, r = event(ds); return pin

def scan(D0, D1, lo, hi, flo, fhi, out, depth=0):
    if flo == fhi: return
    if hi - lo <= F(1, 2**44):
        out.append((lo, hi)); return
    mid = (lo + hi) / 2; fm = form(readings_at(D0, D1, mid))
    scan(D0, D1, lo, mid, flo, fm, out, depth + 1); scan(D0, D1, mid, hi, fm, fhi, out, depth + 1)

def study(D0, D1, grid=400):
    trans = []
    ss = [F(i, grid) for i in range(grid + 1)]
    forms = [form(readings_at(D0, D1, s)) for s in ss]
    for i in range(grid):
        scan(D0, D1, ss[i], ss[i + 1], forms[i], forms[i + 1], trans)
    rows = []
    for lo, hi in trans:
        dsl = readings_at(D0, D1, lo); dsh = readings_at(D0, D1, hi)
        tl, (a, k), (b, m), rl = event(dsl); th = event(dsh)[0]
        Rl, Rh = 8 * dsl[0] * tl, 8 * dsh[0] * th
        if abs(Rh - Rl) < F(1, 10**6):
            rows.append(dict(kind='continuous')); continue
        if Rh < Rl:
            # displaced backwards: a lonely component born before the old event.  Its left end at hi is the exit of
            # runner c (lap kc); report the new component's length at hi (small = just born) and the runners.
            t2, (c, kc), (e, me), r2 = event(dsh)
            rows.append(dict(kind='birth', lo=lo, c=c, e=e, Rl=Rl, Rh=Rh, comp=8 * dsh[0] * (r2 - t2))); continue
        # exact pinch-off: the old component [t, r] closes when some runner c's next entry (lap m_c at lo) meets t:
        # (8k+1) d_c(s) = (8 m_c - 1) d_a(s); take the smallest solution inside the bracket
        cands = []
        for c in range(len(D0)):
            mc = floor(dsl[c] * tl + EIGHTH) + 1
            A = (8 * k + 1) * (D1[c] - D0[c]) - (8 * mc - 1) * (D1[a] - D0[a])
            Bc = (8 * mc - 1) * D0[a] - (8 * k + 1) * D0[c]
            if A != 0:
                sc = Bc / A
                if lo - F(1, 2**40) <= sc <= hi + F(1, 2**40): cands.append((sc, c, mc))
        if not cands:
            rows.append(dict(kind='unresolved', lo=lo, hi=hi, a=a, k=k, Rl=float(Rl), Rh=float(Rh))); continue
        sstar, b, m = min(cands)
        ds = readings_at(D0, D1, sstar)
        tstar = (k + EIGHTH) / ds[a]
        t1 = (m + EIGHTH) / ds[b]
        land, ch = cascade_from(ds, t1)
        if land is None:
            rows.append(dict(kind='NO LANDING', sstar=sstar, a=a, b=b)); continue
        r = min(((floor(d * land + EIGHTH) + 1) - EIGHTH) / d for d in ds)
        Rstar, Rland = 8 * ds[0] * tstar, 8 * ds[0] * land
        rows.append(dict(kind='pinch', sstar=sstar, ok_bracket=True, a=a, k=k, b=b, m=m,
                         Rstar=Rstar, Rland=Rland, agree=abs(Rland - Rh) < F(1, 10**4),
                         comp=8 * ds[0] * (r - land), chain=ch))
    return rows

def targets():
    import io, contextlib
    with contextlib.redirect_stdout(io.StringIO()):
        import case_c_map_v1 as cm
    cm.rnd.seed(26); out = []; n = 0
    for shape in ('even', 'clumped+outliers', 'even+clump'):
        for g1div in (30, 100, 1000):
            c = 0
            while c < 150:
                g = cm.rest(shape); W6 = sum(g); g1 = max(1, W6 // (g1div - 1))
                if g1 + W6 <= 22 * g1: continue
                V = cm.arrangement([g1] + g)
                if len(set(V)) < 8: continue
                c += 1; n += 1
                if n % 30 == 0: out.append((f"C:{shape}/W{g1div}", V))
    rnd = random.Random(2609)
    for i in range(40):
        V = sorted(rnd.sample(range(1, 301), 8)); out.append(("random[1,300]", V))
    return out

def run(args):
    name, V = args
    D1 = [F(v - V[0]) for v in V[1:]]
    W = D1[-1]; D0 = [W * j / 7 for j in range(1, 8)]      # the progression with the same slowest speed and spread
    return name, V, study(D0, D1)

if __name__ == '__main__':
    from multiprocessing import Pool
    T = targets()
    with Pool() as pool:
        res = pool.map(run, T)
    tot = pin = cont = oth = nol = 0; bad_br = dis = 0; neg = 0; handover = {}
    for name, V, rows in res:
        np_ = sum(r['kind'] == 'pinch' for r in rows)
        print(f"== {name:24s} V {V}: pinch-offs {np_}, continuous hand-offs {sum(r['kind']=='continuous' for r in rows)}, "
              f"births {sum(r['kind']=='birth' for r in rows)}, unresolved {sum(r['kind']=='unresolved' for r in rows)}, no landing {sum(r['kind']=='NO LANDING' for r in rows)}")
        for r in rows:
            cont += r['kind'] == 'continuous'; oth += r['kind'] in ('birth',); nol += r['kind'] == 'NO LANDING'
            if r['kind'] == 'birth': print(f"     s~{float(r['lo']):.6f}  birth: displaced back from R {float(r['Rl']):.4f} to R {float(r['Rh']):.4f}, new component (exit of rank {r['c']} .. entry of rank {r['e']}) length {float(r['comp']):.6f} in R")
            if r['kind'] in ('unresolved', 'NO LANDING'): print(f"     {r['kind']}: {r}")
            if r['kind'] != 'pinch': continue
            pin += 1; bad_br += not r['ok_bracket']; dis += not r['agree']; neg += r['comp'] <= 0
            print(f"     s* {float(r['sstar']):.6f}  pinch: rank {r['a']} leaves (lap {r['k']}) as rank {r['b']} enters (lap {r['m']}) "
                  f"at R {float(r['Rstar']):.4f} -> displaced to R {float(r['Rland']):.4f} (component there {float(r['comp']):.4f} in R); "
                  f"handover {r['chain']}{'' if r['agree'] else '  [DISAGREES with the event just after s*]'}"
                  f"{'' if r['ok_bracket'] else '  [s* outside bracket]'}")
    print(f"\ntotal: pinch-offs {pin}; continuous hand-offs {cont}; births {oth}; no landing {nol}; unresolved {sum(r['kind']=='unresolved' for _,_,rows in res for r in rows)}; "
          f"s* outside its bracket {bad_br}; landing disagrees with the event after s* {dis}; landing component of length 0 {neg}")
