#!/usr/bin/env sage
# -*- mode: python -*-
"""
mu6_solving_degree_v1.py  —  EXECUTE PREREG_mu6_solving_degree_v1.md (frozen).
Run under Sage:  sage mu6_solving_degree_v1.py

STEP 1 (this file, the GATE): the d_LF read-out extension + firing plant + negative control.
Per PREREG sec 2 + sec 4: d_LF must be frozen and the firing plant must FIRE before any real cell.
  d_LF(I) := max{ D in [1,Dmax] : macaulay_stats(...)[D]['fall'] > 0 }   (last-fall degree)
Exact GF(p) linear algebra (macaulay_stats); every degree is an integer read from ranks.
"""
import sys, os
from sage.all import *
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from semaev_elimination_v1 import (macaulay_stats, decomposition_system, summation_poly,
                                    decomposable_target)

# ---------- HARNESS EXTENSION (read-out only; macaulay_stats unchanged) ----------
def d_LF_from_stats(stats):
    """last-fall degree = max D with fall>0; also first-fall d_ff = min such D."""
    fell = [D for D in sorted(stats) if stats[D].get('fall', 0) > 0]
    return (fell[0] if fell else None), (fell[-1] if fell else None)

def measure_LF(F, gens_list, xs, Dmax):
    """ONE Macaulay pass at a generous Dmax. d_LF = last fall; stable = last fall sits below the
    ceiling by a margin (>=3) AND quo has settled (quo constant over the last 3 degrees) => not
    Dmax-censored. No redundant second full pass (that doubled cost)."""
    st = macaulay_stats(F, gens_list, xs, Dmax)
    d_ff, d_LF = d_LF_from_stats(st)
    Ds = sorted(st)
    quo_top = st[Ds[-1]]['quo']
    quo_settled = len({st[D]['quo'] for D in Ds[-3:]}) == 1
    margin_ok = (d_LF is not None and d_LF <= Dmax - 3)
    return dict(d_ff=d_ff, d_LF=d_LF, stable=bool(quo_settled and margin_ok),
                quo=quo_top, quo_settled=quo_settled)

def ideal_quo(gens_list, Rx):
    I = Rx.ideal(gens_list); dim = int(I.dimension())
    if dim == 0:   return int(I.vector_space_dimension()), 0, I
    if dim == -1:  return 0, -1, I
    return None, dim, I

# ---------- profile of the REAL m=3 Semaev decomposition system (to match the plant) ----------
def real_profile(p, m, extra, seed=1):
    F = GF(p)
    dt = decomposable_target(F, 0, 7, m, extra=extra, seed=seed)
    tval, V = dt
    Rx, gens, xs = decomposition_system(F, 0, 7, m, tval, V)
    degs = sorted(int(g.degree()) for g in gens)
    return Rx, xs, degs, len(V)

# ---------- FIRING PLANT (sec 4): SPLIT field-eqs (syzygy-rich, low d_LF) vs DENSE field-eqs ----------
# Both share the REAL structured Sx (total-degree 12) and identical field-eq DEGREES (=|V|); only the
# field equations differ: split g_i=prod(x_i - r) (triangular, low regularity) vs generic dense deg-|V|.
# The split structure is common to ALL curves' decomposition systems (NOT the omega-action), so firing
# certifies the d_LF instrument reads a real regularity drop WITHOUT presupposing the mu6 answer.
# quo reported for each (matched-quo is enforced in the PRIMARY arm; liveness needs only the gap, sec 4).
def dense_fieldeq_system(Rx, xs, Sx, v, seed):
    set_random_seed(seed)
    return [Sx] + [Rx.random_element(degree=v, terms=Infinity) for _ in xs]

def main():
    p = 523; m = 3; extra = 1   # |V| = m+extra = 4
    F = GF(p)
    dt = decomposable_target(F, 0, 7, m, extra=extra, seed=1)
    tval, V = dt
    Rx, split_gens, xs = decomposition_system(F, 0, 7, m, tval, V)   # I_low = real system (split)
    Sx = split_gens[0]
    v = len(V); D0 = int(Sx.degree())
    Dmax = 2**(m-1) + m*len(V) + 8                                   # v4 ceiling + margin for d_LF
    print(f"[profile] p={p} m={m} |V|={v}  gen degs={sorted(int(g.degree()) for g in split_gens)}"
          f"  Sx deg={D0}  Dmax={Dmax}", flush=True)

    print("\n[FIRING PLANT] split field-eqs (real system) vs dense field-eqs (same Sx, same degrees):", flush=True)
    dense_gens = dense_fieldeq_system(Rx, xs, Sx, v, seed=7)
    ql, dl, _ = ideal_quo(split_gens, Rx); qh, dh, _ = ideal_quo(dense_gens, Rx)
    rL = measure_LF(F, split_gens, xs, Dmax); print(f"  I_low  (split): dim={dl} quo={ql}  "
          f"d_ff={rL['d_ff']} d_LF={rL['d_LF']} stable={rL['stable']}", flush=True)
    rH = measure_LF(F, dense_gens, xs, Dmax); print(f"  I_high (dense): dim={dh} quo={qh}  "
          f"d_ff={rH['d_ff']} d_LF={rH['d_LF']} stable={rH['stable']}", flush=True)
    fires = (rL['d_LF'] is not None and rH['d_LF'] is not None and rL['d_LF'] < rH['d_LF']
             and rL['stable'] and rH['stable'])
    print(f"  => FIRING PLANT {'FIRES (d_LF reads the known drop)' if fires else 'DOES NOT FIRE -> VOID'}"
          f"   [d_LF low={rL['d_LF']} < high={rH['d_LF']}?]", flush=True)

    print("\n[NEGATIVE CONTROL] two independent dense-field-eq systems (expect Delta ~ 0):", flush=True)
    g1 = dense_fieldeq_system(Rx, xs, Sx, v, seed=101); g2 = dense_fieldeq_system(Rx, xs, Sx, v, seed=202)
    r1 = measure_LF(F, g1, xs, Dmax); r2 = measure_LF(F, g2, xs, Dmax)
    dneg = (r1['d_LF'] - r2['d_LF']) if (r1['d_LF'] and r2['d_LF']) else None
    print(f"  gen1 d_LF={r1['d_LF']} stable={r1['stable']}  gen2 d_LF={r2['d_LF']} stable={r2['stable']}"
          f"  => Delta_neg={dneg}", flush=True)

    print(f"\n[GATE VERDICT] plant_fires={fires}, neg_delta={dneg}. Proceed to cells only if fires & |neg|<=1.",
          flush=True)
    return fires and (dneg is not None and abs(dneg) <= 1)


# ================= STEP 2: PRIMARY arm (j0 vs #E-matched nonCM, quo-matched) + BETA arm =========
from semaev_cm_relation_yield_v4 import primes_1mod3, build_curves, match_nearest, signflip_p

def curve_dLF_by_quo(F, A, B, m, extra, Dmax, seeds):
    """sample decomposable targets; return {quo: d_LF} for CONSISTENT, stable, resolved cells."""
    out = {}
    for s in seeds:
        dt = decomposable_target(F, A, B, m, extra=extra, seed=s)
        if dt is None: continue
        tval, V = dt
        Rx, gens, xs = decomposition_system(F, A, B, m, tval, V)
        I = Rx.ideal(gens)
        if int(I.dimension()) != 0: continue
        r = measure_LF(F, gens, xs, Dmax)
        if r['d_LF'] is not None and r['stable']:
            out.setdefault(int(r['quo']), int(r['d_LF']))
    return out

def beta_maps(p, m, k, seeds):
    """within-j0 SHARP omega-isolation. For beta-INVARIANT V (mu3-orbit-closed) and RANDOM V of the
    SAME size, each containing the target's decomposition x-coords: build {quo: d_LF} maps over seeds.
    Quo-matching is then done by shared-quo (identical to the primary arm) -> Δ_β is quo-matched."""
    F = GF(p)
    cbr = [F(u) for u in range(2, p) if F(u)**3 == 1]
    if not cbr: return {}, {}, 0
    beta = cbr[0]; E = EllipticCurve(F, [0, 7]); G = E.gens()[0]; N = int(E.order())
    invmap = {}; rndmap = {}; szV = 0
    import random as pyr
    for s in seeds:
        pyr.seed(int(s))
        xs0 = None
        for _ in range(200):
            pts = [int(pyr.randrange(1, N))*G for _ in range(m)]
            xc = [P[0] for P in pts]
            if any(P == E(0) for P in pts) or len(set(xc)) < m: continue
            Ss = E(0)
            for P in pts: Ss = Ss + P
            if -Ss != E(0): xs0 = xc; tval = (-Ss)[0]; break
        if xs0 is None: continue
        Vinv = set()
        for x in xs0: Vinv |= {x, beta*x, beta*beta*x}       # mu3-closure of 3 pts -> up to 9 x-coords
        while len(Vinv) < 3*k: r = F(pyr.randrange(1, p)); Vinv |= {r, beta*r, beta*beta*r}
        Vrnd = set(xs0)
        while len(Vrnd) < len(Vinv): Vrnd.add(F(pyr.randrange(0, p)))
        szV = len(Vinv)
        Dmax_b = 2**(m-1) + m*szV + 8                        # size Dmax to ACTUAL |Vinv| (~9, not 3k)
        for Vr, mp in [(list(Vinv), invmap), (list(Vrnd), rndmap)]:
            Rx, gens, xsv = decomposition_system(F, 0, 7, m, tval, Vr)
            I = Rx.ideal(gens)
            if int(I.dimension()) != 0: continue
            r = measure_LF(F, gens, xsv, Dmax_b)
            if r['d_LF'] is not None and r['stable']:
                mp.setdefault(int(r['quo']), int(r['d_LF']))
    return invmap, rndmap, szV

def run_cells(band, m, extra, n_noncm=5):
    v = m + extra; Dmax = 2**(m-1) + m*v + 8
    seeds = list(range(1, 11))
    print(f"\n{'='*70}\n[PRIMARY + BETA] m={m} |V|={v} Dmax={Dmax}  band={band}\n{'='*70}", flush=True)
    prim = []; beta = []
    for p in band:
        F = GF(p)
        curves = build_curves(p, n_noncm, seed=1234+p)
        j0 = [c for c in curves if c['lab'] == 'j0'][0]
        noncm = [c for c in curves if c['lab'] == 'nonCM']
        used = set(); bi = match_nearest(j0['order'], noncm, used)
        if bi is None: continue
        nc = noncm[bi]; egap = abs(nc['order']-j0['order'])
        cap_ok = egap*egap < 4*p          # |gap| < 2*sqrt(p) via integer square
        j0map = curve_dLF_by_quo(F, 0, j0['B'], m, extra, Dmax, seeds)
        ncmap = curve_dLF_by_quo(F, nc['A'], nc['B'], m, extra, Dmax, seeds)
        shared = sorted(set(j0map) & set(ncmap))
        d = dj = dn = None
        if shared and cap_ok:
            q = shared[0]; dj = j0map[q]; dn = ncmap[q]; d = dj - dn; prim.append(d)
        invm, rndm, szV = beta_maps(p, m, k=max(2, (v+2)//3), seeds=seeds[:6])
        shb = sorted(set(invm) & set(rndm))
        bd = None
        if shb:
            qb = shb[0]; bd = invm[qb] - rndm[qb]; beta.append(bd)
        binfo = (f"[βInv@q{shb[0]}={invm[shb[0]]} rnd={rndm[shb[0]]}]" if shb
                 else f"[β noSharedQuo inv={sorted(invm)} rnd={sorted(rndm)}]")
        print(f"  p={p}: gap={egap}(cap={cap_ok}) shQuo={shared[:4]} j0_dLF={dj} ncm_dLF={dn} "
              f"Δ_prim={d}  Δ_β={bd} {binfo}", flush=True)
    def report(name, ds):
        if not ds: print(f"  {name}: no resolved pairs"); return
        obs, pv = signflip_p(ds, R=20000, seed=7, two_sided=True)
        neg = sum(1 for x in ds if x < 0); pos = sum(1 for x in ds if x > 0)
        print(f"  {name}: N={len(ds)} Δ={ds}  mean={obs:+.3f} neg/pos={neg}/{pos}  signflip two-sided p={pv:.4f}", flush=True)
    print("", flush=True); report("PRIMARY Δ (j0 - nonCM, quo-matched)", prim); report("BETA    Δ_β (betaInvV - randomV)", beta)
    return prim, beta

if __name__ == "__main__":
    gate_ok = main()
    if gate_ok:
        band = primes_1mod3(523, 4)      # small band first (tractability); expand if fast
        run_cells(band, m=3, extra=1)
    else:
        print("\nGATE FAILED -> VOID, no cells measured.")
