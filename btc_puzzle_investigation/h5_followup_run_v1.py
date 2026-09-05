# h5_followup_run_v1.py  --  run: sage h5_followup_run_v1.py [--smoke]
#
# Executes PREREG_h5_factor_isolation_and_orbit_quo_v1.md, Exp 1 (F1/F2a/F8; F2b done free
# elsewhere) + Exp 2 (S_m-orbit-reduced quo). Faithful to the frozen instrument.
#
# Design (from the pre-reg):
#   - Curves are the FROZEN schedule (SHA f92cb4bb): j0=(A=0,B=1), j1728, 5 nonCM per prime.
#   - Baseline arm: evaluate all 7 (K=25, seed0=7000, gens-sampling) -> reproduces the leaky log
#     (C6 plant) and supplies F2a (bracket interp) inputs + C4.
#   - E_F1: R_B=8 random j=0 twists (A=0, random B), same K/seed0/sampling; control-free.
#   - E_F8: all 7 baseline curves re-evaluated with random_point sampling, |V| in {4,5}.
#   - Exp 2 orbit: for j0 and the nearest-#E control, also record the S_m-orbit count
#     (distinct sorted multisets of I.variety()) alongside quo=vector_space_dimension.
#   - |V| in {4,5,6}, K=25, 24 frozen primes, m=3.
#
# Exact-int signal path: orders, quo, variety points, orbit counts are ints. Floats appear only
# in ANALYSIS (logmean, ranked against sign-flip null), never here.
#
# Output: append one JSON record per curve-eval to h5_followup_results_v1.jsonl (RESUMABLE:
# a (arm,p,V,lab,A,B) already present is skipped). Plants -> h5_followup_plants_v1.json.

from sage.all import *
import json, os, sys, time, random

BASE = "/Users/trentpalelei/Desktop/Math Ex/btc_puzzle_investigation"
H = BASE + "/semaev_elimination_v1.py"
_g = {'__name__': 'harness_mod'}
exec(open(H).read(), _g)
measure_system      = _g['measure_system']
decomposition_system= _g['decomposition_system']
decomposable_target = _g['decomposable_target']

SMOKE = ('--smoke' in sys.argv)
SCHED = json.load(open(BASE + "/_SCHEDULE_semaev_cm_relation_yield_v4.json"))
RESULTS = BASE + ("/h5_followup_smoke_v1.jsonl" if SMOKE else "/h5_followup_results_v1.jsonl")
PLANTS  = BASE + ("/h5_followup_plants_smoke_v1.json" if SMOKE else "/h5_followup_plants_v1.json")

m = 3
Vs      = [4, 5] if SMOKE else [4, 5, 6]
K       = 5 if SMOKE else 25
R_B     = 3 if SMOKE else 8
SEED0   = 7000
PRIMES  = [e["p"] for e in SCHED][:3] if SMOKE else [e["p"] for e in SCHED]
F8_Vs   = [4, 5, 6]   # pre-reg conditional extension triggered (E_F8 > |V|=5 floor)

# ---- resumability -------------------------------------------------------
done = set()
if os.path.exists(RESULTS):
    for line in open(RESULTS):
        line = line.strip()
        if not line: continue
        r = json.loads(line)
        done.add((r["arm"], r["p"], r["V"], r["lab"], r["A"], r["B"]))
def already(arm,p,V,lab,A,B): return (arm,p,V,lab,A,B) in done
def emit(rec):
    with open(RESULTS, "a") as fh: fh.write(json.dumps(rec, sort_keys=True) + "\n")
    done.add((rec["arm"], rec["p"], rec["V"], rec["lab"], rec["A"], rec["B"]))

# ---- orbit-aware measurement -------------------------------------------
def measure_orbit(F, A, B, m, tval, Vroots, Dmax, want_orbit):
    """quo = vector_space_dimension (matches harness); orbit = # distinct sorted multisets of
    I.variety() (S_m-orbit reduction, the pre-reg's corrected object). Only compute variety if
    want_orbit and dim==0."""
    Rx, gens_list, xs = decomposition_system(F, A, B, m, tval, Vroots)
    I = Rx.ideal(gens_list)
    dim = int(I.dimension())
    if dim == 0:
        q = int(I.vector_space_dimension())
        if want_orbit:
            try:
                var = I.variety()
                vs = len(var)
                orbits = set()
                for sol in var:
                    orbits.add(tuple(sorted(int(sol[xi]) for xi in xs)))
                oc = len(orbits)
            except Exception as ex:
                vs = None; oc = None
        else:
            vs = None; oc = None
        return dict(dim=0, quo=q, vsize=vs, orbit=oc)
    elif dim == -1:
        return dict(dim=-1, quo=0, vsize=(0 if want_orbit else None), orbit=(0 if want_orbit else None))
    else:
        return dict(dim=dim, quo=None, vsize=None, orbit=None)

def gens_target(F, A, B, m, extra, seed):
    return decomposable_target(F, A, B, m, extra=extra, seed=seed)   # gens()[0]-multiples

def randpoint_target(F, A, B, m, extra, seed):
    """F8 variant: factor base + target from E.random_point() instead of gens multiples."""
    E = EllipticCurve(F, [A, B]); pyr = random.Random(int(seed))
    for _ in range(200):
        pts = []
        for _ in range(m):
            P = E.random_point()
            while P == E(0): P = E.random_point()
            pts.append(P)
        xs = [P[0] for P in pts]
        if len(set(xs)) < m: continue
        S = E(0)
        for P in pts: S = S + P
        Ptgt = -S
        if Ptgt == E(0): continue
        Vroots = list(xs)
        for _ in range(extra):
            Q = E.random_point()
            while Q == E(0): Q = E.random_point()
            Vroots.append(Q[0])
        # random.seed for E.random_point reproducibility: seed sage RNG
        return Ptgt[0], Vroots
    return None

def cell(F, A, B, m, extra, K, seed0, sampler, want_orbit):
    Dmax = 2**(m-1) + m*(m+extra) + 5
    quos = []; orbs = []; vszs = []
    if sampler == "randpoint":
        set_random_seed(int(seed0))   # make E.random_point() reproducible
    for k in range(K):
        if sampler == "gens":
            dt = gens_target(F, A, B, m, extra, seed0 + k)
        else:
            dt = randpoint_target(F, A, B, m, extra, seed0 + k)
        if dt is None: continue
        tval, V = dt
        r = measure_orbit(F, A, B, m, tval, V, Dmax, want_orbit)
        if r["dim"] == 0 and r["quo"] is not None:
            quos.append(r["quo"])
            if want_orbit and r["orbit"] is not None:
                orbs.append(r["orbit"]); vszs.append(r["vsize"])
    return quos, orbs, vszs

def is_cyclic(F, A, B):
    try:
        return len(EllipticCurve(F, [A, B]).abelian_group().invariants()) <= 1
    except Exception:
        return None

def match_nearest_orders(j0_order, noncm):
    best = bd = None
    for i, c in enumerate(noncm):
        d = abs(int(c["order"]) - int(j0_order))
        if bd is None or d < bd: bd = d; best = i
    return best

# ---- PLANTS (run once) --------------------------------------------------
def run_plants():
    P = {}
    # (1) orbit-counter unit tests: dedupe of sorted tuples
    alldup = [(3,1,2),(1,3,2),(2,1,3),(1,2,3),(3,2,1),(2,3,1)]   # 6 orderings of {1,2,3}
    dd = len({tuple(sorted(t)) for t in alldup})
    alldist = [(1,2,3),(1,2,4),(1,2,5)]
    da = len({tuple(sorted(t)) for t in alldist})
    P["orbit_counter_allduplicate"] = dict(raw=len(alldup), orbit=dd, expect_orbit=1, ok=(dd==1))
    P["orbit_counter_alldistinct"]  = dict(raw=len(alldist), orbit=da, expect_orbit=3, ok=(da==3))
    # (3) forced-relation check: quo(tval)=quo(z3 tval)=quo(z3^2 tval) on a beta-invariant V (j0 curve)
    p = 523; F = GF(p); A, B = 0, 1
    z3 = F(GF(p).zeta(3)) if False else None
    # cube root of unity in F_p (p = 1 mod 3)
    zeta3 = [x for x in F if x != 1 and x**3 == 1]
    E = EllipticCurve(F, [A, B]); G = E.gens()[0]; N = int(E.order())
    if zeta3:
        z3 = zeta3[0]
        pyr = random.Random(12321)
        # build a beta-invariant V: take some x's and close under x->z3*x
        base = []
        for _ in range(3):
            Q = int(pyr.randrange(1, N)) * G
            if Q != E(0): base.append(Q[0])
        Vinv = set()
        for x in base:
            Vinv.add(x); Vinv.add(z3*x); Vinv.add(z3*z3*x)
        Vinv = [F(x) for x in Vinv]
        # pick a decomposable target on this curve
        dt = gens_target(F, A, B, m, 0, seed=777)
        if dt is not None:
            tval0, _ = dt
            Dmax = 2**(m-1) + m*len(Vinv) + 5
            q0 = measure_orbit(F, A, B, m, tval0,        Vinv, Dmax, False)["quo"]
            q1 = measure_orbit(F, A, B, m, z3*tval0,      Vinv, Dmax, False)["quo"]
            q2 = measure_orbit(F, A, B, m, z3*z3*tval0,   Vinv, Dmax, False)["quo"]
            P["forced_relation_check"] = dict(tval=int(tval0), q0=q0, q1=q1, q2=q2,
                                              ok=(q0 == q1 == q2))
    json.dump(P, open(PLANTS, "w"), indent=2)
    return P

# ---- MAIN ---------------------------------------------------------------
def main():
    t0 = time.time()
    print("H-5 follow-up run  SMOKE=%s  primes=%d  Vs=%s  K=%d  R_B=%d" % (SMOKE, len(PRIMES), Vs, K, R_B))
    plants = run_plants()
    print("PLANTS:", json.dumps(plants))
    frc = plants.get("forced_relation_check")
    if frc and not frc["ok"]:
        print("HALT: forced-relation check failed (instrument bug)."); return
    if not plants["orbit_counter_allduplicate"]["ok"] or not plants["orbit_counter_alldistinct"]["ok"]:
        print("HALT: orbit counter unit test failed."); return

    sched_by_p = {e["p"]: e["curves"] for e in SCHED}
    for p in PRIMES:
        F = GF(p)
        curves = sched_by_p[p]
        j0   = [c for c in curves if c["lab"] == "j0"][0]
        noncm= [c for c in curves if c["lab"] == "nonCM"]
        i0   = match_nearest_orders(j0["order"], noncm)
        ctrl = noncm[i0]
        # random j=0 twists for E_F1 (deterministic per prime)
        rb = random.Random(50000 + p)
        f1_Bs = []
        while len(f1_Bs) < R_B:
            B = rb.randrange(2, p)          # avoid B=1 (that's the baseline j0)
            if B not in f1_Bs: f1_Bs.append(B)
        for V in Vs:
            extra = V - m
            tp = time.time()
            # --- baseline arm: all 7 curves (orbit on j0 + ctrl) ---
            for c in curves:
                orb = (c is j0) or (c is ctrl)
                if already("baseline", p, V, c["lab"], c["A"], c["B"]): continue
                quos, orbs, vszs = cell(F, c["A"], c["B"], m, extra, K, SEED0, "gens", orb)
                emit(dict(arm="baseline", p=p, V=V, lab=c["lab"], A=c["A"], B=c["B"],
                          order=c["order"], mu=c["mu"], is_ctrl=(c is ctrl),
                          cyclic=is_cyclic(F, c["A"], c["B"]),
                          K=K, seed0=SEED0, quos=quos, orbits=(orbs if orb else None),
                          vsizes=(vszs if orb else None)))
            # --- E_F1 arm: R_B random j0 twists (quo only) ---
            for bi, B in enumerate(f1_Bs):
                if already("F1", p, V, "j0rand", 0, B): continue
                quos, _, _ = cell(F, 0, B, m, extra, K, SEED0, "gens", False)
                emit(dict(arm="F1", p=p, V=V, lab="j0rand", A=0, B=B,
                          order=int(EllipticCurve(F, [0, B]).order()), mu=6,
                          cyclic=is_cyclic(F, 0, B), K=K, seed0=SEED0,
                          quos=quos, orbits=None, vsizes=None))
            # --- E_F8 arm: all 7 curves, random_point sampling, |V| in {4,5} ---
            if V in F8_Vs:
                for c in curves:
                    if already("F8", p, V, c["lab"], c["A"], c["B"]): continue
                    quos, _, _ = cell(F, c["A"], c["B"], m, extra, K, SEED0, "randpoint", False)
                    emit(dict(arm="F8", p=p, V=V, lab=c["lab"], A=c["A"], B=c["B"],
                              order=c["order"], mu=c["mu"], is_ctrl=(c is ctrl),
                              cyclic=is_cyclic(F, c["A"], c["B"]), K=K, seed0=SEED0,
                              quos=quos, orbits=None, vsizes=None))
            print("  p=%-5d |V|=%d done  [%.1fs, elapsed %.0fs]" % (p, V, time.time()-tp, time.time()-t0))
    print("ALL DONE  [%.0fs]" % (time.time()-t0))

if __name__ == '__main__':
    sys.stdout.reconfigure(line_buffering=True)
    main()
