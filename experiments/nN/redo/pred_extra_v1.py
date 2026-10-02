# Extra checks: (i) zone-pointer chain predicts the whole path without carrying R; (ii) same-lap blockers; (iii) search for reading 1 as a blocker / max R.
import sys, pickle, random, time
from collections import Counter
exec(open('pred_lib_v1.py').read())
def exit_of(z, xs): return F(8 * z[1] + 1) / xs[z[0]]
def chain_predict(xs):
    """zone pointer map, no R carried: state = the previous setter's zone; R0 = 1/min only for the first step."""
    zc = zones_containing(1 / min(xs), xs); out = []
    while zc:
        y, j, e = max(zc, key=lambda z: (z[2], z[0])); out.append((y, j))
        zc = zones_containing(e, xs)
    return out
def check(xs, C):
    steps, Rend = path(xs); pred = chain_predict(xs); act = [(s['setter'], s['lap']) for s in steps]
    C['arr'] += 1
    if pred != act: C['chain_viol'] += 1
    for s in steps:
        bl = s['blockers']; laps = {y: round(s['R'] * xs[y] / 8) for y in bl}
        if len(set(laps.values())) == 1:
            C['samelap_steps'] += 1
            if s['setter'] != min(bl): C['samelap_LR_viol'] += 1
        else: C['mixedlap_steps'] += 1
        # window: a slower reading blocking at R2 on the setter's lap has ratio > (8j-1)/(8j+1)
        R2 = s['R2']; js = s['lap']; ss = s['setter']
        for y, r in enumerate(xs):
            if y != ss and r < xs[ss] and blocks(R2, r) and round(R2 * r / 8) == js and not r / xs[ss] > F(8 * js - 1, 8 * js + 1): C['window_viol'] += 1
    if any(0 in s['blockers'] for s in steps): C['rank1_blocker_arr'] += 1
    C['maxR_x1000'] = max(C['maxR_x1000'], int(1000 * Rend * min(xs) ))
    for s in steps: C['maxvisitedR_x1000'] = max(C['maxvisitedR_x1000'], int(1000 * s['R2'] * min(xs)))
def mode_sample(args):
    seed, N = args; C = Counter(); rnd = random.Random(seed)
    for name, f in FAMS:
        if name == 'climb': continue
        for _ in range(N): check(f(rnd), C)
    return C
def mode_hunt(args):   # climb on max visited R (normalised units) from chain starts; budget in seconds
    seed, secs = args; rnd = random.Random(seed); C = Counter(); t = time.time(); best_all = 0; found = []
    def score(xs):
        steps, Rend = path(xs); return max([s['R2'] for s in steps], default=1 / min(xs)) * min(xs), steps
    while time.time() - t < secs:
        xs = fam_chain(rnd); b, _ = score(xs); C['starts'] += 1
        for _ in range(120):
            ys = list(xs); i = rnd.randrange(1, 7)
            ys[i] = max(F(11, 10), ys[i] * F(1000 + rnd.randint(-60, 60), 1000) + (q(rnd, rnd.uniform(-1, 1)) if rnd.random() < .25 else 0)); ys = norm(ys)
            if not ok(ys): continue
            sc, st = score(ys); C['evals'] += 1
            if sc >= b: xs, b = ys, sc
            if any(0 in s['blockers'] for s in st): found.append(tuple(ys))
        best_all = max(best_all, b)
        C['best_x1000'] = int(1000 * best_all)
    C['rank1_blocker_found'] = len(found)
    return C, found[:3]
if __name__ == "__main__":
    from multiprocessing import Pool
    t = time.time()
    with Pool(2) as p:
        res = p.map(mode_sample, [(31, 6000), (32, 6000)])
        tot = Counter()
        for C in res:
            for k, v in C.items():
                if k.startswith('max'): tot[k] = max(tot[k], v)
                else: tot[k] += v
        # survey
        rows = pickle.load(open('outcome_survey_v2.pkl', 'rb')); S = Counter()
        for r in rows: check(norm([F(x) for x in r['rho']]), S)
        print("SAMPLE (fresh seeds, all non-climb families):"); [print("  %-22s %d" % (k, tot[k])) for k in ['arr','chain_viol','samelap_steps','samelap_LR_viol','mixedlap_steps','window_viol','rank1_blocker_arr','maxR_x1000','maxvisitedR_x1000']]
        print("SURVEY 20,000:"); [print("  %-22s %d" % (k, S[k])) for k in ['arr','chain_viol','samelap_steps','samelap_LR_viol','mixedlap_steps','window_viol','rank1_blocker_arr','maxR_x1000','maxvisitedR_x1000']]
        print("elapsed %.0fs" % (time.time() - t)); sys.stdout.flush()
        hres = p.map(mode_hunt, [(41, 240), (42, 240)])
    print("HUNT for reading 1 as a blocker (hill-climb on max visited R, normalised units, chain starts):")
    for C, fd in hres: print("  ", dict(C), fd)
