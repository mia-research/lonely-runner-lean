# PREDICT the next change of the cascade's move sequence along a linear deformation, from the current path alone.
# Zones Z(y, j) = (sigma, eps) = ((8j-1)/rho_y, (8j+1)/rho_y).  Path: states R_0 (= 1/rho_min), R_1..R_n (= landing), R_{i+1} = eps of setter A_i.
# Effective crossings (the rule under test):
#  A  sigma_Z = R_i, i < n : Z newly a blocker at R_i; effective iff eps_Z > R_{i+1}  (Z outlasts the setter);  i = n: effective.
#  A' sigma_{A_i} = R_i    : the setter stops being a blocker at R_i: effective.
#  B  eps_Z = R_n          : Z straddles the landing (sigma_Z < R_n): effective.   (eps_{Z(y,0)} = R_0 is silent: R_0 is the max of the j=0 ends, continuous.)
#  C  eps_Z = R_{i+1}, i < n, Z != A_i, sigma_Z < R_i (Z a blocker at R_i): setter swap: effective.
#  D  eps_{A_i} = R_i      : the setter's exit meets the state it jumps from (the move has length 0): effective.
#  start-start crossings and every other start/end crossing: silent.
import sys, random
from fractions import Fraction as F
exec(open('transition_catalogue_v1.py').read().split('\nif __name__ ==')[0])
def rho_at(p, q, s): return [p[i] + q[i] * s for i in range(len(p))]
def solve(num_edge, den_edge, p, q):
    # (8j'+a)/rho_y(s) = (8J+b)/rho_X(s)   with num_edge=(y,a,j'), den_edge=(X,b,J):  (8j'+a) rho_X = (8J+b) rho_y
    (y, a, jp), (X, b, J) = num_edge, den_edge
    A = (8 * jp + a); B = (8 * J + b)
    # A*(p_X + q_X s) = B*(p_y + q_y s)
    den = A * q[X] - B * q[y]
    if den == 0: return None
    return (B * p[y] - A * p[X]) / den
def predicted_next(p, q, s0):
    n = len(p); rho0 = rho_at(p, q, s0)
    steps, Rend = path(rho0)
    X0 = min(range(n), key=lambda i: rho0[i])
    states = [(X0, 0)]            # state i's defining edge: end of zone (runner, lap); R_0 = end of (argmin, j=0)
    for mv in steps: states.append((mv["setter"], mv["lap"]))
    nst = len(states); Rmax = max(Rend, F(1, 1)) + 3
    cands = []
    for i, (X0_, J_) in enumerate(states):
        definers = range(n) if i == 0 else [X0_]            # R_0 = 1/rho_min: any runner may become the smallest before the next event
        for X in definers:
            J = 0 if i == 0 else J_
            for y in range(n):
                if y == X: continue
                jmax = int(max(rho0[y], (p[y] + q[y])) * Rmax / 8) + 3
                for jp in range(0, jmax + 1):
                    for a in (-1, 1):
                        if 8 * jp + a <= 0 and not (a == 1 and jp == 0): continue
                        s = solve((y, a, jp), (X, 1, J), p, q)
                        if s is None or s <= s0 or s > 1: continue
                        if i == 0:
                            rr = rho_at(p, q, s)
                            if any(rr[z] < rr[X] for z in range(n)): continue   # X must be the smallest at s*
                        cands.append((s, i, (y, a, jp)))
    cands.sort(key=lambda c: c[0])
    out = []
    for s, i, (y, a, jp) in cands:
        rho = rho_at(p, q, s)
        sig = lambda yy, j: (8 * j - 1) / rho[yy]; eps = lambda yy, j: (8 * j + 1) / rho[yy]
        R = lambda k: eps(*states[k]) if True else None
        Rk = [eps(*states[k]) for k in range(nst)]
        eff = False
        n_moves = nst - 1
        if a == -1:                                   # start of Z=(y,jp) meets state i
            if i < n_moves:
                if (y, jp) == states[i + 1] if False else False: pass
                setter = states[i + 1]
                if (y, jp) == setter: eff = True                 # A': the setter's own start leaves R_i
                elif eps(y, jp) > Rk[i + 1]: eff = True        # A : Z outlasts the setter
            else: eff = True                                    # A, i = n
        else:                                         # end of Z meets state i
            if i == n_moves and jp >= 1 and sig(y, jp) < Rk[i]: eff = True  # B at the landing (j=0 ends are <= R_0 by definition)
            elif i < n_moves and (y, jp) == states[i + 1]: eff = True   # D: the setter's end meets its own start state: the move vanishes
            elif 1 <= i and i - 1 < n_moves:                    # C: eps_Z = R_i = eps of setter A_{i-1}, Z a blocker at R_{i-1}
                if (y, jp) != states[i] and sig(y, jp) < Rk[i - 1] < eps(y, jp) + F(0): eff = True
        if eff: out.append((s, i, (y, a, jp)))
    return (out[0] if out else None), steps
def observed_next(p, q, s0, N=800):
    lab0 = label(rho_at(p, q, s0)); prev = s0
    for k in range(1, N + 1):
        s = s0 + (1 - s0) * F(k, N)
        if label(rho_at(p, q, s)) != lab0:
            lo, hi = prev, s
            for _ in range(60):
                mid = (lo + hi) / 2
                if label(rho_at(p, q, mid)) == lab0: lo = mid
                else: hi = mid
            return float((lo + hi) / 2), float(prev), float(s)
        prev = s
    return None, None, None
if __name__ == "__main__":
    nrun = int(sys.argv[1]); rnd = random.Random(314); tot = ok = 0; bad = []; nopred = 0
    bases = [("AP", [F(x) for x in range(1, 8)]), ("g15", [F(x) for x in (1, 2, 3, 4, 5, 6, 15)]),
             ("mixed", [F(x, 10) for x in (10, 17, 29, 41, 58, 77, 93)]), ("mixed2", [F(x, 10) for x in (10, 12, 33, 61, 64, 79, 88)]),
             ("3AP", [F(3 * x) for x in range(1, 8)])]
    for name, base in bases:
        for r in range(nrun):
            k = rnd.choice((1, 2, 3, 4)); movers = tuple(sorted(rnd.sample(range(7), k)))
            p = list(base); q = [F(0)] * 7
            for m in movers: q[m] = max(F(3, 10), base[m] + F(rnd.randint(-150, 450), 100)) - base[m]
            for t in range(3):
                s0 = F(rnd.randint(1, 9999), 10007)
                pred, steps = predicted_next(p, q, s0)
                obs, a, b = observed_next(p, q, s0)
                tot += 1
                if obs is None and pred is None: ok += 1; continue
                if obs is None or pred is None:
                    bad.append((name, movers, float(s0), "pred" if pred else "none", pred[0].__float__() if pred else None, obs)); continue
                if a - 1e-12 <= float(pred[0]) <= b + 1e-12 and abs(float(pred[0]) - obs) < 1e-6: ok += 1
                else: bad.append((name, movers, float(s0), float(pred[0]), obs, pred[2]))
    print("next-change predictions:", tot, "; equal to the observed next change:", ok, "; not:", len(bad))
    for b in bad[:15]: print("  MISMATCH", b)
