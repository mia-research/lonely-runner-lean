"""cluster_transfer_claude_v1 (2026-10-05): exact hypotheses for the slow-reading / phased
cluster reduction (cluster_transfer_claude_brief_v1.md, deliverables 1-4).

Setup.  R = 8 d_min t, d_min = 1, readings rho >= 1.  Cluster rho_i = c*x_i (x_i >= 1,
x_min = 1).  Decompose R = a + u/c.  A cluster reading's actual mod-8 value is
(c*x_i)*R = phi_i + x_i*u  with  phi_i = (a*c*x_i) mod 8  (exact identity).  A slow
reading s gives s*R = a*s + (s/c)*u.  Clear is (d*R) mod 8 in [1,7] inclusive; blocked
(strict capture) is outside it, matching quantity_tests_v1.cascade's cd(d*t) </>= 1/8 after
R = 8t.  On an admissible window [A,B] where every slow reading is jointly clear, the
full cascade's blocked set equals the cluster's alone while the state stays in [A,B]:
this is LRC.InertReading.iterate_insert_clear (LonelyRunner/LRC/Spec/InertReadingN.lean),
applied once per slow reading -- ALREADY PROVED, not re-derived here. Below: (1) an exact
identity/correspondence check between the phased-cluster formula and the real restricted
cascade on bounded families; (2) small counterexamples to two simplifications that drop
information the theorem needs; (3) a finite-window rank-word vs transfer-map test; (4) a
recognizer for the already-proved train collapse (LonelyRunner/LRC/Spec/TrainCollapseN.lean).

Caps enforced: <=2000 arrangements, 60s monotonic deadline, cascade move cap 300 per case
(unfinished cases are reported separately, never read as terminated), single foreground
process, no multiprocessing/stdin, exact Fraction/int arithmetic throughout, output <100KB.
"""
import time, random
from fractions import Fraction as F
from math import floor, ceil

T0 = time.monotonic()
DEADLINE = T0 + 60.0
MOVE_CAP = 300
ARR_BUDGET = 2000
_used = 0


class Budget(Exception):
    pass


def spend(n=1):
    global _used
    _used += n
    if _used > ARR_BUDGET:
        raise Budget("arrangement budget exceeded (%d)" % _used)
    if time.monotonic() > DEADLINE:
        raise Budget("60s deadline exceeded")


# ---------- exact R-space max-exit cascade --------------------------------------------
# clear <=> (d*R + delta) mod 8 in [1,7] (inclusive); blocked (strict capture) otherwise.

def frac8(x):
    return x - 8 * floor(x / 8)


def in_way(d, R, delta=F(0)):
    v = frac8(d * R + delta)
    return v < 1 or v > 7


def nxt_R(d, R, delta=F(0)):
    return (8 * ceil((d * R + delta - 1) / 8) + 1 - delta) / d


def run(spec, R0, cap=MOVE_CAP, exit_hi=None):
    """spec: [(d, delta), ...]. Generic max-exit cascade from R0.
    Returns (status, R_end, moves); status in {'landed','exited','cap'}.
    Ties: every setter attaining the max is kept."""
    R, moves = R0, []
    for _ in range(cap):
        B = [(d, delta) for d, delta in spec if in_way(d, R, delta)]
        if not B:
            return 'landed', R, moves
        n = max(nxt_R(d, R, delta) for d, delta in B)
        setters = tuple((d, delta) for d, delta in B if nxt_R(d, R, delta) == n)
        moves.append((R, tuple(B), setters, n))
        if exit_hi is not None and n > exit_hi:
            return 'exited', n, moves
        R = n
    return 'cap', R, moves


def good_intervals(x, Rlo, Rhi):
    out = []
    k = max(0, floor((x * Rlo - 7) / 8))
    while True:
        a, b = F(8 * k + 1) / x, F(8 * k + 7) / x
        if a > Rhi:
            break
        lo, hi = max(a, Rlo), min(b, Rhi)
        if lo <= hi:
            out.append((lo, hi))
        k += 1
    return out


def intersect(A, B):
    i = j = 0
    out = []
    while i < len(A) and j < len(B):
        lo, hi = max(A[i][0], B[j][0]), min(A[i][1], B[j][1])
        if lo <= hi:
            out.append((lo, hi))
        if A[i][1] < B[j][1]:
            i += 1
        else:
            j += 1
    return out


def joint_windows(readings, Rlo=F(1), Rhi=F(400)):
    L = [(Rlo, Rhi)]
    for x in readings:
        L = intersect(L, good_intervals(F(x), Rlo, Rhi))
        if not L:
            return []
    return L


def slow_admissible_window(s, Rmax=F(400)):
    W = joint_windows(s, F(1), Rmax)
    return W[0] if W else None


# ---------- Deliverable 1: exact identity / correspondence check ----------------------

def phased_predict(c, x, a, A, B, cap=MOVE_CAP):
    phis = [(a * c * xi) % 8 for xi in x]
    spec = list(zip(x, phis))
    u_exit = c * (B - A)
    status, u_land, moves = run(spec, F(0), cap=cap, exit_hi=u_exit)
    R_pred = a + u_land / c
    return status, R_pred, moves, phis


def true_restricted(s, c, x, A, B, cap=MOVE_CAP):
    spec = [(F(si), F(0)) for si in s] + [(c * xi, F(0)) for xi in x]
    return run(spec, A, cap=cap, exit_hi=B)


def identity_sweep(cases):
    """cases: list of (s, c, x). For each: find the admissible slow-clear window [A,B],
    then compare the real restricted cascade against the phased-cluster prediction.
    Returns tally + up to 5 recorded mismatches (would indicate a bug or a genuinely
    broken hypothesis, not expected if the window is nondegenerate)."""
    tally = dict(total=0, no_window=0, degenerate=0, matched=0, mismatched=0,
                  ties_seen=0, near_boundary_seen=0, unfinished=0)
    mismatches = []
    for s, c, x in cases:
        spend()
        W = slow_admissible_window(s)
        if W is None:
            tally['no_window'] += 1
            continue
        A, B = W
        if A == B:
            tally['degenerate'] += 1
            continue
        a = A
        st_true, R_true, mv_true = true_restricted(s, c, x, A, B)
        st_ph, R_pred, mv_ph, phis = phased_predict(c, x, a, A, B)
        if any(p in (F(0), F(1), F(7)) for p in phis):
            tally['near_boundary_seen'] += 1
        if any(len(mv[2]) > 1 for mv in mv_true) or any(len(mv[2]) > 1 for mv in mv_ph):
            tally['ties_seen'] += 1
        if st_true == 'cap' or st_ph == 'cap':
            tally['unfinished'] += 1
            continue
        tally['total'] += 1
        if st_true == st_ph and R_true == R_pred:
            tally['matched'] += 1
        else:
            tally['mismatched'] += 1
            if len(mismatches) < 5:
                mismatches.append(dict(s=s, c=c, x=x, A=A, B=B, st_true=st_true,
                                        R_true=R_true, st_ph=st_ph, R_pred=R_pred))
    return tally, mismatches

def gen_identity_cases(rng, n):
    """Bounded random family: 1-2 slow readings (small integers), c from small to large,
    x a small set of Fraction cluster offsets chosen so at least one is typically blocked
    at the window's own entry (forcing real cascade moves, not just a trivial landing)."""
    out = []
    for _ in range(n):
        nS = rng.choice([1, 1, 2])
        s = [F(1)] + sorted(rng.sample(range(2, 40), nS - 1))
        c = F(rng.choice([9, 11, 16, 23, 50, 97, 331, 5003, 20011]))
        nX = rng.choice([2, 3, 3, 4])
        num = sorted(rng.sample(range(1, 97), nX - 1))
        den = rng.choice([1, 2, 3, 4, 6])
        x = [F(1)] + [F(n_, den) for n_ in num]
        x = sorted(set(x))
        if len(x) < 2:
            continue
        out.append((s, c, x))
    return out

# ---------- Deliverable 2: counterexamples to two simplifications ---------------------

def naive_phase_drop(c, x, a, A, B, cap=MOVE_CAP):
    """WRONG: force every phi_i = 0, i.e. pretend the window entry carries no phase
    (valid only when a = 0, e.g. cluster_window_v1.py's single-slow-reading case)."""
    spec = [(xi, F(0)) for xi in x]
    u_exit = c * (B - A)
    status, u_land, moves = run(spec, F(0), cap=cap, exit_hi=u_exit)
    return status, a + u_land / c


def naive_restart_own_opening(c, x, A, B, cap=MOVE_CAP):
    """WRONG (cluster_window_v1.py's model, applied outside its own hypothesis a=0):
    find the cluster's OWN first lonely R'-window (fresh start R'=1) with hi>=c, take
    R'_cand = max(lo, c), predict R = R'_cand / c -- ignores the real window [A,B].
    Any joint-clear window has width <= 6 (reading x=1's own window width, the
    narrowest possible since every x_i >= 1), so a bounded local scan around c
    suffices and keeps this independent of how large c is."""
    for pad in (400, 4000, 40000):
        lo_scan = max(F(1), c - 7)
        W = joint_windows(x, lo_scan, c + pad)
        for lo, hi in W:
            if hi >= c:
                Rp = max(lo, c)
                return 'landed', Rp / c
    return 'cap', None


def counterexample_search(cases):
    tally = dict(total=0, phase_drop_wrong=0, restart_wrong=0, both_wrong=0,
                 unfinished=0)
    examples = []
    for s, c, x in cases:
        spend()
        W = slow_admissible_window(s)
        if W is None:
            continue
        A, B = W
        if A == B:
            continue
        a = A
        st_true, R_true, mv_true = true_restricted(s, c, x, A, B)
        if st_true == 'cap':
            tally['unfinished'] += 1
            continue
        tally['total'] += 1
        st_pd, R_pd = naive_phase_drop(c, x, a, A, B)
        st_ro, R_ro = naive_restart_own_opening(c, x, A, B)
        wrong_pd = not (st_pd == st_true and R_pd == R_true)
        wrong_ro = not (st_ro == st_true and R_ro == R_true)
        if wrong_pd:
            tally['phase_drop_wrong'] += 1
        if wrong_ro:
            tally['restart_wrong'] += 1
        if wrong_pd and wrong_ro:
            tally['both_wrong'] += 1
        if (wrong_pd or wrong_ro) and len(examples) < 6:
            examples.append(dict(s=s, c=c, x=x, a=a, A=A, B=B, R_true=R_true,
                                  phase_drop=(wrong_pd, R_pd), restart=(wrong_ro, R_ro)))
    return tally, examples

# ---------- Deliverable 3: rank word vs transfer map ----------------------------------

def setter_lap(d, R, delta):
    return ceil((d * R + delta - 1) / 8)


def window_run_signature(spec, R0, exit_hi, cap=MOVE_CAP):
    """Run clipped to [R0, exit_hi]. Returns:
    coarse  = tuple(|B_j| for each move)                       (ordered blocking sizes)
    fine    = tuple((rank(setter) at move j, its lap) for each move, rank by sorted
               order of the base readings d at call time)       (the transfer map)
    status, R_land."""
    order = sorted(range(len(spec)), key=lambda i: spec[i][0])
    rank = {spec[i][0]: r for r, i in enumerate(order)}
    status, R, moves = run(spec, R0, cap=cap, exit_hi=exit_hi)
    coarse = tuple(len(B) for _, B, _, _ in moves)
    fine = tuple(tuple(sorted((rank[d], setter_lap(d, Rj, delta)) for d, delta in st))
                 for Rj, _, st, _ in moves)
    return coarse, fine, status, R


def rank_word_vs_transfer_map(cases):
    """Group configs by the coarse blocking-size word (clipped to their own admissible
    window); within a group, check whether the fine (rank, lap) transfer signature also
    agrees. Equal coarse word with unequal fine signature is the trap named in the
    brief: do not read a shared rank word as a shared mechanism."""
    groups = {}
    for s, c, x in cases:
        spend()
        W = slow_admissible_window(s)
        if W is None:
            continue
        A, B = W
        if A == B:
            continue
        a = A
        phis = [(a * c * xi) % 8 for xi in x]
        spec = list(zip(x, phis))
        u_exit = c * (B - A)
        coarse, fine, status, R = window_run_signature(spec, F(0), u_exit)
        if status == 'cap':
            continue
        groups.setdefault(coarse, []).append((fine, x, phis, c, status, R))
    same_word_same_map = 0
    same_word_diff_map = 0
    diff_examples = []
    for coarse, members in groups.items():
        if len(members) < 2:
            continue
        fines = set(m[0] for m in members)
        if len(fines) == 1:
            same_word_same_map += len(members) - 1
        else:
            same_word_diff_map += 1
            if len(diff_examples) < 4:
                diff_examples.append(dict(coarse=coarse, n_members=len(members),
                                           n_distinct_fine=len(fines),
                                           sample=[(m[1], m[2], m[3], m[5]) for m in members[:3]]))
    return dict(groups=len(groups), multi_member_groups=sum(1 for m in groups.values() if len(m) > 1),
                same_word_same_map=same_word_same_map, same_word_diff_map=same_word_diff_map), diff_examples

# ---------- Deliverable 4: recognize (don't recount) the proved train collapse --------
# Cites LonelyRunner/LRC/Spec/TrainCollapseN.lean (lonely_of_train_collapse), already
# proved, no sorry: core C (positive, <=m), train offsets E (<=m), |C|+|E|<=7, N>=56m,
# and i<j in E with no e in E at the midpoint (2e != i+j for all e in E). When a readings
# set matches this shape the isolation instant for EVERY such N is already known to exist
# in [2 tau, 2 tau + 1/N) -- no cascade re-run per N is needed.

def recognize_train_collapse(S):
    S = sorted(set(int(v) for v in S))
    n = len(S)
    if n < 2 or any(v <= 0 for v in S):
        return None
    for k in range(2, n + 1):
        top, rest = S[n - k:], S[:n - k]
        if len(rest) + k > 7:
            continue
        m = max([0] + rest + [top[-1] - top[0]])
        N = top[0]
        if N < 56 * m:
            continue
        E = [e - N for e in top]
        pair = None
        for ii in range(len(E)):
            for jj in range(ii + 1, len(E)):
                i, j = E[ii], E[jj]
                if all(2 * e != i + j for e in E):
                    pair = (i, j)
                    break
            if pair:
                break
        if pair:
            return dict(C=tuple(rest), N=N, E=tuple(E), m=m, pair=pair)
    return None


def train_collapse_sweep(sets):
    hit = 0
    examples = []
    for S in sets:
        spend()
        r = recognize_train_collapse(S)
        if r:
            hit += 1
            if len(examples) < 4:
                examples.append((tuple(sorted(S)), r))
    return dict(total=len(sets), recognized=hit), examples

# ---------- driver ----------------------------------------------------------------

def gen_integer_train_cases(rng, n):
    """Additive-offset shapes matching TrainCollapseN's own hypotheses (core/offsets
    bounded by m, N scaled relative to m), mixed with shapes that just miss one
    hypothesis (margin or cardinality), to show the recognizer discriminates."""
    out = []
    for _ in range(n):
        m = rng.randint(2, 6)
        ncore = rng.randint(0, 3)
        core = sorted(rng.sample(range(1, m + 1), min(ncore, m))) if ncore else []
        ne = rng.randint(2, 7 - len(core))
        ne = max(ne, 2)
        E = sorted(set([0] + rng.sample(range(0, m + 1), min(ne - 1, m + 1))))
        margin_ok = rng.random() < 0.6
        N = rng.randint(56, 60) * m if margin_ok else rng.randint(1, 55) * max(m, 1)
        out.append([v for v in core] + [N + e for e in E])
    return out


if __name__ == '__main__':
    report = []

    def emit(line):
        report.append(line)

    try:
        emit("=== Deliverable 1: identity / correspondence sweep ===")
        cases1 = gen_identity_cases(random.Random(7), 220)
        tally1, mism1 = identity_sweep(cases1)
        emit("tally: %s" % tally1)
        emit("mismatches (bugs or genuine hypothesis breaks, expect none): %d" % len(mism1))
        for m_ in mism1:
            emit("  MISMATCH %s" % m_)

        emit("")
        emit("=== Deliverable 2: counterexamples to dropping the phase / restarting fresh ===")
        cases2a = [(s, c, x) for s, c, x in gen_identity_cases(random.Random(11), 150) if len(s) == 1]
        cases2b = [(s, c, x) for s, c, x in gen_identity_cases(random.Random(23), 150) if len(s) > 1]
        t2a, ex2a = counterexample_search(cases2a)
        t2b, ex2b = counterexample_search(cases2b)
        emit("single-slow-reading cases (a = A = 1 always): %s" % t2a)
        emit("  -> dropping the phase is wrong even here (phi_i = c*x_i mod 8 generically != 0);")
        emit("     'restart at own opening' happens to coincide with cluster_window_v1.py's own")
        emit("     model and is correct whenever a = 1 (its stated use case).")
        emit("multi-slow-reading cases (a = A generically != 1): %s" % t2b)
        headline = dict(s=[1, 32], c=9, x=[1, 3, 7])
        s, c, x = [F(1), F(32)], F(9), [F(1), F(3), F(7)]
        A, B = slow_admissible_window(s)
        st_true, R_true, mv = true_restricted(s, c, x, A, B)
        st_pd, R_pd = naive_phase_drop(c, x, A, A, B)
        st_ro, R_ro = naive_restart_own_opening(c, x, A, B)
        emit("headline small counterexample (both simplifications, one arrangement):")
        emit("  S = {1,9,27,32,63} (=s union c*x, c=9, x=[1,3,7], s=[1,32])")
        emit("  admissible slow-clear window [A,B] = [%s, %s]" % (A, B))
        emit("  TRUE restricted landing:          R = %s  (%s, %d move)" % (R_true, st_true, len(mv)))
        emit("  naive phase-drop (phi_i := 0):     R = %s  (%s)  -- wrong" % (R_pd, st_pd))
        emit("  naive restart-at-own-opening:      R = %s  (%s)  -- outside [A,B], wrong" % (R_ro, st_ro))

        emit("")
        emit("=== Deliverable 3: ordered-blocking word vs transfer map ===")
        cases3 = gen_identity_cases(random.Random(31), 200)
        t3, diffs3 = rank_word_vs_transfer_map(cases3)
        emit("tally: %s" % t3)
        emit("same coarse word, different (rank,lap) transfer map -- the trap: %d groups" %
             t3['same_word_diff_map'])
        for d in diffs3[:2]:
            emit("  coarse=%s: %d members, %d distinct transfer maps" %
                 (d['coarse'], d['n_members'], d['n_distinct_fine']))

        emit("")
        emit("=== Deliverable 4: recognize (don't recount) the proved train collapse ===")
        sets4 = gen_integer_train_cases(random.Random(41), 300)
        t4, ex4 = train_collapse_sweep(sets4)
        emit("tally: %s" % t4)
        for S, r in ex4:
            emit("  recognized %s -> %s (cite LonelyRunner/LRC/Spec/TrainCollapseN.lean, no re-run)" % (S, r))

        emit("")
        emit("=== Caps ===")
        emit("arrangements spent: %d / %d budget; elapsed %.2fs / 60s deadline" %
             (_used, ARR_BUDGET, time.monotonic() - T0))
    except Budget as e:
        emit("")
        emit("STOPPED EARLY (cap hit): %s" % e)
        emit("arrangements spent: %d / %d; elapsed %.2fs" % (_used, ARR_BUDGET, time.monotonic() - T0))

    out = "\n".join(report)
    with open("cluster_transfer_claude_v1.out", "w") as f:
        f.write(out + "\n")
    print(out)
