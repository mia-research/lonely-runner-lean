#!/usr/bin/env python3
"""slot_deform_v1 -- order six, slot occupancy and flank types along the straight-line deformation
from the AP (1,2,3,4,5) to each SixResidual set (first column of six_cascade_observe_v1.tsv).
Observation only. Exact Fraction arithmetic throughout.

Lonely interval identity. A connected lonely interval of v has a constant lap vector
m_i = floor(v_i t); conversely, for a lap vector m the lonely set with those laps is the single
closed interval I_m(v) = [max_i (m_i+1/6)/v_i, min_i (m_i+5/6)/v_i] (empty when max > min).
Following "the lonely interval containing (or nearest to) the previous instant" is implemented
as: keep m fixed while I_m(v(s)) is non-empty. Non-emptiness is the set of s with
(m_i+1/6) v_j(s) <= (m_j+5/6) v_i(s) for all i,j, linear in s, so the death instant is exact.

Instant rule (fixed): the LEFT ENDPOINT L(s) of the followed interval. (The cascade instant of
any arrangement is the left endpoint of its own interval, so this is "the cascade instant
restricted to the followed interval".)

Events inside a segment of fixed m are located exactly: with the binding (entry) runner b fixed,
every comparison that can change the type -- binding switch, reading vs a slot boundary
(1/4, 5/12, 7/12, 3/4), reading vs reading -- is a linear equation in s. All roots are collected
and the type is evaluated on every sub-interval (at its midpoint and at both ends +- eps) and at
each root. Guard: the three in-sub-interval evaluations must agree (count reported).

After a death at s*, restart from the cascade instant of v(s* + EPS), EPS = 1/10^12, and check
that the restart lap vector is alive back to s* (count reported).
"""
import sys, ast
from fractions import Fraction as F
from collections import Counter, defaultdict

AP = (1, 2, 3, 4, 5)
SIXTH, FIVE6 = F(1, 6), F(5, 6)
BOUNDS = (F(1, 4), F(5, 12), F(7, 12), F(3, 4))
EPS = F(1, 10**12)


def frac(x):
    return x - (x.numerator // x.denominator)


def vs(S, s):
    return tuple((1 - s) * a + s * b for a, b in zip(AP, S))


def cascade(v):
    t = F(1, 6 * v[0]); moves = 0
    while True:
        nxt = []
        for d in v:
            x = d * t; N = round(x)
            if abs(x - N) < SIXTH:
                nxt.append(F(6 * N + 1, 6 * d))
        if not nxt:
            return t, moves
        t = max(nxt); moves += 1


def lonely(v, t):
    return all(SIXTH <= frac(d * t) <= FIVE6 for d in v)


def laps(v, t):
    return tuple((d * t).numerator // (d * t).denominator for d in v)


def type_at(v, t):
    """type = (occupancy by rank, entry-flank ranks, exit-flank ranks); slot ties as 'k|k+1'."""
    r = [frac(d * t) for d in v]
    occ = []
    for x in r:
        y = 6 * x
        k = y.numerator // y.denominator
        if y - k == F(1, 2):
            occ.append(f"{k}|{k+1}")
        else:
            occ.append(str(round(y)))
    lo, hi = min(r), max(r)
    ent = tuple(i + 1 for i, x in enumerate(r) if x == lo)
    ex = tuple(i + 1 for i, x in enumerate(r) if x == hi)
    return (tuple(occ), ent, ex)


def fmt_type(ty):
    occ, ent, ex = ty
    e = lambda t: "+".join(map(str, t))
    return f"[{','.join(occ)}] in{e(ent)} out{e(ex)}"


def slot_counts(occ):
    c = Counter()
    for o in occ:
        if "|" not in o:
            c[int(o)] += 1
    return c


def ideal_distance(ty):
    occ, ent, ex = ty
    if any("|" in o for o in occ):
        return None, None
    sl = [int(o) for o in occ]
    off = sum(1 for i, k in enumerate(sl) if k != i + 1)
    perm = tuple(sl) if sorted(sl) == [1, 2, 3, 4, 5] else None
    return off, perm


def alive_range(S, m):
    """closed s-interval in [0,1] where I_m(v(s)) is non-empty, or None."""
    lo, hi = F(0), F(1)
    for i in range(5):
        for j in range(5):
            if i == j: continue
            # (m_i+1/6) v_j(s) - (m_j+5/6) v_i(s) <= 0 ; v_k(s) = AP_k + s (S_k - AP_k)
            a = (m[i] + SIXTH) * AP[j] - (m[j] + FIVE6) * AP[i]
            b = (m[i] + SIXTH) * (S[j] - AP[j]) - (m[j] + FIVE6) * (S[i] - AP[i])
            if b == 0:
                if a > 0: return None
            elif b > 0:
                hi = min(hi, -a / b)
            else:
                lo = max(lo, -a / b)
    return (lo, hi) if lo <= hi else None


def Lm(v, m):
    return max((mi + SIXTH) / d for mi, d in zip(m, v))


def Rm(v, m):
    return min((mi + FIVE6) / d for mi, d in zip(m, v))


def roots(S, m, s0, s1):
    """all s in (s0,s1) solving the linear equations that can change the type at L(s)."""
    D = [S[k] - AP[k] for k in range(5)]
    out = set()

    def lin(a, b):  # a + b s = 0
        if b != 0:
            r = -a / b
            if s0 < r < s1: out.add(r)

    for b in range(5):
        cb = m[b] + SIXTH
        for i in range(5):
            if i != b:  # binding switch: (m_i+1/6) v_b = cb v_i
                lin((m[i] + SIXTH) * AP[b] - cb * AP[i], (m[i] + SIXTH) * D[b] - cb * D[i])
            for c in BOUNDS:  # reading_i = c : v_i cb = (c+m_i) v_b
                lin(AP[i] * cb - (c + m[i]) * AP[b], D[i] * cb - (c + m[i]) * D[b])
            for j in range(i + 1, 5):  # reading_i = reading_j : (v_i - v_j) cb = (m_i-m_j) v_b
                lin((AP[i] - AP[j]) * cb - (m[i] - m[j]) * AP[b], (D[i] - D[j]) * cb - (m[i] - m[j]) * D[b])
    return sorted(out)


def classify(ta, tb):
    """event kinds between two types (before ta, after tb)."""
    kinds = []
    oa, ea, xa = ta; ob, eb, xb = tb
    for i in range(5):
        if oa[i] != ob[i]:
            kinds.append(f"slot r{i+1}:{oa[i]}->{ob[i]}")
    ca, cb = slot_counts(oa), slot_counts(ob)
    for k in range(1, 6):
        if ca[k] < 2 <= cb[k]: kinds.append(f"share-on s{k}")
        if ca[k] >= 2 > cb[k]: kinds.append(f"share-off s{k}")
    if ea != eb: kinds.append(f"entry {'+'.join(map(str,ea))}->{'+'.join(map(str,eb))}")
    if xa != xb: kinds.append(f"exit {'+'.join(map(str,xa))}->{'+'.join(map(str,xb))}")
    return kinds


def kind_of(k):
    return k.split()[0]


def run_path(S, guard, ctrl, keep_detail=False):
    """returns dict with events, segments."""
    events = []      # (s, kinds or ['DEATH'], type_before, type_at, type_after)
    segs = []
    s = F(0)
    m = (0, 0, 0, 0, 0)
    rng = alive_range(S, m)
    assert rng is not None and rng[0] == 0
    first = True
    while True:
        lo, hi = rng
        s_start = s
        segs.append((m, s_start, hi))
        crit = [s_start] + roots(S, m, s_start, hi) + [hi]
        prev_ty = None
        for a, b in zip(crit, crit[1:]):
            if a == b:
                continue
            mid = (a + b) / 2
            v = vs(S, mid); t = Lm(v, m)
            ty = type_at(v, t)
            # guard: ends of the sub-interval
            span = b - a
            for p in (a + span / 1000, b - span / 1000):
                vp = vs(S, p)
                guard["checks"] += 1
                if type_at(vp, Lm(vp, m)) != ty:
                    guard["mismatch"] += 1
            # control: direct lonely check at L, at mid of [L,R], and outside the interval
            R = Rm(v, m)
            ctrl["n"] += 1
            ok = lonely(v, t) and lonely(v, (t + R) / 2) and laps(v, t) == m
            dlt = F(1, 10**9)
            ok = ok and not lonely(v, t - dlt * t) and not lonely(v, R + dlt * R)
            ctrl["agree"] += ok
            if prev_ty is not None and ty != prev_ty:
                va = vs(S, a)
                events.append((a, classify(prev_ty, ty), prev_ty, type_at(va, Lm(va, m)), ty, m))
            prev_ty = ty
            if keep_detail is not False:
                keep_detail.append((mid, m, t, [frac(d * t) for d in v], ty))
        if hi == 1:
            v1 = vs(S, F(1))
            final_ty = type_at(v1, Lm(v1, m))
            return dict(events=events, segs=segs, final_m=m, final_ty=final_ty, first_ty=None)
        # death at hi
        vh = vs(S, hi); ty_death = type_at(vh, Lm(vh, m))
        sn = hi + EPS
        vn = vs(S, sn)
        T, _ = cascade(vn)
        m2 = laps(vn, T)
        rng2 = alive_range(S, m2)
        ctrl["restart"] += 1
        ctrl["restart_back"] += (rng2[0] <= hi)
        s_new = max(rng2[0], hi)
        vn2 = vs(S, s_new); ty_after = type_at(vn2, Lm(vn2, m2))
        before = prev_ty if prev_ty is not None else ty_death
        events.append((hi, ["DEATH"], before, ty_death, ty_after, (m, m2)))
        m, rng, s = m2, rng2, s_new


def main():
    k = int(sys.argv[1]) if len(sys.argv) > 1 else 1
    rows = []
    with open("six_cascade_observe_v1.tsv") as fh:
        next(fh)
        for line in fh:
            f = line.rstrip("\n").split("\t")
            rows.append((ast.literal_eval(f[0]), F(f[5])))
    rows = rows[::k]
    print(f"slot_deform_v1: {len(rows)} sets (every {k}-th row of six_cascade_observe_v1.tsv)")
    print("instant rule: left endpoint of the followed lonely interval (lap vector held fixed)")
    print("event location: exact rational roots of linear equations in s; no grid resolution")
    print()

    guard = Counter(); ctrl = Counter()
    T_agree = 0
    step1 = Counter(); dist_off = Counter(); perms = Counter(); tieT = 0
    ev_kind = Counter(); per_path_kinds = defaultdict(Counter)
    trans = Counter(); death_prec = Counter(); deaths_per_path = Counter()
    deaths_after0 = Counter(); final_eq = 0; final_eq_m = 0
    restart0 = Counter(); n_events = Counter()
    examples = []
    for idx, (S, Ttsv) in enumerate(rows):
        T, mv = cascade(S)
        T_agree += (T == Ttsv)
        ty = type_at(S, T)
        step1[ty] += 1
        if any("|" in o for o in ty[0]) or len(ty[1]) > 1 or len(ty[2]) > 1:
            tieT += 1
        off, perm = ideal_distance(ty)
        dist_off[off] += 1
        if perm is not None: perms[perm] += 1
        R = run_path(S, guard, ctrl)
        evs = R["events"]
        nd = sum(1 for e in evs if e[1] == ["DEATH"])
        deaths_per_path[nd] += 1
        deaths_after0[sum(1 for e in evs if e[1] == ["DEATH"] and e[0] > 0)] += 1
        n_events[len(evs)] += 1
        for j, e in enumerate(evs):
            for kk in e[1]:
                ev_kind[kind_of(kk)] += 1
            trans[(fmt_type(e[2]), fmt_type(e[4]))] += 1
            if e[1] == ["DEATH"]:
                if e[0] == 0:
                    restart0[(e[5][1], Lm(AP, e[5][1]))] += 1
                # immediately preceding event within the dying segment
                prev = None
                for q in range(j - 1, -1, -1):
                    if evs[q][1] == ["DEATH"]:
                        break
                    prev = evs[q]; break
                if e[0] == 0:
                    death_prec["(death at s=0, path start)"] += 1
                elif prev is None:
                    death_prec["(none in segment)"] += 1
                else:
                    death_prec[" & ".join(kind_of(x) for x in prev[1])] += 1
        final_eq += (R["final_ty"] == ty)
        final_eq_m += (R["final_m"] == laps(S, T))
        if len(examples) < 400:
            examples.append((S, T, ty, R))

    print("== CONTROLS ==")
    print(f"cascade T recomputed == TSV T: {T_agree}/{len(rows)}")
    print(f"lonely-interval direct check (L lonely, (L+R)/2 lonely, laps(L)=m, L-1e-9L and R+1e-9R not lonely): "
          f"{ctrl['agree']}/{ctrl['n']} sampled sub-interval points agree")
    print(f"guard (type at both ends of each sub-interval == type at its midpoint): "
          f"{guard['checks']-guard['mismatch']}/{guard['checks']}")
    print(f"restarts after a death: {ctrl['restart']}; restart lap vector alive back to the death s: "
          f"{ctrl['restart_back']}/{ctrl['restart']}")
    print()
    print("== TASK 1: type at the cascade instant T ==")
    print(f"distinct types: {len(step1)}; types carrying a tie: {tieT}")
    ideal = (("1", "2", "3", "4", "5"), (1,), (5,))
    print(f"sets at the ideal type: {step1[ideal]}")
    print(f"sets at the reversed type [5,4,3,2,1] in5 out1: {step1[(('5','4','3','2','1'),(5,),(1,))]}")
    print("commonest 25 types (count, off-slot runners, permutation if one per slot):")
    for ty, c in step1.most_common(25):
        off, perm = ideal_distance(ty)
        print(f"  {c:6d}  {fmt_type(ty)}  off={off}  perm={perm}")
    print("runners off their ideal slot (count of sets):", dict(sorted(dist_off.items(), key=lambda x: (x[0] is None, x[0]))))
    print(f"one-runner-per-slot occupancies: {sum(perms.values())} sets, {len(perms)} distinct permutations:")
    for p, c in perms.most_common():
        print(f"  {c:6d}  {p}")
    ent = Counter(t[1] for t in step1.elements()); ex = Counter(t[2] for t in step1.elements())
    print("entry flank rank at T:", dict(ent.most_common()))
    print("exit flank rank at T:", dict(ex.most_common()))
    print()
    print("== TASK 2: deformation paths ==")
    print("events per path (count of paths):", dict(sorted(n_events.items())))
    print("event kinds (total over all paths):", dict(ev_kind.most_common()))
    print("deaths per path (count of paths):", dict(sorted(deaths_per_path.items())))
    print("deaths per path excluding the death at s=0 (count of paths):", dict(sorted(deaths_after0.items())))
    print("restart after the s=0 death: lap vector m and its interval's left endpoint at s=0 (top 15):")
    for (mm, L0), c in restart0.most_common(15):
        print(f"  {c:6d}  m={mm}  L(0)={L0}")
    print(f"distinct restart lap vectors at s=0: {len(restart0)}")
    print(f"type at s=1 equals step-1 type at T: {final_eq}/{len(rows)}; same lap vector: {final_eq_m}/{len(rows)}")
    print("event immediately preceding each death (within the dying segment):")
    for kk, c in death_prec.most_common():
        print(f"  {c:6d}  {kk}")
    print(f"distinct transitions (type -> type): {len(trans)}; commonest 30:")
    for (a, b), c in trans.most_common(30):
        print(f"  {c:6d}  {a}  ->  {b}")
    print()
    print("== TASK 3: worked examples ==")
    for S, T, ty, R in [examples[0], examples[1], examples[len(examples) // 2]]:
        print(f"S={S}  cascade T={T}  readings at T={[str(frac(d*T)) for d in S]}  type={fmt_type(ty)}")
        print(f"  segments (lap vector, s from, s to): {[(m, str(a), str(b)) for m, a, b in R['segs']]}")
        for e in R["events"]:
            s = e[0]; m = e[5] if e[1] != ['DEATH'] else e[5][0]
            v = vs(S, s); L = Lm(v, m)
            print(f"  s={s}  v={[str(x) for x in v]}  L={L}  readings={[str(frac(d*L)) for d in v]}")
            print(f"     {e[1]}  {fmt_type(e[2])} -> {fmt_type(e[4])}" + (f"  restart m={e[5][1]}" if e[1] == ['DEATH'] else ""))
        print(f"  final type at s=1: {fmt_type(R['final_ty'])}")


if __name__ == "__main__":
    main()
