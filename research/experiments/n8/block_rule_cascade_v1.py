#!/usr/bin/env python3
"""Block rule and bounded region, tested through the cascade (exact integers/Fractions only, no floats).

Cascade semantics are Fresh/Framework.lean literally:
  InWay d t        :  distInt(d t) < 1/8
  nextOpening d t  :  (ceil(d t - 1/8) + 1/8) / d
  IsMove           :  none in the way -> fixed;  else t' = max over in-the-way d of nextOpening d t
  start            :  t0 = 1/(8 d_min).   Reading coordinate  R = 8 d_min t.
Integer disparity sets S (reading sets); all arithmetic on t = p/q with integers.
"""
import sys, itertools
from fractions import Fraction as Fr
from math import gcd, ceil

def in_way(d, p, q):            # distInt(d p/q) < 1/8
    r = (d * p) % q
    return 8 * min(r, q - r) < q

def next_open(d, p, q):         # (ceil(d t - 1/8) + 1/8)/d as (num, den)
    k = -((q - 8 * d * p) // (8 * q))        # ceil((8 d p - q)/(8 q))
    return (8 * k + 1, 8 * d)

def cascade(S):
    """S: sorted tuple of positive ints.  Returns dict with t*, moves, setter(s), opener(s), closer(s)."""
    dmin = S[0]
    p, q = 1, 8 * dmin
    moves = 0
    setters = (dmin,)                 # at the start d_min sits at exactly 1/8
    while True:
        way = [d for d in S if in_way(d, p, q)]
        if not way:
            break
        best = None; bs = []
        for d in way:
            a, b = next_open(d, p, q)
            g = gcd(a, b); a //= g; b //= g
            if best is None or a * best[1] > best[0] * b:
                best = (a, b); bs = [d]
            elif a * best[1] == best[0] * b:
                bs.append(d)
        p, q = best
        moves += 1
        setters = tuple(bs)
        if moves > 100000:
            return None
    # opener set: d with d t == 1/8 mod 1 ; closer set: least zone start >= t
    openers = tuple(d for d in S if (8 * d * p - q) % (8 * q) == 0)
    cl = None; cs = []
    for d in S:
        # smallest N with (N - 1/8)/d >= t  <=>  N >= d t + 1/8  <=> 8 q N >= 8 d p + q
        N = -((-(8 * d * p + q)) // (8 * q))
        a, b = 8 * N - 1, 8 * d
        if cl is None or a * cl[1] < cl[0] * b:
            cl = (a, b); cs = [d]
        elif a * cl[1] == cl[0] * b:
            cs.append(d)
    t = Fr(p, q); tc = Fr(cl[0], cl[1])
    return dict(t=t, R=8 * dmin * t, moves=moves, setters=setters, openers=openers,
                closers=tuple(cs), tclose=tc, cell=tc - t)

def clear_at(S, t):
    p, q = t.numerator, t.denominator
    return all(not in_way(d, p, q) for d in S)

def first_lonely_by_openings(S, jmax):
    """Independent check (boundary-set/localisation): least lonely opening (j+1/8)/e >= 1/(8 dmin)."""
    lo = Fr(1, 8 * S[0]); best = None
    for e in S:
        j0 = max(0, ceil(lo * e - Fr(1, 8)))
        for j in range(j0, j0 + jmax):
            t = Fr(8 * j + 1, 8 * e)
            if t < lo: continue
            if best is not None and t >= best: break
            if clear_at(S, t):
                best = t; break
    return best

def rank(S, d): return S.index(d) + 1


# ---------------------------------------------------------------------------------------------
# derived objects
# ---------------------------------------------------------------------------------------------
def cascade_from(S, t0):
    """The cascade (IsMove iterated) started at t0 instead of 1/(8 d_min): first fixed point."""
    p, q = t0.numerator, t0.denominator
    while True:
        way = [d for d in S if in_way(d, p, q)]
        if not way:
            return Fr(p, q)
        best = None
        for d in way:
            a, b = next_open(d, p, q)
            if best is None or a * best[1] > best[0] * b:
                best = (a, b)
        g = gcd(best[0], best[1]); p, q = best[0] // g, best[1] // g

def separated(T, S):
    """Separated8 T S, literally: some m with nonempty slow part {<= m}, nonempty fast part {> m}, T c <= x across."""
    for m in range(min(S), max(S)):
        lo = [s for s in S if s <= m]; hi = [s for s in S if s > m]
        if lo and hi and all(T * c <= x for c in lo for x in hi):
            return True
    return False

def rmax(S):
    return max(Fr(S[i + 1], S[i]) for i in range(len(S) - 1))

# ---------------------------------------------------------------------------------------------
# experiments
# ---------------------------------------------------------------------------------------------
import collections, time
from multiprocessing import Pool

def cores_upto(maxsize, B):
    for k in range(1, maxsize + 1):
        for C in itertools.combinations(range(1, B + 1), k):
            yield C

def block_start(T, M):            # least integer x with T*M <= x
    return ceil(Fr(T) * M)

# ---- section 0: cross-checks ----------------------------------------------------------------
def section0():
    out = []
    hand = [  # (S, t*, moves, setter)   derived by hand from InWay / nextOpening, see header comments
        ((1, 2), Fr(1, 8), 0, (1,)),
        ((1, 8), Fr(9, 64), 1, (8,)),
        ((1, 2, 3, 4, 5, 7, 8), Fr(9, 56), 2, (7,)),          # paper P7.1 worked example, certificate (e,j)=(7,1)
        ((1, 2, 3, 4, 5, 6, 7), Fr(1, 8), 0, (1,)),            # d_max <= 7 d_min
        ((2, 3, 16), Fr(9, 128), 1, (16,)),
    ]
    out.append("0. CROSS-CHECKS")
    out.append("  hand values: 8 d_min t0 = 1; (1,8): 8*(1/8)=1 in way, next opening (1+1/8)/8 = 9/64; (2,3,16): t0=1/16, 16/16=1 in way,")
    out.append("  next opening (9/8)/16 = 9/128, then 2*9/128=9/64, 3*9/128=27/128, 16*9/128=9/8 all clear.")
    for S, t, m, st in hand:
        r = cascade(S)
        ok = (r['t'] == t and r['moves'] == m and r['setters'] == st)
        assert ok, (S, r)
        out.append(f"  S={S}: t*={r['t']} moves={r['moves']} setter={r['setters']} R*={r['R']}  hand-value match: {ok}")
    n = 0; bad = 0; byk = collections.Counter()
    for k in range(1, 8):
        Bk = {1: 40, 2: 30, 3: 20, 4: 18, 5: 14, 6: 13, 7: 13}[k]
        for S in itertools.combinations(range(1, Bk + 1), k):
            r = cascade(S); b = first_lonely_by_openings(S, 400); n += 1; byk[k] += 1
            if r is None or b != r['t'] or not clear_at(S, r['t']): bad += 1
    out.append(f"  cascade landing vs independent search (least lonely opening (j+1/8)/e >= 1/(8 d_min), e in S, any j): {n} sets, mismatches {bad}")
    out.append(f"  sets per size: {dict(byk)}")
    # R=1 criterion: no move iff no reading rho = d/d_min has rho mod 8 in (-1,1)  (cascade coordinate, definitional)
    nbad = 0; N = 0
    for S in itertools.combinations(range(1, 15), 5):
        r = cascade(S); N += 1
        rho_clear = all(min(Fr(d, S[0]) % 8, 8 - Fr(d, S[0]) % 8) >= 1 for d in S)
        if (r['moves'] == 0) != rho_clear: nbad += 1
    out.append(f"  no-move  <=>  every rho=d/d_min has rho mod 8 in [1,7]  : {N} sets, mismatches {nbad}")
    return out

# ---- section A: one (f, T) cell of the block study --------------------------------------------
FPARAMS = {1: (6, 8, 192), 2: (5, 9, 40), 3: (4, 8, 22), 4: (3, 8, 16)}   # f -> (max |C|, core bound, window width)

def taskA(args):
    f, T = args
    cs, B, W = FPARAMS[f]
    N = 0
    typ = collections.Counter(); setter = collections.Counter(); closer = collections.Counter()
    moves = collections.Counter(); dsetidx = collections.Counter()
    ident_bad = 0; r7 = 0; maxR = Fr(0)
    xl0 = 0; xlpos = 0; xlpos_viol_f4 = 0; f1_suff_viol = 0; f1_nec_viol = 0
    maxDxmin = Fr(0)
    land_by_core = collections.defaultdict(set)
    for C in cores_upto(cs, B):
        if len(C) + f > 7: continue
        rc = cascade(C); tC = rc['t']; tcl = rc['tclose']; L = tcl - tC; M = max(C)
        x0 = block_start(T, M)
        for F in itertools.combinations(range(x0, x0 + W), f):
            S = C + F; r = cascade(S); N += 1
            u = cascade_from(F, tC)
            if u <= tcl: ok = (r['t'] == u)
            else: ok = (r['t'] > tcl)
            if not ok: ident_bad += 1
            ty = 'U' if u == tC else ('D' if u <= tcl else 'X')
            typ[ty] += 1
            land_by_core[C].add(r['t'])
            sc = 'block' if all(d in F for d in r['setters']) else ('core' if all(d in C for d in r['setters']) else 'mixed')
            setter[ty, sc] += 1
            cc = 'block' if all(d in F for d in r['closers']) else ('core' if all(d in C for d in r['closers']) else 'mixed')
            closer[ty, cc] += 1
            moves[min(r['moves'], 5)] += 1
            if ty == 'D' and sc == 'block': dsetidx[F.index(r['setters'][-1]) if len(r['setters']) else -1] += 1
            if r['R'] > 7: r7 += 1
            maxR = max(maxR, r['R'])
            Dxm = (u - tC) * F[0]
            maxDxmin = max(maxDxmin, Dxm)
            if ty == 'X':
                if L == 0: xl0 += 1
                else:
                    xlpos += 1
                    if not (4 * L * F[0] < f): xlpos_viol_f4 += 1
            if f == 1:
                x = F[0]
                if 4 * L * x >= 1 and ty == 'X': f1_suff_viol += 1      # sufficiency: 4 L x >= 1  =>  not X
                if ty == 'X' and L > 0 and not (4 * L * x < 1): f1_nec_viol += 1
    varies = sum(1 for C, s in land_by_core.items() if len(s) > 1)
    return (f, T, dict(N=N, typ=dict(typ), setter=dict(setter), closer=dict(closer), moves=dict(moves),
            dsetidx=dict(dsetidx), ident_bad=ident_bad, r7=r7, maxR=maxR, xl0=xl0, xlpos=xlpos,
            xlpos_viol=xlpos_viol_f4, f1_suff_viol=f1_suff_viol, maxDxmin=maxDxmin,
            ncores=len(land_by_core), varies=varies))

TLIST = [Fr(2), Fr(5, 2), Fr(3), Fr(4), Fr(6), Fr(8), Fr(17, 2), Fr(9), Fr(12), Fr(16), Fr(24), Fr(32)]

def fmtT(T): return str(T) if T.denominator == 1 else f"{T.numerator}/{T.denominator}"

def sectionA():
    out = []
    out.append("A. BLOCK RULE: core C (|C|+f <= 7, values <= B), block F of f integers in [ceil(T*max C), ceil(T*max C)+W), all combinations")
    out.append("   core family per f: (max|C|, B, W) = " + str({f: FPARAMS[f] for f in FPARAMS}))
    out.append("   t_C, L_C = landing and landing-cell length of the CORE ALONE (cell = [t_C, tclose_C], tclose_C = least zone start after t_C).")
    out.append("   u = first point >= t_C clear for F alone (cascade of F started at t_C).  Type U: u=t_C;  D: t_C<u<=tclose_C;  X: u>tclose_C.")
    out.append("   identity checked on every set: t*(S)=u if u<=tclose_C, and t*(S)>tclose_C otherwise  (violations column).")
    tasks = [(f, T) for f in (1, 2, 3, 4) for T in TLIST]
    with Pool(10) as P:
        res = P.map(taskA, tasks, chunksize=1)
    for f in (1, 2, 3, 4):
        out.append("")
        out.append(f"  f = {f}")
        out.append("   T      N        U       D       X      X(L=0) X(L>0)  ident_viol  R*>7  maxR*   cores  cores-with-varying-landing  max (u-t_C)*x_min")
        for (ff, T, d) in res:
            if ff != f: continue
            t = d['typ']
            out.append(f"   {fmtT(T):<6} {d['N']:<8} {t.get('U',0):<7} {t.get('D',0):<7} {t.get('X',0):<7} {d['xl0']:<6} {d['xlpos']:<6} {d['ident_bad']:<10} {d['r7']:<5} {str(d['maxR']):<8} {d['ncores']:<6} {d['varies']:<26} {d['maxDxmin']} ({float(d['maxDxmin']):.4f})")
        out.append("   setter / closer class of the landing, by type (T = 2, 9, 32):")
        for (ff, T, d) in res:
            if ff == f and T in (Fr(2), Fr(9), Fr(32)):
                out.append(f"     T={fmtT(T)}: setter {dict(sorted(d['setter'].items()))}")
                out.append(f"            closer {dict(sorted(d['closer'].items()))}")
                out.append(f"            moves  {dict(sorted(d['moves'].items()))} (5 = five or more);   D with block setter, setter's index inside F (0 = smallest): {dict(sorted(d['dsetidx'].items()))}")
        if f == 1:
            tot = sum(d['f1_suff_viol'] for (ff, T, d) in res if ff == 1)
            out.append(f"   f=1 criterion: L_C>0 and 4*L_C*x >= 1  =>  not X.   violations over all T: {tot}")
        v = sum(d['xlpos_viol'] for (ff, T, d) in res if ff == f)
        out.append(f"   X with L_C>0 and NOT (4*L_C*x_min < f): {v}   [OBS diagnostic only; f/(4 x_min) is a sum of zone widths, not offered as a lemma]")
    return out

# ---- section A2: no uniform T0 (exact), family showing dependence on F at every T ---------------
def sectionA2():
    out = []
    out.append("A2. NO UNIFORM THRESHOLD IN T: cores with L_C>0 and the T needed so that a single block runner x >= T*max C stays inside the core's cell")
    out.append("   (needed: 1/(4 L_C max C) <= T, from t_x - t_C < 1/(4x) and the cell having length L_C).  sup over cores:")
    for cs, B in [(3, 12), (3, 24), (3, 40), (4, 20), (6, 10), (6, 13)]:
        mx = Fr(0); arg = None; n = 0; n0 = 0
        for C in cores_upto(cs, B):
            rc = cascade(C); L = rc['cell']; n += 1
            if L == 0: n0 += 1; continue
            v = 1 / (4 * L * max(C))
            if v > mx: mx = v; arg = (C, str(rc['t']), str(L))
        out.append(f"   |C|<={cs}, values<={B}: cores {n}, cores with L_C=0: {n0}, sup 1/(4 L max C) = {mx} ({float(mx):.3f}) at C,t_C,L_C = {arg}")
    out.append("   L_C = 0 cores (cell is a point: some core runner sits at exactly 7/8 of a lap at t_C, i.e. c*t_C = N - 1/8) keep escapes X at EVERY T tested (X(L=0) column of section A).")
    out.append("")
    out.append("A3. DEPENDENCE ON F AT EVERY T (family, f=1). Core C=(1,), t_C=1/8, R_C=1.  Block x=8k (x*t_C = k, a whole lap, in the way):")
    for T in (2, 9, 32, 128, 1024):
        xs = [x for x in range(block_start(T, 1), block_start(T, 1) + 40) if x % 8 == 0][:2]
        row = []
        for x in xs:
            r = cascade((1, x)); row.append(f"x={x}: R*={r['R']} (=1+1/x: {r['R'] == 1 + Fr(1, x)}), setter {r['setters']}")
        x1 = block_start(T, 1)
        r1 = cascade((1, x1 + 1 if x1 % 8 == 0 else x1))
        row.append(f"x={x1 + 1 if x1 % 8 == 0 else x1} (not = 0 mod 8): R*={r1['R']}")
        out.append(f"   T={T}: " + ";  ".join(row))
    out.append("   Singleton cores (d_min = max C = c), one block x: R*=1 iff rho = x/c has rho mod 8 in [1,7] (period 8 in rho, no threshold).")
    bad = 0; N = 0; first_nonperiodic = None
    for c in range(1, 9):
        for x in range(2 * c, 400 * c):
            if x == c: continue
            r = cascade((c, x)); N += 1
            rho = Fr(x, c); cl = min(rho % 8, 8 - rho % 8) >= 1
            if (r['R'] == 1) != cl: bad += 1
    out.append(f"   checked {N} pairs (c<=8, 2c<=x<400c): mismatches {bad}")
    out.append("   Displacement size for L_C>0 cores: max over F-window of (R* - R_C) times x_min, by T (f=1, C in {(1,2,3),(2,5),(3,4,5),(1,)} ):")
    for C in [(1, 2, 3), (2, 5), (3, 4, 5), (1, 2, 3, 4, 5, 6)]:
        rc = cascade(C)
        row = []
        for T in (2, 9, 32, 128, 1024):
            x0 = block_start(T, max(C)); mxv = Fr(0)
            for x in range(x0, x0 + 600):
                r = cascade(C + (x,)); mxv = max(mxv, (r['R'] - rc['R']) * x)
            row.append(f"T={T}: {float(mxv):.4f}")
        out.append(f"     C={C}: R_C={rc['R']}, L_C={rc['cell']}  max (R*-R_C)*x over x in [T max C, +600): " + ", ".join(row))
    out.append("   Wide-ratio sample for the displacement diagnostic (f=2, F=(x,y), y up to 40x): max (u-t_C)*x_min over cores |C|<=3 B<=9:")
    mx = Fr(0); arg = None
    for C in cores_upto(3, 9):
        tC = cascade(C)['t']
        for x in range(9 * max(C), 9 * max(C) + 30):
            for y in sorted(set(int(x * m) + s for m in (1, 2, 3, 5, 8, 13, 21, 40) for s in (1, 2, 3, 5, 7))):
                if y <= x: continue
                u = cascade_from((x, y), tC); v = (u - tC) * x
                if v > mx: mx = v; arg = (C, x, y)
    out.append(f"     max = {mx} ({float(mx):.4f}) at (C,x,y) = {arg}")
    return out


# ---- section A4: exceptions traced, and the first-displacement formula -----------------------------
def trace(S):
    p, q = 1, 8 * S[0]; lines = []
    while True:
        way = [d for d in S if in_way(d, p, q)]
        lines.append(f"      t={Fr(p, q)}  (R={8 * S[0] * Fr(p, q)})  in the way: {way}")
        if not way: break
        best = None; arg = None
        for d in way:
            a, b = next_open(d, p, q)
            if best is None or a * best[1] > best[0] * b: best = (a, b); arg = d
        g = gcd(best[0], best[1]); p, q = best[0] // g, best[1] // g
        lines[-1] += f"  -> opening of {arg} at {Fr(p, q)}"
    return lines

def sectionA4():
    out = []
    out.append("A4. EXCEPTIONS UNDERSTOOD (type X = the block pushes t out of the core's landing cell).")
    out.append("   (a) L_C = 0: C=(1,2,3,4,5,7), t_C=1/8, closer 7 sits at 7*(1/8)=7/8 = 1 - 1/8, the cell [1/8, 1/8] is a point.  F=(x,), x=8k (x*t_C=k, in the way):")
    for x in (48, 256):
        S = (1, 2, 3, 4, 5, 7, x)
        out.append(f"     S={S}:"); out += trace(S)
    out.append("   the first block opening 1/8 + 1/(8x) is past the point, so runner 7 (7t = 7/8 + 7/(8x), inside its zone) is in the way, and the cascade continues on the CORE's scale.")
    out.append("   (b) L_C > 0 but 4 L_C x < 1: C=(1,6,8), t_C=9/64, L_C=1/192 (opener 8, closer 6).  Block x with x*t_C in the way and x < 48 (= 1/(4 L_C)):")
    rc = cascade((1, 6, 8))
    out.append(f"     core alone: t_C={rc['t']} setters={rc['setters']} closers={rc['closers']} tclose={rc['tclose']} cell L_C={rc['cell']}")
    shown = 0
    for x in range(16, 400):
        r = cascade((1, 6, 8, x))
        if r['t'] > rc['tclose'] and shown < 2:
            out.append(f"     x={x}: 4*L_C*x = {4 * rc['cell'] * x}  (<1: {4 * rc['cell'] * x < 1})"); out += trace((1, 6, 8, x)); shown += 1
    xs_all = [x for x in range(16, 2000) if cascade((1, 6, 8, x))['t'] > rc['tclose']]
    out.append(f"     all x in [16,2000) with t*(1,6,8,x) > tclose_C: {xs_all}; largest = {max(xs_all)} < 48: {max(xs_all) < 48}")
    out.append("   (c) first-displacement formula, f=1, core with R_C=1 (no move): x in the way at t_C=1/(8 d_min) iff s = x mod 8 d_min (signed, |s| < d_min); its opening is")
    out.append("       R = 1 + (d_min - s)/x.  Checked: when the block is the only runner moved (moves = 1) R* equals that value; other cases (moves > 1) counted.")
    ok = 0; more = 0; bad = 0
    for C in cores_upto(5, 9):
        rc = cascade(C)
        if rc['moves'] != 0: continue
        dm = C[0]
        for x in range(3 * max(C), 3 * max(C) + 8 * dm * 4):
            s = ((x + 4 * dm) % (8 * dm)) - 4 * dm
            if abs(s) >= dm: continue
            r = cascade(C + (x,))
            if r['moves'] == 1:
                if r['R'] == 1 + Fr(dm - s, x): ok += 1
                else: bad += 1
            else: more += 1
    out.append(f"       moves=1 and formula holds: {ok};  moves=1 and formula fails: {bad};  moves>1 (a core runner is pushed in the way after the displacement): {more}")
    return out

# ---- section B -----------------------------------------------------------------------------------
BPOP = [(7, 24), (6, 26), (5, 34), (4, 50), (3, 80)]
TB = (2, 3, 4, 8)

def taskB(kB):
    k, B = kB
    rows = []
    for S in itertools.combinations(range(1, B + 1), k):
        r = cascade(S)
        rm = rmax(S)
        rows.append((S, r['t'], r['R'], r['moves'], rank(S, r['setters'][-1]), tuple(rank(S, d) for d in r['closers']), rm))
    return k, B, rows

def sectionB():
    out = []
    out.append("B. BOUNDED REGION: all k-subsets of [1..B] as reading sets, for (k,B) in " + str(BPOP))
    with Pool(5) as P:
        res = P.map(taskB, BPOP, chunksize=1)
    for k, B, rows in res:
        out.append("")
        out.append(f"  k={k}, B={B}: {len(rows)} sets")
        # separated equivalence
        mism = 0
        for S, t, R, mv, sr, cr, rm in rows[::7]:
            for T in TB:
                if separated(T, S) != (rm >= T): mism += 1
        out.append(f"   Separated8 T (literal) <=> max consecutive ratio >= T : checked on every 7th set x T in {TB}, mismatches {mism}")
        for T in TB:
            sep = [x for x in rows if x[6] >= T]; non = [x for x in rows if x[6] < T]
            out.append(f"   T={T}: separated {len(sep)}, NOT separated {len(non)}")
            for name, grp in (("sep", sep), ("non", non)):
                if not grp: continue
                n = len(grp)
                mv = collections.Counter(min(x[3], 4) for x in grp)
                sr = collections.Counter(x[4] for x in grp)
                cr = collections.Counter(min(x[5]) if len(x[5]) else 0 for x in grp)
                R1 = sum(1 for x in grp if x[2] == 1)
                maxR = max(x[2] for x in grp)
                R7 = sum(1 for x in grp if x[2] > 7)
                out.append(f"     {name}: n={n} R*=1: {R1} ({R1/n:.4f})  moves {dict(sorted(mv.items()))} (4=four+)  max R*={maxR} ({float(maxR):.3f})  R*>7: {R7}")
                out.append(f"          setter rank {dict(sorted(sr.items()))}")
                out.append(f"          closer rank (least rank of closer set) {dict(sorted(cr.items()))}")
        # theorem-8 consequence on rmax
        moved = [x for x in rows if x[3] > 0]
        viol = sum(1 for x in moved if not (x[6] ** (k - 1) > 7))
        mn = min(x[6] for x in moved)
        out.append(f"   moved sets (R*>1): {len(moved)}; each satisfies rmax^(k-1) > 7 (consequence of: moved => rho_max > 7, Thm 8): violations {viol}; least rmax among moved sets = {mn} ({float(mn):.4f}); 7^(1/(k-1)) = {7 ** (1.0 / (k - 1)):.4f} (float, display only)")
    # clusters
    out.append("")
    out.append("  Scale clusters at T=8 (= 1 + #{consecutive ratios >= 8}); outcome by cluster count, all populations pooled per k:")
    for k, B, rows in res:
        byc = collections.defaultdict(collections.Counter)
        for S, t, R, mv, sr, cr, rm in rows:
            nc = 1 + sum(1 for i in range(len(S) - 1) if Fr(S[i + 1], S[i]) >= 8)
            c = byc[nc]; c['n'] += 1; c['R=1'] += (R == 1); c['moves>=2'] += (mv >= 2); c['setter_last_rank'] += (sr == k)
        out.append(f"   k={k}: " + "; ".join(f"clusters={nc}: n={c['n']} R*=1 {c['R=1']/c['n']:.3f} moves>=2 {c['moves>=2']/c['n']:.3f} setter=top {c['setter_last_rank']/c['n']:.3f}" for nc, c in sorted(byc.items())))
    # top-element irrelevance by ratio of the top two
    out.append("")
    out.append("  Probability that dropping the TOP reading leaves the landing unchanged (type U for f=1 on natural sets), by ratio s_k/s_{k-1}:")
    for k, B in ((7, 24), (4, 50)):
        stat = collections.defaultdict(lambda: [0, 0])
        for S in itertools.combinations(range(1, B + 1), k):
            same = cascade(S)['t'] == cascade(S[:-1])['t']
            ratio = Fr(S[-1], S[-2])
            key = next(T for T in (Fr(5, 4), Fr(3, 2), Fr(2), Fr(3), Fr(4), Fr(8), Fr(16), Fr(10**9)) if ratio < T)
            stat[key][0] += 1; stat[key][1] += same
        out.append(f"   k={k}, B={B}: " + "; ".join(f"ratio<{fmtT(key) if key < 10**8 else 'inf'}: {v[1]}/{v[0]}={v[1]/v[0]:.4f}" for key, v in sorted(stat.items())))
    # identity on natural separated sets: core = below the lowest cut with ratio >= T
    out.append("")
    out.append("  Decomposition identity on natural separated sets (core = elements below the LOWEST cut with ratio >= T, F = the rest):")
    for k, B, rows in res:
        for T in (3, 8):
            cnt = collections.Counter(); bad = 0
            for S, t, R, mv, sr, cr, rm in rows:
                cut = next((i for i in range(len(S) - 1) if Fr(S[i + 1], S[i]) >= T), None)
                if cut is None: continue
                C = S[:cut + 1]; F = S[cut + 1:]
                rc = cascade(C); tC = rc['t']; tcl = rc['tclose']
                u = cascade_from(F, tC)
                ok = (t == u) if u <= tcl else (t > tcl)
                if not ok: bad += 1
                cnt['U' if u == tC else ('D' if u <= tcl else 'X')] += 1
            out.append(f"   k={k}, B={B}, T={T}: types {dict(cnt)}, identity violations {bad}")
    return out

if __name__ == "__main__":
    t0 = time.time()
    print("block_rule_cascade_v1.py  -- exact integer/Fraction arithmetic; cascade = Fresh/Framework.lean InWay, nextOpening, IsMove")
    print("Rules: 1, 5, 6, 7, 13, 15, 16, 18, 21.  Grades: [OBS] data;  [reasoned] argument not formalised;  no [L] claims in this file.")
    print()
    for sec in (section0, sectionA, sectionA2, sectionA4, sectionB):
        for line in sec(): print(line)
        print(flush=True)
    print(f"(elapsed {time.time() - t0:.0f}s)")
