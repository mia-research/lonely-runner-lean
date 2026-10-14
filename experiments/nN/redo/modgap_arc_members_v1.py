"""modgap_arc_members_v1 (2026-10-06): the arc criterion A on the stored residual members and the hard sets, which all lie
outside the box 36/5 <= rho_i <= 16 of modgap_tree_exact_v1 (their largest ratio d_7/d_1 exceeds 16).  Exact (Fractions).
A(S): m = d_min, C = S minus m; the 1/7-cascade of C started at 1/(7m) lands at most 6/(7m)  (u = 7 m t in [1, 6]).
[L] lonely_cons_of_arc (BystanderN.lean): A(S) implies S lonely at 1/7, hence at 1/8 (lonelyList_seven_to_eight).
Recorded per population: rho_min = d_2/d_1 and rho_max = d_7/d_1 against the box; A true/false; for A false, the landing
u* = 7 m t* of C's cascade from u = 1 (exact), whether it lies in d_min's second arc [8, 13], and rho_min.
Populations: C, BS (full_residual), DA, DB (divisible_members_v2), T1 (members_5978 minus those), ../hard_sets_41_60.json.
Also: the 1,566 gcd-1 7-subsets of [1, 44] on which A is false (modgap_arc_enum_v2_fails_top44.json, E415), checked against the
full residual predicate (full_residual, all 22 fields) and the record's v1 residual (eight_residual, shift_levels_six_eight_v1.py).
"""
import sys, json, collections
from fractions import Fraction as F
sys.path.insert(0, '.')
from members_reach_check_v1 import load, full_residual, cd

E7 = F(1, 7)


def cascade_from(C, t, thr=E7, cap=100000):
    for _ in range(cap):
        bl = [d for d in C if cd(d * t) < thr]
        if not bl:
            return t
        t = max(F(7 * round(d * t) + 1, 7 * d) for d in bl)
    return None


def arc(S):
    m = S[0]; C = S[1:]
    t = cascade_from(C, F(1, 7 * m))
    return t, 7 * m * t


if __name__ == '__main__':
    out = open('modgap_arc_members_v1.out', 'w'); out.write(__doc__ + "\n")
    st = json.load(open('divisible_members_v2.json'))
    Cm = [S for S in dict.fromkeys(load('../residual_members_C_list_v1.json')) if full_residual(S)]
    BS = [S for S in dict.fromkeys(load('both_shadowed_members_v1.json')) if full_residual(S)]
    DA = [tuple(sorted(S)) for S in st['A']]; DB = [tuple(sorted(S)) for S in st['B']]
    raw = json.load(open('members_5978_v1.json')); known = set(Cm) | set(BS) | set(DA) | set(DB)
    T1 = [S for S in dict.fromkeys(tuple(sorted(x[2])) for x in raw) if S not in known]
    hard = [tuple(sorted(S)) for S in json.load(open('../hard_sets_41_60.json'))]
    for nm, sets in [('C', Cm), ('BS', BS), ('DA', DA), ('DB', DB), ('T1', T1), ('hard41_60', hard)]:
        c = collections.Counter(); fails = []
        for S in sets:
            m = S[0]; rmin = F(S[1], m); rmax = F(S[-1], m)
            t, u = arc(S)
            ok = u <= 6
            c[('A', ok)] += 1
            c[('box', rmin >= F(36, 5) and rmax <= 16)] += 1
            c[('rho_min >= 36/5', rmin >= F(36, 5), 'A', ok)] += 1
            if not ok:
                fails.append((rmin, u, S))
                c[('A false: landing in d_min second arc [8, 13]', 8 <= u <= 13)] += 1
        out.write("\n%s: %d sets: %s\n" % (nm, len(sets), dict(sorted(c.items(), key=str))))
        for rmin, u, S in sorted(fails)[-5:]:
            out.write("  A false, largest rho_min: rho_min = %s (num/den digits %d/%d), landing u = %s\n" %
                      ('%d/%d' % (rmin.numerator, rmin.denominator) if len(str(rmin.numerator)) < 12 else '[%d-digit]' % len(str(rmin.numerator)),
                       len(str(rmin.numerator)), len(str(rmin.denominator)),
                       u if len(str(u.numerator)) < 30 else '[%d-digit fraction]' % len(str(u.numerator))))
        out.flush()
    fl = [tuple(sorted(x)) for x in json.load(open('modgap_arc_enum_v2_fails_top44.json'))]
    here = __import__('os').getcwd(); __import__('os').chdir('..')
    sys.argv = ['x', '30']
    ns = {}
    exec(open('shift_levels_six_eight_v1.py').read().split('t0 = time.time()')[0], ns)
    __import__('os').chdir(here)
    inv1 = [S for S in fl if ns['eight_residual'](S)]
    out.write("\nA false on [1,44] (E415): %d sets; in the full residual: %d; in the v1 residual: %d: %s\n" %
              (len(fl), sum(1 for S in fl if full_residual(S)), len(inv1), inv1))
    out.close(); print(open('modgap_arc_members_v1.out').read()[len(__doc__):])
