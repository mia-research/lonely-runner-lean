"""modgap_rule_v1 (2026-10-06): candidate rules tying the residue pattern to the landing, read off modgap_landing_v1,
tested on the sets they were read from and on new arrangements.  Exact (integers and Fractions).  Exceptions are
written individually to modgap_rule_v1_exceptions.out.

Notation: t* the cascade's first lonely instant, [t*, t_R] its lonely component, a_A/q_A its least-denominator
rational (the least modulus whose residue map accounts for the landing, P2), e an opener (e t* = J + 1/8), f a
closer (f t_R = M + 7/8).  Balance point b: the unique instant of [t*, t_R] at which the subject's two flank gaps are
equal (the right gap increases and the left gap decreases along the component).
[P] (by hand, checked below as BCHK): at b the right-flank reading d1 and the left-flank reading d2 stand at mirror
positions, so (d1 + d2) b is a whole number: b is a grid instant of modulus (d1 + d2)/g, the modulus at which
d1 = -d2.  At b the margin min_d ||d b|| is the largest over the component.

Rules (each statement is about the least-denominator rational a_A/q_A of the landing component):
  RU [P] if a unit fraction lies in [t*, t_R] then a_A/q_A = 1/ceil(1/t_R) (modgap_map_v1 P6).  Derivation check.
  RM     otherwise a_A/q_A is the opener-closer mediant (J + M + 1)/(e + f) for some opener e and closer f.
  RB     otherwise a_A/q_A is the balance point b.
  RG     otherwise some pair of readings stands at mirror positions at a_A/q_A (q_A | d1 + d2, d1 != d2, or q_A | 2d):
         a_A/q_A is the mediant of an opening of d1 and an exit of d2 (same form as RM, another pair).
         Control for RG: the share of all residue isolations a/q, q <= 2 d_max, a/q <= 2, with a mirror pair.
  RD     D_max at the landing modulus: replace the fastest reading d_max by d_max + q_A (same residues mod q_A, so the
         same gaps at every q_A-grid instant).  Prediction: the new set's landing is the left end of the component of
         a_A/q_A (the landing grid is a function of the residue pattern mod q_A).
  Members (read on C, BS, DA, DB in modgap_landing_v1): RU applies to every member (MU); every q in [2, 64] divides
         some reading (MD); the least modulus <= 200 with a residue isolation is 67, 71 or 73 (MQ).
Populations.  Built on: S1, S2 and the stored members (as in modgap_landing_v1).  New arrangements (rule 10):
  T1  members_5978_v1.json, entries [id, type, readings], those not in C, BS, DA, DB (all pass full_residual)
  T2  every 7-subset of [1, 28] containing 1 with d_max >= 25 (d_min = 1; disjoint from S1)
  T3  every 7-subset of [1, 40] whose residues mod 8 are exactly {0, 1, 2, 3, 5, 6, 7}, gcd 1 (type (1;o,o,o,o,t,t))
"""
import sys, json, itertools, math, collections, time
from fractions import Fraction as F
from math import gcd
from functools import reduce
sys.path.insert(0, '.')
from modgap_lib_v1 import (load, full_residual, cascade, lonely, cd, frac, openers, component, simplest, positions,
                           is_iso, left_end, E8)

T0 = time.time()
E78 = F(7, 8)


def balance(S, t, tR):
    P = {d: frac(d * t) for d in S}
    gp = lambda s: min(P[d] + d * (s - t) for d in S)
    gm = lambda s: min(1 - P[d] - d * (s - t) for d in S)
    for d1 in S:
        for d2 in S:
            s = t + (1 - P[d1] - P[d2]) / (d1 + d2)
            if t <= s <= tR and gp(s) == gm(s):
                return s, d1, d2
    return None


def farey_parents(r):
    """Stern-Brocot parents of r = a/q (q > 1): the Farey neighbours L < r < U with det 1 and denominators < q."""
    a, q = r.numerator, r.denominator
    # L = l1/l2 with a*l2 - l1*q = 1, 0 < l2 < q
    l2 = pow(a, -1, q); l1 = (a * l2 - 1) // q
    u2 = q - l2; u1 = a - l1
    return F(l1, l2), F(u1, u2)


def mirror_pairs(S, a, q):
    pos = positions(S, a, q)
    mp = [(d1, d2) for d1, d2 in itertools.combinations(S, 2) if (pos[d1] + pos[d2]) % q == 0]
    hp = [d for d in S if 2 * pos[d] == q]
    cp = [(d1, d2) for d1, d2 in itertools.combinations(S, 2) if pos[d1] == pos[d2]]
    return mp, hp, cp


def study(S):
    t = cascade(S); tR, cl = component(S, t); op = openers(S, t)
    sA = simplest(t, tR); a, q = sA.numerator, sA.denominator
    unit = t < 1 and F(1, math.ceil(1 / tR)) >= t
    meds = {F(int(e * t - E8) + int(f * tR - E78) + 1, e + f): (e, f) for e in op for f in cl}
    b = balance(S, t, tR)
    return dict(S=S, t=t, tR=tR, op=op, cl=cl, sA=sA, unit=unit, meds=meds, b=b)


cnt = collections.Counter()
exo = open('modgap_rule_v1_exceptions.out', 'w')
exo.write("modgap_rule_v1 exceptions, one per line (exact).  RM/RB/RG lines: population, readings, t*, t_R, openers, "
          "closers, a_A/q_A, Farey parents L < t* and U > t_R (what forces a_A/q_A: the least-denominator rational of "
          "the component, its parents outside it), the opener-closer mediants, the balance point (b, d1, d2), mirror "
          "pairs, half readings, coincident pairs at a_A/q_A, and the class: 'mirror' (same form as RM, another pair), "
          "'coincidence only' (two readings at one position: a meeting instant), 'not understood' (neither).\n"
          "RD lines: population, readings, q_A, a_A, t*(S), t*(S'), left end of the a_A/q_A component of S', whether "
          "the shifted reading is the only reading of S in the way at t*(S') (forced: S and S' differ in that reading "
          "only), and the openers of S' at t*(S').\n")


def run_rules(name, sets, do_rd):
    out = []
    c = collections.Counter(); ctrl = collections.Counter(); bchk = [0, 0]
    rd = collections.Counter()
    for S in sets:
        r = study(S)
        t, tR, sA = r['t'], r['tR'], r['sA']; a, q = sA.numerator, sA.denominator
        # balance-point derivation check
        if r['b'] is not None:
            b, d1, d2 = r['b']
            ok = (((d1 + d2) * b).denominator == 1 and (frac(d1 * b) + frac(d2 * b) == 1 or (d1 == d2 and frac(d1 * b) == F(1, 2)))
                  and min(cd(d * b) for d in S) >= max(min(cd(d * s) for d in S) for s in (t, tR, sA)))
            bchk[0] += ok
        bchk[1] += 1
        if r['unit']:
            c['RU applies'] += 1
            c[('RU derivation', sA == F(1, math.ceil(1 / tR)))] += 1
        else:
            c['not U'] += 1
            rm = sA in r['meds']; rb = r['b'] is not None and sA == r['b'][0]
            mp, hp, cp = mirror_pairs(S, a, q); rg = bool(mp or hp)
            c[('RM', rm)] += 1; c[('RB', rb)] += 1; c[('RG', rg)] += 1; c[('RM or RB', rm or rb)] += 1
            if not rm or not rb or not rg:
                L, U = farey_parents(sA) if q > 1 else (None, None)
                forced = (L is not None and L < t and U > tR)
                cls = 'mirror' if rg else ('coincidence only' if cp else 'not understood')
                c[('exception class (not RM)', cls)] += (not rm)
                c[('Farey parents outside the component (not RM)', forced)] += (not rm)
                exo.write("%s RMBG rm=%d rb=%d rg=%d S=%s t*=%s t_R=%s op=%s cl=%s qA=%s L=%s U=%s forced=%s meds=%s b=%s "
                          "mirror=%s half=%s coinc=%s class=%s\n" %
                          (name, rm, rb, rg, S, t, tR, r['op'], r['cl'], sA, L, U, forced,
                           {str(k): v for k, v in r['meds'].items()}, (str(r['b'][0]), r['b'][1], r['b'][2]) if r['b'] else None,
                           mp, hp, cp, cls))
        if do_rd:
            dmax = S[-1]; d2 = dmax + q
            S2 = tuple(sorted(S[:-1] + (d2,)))
            t2 = cascade(S2); le = left_end(S2, a, q)
            ok = (t2 == le)
            rd[('RD', ok)] += 1
            if not ok:
                only = [d for d in S if cd(d * t2) < E8] == [dmax]
                op2 = openers(S2, t2)
                kind = 't\' < t*' if t2 < t else ('t\' = t*' if t2 == t else 't* < t\' < left end')
                rd[('RD exception', kind, 'only d_max in the way of S at t\'' if only else 'other', 'image opens' if d2 in op2 else 'another opens')] += 1
                exo.write("%s RD S=%s qA=%d aA=%d t*=%s t'=%s left_end=%s only_dmax_in_way=%s openers'=%s\n" %
                          (name, S, q, a, t, t2, le, only, op2))
            else:
                rd[('RD holds', 'same landing' if t2 == t else 'landing moved, same grid')] += 1
    return c, bchk, rd


def rg_control(sets, cap=3000):
    """Share of residue isolations (q <= 2 d_max, a/q <= 2) with a mirror pair, over the first `cap` sets."""
    tot = 0; mir = 0
    for S in sets[:cap]:
        for q in range(2, 2 * S[-1] + 1):
            for a in range(1, 2 * q + 1):
                if gcd(a, q) == 1 and is_iso(S, a, q):
                    tot += 1; mp, hp, cp = mirror_pairs(S, a, q); mir += bool(mp or hp)
    return mir, tot


def s1():
    for r in itertools.combinations(range(2, 25), 6):
        yield (1,) + r


def s2():
    pools = {r: [d for d in range(1, 41) if d % 8 == r] for r in range(8)}
    for m in itertools.combinations(pools[0], 2):
        for p in itertools.product(pools[1], pools[2], pools[3], pools[5], pools[7]):
            S = tuple(sorted(m + p))
            if reduce(gcd, S) == 1:
                yield S


def t2():
    for r in itertools.combinations(range(2, 29), 6):
        if r[-1] >= 25:
            yield (1,) + r


def t3():
    pools = {r: [d for d in range(1, 41) if d % 8 == r] for r in range(8)}
    for p in itertools.product(pools[0], pools[1], pools[2], pools[3], pools[5], pools[6], pools[7]):
        S = tuple(sorted(p))
        if reduce(gcd, S) == 1:
            yield S


out = open('modgap_rule_v1.out', 'w'); out.write(__doc__ + "\n")


def w(s):
    out.write(s + "\n"); out.flush(); print(s)


store = json.load(open('divisible_members_v2.json'))
C = [S for S in dict.fromkeys(load('../residual_members_C_list_v1.json')) if full_residual(S)]
BS = [S for S in dict.fromkeys(load('both_shadowed_members_v1.json')) if full_residual(S)]
DA = list(dict.fromkeys(tuple(sorted(S)) for S in store['A'])); DB = list(dict.fromkeys(tuple(sorted(S)) for S in store['B']))
known = set(C) | set(BS) | set(DA) | set(DB)
raw = json.load(open('members_5978_v1.json'))
T1 = [S for S in dict.fromkeys(tuple(sorted(x[2])) for x in raw) if S not in known]
T1fr = sum(1 for S in T1 if full_residual(S))

pops = [('S1 (built on)', list(s1()), True), ('S2 (built on)', list(s2()), True),
        ('members C+BS+DA+DB (built on)', C + BS + DA + DB, False),
        ('T2 (new)', list(t2()), True), ('T3 (new)', list(t3()), True), ('T1 (new members)', T1, False)]
for name, sets, do_rd in pops:
    c, bchk, rd = run_rules(name.split()[0], sets, do_rd)
    w("\n==== %s: %d sets   [elapsed %ds]" % (name, len(sets), time.time() - T0))
    if name.startswith('T1'):
        w("  T1: %d sets not in C/BS/DA/DB, of which full_residual %d" % (len(T1), T1fr))
    w("  balance-point derivation check (mirror flank pair, (d1+d2) b whole, margin at b >= margin at t*, t_R, a_A/q_A): [T %d/%d]" % tuple(bchk))
    w("  RU applies %d; RU derivation [T %d/%d]" % (c['RU applies'], c[('RU derivation', True)], c['RU applies']))
    nu = c['not U']
    for rr in ('RM', 'RB', 'RG', 'RM or RB'):
        w("  %-8s [T %d/%d]" % (rr, c[(rr, True)], nu))
    w("  exceptions to RM by class: %s" % {k[1]: v for k, v in c.items() if isinstance(k, tuple) and k[0] == 'exception class (not RM)'})
    w("  exceptions to RM with Farey parents of a_A/q_A outside [t*, t_R] (forcing check): %s" %
      {k[1]: v for k, v in c.items() if isinstance(k, tuple) and k[0].startswith('Farey')})
    if do_rd:
        w("  RD (d_max -> d_max + q_A): [T %d/%d]; holds: %s" % (rd[('RD', True)], rd[('RD', True)] + rd[('RD', False)],
          {k[1]: v for k, v in rd.items() if k[0] == 'RD holds'}))
        for k, v in sorted(rd.items(), key=str):
            if k[0] == 'RD exception':
                w("    RD exception %s: %d" % (k[1:], v))
    if name.split()[0] in ('S1', 'T2'):
        mir, tot = rg_control(sets)
        w("  RG control: residue isolations with a mirror pair, first 3000 sets: %d of %d" % (mir, tot))

# members-only rules
def mem_rules(sets):
    mu = md = mq = 0; kq = 0
    for S in sets:
        t = cascade(S); tR, cl = component(S, t)
        mu += (t < 1 and F(1, math.ceil(1 / tR)) >= t)
        md += all(any(d % q == 0 for d in S) for q in range(2, 65))
        q0 = None
        for q in range(2, 201):
            rs = [d % q for d in S]
            hit = next((a for a in range(1, q) if gcd(a, q) == 1 and all(q <= 8 * (a * r % q) <= 7 * q for r in rs)), None)
            if hit is not None:
                q0 = (hit, q); break
        mq += (q0 is not None and q0[1] in (67, 71, 73))
        kq += (q0 is not None and math.floor(q0[1] * t) == 0)
    return mu, md, mq, kq
for name, sets in (('members C+BS+DA+DB (built on)', C + BS + DA + DB), ('T1 (new members)', T1)):
    mu, md, mq, kq = mem_rules(sets)
    w("\n==== member rules on %s (%d sets): MU [T %d/%d]; MD [T %d/%d]; MQ [T %d/%d]; floor(q0 t*) = 0 [T %d/%d]" %
      (name, len(sets), mu, len(sets), md, len(sets), mq, len(sets), kq, len(sets)))
w("\ntotal elapsed %ds" % (time.time() - T0))
out.close(); exo.close()
