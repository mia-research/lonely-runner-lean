"""modgap_split_v1 (2026-10-06): owner's question: where the speed-mod view (which readings fix the landing) and the gap-mod view
(the least-denominator rational in [t*, t_R]) disagree.  Exact.
Objects per set S: t* = cascade(S); setters P = readings that set a step of the cascade path; T = a minimal subset with
cascade(T) = t* (least size, first in lexicographic order); opener e (e t* = J + 1/8); closer f at t_R (f t_R = M + 7/8);
t_R(T) = right end of the lonely component of T alone at t* (>= t_R(S)).
Statements recorded:
  SP1 [P] cascade(P) = t*, so T is inside some P-sized subset; |T| <= |P|.
  SP2  closer f in T?  and f in P?  (if not: the right end t_R, hence the rational a_A/q_A, is fixed by a reading that plays no
       part in fixing t*.)
  SP3  simplest rational in [t*, t_R(T)] against simplest rational in [t*, t_R(S)]: equal? denominators.
Populations: the 752 'not understood' exceptions of modgap_rule_v1_exceptions.out (E), and a matched sample of the same
populations' sets that satisfy RM (the mediant rule) (R), first 752 per population order.
"""
import re, ast, itertools, collections, sys, math
sys.path.insert(0, '.')
from fractions import Fraction as F
from modgap_lib_v1 import cascade, cascade_path, openers, component, simplest, E8
out = open('modgap_split_v1.out', 'w'); out.write(__doc__ + "\n")
def info(S):
    t = cascade(S); path = cascade_path(S); P = sorted({d for _, d in path if d})
    T = next(T for k in range(1, 8) for T in itertools.combinations(S, k) if cascade(list(T)) == t)
    tR, cl = component(S, t); tRT, clT = component(T, t); op = openers(S, t)
    sS = simplest(t, tR); sT = simplest(t, tRT)
    return dict(S=S, t=t, P=P, T=T, op=op, cl=cl, tR=tR, tRT=tRT, sS=sS, sT=sT)
E = []
for line in open('modgap_rule_v1_exceptions.out'):
    if 'class=not understood' in line:
        E.append(ast.literal_eval(re.search(r' S=(\([^)]*\))', line).group(1)))
R = []
for line in open('modgap_rule_v1_exceptions.out'):
    pass
def summarise(name, sets):
    c = collections.Counter(); ex = []
    for S in sets:
        r = info(S)
        f = r['cl'][0]
        c[('|T|', len(r['T']))] += 1; c[('|P|', len(r['P']))] += 1
        c[('closer in T', f in r['T'])] += 1; c[('closer in P', f in r['P'])] += 1
        c[('opener in T', r['op'][0] in r['T'])] += 1
        c[('rational from T alone equals S rational', r['sT'] == r['sS'])] += 1
        c[('t_R(T) = t_R(S)', r['tRT'] == r['tR'])] += 1
        if len(ex) < 12: ex.append(r)
    out.write("\n==== %s: %d sets\n" % (name, len(sets)))
    for k, v in sorted(c.items(), key=str): out.write("  %s: %d\n" % (k, v))
    for r in ex:
        out.write("  S=%s t*=%s P=%s T=%s opener=%s closer=%s t_R(S)=%s t_R(T)=%s rational(S)=%s rational(T)=%s\n" %
                  (r['S'], r['t'], r['P'], r['T'], r['op'], r['cl'], r['tR'], r['tRT'], r['sS'], r['sT']))
summarise('E: the 752 not-understood exceptions', E)
# comparison: sets of the same shapes that are NOT exceptions and not unit-fraction
import itertools as it
def s1():
    for r in it.combinations(range(2, 25), 6): yield (1,) + r
cmp = []; Eset = set(E)
for S in s1():
    if len(cmp) >= 752: break
    t = cascade(S); tR, cl = component(S, t)
    if t < 1 and F(1, math.ceil(1 / tR)) >= t: continue
    if S in Eset: continue
    cmp.append(S)
summarise('C: first 752 non-unit-fraction S1 sets that are not exceptions (comparison)', cmp)
out.close(); print(open('modgap_split_v1.out').read()[len(__doc__):])
