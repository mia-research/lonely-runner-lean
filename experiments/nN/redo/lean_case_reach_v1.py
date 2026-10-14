"""E402 (2026-10-05), lean_case_reach_v1: which residue patterns of the residual's crowded level the Lean cases of
ParityDescentN, ParityDescentTwoN and ParityCoverN settle, read off each theorem's hypotheses exactly; and the same on
the stored residual members (all 22 fields).  No instant is computed here: each theorem is proved in Lean
(axiom records experiments/nN/parity_descent_print_axioms_v3.out, parity_descent_two_print_axioms_v1.out,
parity_cover_print_axioms_v1.out); this script only evaluates which hypotheses hold.

Theorems (hypotheses as stated in Lean; m = #multiples of 8, f = #(= 4 mod 8), t = #(= 2 mod 4), o = #odd):
 T1 lonely_eight_of_parity_descent: ParitySplit8(non-multiples) and m <= 6
 T2 lonely_eight_of_quarter_shift: t = 0, o <= 3, m + f <= 6
 T3 lonely_eight_of_silent_four: m <= 3, f <= 1, o + t <= 3
 T4 lonely_eight_of_quarter_three_one: o <= 3, m + f <= 3, t <= 1
 T5 lonely_eight_of_eighth_le_three: ParitySplit8(odd and 2 mod 4 readings) and m + f <= 3
 T6 lonely_eight_of_oott: odd and 2 mod 4 readings are exactly two odd w1, w2 with w2 not = +-w1 mod 8 and two
    2 mod 4, and m + f <= 3
Conditional rows (not proved; M(2,2), M(1,3) delegated): T4' = quarter level with o <= 3 and the mixed instant for
(m + f, t) in {(2,2), (1,3)}; T5' = eighth level with the split and (m, f) in {(2,2), (1,3)}.
"""
import itertools, sys, collections
sys.path.insert(0, '.')

def cost(r): return 2 if r % 2 or r % 4 == 2 else 4
def psplit(rs):
    od = sum(1 for r in rs if r % 2); ev = [cost(r) for r in rs if r % 2 == 0]
    for mask in range(1 << len(ev)):
        a = sum(ev[i] for i in range(len(ev)) if mask >> i & 1); b = sum(ev) - a
        if not (od + a < 4 or od + b < 4): return False
    return True

def settled(m, rs, conditional=False):
    o = sum(1 for r in rs if r % 2); t = sum(1 for r in rs if r % 4 == 2); f = sum(1 for r in rs if r == 4)
    ot = [r for r in rs if r != 4]
    hits = []
    if psplit(rs) and m <= 6: hits.append('T1')
    if t == 0 and o <= 3 and m + f <= 6: hits.append('T2')
    if m <= 3 and f <= 1 and o + t <= 3: hits.append('T3')
    if o <= 3 and m + f <= 3 and t <= 1: hits.append('T4')
    if psplit(ot) and m + f <= 3: hits.append('T5')
    ws = [r for r in ot if r % 2]; ts = [r for r in ot if r % 4 == 2]
    if len(ws) == 2 and len(ts) == 2 and len(ot) == 4 and ws[0] != ws[1] and (ws[0] + ws[1]) % 8 != 0 and m + f <= 3:
        hits.append('T6')
    if conditional:
        if o <= 3 and (m + f, t) in ((2, 2), (1, 3)): hits.append("T4'")
        if psplit(ot) and (m, f) in ((2, 2), (1, 3)): hits.append("T5'")
    return hits

def typ(rs): return ''.join(sorted('o' if r % 2 else ('t' if r % 4 == 2 else 'f') for r in rs))

if __name__ == '__main__':
    out = open('lean_case_reach_v1.out', 'w'); out.write(__doc__ + "\n")
    for m in (1, 2, 3, 4):
        n = 7 - m
        pats = [p for p in itertools.combinations_with_replacement((1, 2, 3, 4, 5, 6, 7), n)
                if sum(1 for r in p if r % 2) >= 2 and sum(cost(r) for r in p) >= 8]
        byt = collections.defaultdict(lambda: [0, 0, 0])
        for p in pats:
            h = settled(m, p); hc = settled(m, p, True)
            b = byt[typ(p)]; b[0] += 1; b[1] += bool(h); b[2] += bool(hc)
        tot = len(pats); s = sum(v[1] for v in byt.values()); sc = sum(v[2] for v in byt.values())
        out.write("\nshape (%d,%d): patterns %d; settled by Lean cases %d; with the conditional rows %d\n" % (m, n, tot, s, sc))
        for ty in sorted(byt):
            v = byt[ty]
            out.write("  type %s: %d patterns, Lean %d, with conditional %d\n" % (ty, v[0], v[1], v[2]))
    from members_reach_check_v1 import load, full_residual
    for fn in ['../residual_members_C_list_v1.json', 'both_shadowed_members_v1.json']:
        sets = [S for S in dict.fromkeys(load(fn)) if full_residual(S)]
        c = collections.Counter()
        for S in sets:
            mult = [d for d in S if d % 8 == 0]; rs = tuple(sorted(d % 8 for d in S if d % 8))
            h = settled(len(mult), rs); hc = settled(len(mult), rs, True)
            c['Lean' if h else ('conditional only' if hc else 'open')] += 1
        out.write("\n%s: %d residual members: %s\n" % (fn, len(sets), dict(c)))
    out.close(); print(open('lean_case_reach_v1.out').read()[len(__doc__):])
