# X24 pilot Lean slice generator, v1 (2026-11-28).  Reads x24_leafdump_v1.jsonl (the
# verified per-leaf certificate dump of the X24 band n7 in [23,26)) and emits
# LonelyRunnerFresh/Fresh/X24Pilot.lean: per-leaf membership theorems for a ~20-leaf
# pilot, type-balanced over the certificate shapes present (all dump leaves sit at
# D = 64 with equal volume, so "smallest" degenerates; within each shape the smallest
# cell tuple leads; >= 4 carve-containing w1 leaves so the BandW1 shape is exercised on
# true carve leaves).
#   window   leaves -> Fresh.BandNoCarve.BandWindowType (Fresh.Certs.WindowCert)
#   fixedR0  leaves -> Fresh.BandNoCarve.BandFixedR0  (Fresh.Certs.FixedClearCert)
#   w1       leaves -> Fresh.BandNoCarve.BandW1       (via the file's w1_of_faces step)
# Every emitted certificate is re-verified here (exact Fractions) before emission; the
# generator aborts on any mismatch.  Faces are the dyadic leaf cells (k/D form); the
# index mapping is the E832/E845 convention: Lean index 0 = rho1 = 1, artifact index i
# = Lean index i+1.  usage: python -I x24_pilot_gen_v1.py <dump.jsonl> <out.lean>
import sys, json
from fractions import Fraction as F

def rd(s):
    a, _, b = s.partition('/')
    return F(int(a), int(b)) if b else F(int(a))

def rn(x):
    """Lean numeral: (num:ℝ)/den form"""
    x = F(x)
    if x.denominator == 1: return '(%d:ℝ)' % x.numerator
    return '(%d:ℝ)/%d' % (x.numerator, x.denominator)

def verify(rec):
    D, n, c = rec['D'], rec['n'], rec['cert']
    lo = [F(1)] + [F(n[i], D) for i in range(6)]
    hi = [F(1)] + [F(n[i] + 1, D) for i in range(6)]
    j = c['j']
    assert len(j) == 7
    if c['kind'] in ('window', 'fixedR0'):
        X = rd(c['X']); Y = rd(c['Y'])
        assert F(1) <= X <= Y <= F(7)
        if c['kind'] == 'fixedR0': assert X == Y
        if c['kind'] == 'window': assert X < Y
        for i in range(7):
            assert F(8*j[i] + 1) <= lo[i] * X and hi[i] * Y <= F(8*j[i] + 7), (rec['n'], i)
        assert j[0] == 0
        return lo, hi
    S = rd(c['S'])
    assert F(9) <= S <= F(15)
    for i in range(7):
        assert F(8*j[i] + 1) <= lo[i] * S and hi[i] * S <= F(8*j[i] + 7), (rec['n'], i)
    assert j[0] == 1
    return lo, hi

def main():
    dump = sys.argv[1]; out = sys.argv[2]
    recs = [json.loads(l) for l in open(dump)]
    for r in recs:
        assert r['type'] != 'resistant', 'resistant leaf in dump: %s' % r['n']
    def vol(r): return (-r['D'], r['n'])
    # All dump leaves sit at D = 64 (no subdivision fired), so every leaf has the SAME
    # volume and "smallest ~20" degenerates; the pilot is therefore type-balanced over
    # the certificate shapes actually present (window / fixedR0 / w1), smallest-cell-
    # tuple first within each shape, with >= 4 carve-containing w1 leaves so the
    # BandW1 shape is exercised on true carve leaves.
    carve_w1 = sorted([r for r in recs if r['type'] == 'w1' and r['carves']], key=vol)
    plain_w1 = sorted([r for r in recs if r['type'] == 'w1' and not r['carves']], key=vol)
    fixed = sorted([r for r in recs if r['type'] == 'fixedR0'], key=vol)
    winds = sorted([r for r in recs if r['type'] == 'window'], key=vol)
    pilot = carve_w1[:4] + winds[:2] + fixed[:7] + plain_w1[:7]
    if len(carve_w1) < 4:
        pilot = carve_w1 + winds[:2] + fixed[:9] + plain_w1[:9]
    sys.stderr.write('pilot size %d (window %d fixedR0 %d w1 %d, carve-w1 %d)\n' % (
        len(pilot),
        sum(1 for r in pilot if r['type'] == 'window'),
        sum(1 for r in pilot if r['type'] == 'fixedR0'),
        sum(1 for r in pilot if r['type'] == 'w1'),
        sum(1 for r in pilot if r['type'] == 'w1' and r['carves'])))

    L = []
    w = L.append
    w('import Fresh.BandNoCarve')
    w('')
    w('/-!')
    w('# X24 pilot slice: per-leaf membership theorems for the (23,25) band residue')
    w('')
    w('Data-side pilot for the X24 (23,25) residue (E983 item 3; the band with no')
    w('certificate dump).  Source: `x24_leafdump_v1.jsonl` (exact-Fraction certificates,')
    w('independently re-verified), built on the fixed-R0-resistant leaves of the verbatim')
    w('E832 DFS (`frontier_box_dfs_v1.c` run `23 26 64`: 297,765 root boxes = the audit')
    w('universe of `obligation_audit_2026_11_11/x24.out`, 27,349 resistant leaves at')
    w('D = 64; the run reproduces E832\'s recorded `[23,25)` D = 32 artifact bit-for-bit:')
    w('179,010 root boxes, 9,533,510 nodes, 7,200 leaves).  Classification (exact,')
    w('uniform-lap family, no subdivision needed at D = 64): 6,323 fixedR0 (exact')
    w('single-point W0 windows off the C certifier\'s dyadic grid -- the E833 item 4')
    w('mechanism) + 21,026 w1 (a common clear point in [9,15] with per-reading laps --')
    w('the `Fresh.BandNoCarve.BandW1` payload; the X24 carve region lives here).  No')
    w('resistant leaves, no START/END boundary artifacts (the resistant slab rho6 in')
    w('[6.52, 7.02] touches neither 22.5 nor 25.5).')
    w('')
    w('Carve cross-check: all 90 in-band recorded carves (E828/E829 loader; 6 of the 96')
    w('sit in the lap-2 strip rho7 in (15,17), outside X24) are exact carves of [1,7]')
    w('with a W1-clear component below 17, and each lies in EXACTLY ONE w1 leaf (78')
    w('carve-containing leaves; 0 carves in any W0-certified leaf).')
    w('')
    w('This file: a ~20-leaf pilot, type-balanced over the shapes present (all dump')
    w('leaves are D = 64 with equal volume, so smallest-volume selection degenerates;')
    w('within each shape the smallest cell tuple leads; carve-containing w1 leaves lead')
    w('the w1 shape), each as a per-leaf membership theorem.  Index mapping (E832/E845')
    w('convention): Lean')
    w('index 0 = rho1 = 1 (`loLxx 0 = hiLxx 0 = 1`), artifact index i = Lean index i+1.')
    w('The certificate inequalities are all closed rational comparisons, proved by')
    w('`norm_num`; the full landing is per-leaf theorems of exactly this shape, one per')
    w('JSONL line (27,349 leaves; the pilot is the worked pattern).')
    w('-/')
    w('')
    w('namespace Fresh.X24Pilot')
    w('')
    w('open Fresh.Certs')
    w('')
    w('/-- The W1 step, index-uniform: box faces + per-reading laps give `BandW1`.')
    w('Index 0 is carried by the faces themselves (`L 0 = H 0 = 1`, so `hbox 0` pins')
    w('`g 0 = 1` and `S` lies in rho1\'s own gap `[9,15]`). -/')
    w('theorem w1_of_faces {g : Fin 7 → ℝ} {S : ℝ} {L H : Fin 7 → ℝ} {J : Fin 7 → ℤ}')
    w('    (hS9 : 9 ≤ S) (hS15 : S ≤ 15)')
    w('    (hcert : ∀ i, (((8 * J i : ℤ) : ℝ) + 1) ≤ L i * S ∧ H i * S ≤ (((8 * J i : ℤ) : ℝ) + 7))')
    w('    (hbox : ∀ i, L i ≤ g i ∧ g i ≤ H i) :')
    w('    Fresh.BandNoCarve.BandW1 g := by')
    w('  refine ⟨S, hS9, hS15, fun i => ?_⟩')
    w('  obtain ⟨h1, h2⟩ := hcert i')
    w('  obtain ⟨k1, k2⟩ := hbox i')
    w('  have hS0 : (0 : ℝ) ≤ S := by linarith')
    w('  refine ⟨J i, Set.mem_Icc.mpr ⟨?_, ?_⟩⟩')
    w('  · exact le_trans h1 (mul_le_mul_of_nonneg_right k1 hS0)')
    w('  · exact le_trans (mul_le_mul_of_nonneg_right k2 hS0) h2')
    w('')
    w('#print axioms w1_of_faces')
    w('')

    for idx, r in enumerate(pilot, start=1):
        lo, hi = verify(r)
        D, n, c, t = r['D'], r['n'], r['cert'], r['type']
        name = 'x24_leaf_%02d' % idx
        prov = ('JSONL leaf D=%d n=%s, type %s, carves %s%s' %
                (D, n, t, r['carves'][:6] if r['carves'] else [],
                 (' (of 90 in-band)' if r['carves'] else '')))
        w('/-- %s -/' % prov)
        w('noncomputable def lo%s : Fin 7 → ℝ := ![1, %s]' %
          (name, ', '.join('(%d:ℝ)/%d' % (n[i], D) for i in range(6))))
        w('noncomputable def hi%s : Fin 7 → ℝ := ![1, %s]' %
          (name, ', '.join('(%d:ℝ)/%d' % (n[i] + 1, D) for i in range(6))))
        w('def j%s : Fin 7 → ℤ := ![%s]' % (name, ', '.join(str(x) for x in c['j'])))
        if t in ('window', 'fixedR0'):
            X = rd(c['X'])
            if t == 'window':
                Y = rd(c['Y'])
                w('theorem %s (g : Fin 7 → ℝ)' % name)
                w('    (hbox : ∀ i : Fin 7, lo%s i ≤ g i ∧ g i ≤ hi%s i) :' % (name, name))
                w('    Fresh.BandNoCarve.BandWindowType g :=')
                w('  ⟨⟨lo%s, hi%s, %s, %s, j%s,' % (name, name, rn(X), rn(Y), name))
                w('    by norm_num, by norm_num, by norm_num,')
                w('    by intro i; fin_cases i <;> simp [lo%s, hi%s] <;> norm_num,' % (name, name))
                w('    by intro i; fin_cases i <;> simp [lo%s] <;> norm_num,' % name)
                w('    by intro i; fin_cases i <;> simp [lo%s, j%s] <;> norm_num,' % (name, name))
                w('    by intro i; fin_cases i <;> simp [hi%s, j%s] <;> norm_num⟩,' % (name, name))
                w('   hbox⟩')
            else:
                w('theorem %s (g : Fin 7 → ℝ)' % name)
                w('    (hbox : ∀ i : Fin 7, lo%s i ≤ g i ∧ g i ≤ hi%s i) :' % (name, name))
                w('    Fresh.BandNoCarve.BandFixedR0 g :=')
                w('  ⟨⟨lo%s, hi%s, %s, j%s,' % (name, name, rn(X), name))
                w('    by norm_num, by norm_num,')
                w('    by intro i; fin_cases i <;> simp [lo%s, hi%s] <;> norm_num,' % (name, name))
                w('    by intro i; fin_cases i <;> simp [lo%s, hi%s, j%s] <;> norm_num⟩,' % (name, name, name))
                w('   hbox⟩')
        else:
            S = rd(c['S'])
            w('theorem %s (g : Fin 7 → ℝ)' % name)
            w('    (hbox : ∀ i : Fin 7, lo%s i ≤ g i ∧ g i ≤ hi%s i) :' % (name, name))
            w('    Fresh.BandNoCarve.BandW1 g :=')
            w('  w1_of_faces (S := %s) (J := j%s) (by norm_num) (by norm_num)' % (rn(S), name))
            w('    (by intro i; fin_cases i <;> simp [lo%s, hi%s, j%s] <;> norm_num)' % (name, name, name))
            w('    hbox')
        w('')
        w('#print axioms %s' % name)
        w('')
    w('end Fresh.X24Pilot')
    with open(out, 'w') as f:
        f.write('\n'.join(L) + '\n')
    sys.stderr.write('wrote %s (%d lines)\n' % (out, len(L)))

if __name__ == '__main__':
    main()
