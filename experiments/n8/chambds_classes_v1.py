# chambds_classes_v1.py -- the chamber DATASHEET generator (data side): parse the chamber
# probe dump (v3_chamber_open_probe_v1_dump.json) and classify every chamber class by which
# Lean-consumable certificate applies, emitting the class table TSV + counts + a JSON of the
# instances for the Lean generator (chambds_lean_gen_v1.py).
#
# Certificate kinds.  TWO evaluation scopes, both reported (anti-suppression: neither is
# buried; the census construction decides which can fire):
#   (S1) CHAMBER-WINDOW-UNIFORM (the task's (a)/(b), chamber_test semantics at the class's
#        q-window endpoints [Llo/Rhi, Lhi/Rlo]): D1 iff 9*(8kL+1)*Rhi <= 7*(8kR-1)*Llo
#        (q_min >= 9*phi/7); D2 iff q_min > phi and (8*J(q_min)+1)*Rhi <= 25*(8kR-1).
#        The v2 instrument dumps a case ONLY when chamber_test returns OPEN for it, so this
#        scope CANNOT fire on the census -- verified below, not assumed.
#   (S2) COMPONENT-LEVEL at the class's FIXED component edges (A,B) (the key's a,b -- the
#        instrument's own COMP-DEAD kill component for every recorded tuple): band j of [A,B]
#        is ((8j-1)/A, (8j+1)/B), nonempty iff (8j-1)*B < (8j+1)*A;  D1 iff 9*A <= 7*B (no
#        band ever opens);  else D2 iff (8*J_ab+1) <= 25*B with J_ab = largest nonempty band
#        (the top band ends at/below 25, so the component is dead over [25, inf));  else the
#        component has a band over [25,50] and the death needs interlacing (OWED).
#   E894-START  the START boundary component [1, b_t], line 33*Rhi <= 31*(8kR-1) at the window
#               (b_t >= 33/31 for every chamber tuple since rho_R <= Rhi).  (The instrument
#               routes boundary certificates out of the census -- expected 0; templates built.)
#   E894-END    the END boundary component [a_t, 7], line 177*(8kL+1) <= 1225*Llo.  (0 expected.)
#   REFINED-DEAD neither 2-line fires but the class's refined chamber-interior probe found no
#               alive tuple (the probe's verdict is the certificate; data-side only).
#   OWED        none of the above at either scope: honest tag naming the band-union datum.
#
# The S2 kinds are the Lean-emittable per-class arithmetic certificates: the class key fixes
# (A,B), so "the certifying component [A,B] is race-dead over [25,50]" is a closed literal
# fact (exactly feasible_set(A,B,25,50) = ∅, the instrument's COMP-DEAD).  The S1 uniform
# claim over the whole chamber (every tuple of the cell-box) stays OWED at the Lean level:
# it needs the hyperplane-partition/band-union lemma (future work; the probe's no-alive-on-
# grid evidence is the data-side support).
#
# The exact race-band shape consumed in Lean (chamber tuple with boundary assignment
# (kL, kR), readings rho_L in the L-window, rho_R in the R-window): the certifying
# component's lap-j band is [(8j-1)*rho_L/(8kL+1), (8j+1)*rho_R/(8kR-1)) and the tail r keeps
# the component alive at lap j iff r lies in that band.  All emitted lines are CLOSED numeral
# inequalities in the window literals (linear in Llo/Rhi), proved in Lean by norm_num; the
# shared template theorems do the j-symbolic work once.
#
# chamber_test / J_of / phi_of are COPIED VERBATIM in their formulas from
# conjT3_boxcheck2_v1.py (that module is NEVER imported -- its module level runs a 38.7M
# sweep).  No existing file is modified; outputs are the NEW files
# chambds_classes_v1.tsv / chambds_counts_v1.out / chambds_instances_v1.json.
import sys, os, json, time
from fractions import Fraction as F
from collections import Counter

DIR = '/Users/trentpalelei/Desktop/Math Ex/experiments/n8/'
DUMPF = DIR + 'v3_chamber_open_probe_v1_dump.json'
TSVF = DIR + 'chambds_classes_v1.tsv'
CNTF = DIR + 'chambds_counts_v1.out'
JSONF = DIR + 'chambds_instances_v1.json'

CELLBOUNDS = {'P': (F(1), F(7)), 'S1': (F(7), F(9)), 'G1': (F(9), F(15)),
              'S2': (F(15), F(17)), 'E': (F(17), F(17))}

def phi_of(kL, kR): return F(8 * kL + 1, 8 * kR - 1)          # verbatim conjT3_boxcheck2_v1

def J_of(q, kL, kR, cap=100000):                               # verbatim conjT3_boxcheck2_v1
    phi = F(8 * kL + 1, 8 * kR - 1)
    if q <= phi: return None
    j = 1; J = 0
    while F(8 * j - 1) * q < F(8 * j + 1) * phi:
        J = j; j += 1
        if j > cap: return cap
    return J

def chamber_windows(kL, kR, cL, cR, a, b):                     # verbatim v3_chamber_open_probe_v1
    cL_lo, cL_hi = CELLBOUNDS[cL]; cR_lo, cR_hi = CELLBOUNDS[cR]
    rhoL_lo = max(cL_lo, F(8 * kL - 1) / a); rhoL_hi = min(cL_hi, F(8 * kL + 1) / a)
    rhoR_lo = max(cR_lo, F(8 * kR - 1) / b); rhoR_hi = min(cR_hi, F(8 * kR + 1) / b)
    return rhoL_lo, rhoL_hi, rhoR_lo, rhoR_hi

def main():
    t0 = time.time()
    d = json.load(open(DUMPF))
    rows = d['results']
    counts_out = []
    def C(*a):
        s = ' '.join(str(x) for x in a)
        print(s, flush=True); counts_out.append(s)

    C('# chambds_classes_v1 -- chamber datasheet classification; dump:',
      os.path.basename(DUMPF), '| cutoff lines:', d['cutoff']['cutoff_lines'],
      '| open cases:', d['cutoff']['n_open'], '| classes:', len(rows))

    out = open(TSVF, 'w')
    hdr = ['idx', 'skel', 'kL', 'kR', 'cL', 'cR', 'a', 'b', 'n_cases', 'verdict', 'refined',
           'kind', 'Llo', 'Lhi', 'Rlo', 'Rhi', 'qmin', 'qmax', 'Jm',
           'line_D1', 'line_D2', 'line_band0', 'line_phi', 'line_start', 'line_end', 'notes']
    out.write('# chamber datasheet: class -> certificate kind -> emitted literals\n')
    out.write('# ' + '\t'.join(hdr) + '\n')

    kind_hist = Counter()
    kind_by_verdict = Counter()
    s1_hist = Counter()
    instances = []          # for the Lean generator: D1/D2/E894 instances only
    owed_by_skel = Counter()
    owed_examples = []
    n_degen = 0
    for idx, r in enumerate(sorted(rows, key=lambda x: -x['n_cases'])):
        skel = ''.join(r['skel']); kL = int(r['kL']); kR = int(r['kR'])
        cL, cR = r['cL'], r['cR']; a = F(r['a']); b = F(r['b'])
        verdict, refined, n_cases = r['verdict'], r['refined'], r['n_cases']
        Llo, Lhi, Rlo, Rhi = chamber_windows(kL, kR, cL, cR, a, b)
        degen = Llo > Lhi or Rlo > Rhi
        qmin = Llo / Rhi if not degen else None
        qmax = Lhi / Rlo if not degen else None
        phi = phi_of(kL, kR)
        # ---- S1: chamber-window-uniform 2-line (chamber_test semantics at the q endpoints) ----
        fires_S1_D1 = 9 * (8 * kL + 1) * Rhi <= 7 * (8 * kR - 1) * Llo
        s1 = 'OPEN'
        if not degen and not (a == 1 or b == 7):
            if fires_S1_D1:
                s1 = 'D1'
            else:
                Jm_ = J_of(qmin, kL, kR)
                if Jm_ is not None and F(8 * Jm_ + 1) * Rhi <= 25 * (8 * kR - 1):
                    s1 = 'D2'
                elif Jm_ is None:
                    s1 = 'qle-phi'
        # ---- S2: component-level 2-line at the FIXED (a,b) ----
        s2_J = ''
        if a == 1 or b == 7:
            s2 = 'BOUNDARY'
        elif 9 * a <= 7 * b:
            s2 = 'D1'                                    # no band ever opens
        else:
            j = 1; J = 0
            while F(8 * j - 1) * b < F(8 * j + 1) * a:
                J = j; j += 1
                if j > 200000: break
            s2_J = str(J)
            if F(8 * J + 1) <= 25 * b:
                s2 = 'D2'                                # top band <= 25: dead over [25, inf)
            else:
                s2 = 'OWED'                              # band over [25,50]: interlacing needed
        # ---- datasheet kind (precedence) ----
        kind, Jm = None, ''
        line_D1 = line_D2 = line_band0 = line_phi = line_start = line_end = ''
        notes = []
        if degen:
            kind = 'DEGENERATE'; n_degen += 1
        elif a == 1:
            ok = F(33) * Rhi <= 31 * (8 * kR - 1)
            line_start = 'T' if ok else 'F'
            kind = 'E894-START' if ok else 'OWED'
            if ok:
                instances.append(dict(idx=idx, kind='E894-START', skel=skel, kL=kL, kR=kR,
                                      Llo=str(Llo), Lhi=str(Lhi), Rlo=str(Rlo), Rhi=str(Rhi),
                                      a=str(a), b=str(b), n_cases=n_cases))
        elif b == 7:
            ok = F(177) * (8 * kL + 1) <= F(1225) * Llo
            line_end = 'T' if ok else 'F'
            kind = 'E894-END' if ok else 'OWED'
            if ok:
                instances.append(dict(idx=idx, kind='E894-END', skel=skel, kL=kL, kR=kR,
                                      Llo=str(Llo), Lhi=str(Lhi), Rlo=str(Rlo), Rhi=str(Rhi),
                                      a=str(a), b=str(b), n_cases=n_cases))
        elif s2 == 'D1':
            kind = 'D1'; line_D1 = 'T'
            assert a >= 1 and a <= b and 9 * a <= 7 * b, (idx, a, b)
            instances.append(dict(idx=idx, kind='D1', skel=skel, kL=kL, kR=kR,
                                  Llo=str(Llo), Lhi=str(Lhi), Rlo=str(Rlo), Rhi=str(Rhi),
                                  a=str(a), b=str(b), n_cases=n_cases, Jm=''))
        elif s2 == 'D2':
            kind = 'D2'; Jm = s2_J
            line_D2 = line_band0 = 'T'
            assert a >= 1 and a < b and b <= 7, (idx, a, b)
            assert F(8 * int(s2_J) + 1) <= 25 * b, (idx, a, b, s2_J)          # hJ2 line
            assert a + b <= 8 * (int(s2_J) + 1) * (b - a), (idx, a, b, s2_J)  # hJ1 line
            instances.append(dict(idx=idx, kind='D2', skel=skel, kL=kL, kR=kR,
                                  Llo=str(Llo), Lhi=str(Lhi), Rlo=str(Rlo), Rhi=str(Rhi),
                                  a=str(a), b=str(b), n_cases=n_cases, Jm=s2_J))
        else:
            kind = 'OWED'
        # scope-1 report columns (the uniform claim; expected OPEN everywhere by construction)
        s1_hist[s1] += 1
        if kind in ('D1', 'D2') and verdict == 'GRID-TOO-COARSE':
            notes.append('refined-dead-also')
        if kind == 'OWED' and verdict == 'GRID-TOO-COARSE' and str(refined).startswith('dead'):
            kind = 'REFINED-DEAD'   # the probe's refined-interior verdict is the certificate
        if kind == 'OWED':
            owed_by_skel[skel] += 1
            if len(owed_examples) < 12:
                owed_examples.append(dict(idx=idx, skel=skel, kL=kL, kR=kR, cL=cL, cR=cR,
                                          a=str(a), b=str(b), qmin=str(qmin), qmax=str(qmax),
                                          s1=s1, verdict=verdict, notes=notes))
        kind_hist[kind] += 1
        kind_by_verdict[(verdict, kind)] += 1
        out.write('\t'.join([str(idx), skel, str(kL), str(kR), cL, cR, str(a), str(b),
                             str(n_cases), verdict, str(refined).split('(')[0], kind,
                             str(Llo), str(Lhi), str(Rlo), str(Rhi),
                             str(qmin), str(qmax), Jm,
                             line_D1, line_D2, line_band0, line_phi, line_start, line_end,
                             'S1=' + s1] + [';'.join(notes)]) + '\n')
    out.close()

    C('# certificate-kind histogram, S2 scope (component-level 2-line at the FIXED (a,b);'
      ' precedence E894 > D1 > D2 > REFINED-DEAD > OWED):')
    for k in ('E894-START', 'E894-END', 'D1', 'D2', 'REFINED-DEAD', 'OWED', 'DEGENERATE'):
        C('#   %-13s %d' % (k, kind_hist.get(k, 0)))
    C('# S1 scope (chamber-window-UNIFORM 2-line at the q-window endpoints, chamber_test'
      ' semantics) -- the census dumps only chamber_test==OPEN cases, so S1 cannot fire:'
      ' verified, not assumed:')
    for k in ('D1', 'D2', 'qle-phi', 'OPEN'):
        C('#   %-13s %d' % (k, s1_hist.get(k, 0)))
    C('# kind x probe-verdict cross-tab (S2 scope):')
    for (v, k), n in sorted(kind_by_verdict.items()):
        C('#   %-18s %-13s %d' % (v, k, n))
    C('# total cases represented: %d (case:class ratio %.0f:1)'
      % (sum(r['n_cases'] for r in rows), d['cutoff']['n_open'] / max(1, len(rows))))
    C('# Lean-emittable instances (D1+D2+E894): %d of %d classes'
      % (len(instances), len(rows)))
    C('# OWED classes: %d; OWED by skeleton (top 10): %s'
      % (kind_hist.get('OWED', 0),
         ', '.join('%s:%d' % kv for kv in owed_by_skel.most_common(10))))
    C('# OWED examples (first 12, with failure notes):')
    for e in owed_examples:
        C('#   %s' % json.dumps(e))
    C('# degenerate-window classes: %d' % n_degen)
    C('# elapsed %.1fs' % (time.time() - t0))

    json.dump(dict(instances=instances,
                   kind_hist=dict(kind_hist),
                   owed_by_skel=dict(owed_by_skel),
                   n_classes=len(rows)),
              open(JSONF, 'w'))
    C('# json: %s' % JSONF)
    open(CNTF, 'w').write('\n'.join(counts_out) + '\n')

if __name__ == '__main__':
    main()
