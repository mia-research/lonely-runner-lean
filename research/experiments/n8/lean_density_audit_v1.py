"""lean_density_audit_v1 (2026-10-07, log E426): the artifact behind E426 item 3.
(a) every Prop-valued `def`/`abbrev` in LonelyRunner/LonelyRunner/LRC/{Spec,Cascade} (a def whose header before `:=` ends in `: Prop`);
(b) the import closure of the n=8 path's top modules, and whether it contains Theorem52_Weyl, Lemma41_PositiveMeasure or Theorem121_Main;
(c) lines of Defs.lean that use a measure-theoretic name; (d) lines of the order-six port that use a measure lemma."""
import os, re
R = 'LonelyRunner/LonelyRunner/LRC'
out = []
props = []
for d in ['Spec', 'Cascade']:
    for root, _, fs in os.walk(os.path.join(R, d)):
        for f in sorted(fs):
            if not f.endswith('.lean'): continue
            p = os.path.join(root, f); L = open(p).read().split('\n')
            for i, l in enumerate(L):
                m = re.match(r'\s*(?:private |protected )?(?:noncomputable )?(?:abbrev|def) ([^\s(:{\[]+)', l)
                if not m: continue
                head = ' '.join(L[i:i + 8]).split(':=')[0].strip()
                if head.endswith('Prop') or re.search(r'\)\s*:\s*Prop\b', head):
                    props.append('%s:%d %s' % (os.path.relpath(p, R), i + 1, m.group(1)))
out.append('(a) Prop-valued definitions in Spec/ and Cascade/: %d' % len(props))
out += ['    ' + x for x in props]
tops = ['Target', 'OrderEightCasesN', 'Order8SkeletonN', 'RegimeSkeletonN', 'EndRunnerN', 'RealEightN']
seen = set(); stack = ['LonelyRunner.LRC.Spec.' + t for t in tops]
while stack:
    m = stack.pop()
    if m in seen or not m.startswith('LonelyRunner.'): continue
    seen.add(m)
    p = os.path.join('LonelyRunner', *m.split('.')) + '.lean'
    if not os.path.exists(p): continue
    for l in open(p):
        mm = re.match(r'import (\S+)', l)
        if mm: stack.append(mm.group(1))
out.append('(b) import closure of %s: %d LonelyRunner modules' % (', '.join(tops), len(seen)))
for bad in ['Theorem52_Weyl', 'Lemma41_PositiveMeasure', 'Theorem121_Main']:
    out.append('    contains %s: %s' % (bad, any(bad in s for s in seen)))
pat = re.compile(r'volume|MeasurableSet|measurable|∀ᵐ|∫|MeasureTheory\.|Measure\.')
dl = [('%d: %s' % (i + 1, l.strip())) for i, l in enumerate(open(os.path.join(R, 'Defs.lean'))) if pat.search(l) and not l.startswith('import')]
out.append('(c) Defs.lean lines using a measure name (imports excluded): %d' % len(dl)); out += ['    ' + x for x in dl]
six = []
for f in sorted(os.listdir(os.path.join(R, 'Spec'))):
    if f.startswith('OrderSix') and f.endswith('.lean'):
        for i, l in enumerate(open(os.path.join(R, 'Spec', f))):
            if pat.search(l) or re.search(r'\bae\b', l): six.append('%s:%d: %s' % (f, i + 1, l.strip()[:120]))
out.append('(d) order-six port lines using a measure lemma (pattern volume|MeasurableSet|measurable|ae|integral): %d' % len(six)); out += ['    ' + x for x in six]
open('experiments/n8/lean_density_audit_v1.out', 'w').write('\n'.join(out) + '\n')
print('\n'.join(x for x in out if not x.startswith('    ') or 'contains' in x))
