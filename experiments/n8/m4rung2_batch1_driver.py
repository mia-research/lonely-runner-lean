# m4rung2_batch1_driver.py -- batch-1 per-box pipeline driver for the M4 rung-2
# certificate-transcription scaling run:
#   recon (m4rung2_recon_v1.py, [T 32/32] required) -> generate (m4rung2_gen_v1.py)
#   -> ONE lean compile at a time (the task's verbatim per-file recipe) -> axiom scan
#   (exit 0 AND every '#print axioms' set a subset of {propext, Classical.choice,
#   Quot.sound}; sorryAx anywhere = FAIL; wrapped multi-line axiom lists joined).
# Results append to m4rung2_batch1_results.tsv after EVERY box (honest partial banking).
# Boxes are processed in the tree-size-ascending order of m4rung2_batch1_selection.json;
# --deadline-min N stops starting new boxes after N minutes of wall time.  python3 -I.
import json, os, re, resource, subprocess, sys, time

HERE = os.path.dirname(os.path.abspath(__file__))
FRESH = os.path.normpath(os.path.join(HERE, '..', '..', 'LonelyRunnerFresh'))
REPO = os.path.normpath(os.path.join(FRESH, '..', 'LonelyRunner'))
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}
TSV = os.path.join(HERE, 'm4rung2_batch1_results.tsv')


def lean_path():
    lp = subprocess.run(['lake', 'env', 'printenv', 'LEAN_PATH'], cwd=REPO,
                        capture_output=True, text=True, check=True).stdout.strip()
    keep = [p for p in lp.split(':') if p and p != os.path.join(REPO, '.lake/build/lib/lean')]
    return os.path.join(FRESH, 'build') + ':' + ':'.join(keep)


def axscan(log, nprints):
    """Parse '#print axioms' outputs (joining wrapped bracket lists). Returns
    (ok, ndecl, badsets, errs, sorry)."""
    txt = open(log).read()
    errs = [l for l in txt.splitlines() if ': error:' in l]
    sorry = ('sorryAx' in txt or 'declaration uses \'sorry\'' in txt)
    sets = []
    for m in re.finditer(r"depends on axioms: \[(.*?)\]", txt, re.S):
        sets.append({a.strip() for a in m.group(1).split(',') if a.strip()})
    bad = sorted({tuple(sorted(s)) for s in sets if not s <= ALLOWED})
    ok = (not errs) and (not sorry) and len(sets) == nprints and not bad
    return ok, len(sets), [list(b) for b in bad], len(errs), sorry


def main():
    deadline_min = None
    args = [a for a in sys.argv[1:] if not a.startswith('--')]
    for a in sys.argv[1:]:
        if a.startswith('--deadline-min'):
            deadline_min = float(a.split('=')[1])
    sel = json.load(open(os.path.join(HERE, 'm4rung2_batch1_selection.json')))
    nodes_of = {tuple(b): n for b, n in zip(sel['selection'], sel['nodes'])}
    if args:   # explicit box tuples, e.g. 1,2,3,5,7,10,12
        boxes = [tuple(int(x) for x in a.split(',')) for a in args]
    else:
        boxes = [tuple(b) for b in sel['selection']]
    # skip boxes already recorded PASS in the TSV (restart-safe)
    done = set()
    if os.path.exists(TSV):
        for l in open(TSV):
            f = l.rstrip('\n').split('\t')
            if len(f) > 5 and f[5] == 'PASS':
                done.add(tuple(int(x) for x in f[0].split(',')))
    todo = [b for b in boxes if b not in done]
    print('boxes given=%d done(PASS)=%d todo=%d' % (len(boxes), len(done), len(todo)),
          flush=True)
    LP = lean_path()
    t0 = time.time()
    for b in todo:
        if deadline_min is not None and (time.time() - t0) / 60 > deadline_min:
            print('DEADLINE reached, stopping before %s' % (b,), flush=True)
            break
        box = '_'.join(str(x) for x in b)
        nodes = nodes_of.get(b, '?')
        row = [','.join(str(x) for x in b), str(nodes)]
        # ---- recon ----
        t1 = time.time()
        rlog = os.path.join(HERE, 'm4rung2_recon_%s.out' % box)
        with open(rlog, 'w') as f:
            r = subprocess.run([sys.executable, '-I', 'm4rung2_recon_v1.py',
                                ','.join(str(x) for x in b)], cwd=HERE,
                               stdout=f, stderr=subprocess.STDOUT)
        rt = time.time() - t1
        rtxt = open(rlog).read()
        m = re.search(r'recon \[T (\d+)/(\d+)\]', rtxt)
        tok = r.returncode == 0 and m and m.group(1) == m.group(2)
        row.append('%s [T %s/%s]' % ('%.1fs' % rt, m.group(1) if m else '?',
                                     m.group(2) if m else '?'))
        if not tok:
            row += ['-', '-', 'FAIL', 'recon not [T n/n]: %s' % (
                [l for l in rtxt.splitlines() if '[F]' in l][:3] or rtxt[-300:],)]
            with open(TSV, 'a') as f:
                f.write('\t'.join(row) + '\n'); f.flush()
            print('%s RECON-FAIL' % box, flush=True)
            continue
        # ---- generate ----
        t1 = time.time()
        g = subprocess.run([sys.executable, '-I', 'm4rung2_gen_v1.py',
                            ','.join(str(x) for x in b)], cwd=HERE,
                           capture_output=True, text=True)
        gt = time.time() - t1
        src = os.path.join(FRESH, 'Fresh', 'M4CertRung2_%s.lean' % box)
        if g.returncode != 0 or not os.path.exists(src):
            row += ['%.1fs' % gt, '-', 'FAIL', 'generator abort: %s' % g.stderr.strip()[-400:]]
            with open(TSV, 'a') as f:
                f.write('\t'.join(row) + '\n'); f.flush()
            print('%s GEN-FAIL %s' % (box, g.stderr.strip()[-200:]), flush=True)
            continue
        nprints = open(src).read().count('#print axioms')
        row.append('%.1fs' % gt)
        # ---- compile (ONE at a time); CPU time via getrusage children delta ----
        t1 = time.time()
        ru0 = resource.getrusage(resource.RUSAGE_CHILDREN).ru_utime
        clog = os.path.join(HERE, 'm4rung2_compile_%s.log' % box)
        env = dict(os.environ, LEAN_PATH=LP)
        with open(clog, 'w') as f:
            try:
                c = subprocess.run(['lean', 'Fresh/M4CertRung2_%s.lean' % box, '-R', '.',
                                    '-o', 'build/Fresh/M4CertRung2_%s.olean' % box],
                                   cwd=FRESH, env=env, stdout=f, stderr=subprocess.STDOUT,
                                   timeout=3000)
            except subprocess.TimeoutExpired:
                row += ['>3000s', 'FAIL', 'compile wall-timeout (3000s safety cap) -- SLOW, retry later']
                with open(TSV, 'a') as f:
                    f.write('\t'.join(row) + '\n')
                print('%s COMPILE-TIMEOUT' % box, flush=True)
                continue
        ct = time.time() - t1
        cpu = resource.getrusage(resource.RUSAGE_CHILDREN).ru_utime - ru0
        row.append('%.0fs wall/%.0fs cpu' % (ct, cpu))
        # ---- axiom scan ----
        if c.returncode != 0:
            errclass = 'exit %d; ' % c.returncode + '; '.join(
                [l.strip()[:160] for l in open(clog) if ': error:' in l][:3])
            row += ['FAIL', errclass]
        else:
            ok, nd, bad, nerr, sorr = axscan(clog, nprints)
            if ok:
                note = '%d/%d axioms all in {propext, Classical.choice, Quot.sound}' % (nd, nprints)
                if ct > 600:
                    note += ' -- SLOW WALL (contention; cpu=%ds)' % cpu
                row += ['PASS', note]
            else:
                row += ['FAIL', 'axscan: sets=%d/%d bad=%s errs=%d sorry=%s'
                        % (nd, nprints, bad, nerr, sorr)]
        with open(TSV, 'a') as f:
            f.write('\t'.join(row) + '\n')
        print('%s %s (nodes=%d compile=%s)' % (box, row[4], nodes, row[3]), flush=True)


if __name__ == '__main__':
    main()
