# m4fix_driver.py -- mass-run driver for the 10,211 C3-killed boxes (m4fix pipeline).
# DELTA-DERIVED from the proven m4rung2_batch2_driver.py (batch 1 = 25/25 PASS): same
# compile -> axiom-check recipe (ONE lean compile at a time, axiom scan exit 0 AND every
# '#print axioms' set a subset of {propext, Classical.choice, Quot.sound}; sorryAx anywhere
# = FAIL; wrapped multi-line axiom lists joined), same honest-partial TSV banking, same
# daemonizable shape, plus the C3 adaptations:
#   * boxes come from m4fix_res_v1.jsonl (10,211 constructed m4res records), 25 per batch,
#     tree-size ascending (ties broken by tuple order);
#   * the recon step is m4fix_recon_v1.py (constructed-record bank layer; [T n/n] required);
#   * a per-box reach_utc verdict dump (m4fix_utc_v1.py, [T n/n] required) feeds the
#     generator's OWED (b) verdict layer;
#   * the generator is m4fix_gen_v1.py (emits Fresh/M4FixRung2_<box>.lean; the composed
#     theorems consume the mini-bank Fresh.M4FixResBank_v1, emitted+compiled ONCE per run
#     by m4fix_bank_v1.py -- hash-skipped when the box set is unchanged);
#   * boxes whose forest exceeds 1000 nodes go leaf-only: the gen then emits
#     Fresh/M4FixRung2_<box>_t<root>.lean subtree files; ALL of them must compile+scan.
# Results append to m4fix_results.tsv after EVERY box (8 columns).  At --deadline-min N no
# NEW box is started after N minutes; unstarted boxes are banked as UNSUPPORTED (budget).
# Usage: python3 -I m4fix_driver.py [--batch K] [--deadline-min N] [7tuple,7tuple,...]
import json, os, re, resource, subprocess, sys, time, glob

HERE = os.path.dirname(os.path.abspath(__file__))
FRESH = os.path.normpath(os.path.join(HERE, '..', '..', 'LonelyRunnerFresh'))
REPO = os.path.normpath(os.path.join(FRESH, '..', 'LonelyRunner'))
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}
TSV = os.path.join(HERE, 'm4fix_results.tsv')
BANK = os.path.join(FRESH, 'Fresh', 'M4FixResBank_v1.lean')
BANKHASHF = os.path.join(HERE, 'm4fix_bank_hash.txt')


def lean_path():
    lp = subprocess.run(['lake', 'env', 'printenv', 'LEAN_PATH'], cwd=REPO,
                        capture_output=True, text=True, check=True).stdout.strip()
    keep = [p for p in lp.split(':') if p and p != os.path.join(REPO, '.lake/build/lib/lean')]
    return os.path.join(FRESH, 'build') + ':' + ':'.join(keep)


def axscan(txt, nprints):
    """Parse '#print axioms' outputs (joining wrapped bracket lists). Returns
    (ok, ndecl, badsets, nerrs, sorry)."""
    errs = [l for l in txt.splitlines() if ': error:' in l]
    sorry = ('sorryAx' in txt or "declaration uses 'sorry'" in txt)
    sets = []
    for m in re.finditer(r"depends on axioms: \[(.*?)\]", txt, re.S):
        sets.append({a.strip() for a in m.group(1).split(',') if a.strip()})
    bad = sorted({tuple(sorted(s)) for s in sets if not s <= ALLOWED})
    ok = (not errs) and (not sorry) and len(sets) == nprints and not bad
    return ok, len(sets), [list(b) for b in bad], len(errs), sorry


def compile_one(fname, LP, timeout=3000):
    """Compile Fresh/<fname> with the verbatim recipe. Returns
    (ok, ct, cpu, errclass_or_note, nprints)."""
    src = os.path.join(FRESH, 'Fresh', fname)
    if not os.path.exists(src):
        return False, 0.0, 0.0, 'source missing: Fresh/%s' % fname, 0
    nprints = open(src).read().count('#print axioms')
    stem = fname[:-len('.lean')]
    t1 = time.time()
    ru0 = resource.getrusage(resource.RUSAGE_CHILDREN).ru_utime
    clog = os.path.join(HERE, 'm4fix_compile_%s.log' % stem)
    env = dict(os.environ, LEAN_PATH=LP)
    with open(clog, 'w') as f:
        try:
            c = subprocess.run(['lean', 'Fresh/%s' % fname, '-R', '.',
                                '-o', 'build/Fresh/%s.olean' % stem],
                               cwd=FRESH, env=env, stdout=f, stderr=subprocess.STDOUT,
                               timeout=timeout)
        except subprocess.TimeoutExpired:
            return False, float(timeout), 0.0, \
                'compile wall-timeout (%ds safety cap) -- SLOW, retry later' % timeout, nprints
    ct = time.time() - t1
    cpu = resource.getrusage(resource.RUSAGE_CHILDREN).ru_utime - ru0
    if c.returncode != 0:
        errclass = 'exit %d; ' % c.returncode + '; '.join(
            [l.strip()[:160] for l in open(clog) if ': error:' in l][:3])
        return False, ct, cpu, errclass, nprints
    ok, nd, bad, nerr, sorr = axscan(open(clog).read(), nprints)
    if ok:
        note = '%d/%d axioms all in {propext, Classical.choice, Quot.sound}' % (nd, nprints)
        if ct > 600:
            note += ' -- SLOW WALL (contention; cpu=%ds)' % cpu
        return True, ct, cpu, note, nprints
    return False, ct, cpu, ('axscan: sets=%d/%d bad=%s errs=%d sorry=%s'
                            % (nd, nprints, bad, nerr, sorr)), nprints


def bank(rows_todo, LP):
    """Emit + (hash-skip) compile + axiom-check the mini-bank for the union of the boxes
    needed (todo) and the boxes already PASS-banked (so old rows stay recompilable)."""
    need = set(rows_todo)
    if os.path.exists(TSV):
        for l in open(TSV):
            f = l.rstrip('\n').split('\t')
            if len(f) > 6 and f[6] == 'PASS':
                need.add(f[0])
    args = sorted(need)
    r = subprocess.run([sys.executable, '-I', 'm4fix_bank_v1.py'] + args,
                       cwd=HERE, capture_output=True, text=True)
    if r.returncode != 0 or not os.path.exists(BANK):
        return False, 'bank emitter abort: %s' % (r.stderr.strip()[-400:],)
    h = [l for l in r.stdout.splitlines() if l.startswith('BANKHASH ')][0].split()[1]
    prev = open(BANKHASHF).read().strip() if os.path.exists(BANKHASHF) else None
    olean = os.path.join(FRESH, 'build', 'Fresh', 'M4FixResBank_v1.olean')
    if h == prev and os.path.exists(olean):
        return True, 'mini-bank hash-unchanged, reusing %s' % os.path.basename(olean)
    ok, ct, cpu, note, npr = compile_one('M4FixResBank_v1.lean', LP, timeout=1200)
    if ok:
        with open(BANKHASHF, 'w') as f:
            f.write(h + '\n')
    return ok, 'mini-bank (%d records, %d #print axioms): %s' % (len(args), npr, note)


def main():
    deadline_min = None
    args = [a for a in sys.argv[1:] if not a.startswith('--')]
    for a in sys.argv[1:]:
        if a.startswith('--deadline-min'):
            v = a.split('=', 1)[1] if '=' in a else \
                sys.argv[sys.argv.index(a) + 1]
            deadline_min = float(v)
    recs = [json.loads(l) for l in open(os.path.join(HERE, 'm4fix_res_v1.jsonl'))]
    recs.sort(key=lambda r: (r['nodes'], tuple(r['t'])))
    batch = 0
    for a in sys.argv[1:]:
        if a.startswith('--batch'):
            v = a.split('=', 1)[1] if '=' in a else \
                sys.argv[sys.argv.index(a) + 1]
            batch = int(v)
    if args:   # explicit 7-tuple boxes, e.g. 1,1,1,1,4,6,15
        boxes = [tuple(int(x) for x in a.split(',')) for a in args]
        nodes_of = {tuple(r['box']): r['nodes'] for r in recs}
    else:
        sl = recs[25 * batch:25 * batch + 25]
        boxes = [tuple(r['box']) for r in sl]
        nodes_of = {tuple(r['box']): r['nodes'] for r in recs}
    # skip boxes already recorded PASS in the TSV (restart-safe)
    done = set()
    if os.path.exists(TSV):
        for l in open(TSV):
            f = l.rstrip('\n').split('\t')
            if len(f) > 6 and f[6] == 'PASS':
                done.add(tuple(int(x) for x in f[0].split(',')))
    todo = [b for b in boxes if b not in done]
    print('batch=%d boxes given=%d done(PASS)=%d todo=%d' % (
        batch, len(boxes), len(done), len(todo)), flush=True)
    if not todo:
        summarize(boxes)
        return
    LP = lean_path()
    tok, bnote = bank(['_'.join(str(x) for x in b) for b in todo], LP)
    print('BANK: %s -> %s' % ('OK' if tok else 'FAIL', bnote), flush=True)
    if not tok:
        for b in todo:
            with open(TSV, 'a') as f:
                f.write('\t'.join([','.join(map(str, b)), str(nodes_of.get(b, '?')),
                                   '-', '-', '-', '-', 'FAIL', 'mini-bank: ' + bnote]) + '\n')
        summarize(boxes)
        return
    t0 = time.time()
    for b in todo:
        if deadline_min is not None and (time.time() - t0) / 60 > deadline_min:
            row = [','.join(map(str, b)), str(nodes_of.get(b, '?')), '-', '-', '-', '-',
                   'UNSUPPORTED', 'budget deadline (%.0f min) reached before start'
                   % deadline_min]
            with open(TSV, 'a') as f:
                f.write('\t'.join(row) + '\n'); f.flush()
            print('%s UNSUPPORTED (budget)' % '_'.join(map(str, b)), flush=True)
            continue
        box = '_'.join(str(x) for x in b)
        nodes = nodes_of.get(b, '?')
        row = [','.join(str(x) for x in b), str(nodes)]
        # ---- recon ----
        t1 = time.time()
        rlog = os.path.join(HERE, 'm4fix_recon_%s.out' % box)
        try:
            with open(rlog, 'w') as f:
                r = subprocess.run([sys.executable, '-I', 'm4fix_recon_v1.py',
                                    ','.join(str(x) for x in b)], cwd=HERE,
                                   stdout=f, stderr=subprocess.STDOUT, timeout=3000)
        except subprocess.TimeoutExpired:
            row += ['-', '-', '-', 'FAIL', 'recon wall-timeout (3000s cap)']
            with open(TSV, 'a') as f:
                f.write('\t'.join(row) + '\n'); f.flush()
            print('%s RECON-TIMEOUT' % box, flush=True)
            continue
        rt = time.time() - t1
        rtxt = open(rlog).read()
        m = re.search(r'recon \[T (\d+)/(\d+)\]', rtxt)
        tok = r.returncode == 0 and m and m.group(1) == m.group(2)
        row.append('%s [T %s/%s]' % ('%.1fs' % rt, m.group(1) if m else '?',
                                     m.group(2) if m else '?'))
        if not tok:
            row += ['-', '-', '-', 'FAIL', 'recon not [T n/n]: %s' % (
                [l for l in rtxt.splitlines() if '[F]' in l or 'Error' in l][:3] or rtxt[-300:])]
            with open(TSV, 'a') as f:
                f.write('\t'.join(row) + '\n'); f.flush()
            print('%s RECON-FAIL' % box, flush=True)
            continue
        # ---- reach_utc verdict dump ----
        t1 = time.time()
        ulog = os.path.join(HERE, 'm4fix_utc_%s.out' % box)
        try:
            with open(ulog, 'w') as f:
                u = subprocess.run([sys.executable, '-I', 'm4fix_utc_v1.py',
                                    ','.join(str(x) for x in b)], cwd=HERE,
                                   stdout=f, stderr=subprocess.STDOUT, timeout=3000)
        except subprocess.TimeoutExpired:
            row += ['-', '-', 'FAIL', 'utc wall-timeout (3000s cap)']
            with open(TSV, 'a') as f:
                f.write('\t'.join(row) + '\n'); f.flush()
            print('%s UTC-TIMEOUT' % box, flush=True)
            continue
        ut = time.time() - t1
        utxt = open(ulog).read()
        m = re.search(r'reachutc \S+ \[T (\d+)/(\d+)\]', utxt)
        uok = u.returncode == 0 and m and m.group(1) == m.group(2)
        row.append('%s [T %s/%s]' % ('%.1fs' % ut, m.group(1) if m else '?',
                                     m.group(2) if m else '?'))
        if not uok:
            row += ['-', '-', 'FAIL', 'utc not [T n/n]: %s' % (
                [l for l in utxt.splitlines() if '[F]' in l or 'Error' in l][:3] or utxt[-300:])]
            with open(TSV, 'a') as f:
                f.write('\t'.join(row) + '\n'); f.flush()
            print('%s UTC-FAIL' % box, flush=True)
            continue
        # ---- generate ----
        t1 = time.time()
        try:
            g = subprocess.run([sys.executable, '-I', 'm4fix_gen_v1.py',
                                ','.join(str(x) for x in b)], cwd=HERE,
                               capture_output=True, text=True, timeout=1200)
        except subprocess.TimeoutExpired:
            row += ['-', '-', 'FAIL', 'gen wall-timeout (1200s cap)']
            with open(TSV, 'a') as f:
                f.write('\t'.join(row) + '\n'); f.flush()
            print('%s GEN-TIMEOUT' % box, flush=True)
            continue
        gt = time.time() - t1
        src = os.path.join(FRESH, 'Fresh', 'M4FixRung2_%s.lean' % box)
        leafonly = 'leaf-only mode' in g.stdout
        if leafonly:
            files = sorted(os.path.basename(p) for p in glob.glob(
                os.path.join(FRESH, 'Fresh', 'M4FixRung2_%s_t*.lean' % box)))
        else:
            files = ['M4FixRung2_%s.lean' % box]
        if g.returncode != 0 or not files or not all(
                os.path.exists(os.path.join(FRESH, 'Fresh', fn)) for fn in files):
            row += ['%.1fs' % gt, '-', 'FAIL', 'generator abort: %s' % g.stderr.strip()[-400:]]
            with open(TSV, 'a') as f:
                f.write('\t'.join(row) + '\n'); f.flush()
            print('%s GEN-FAIL %s' % (box, g.stderr.strip()[-200:]), flush=True)
            continue
        row.append('%s%.1fs' % ('leafonly(%d files) ' % len(files) if leafonly else '', gt))
        # ---- compile ONE at a time + axiom scan (all files must pass) ----
        allok = True; notes = []; ctn = []
        for fn in files:
            ok, ct, cpu, note, npr = compile_one(fn, LP)
            allok = allok and ok
            ctn.append('%.0fs' % ct)
            notes.append(note if ok else '%s: %s' % (fn, note))
            if not ok:
                break
        row.append('+'.join(ctn) + 's')
        if allok:
            note = ' | '.join(notes)
            row += ['PASS', note]
        else:
            row += ['FAIL', notes[-1]]
        with open(TSV, 'a') as f:
            f.write('\t'.join(row) + '\n'); f.flush()
        print('%s %s (nodes=%s compile=%s%s)' % (
            box, row[6], nodes, row[5],
            '' if allok else ' -- ' + row[7][:120]), flush=True)
    summarize(boxes)


def summarize(boxes):
    want = [','.join(str(x) for x in b) for b in boxes]
    rows = {}
    if os.path.exists(TSV):
        for l in open(TSV):
            f = l.rstrip('\n').split('\t')
            if len(f) > 7 and f[0] in want:
                rows[f[0]] = f
    npass = sum(1 for f in rows.values() if f[6] == 'PASS')
    nfail = sum(1 for f in rows.values() if f[6] == 'FAIL')
    nuns = sum(1 for f in rows.values() if f[6] == 'UNSUPPORTED')
    print('== m4fix batch summary: %d/%d PASS, %d FAIL, %d UNSUPPORTED ==' % (
        npass, len(want), nfail, nuns), flush=True)
    for f in rows.values():
        if f[6] != 'PASS':
            print('  %s %s: %s' % (f[0], f[6], f[7][:160]), flush=True)


if __name__ == '__main__':
    main()
