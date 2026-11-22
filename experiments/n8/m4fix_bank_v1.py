# m4fix_bank_v1.py -- emit the C3 mini-bank Lean file Fresh/M4FixResBank_v1.lean: per box a
# `m4res_<box> : M4Res` def (the CONSTRUCTED record: `m4fix_res_v1.jsonl` shape fields, with
# the leaf-kind/frontier/lzones PLACEHOLDER fields filled from the instrumented re-run
# `m4comp_cert_ckpt_v1.jsonl`) and a `m4resData_<box> : M4ResData m4res_<box>` theorem
# discharging the validity predicate by `simp [M4ResData, m4res_<box>, InLeafEnvB] <;>
# norm_num` -- exactly the pattern of the 2,329 banked instances in Fresh.MechDataBatch.
# The C3 boxes have no banked `Fresh.MechDataBatch.m4res_<box>` record (E923's named gap);
# this mini-bank supplies the record side of the data connection so the m4fix per-box
# generators can state the composed theorems verbatim.  The pipeline's live cross-checks:
# m4fix_recon_v1.py re-derives the tree and [T]-verifies every record field against ckpt1 +
# ckpt2 + the live DFS; the Lean kernel re-checks all arithmetic of M4ResData here.
#
# New file; no existing file is edited.  Deterministic output (sorted by box name), so the
# driver can hash-skip recompiles when the box set is unchanged.
# Usage: python3 -I m4fix_bank_v1.py <box7tuple '1,1,1,1,4,6,15'> [...] | --stdin
import json, os, sys, hashlib

HERE = os.path.dirname(os.path.abspath(__file__))
FRESH = os.path.normpath(os.path.join(HERE, '..', '..', 'LonelyRunnerFresh'))
OUT = os.path.join(FRESH, 'Fresh', 'M4FixResBank_v1.lean')
MECH = os.path.join(FRESH, 'Fresh', 'MechDataBatch.lean')
FIXJSONL = os.path.join(HERE, 'm4fix_res_v1.jsonl')
CKPT2 = os.path.join(HERE, 'm4comp_cert_ckpt_v1.jsonl')


def optq(s):
    # '49/15' | '18' | '' | None  ->  'some (49 / 15 : ℚ)' | 'some (18 : ℚ)' | 'none'
    if s in (None, ''):
        return 'none'
    if '/' in s:
        a, b = s.split('/')
        return 'some (%s / %s : ℚ)' % (a, b)
    return 'some (%s : ℚ)' % s


def optn(v):
    return 'none' if v is None else 'some %d' % int(v)


def main():
    args = sys.argv[1:]
    if args and args[0] == '--stdin':
        names = [l.strip() for l in sys.stdin if l.strip()]
    else:
        names = [a.replace(',', '_') for a in args]
    assert names, 'pass box 7-tuples (leading 1), e.g. 1,1,1,1,4,6,15'
    for nm in names:
        parts = nm.split('_')
        assert len(parts) == 7 and parts[0] == '1', ('box must be the 7-tuple', nm)

    fix = {}
    for l in open(FIXJSONL):
        r = json.loads(l)
        fix['_'.join(str(x) for x in r['box'])] = r
    ck2 = {}
    for l in open(CKPT2):
        r = json.loads(l)
        ck2[tuple(r['t'])] = r

    mech = open(MECH).read()   # disjointness: C3 names must not shadow banked records
    rows = []
    for nm in sorted(set(names)):
        f = fix.get(nm)
        assert f is not None, ('no constructed record in m4fix_res_v1.jsonl', nm)
        t = tuple(f['t'])
        c = ck2.get(t)
        assert c is not None, ('no ckpt2 record', t)
        assert f['fire'] is True and c['fire'] is True and c['kind'] == 'closed', (nm, t)
        lz = sorted(set((int(a), int(b)) for (a, b) in c['last_zones']))
        assert 'def m4res_%s ' % nm not in mech and 'def m4res_%s:' % nm not in mech, \
            ('name collision with a banked record', nm)
        rows.append((nm, f, c, lz))
    rows.sort(key=lambda x: x[0])

    L = []
    w = L.append
    w('import Fresh.M4CertSound')
    w('')
    w('/-!')
    w('# M4FixResBank_v1: the CONSTRUCTED C3 mini-bank (m4res_* + m4resData_* records)')
    w('')
    w('Written by `experiments/n8/m4fix_bank_v1.py` (new file; nothing existing is edited).')
    w('The %d boxes below are C3-killed residual boxes (merged U-closure key aA,' % len(rows))
    w('`Fresh.UClosureKill`): they HAVE an M4-fired DFS certificate -- the two checkpoint')
    w('artifacts `j2_admit_cert2_checkpoint.jsonl` and `m4comp_cert_ckpt_v1.jsonl` agree')
    w('field-for-field on leaves/nodes/maxdepth/nstart over all 10,211 of them -- but NO')
    w('banked `Fresh.MechDataBatch.m4res_<box>` record (E923\'s named gap).  This file')
    w('supplies the record side: the shape fields from the constructed record')
    w('(`m4fix_res_v1.jsonl`, built from the j2 checkpoint) and the leaf-kind / frontier /')
    w('lzones fields from the instrumented re-run (`m4comp_cert_ckpt_v1.jsonl`) -- in the')
    w('constructed record those are placeholders (the j2 checkpoint does not record them),')
    w('and this is exactly the fill m4fix_res_v1.py documents.  Per box the pipeline\'s')
    w('live cross-check is `experiments/n8/m4fix_recon_v1.py` ([T n/n]: the reconstructed')
    w('DFS tree against ckpt1 + ckpt2 + this record, all 16 fields), and the kernel')
    w('re-checks every arithmetic condition of `M4ResData` here.  A python-side pre-flight')
    w('audit of all 10,211 records (0 violations) is in the m4fix run log.')
    w('-/')
    w('')
    w('namespace Fresh.MechDataBatch')
    w('')
    for nm, f, c, lz in rows:
        w('/-- `m4res_%s`: the CONSTRUCTED residual-certificate record of the C3-killed box' % nm)
        w('(t = %s, merged U-closure key aA): shape fields from `m4fix_res_v1.jsonl`' % (f['t'],))
        w('(built from `j2_admit_cert2_checkpoint.jsonl`), leaf-kind / frontier / lzones')
        w('fields from the instrumented re-run `m4comp_cert_ckpt_v1.jsonl`.  Reconstructed')
        w('live and [T]-verified per box by `m4fix_recon_v1.py`; validity kernel-checked')
        w('below. -/')
        w('-- STANDING: DATA')
        w('def m4res_%s : M4Res :=' % nm)
        w('  ⟨[%s], %d, %d, %d, %d, %d, %d, %d, %s,' % (
            ', '.join(str(x) for x in f['box']),
            f['leaves'], f['nodes'], f['maxdepth'], f['nstart'],
            int(c['reach_leaves']), int(c['deadend_leaves']), int(c['start_infeas']),
            '[' + ', '.join('(%d, %d)' % z for z in lz) + ']'))
        w('    %s, %s, %s, %s, %s, %s, %s⟩' % (
            optq(c['lf_min']), optq(c['lf_med']), optq(c['lf_max']),
            optn(c['ld_min']), optn(c['ld_max']), optn(c['dd_min']), optn(c['dd_max'])))
        w('')
        w('theorem m4resData_%s : M4ResData m4res_%s := by' % (nm, nm))
        w('  simp [M4ResData, m4res_%s, InLeafEnvB] <;> norm_num' % nm)
        w('')
        w('#print axioms m4resData_%s' % nm)
        w('')
    w('end Fresh.MechDataBatch')
    w('')

    body = '\n'.join(L) + '\n'
    old = open(OUT).read() if os.path.exists(OUT) else None
    if old == body:
        print('mini-bank unchanged (%d records): %s' % (len(rows), OUT))
    else:
        with open(OUT, 'w') as f:
            f.write(body)
        print('wrote %s (%d records, %d lines)' % (OUT, len(rows), len(L)))
    print('BANKHASH ' + hashlib.sha256(body.encode()).hexdigest()[:16])


if __name__ == '__main__':
    main()
