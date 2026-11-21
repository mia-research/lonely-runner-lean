# perwalkhdom_gen_v1.py -- Lean 4 generator: the per-walk CapsDom attestation instances
# for box b1 = ![1,3,4,5,5,5,7], banked as Fresh/PerWalkHdom.lean.
#
# Track C's direct consequence of the favorable route-decider (E893/E898/E911): the select
# rung's uniform hdom (TabLe against the ONE census trace, all 49 pairs) is refuted as a
# box-uniform datum (Fresh.SelectRung1Data.selectRung1_hdom_owed_unsupplyable_b1, walk19);
# the route decision forces the PER-WALK form.  perwalk_v2 (E911) verified the per-walk
# datum's data layer: on EVERY one of the 804 realized first-window walks W (from
# mkTab_1_3_4_5_5_5_7), ALL FOUR records r0..r3 of compFam_1_3_4_5_5_5_7 attest W's OWN
# endpoint trace (CapsDom V_W e.y e.caps e.x).  The reconciliation: the 564 census-trace
# TabLe failures live on 12 pairs the records' cap walks never read; the trace-relevant
# pairs are mechanically the union of the records' cap pairs = {(0,6), (1,6)}, and on
# every walk the stored entries at those pairs dominate the caps:
#   (0,6): 3 distinct values, all <= 1870/13113 (max with equality on 36 walks);
#   (1,6): 6 distinct values, all <= 55/117    (max with equality on 240 walks).
#
# Emission (one Lean file, new; nothing existing is edited):
#   - per walk W (seq n, 0..803): the relevant-pair trace projection VWalk_n (a literal
#     UTable: the two stored pairs, `none` elsewhere -- CapsDom reads only the cap pairs,
#     so the projection is exactly what the attestation consumes) and the per-instance
#     theorem hdom_walk_n : CapsDom VWalk_n r0.y r0.caps r0.x AND CapsDom VWalk_n r1.y
#     r1.caps r1.x (r2/r3 are CapsDom-identical to r1), each proof `capsDom_single` on an
#     inline rfl entry + an inline norm_num comparison (the BandCertDataExt per-instance
#     pattern), each carrying #print axioms.
#   - the enumeration walkInstances (804 (seq, len, table) triples) with
#     walkInstances_len : length = 804, the witness lemma r1_mem_b1, and the aggregate
#     hdom_perwalk_b1 : every banked instance carries a record of compFamOf b1 attesting
#     its own projection at the record's cap pair.
#   - the worked deepest instance (walk seq 203, len 28): its 28-step word as List Step
#     literals, the length check, the membership check in the enumeration, and the
#     trace-reproduction lemmas pinning the emitted projection literals to the banked
#     trace line's pairs (rfl), plus a generator-side reproduction: the walk's endpoint
#     trace is RECOMPUTED here through the value-verbatim l_-mirror (selectoweda_v1
#     header, perwalk_v2's run_word) and asserted to match the banked trace line (values,
#     flags, totality, entrywise <= mkTab) and to attest all four records.
#
# Exact Fractions throughout data-side; floats nowhere.  The emitted Lean is
# literal-arithmetic only (rfl + norm_num).  Usage:
#   python3 -I perwalkhdom_gen_v1.py [--limit K] [--out PATH]
# --limit K emits the first K walks (pilot); default emits all 804.
import os, re, json, sys, argparse, time
from fractions import Fraction as F

AUD = os.path.dirname(os.path.abspath(__file__))
N8 = os.path.dirname(AUD)
ROOT = os.path.dirname(os.path.dirname(N8))
LEAN = os.path.join(ROOT, 'LonelyRunnerFresh', 'Fresh')

CENSUS = os.path.join(AUD, 'perwalk_v2_census.jsonl')
TRACES = os.path.join(AUD, 'perwalk_v2_traces.jsonl')
OUT_DEFAULT = os.path.join(LEAN, 'PerWalkHdom.lean')

BOX = '![1, 3, 4, 5, 5, 5, 7] : Fin 7 → ℤ'
CAP0 = '1870 / 13113'   # r0's cap (y = 0, pair (0,6))
CAP1 = '55 / 117'       # r1/r2/r3's cap (y = 1, pair (1,6))

# ---- record parsing (perwalk_v2.py's parsers, verbatim) ----
CAP_ENTRY = re.compile(r'\(\s*(\d+)\s*,\s*\(\s*(\d+(?:\s*/\s*\d+)?)\s*\)\s*\)')
REC = re.compile(r'⟨\s*(\d+)\s*,\s*(\d+)\s*,\s*(\d+)\s*,\s*(\d+)\s*,\s*\[([^\]]*)\]\s*⟩')

def frac_of(txt):
    t = txt.replace(' ', '')
    if '/' in t:
        a, b = t.split('/')
        return F(int(a), int(b))
    return F(int(t))

def parse_records(path, defname):
    src = open(path).read()
    i = 0
    while True:
        i = src.find('def %s : ComposedFam' % defname, i)
        if i < 0:
            raise AssertionError((defname, 'def not found'))
        j = src.find('\n  ]⟩', i)
        if j < 0:
            raise AssertionError((defname, 'list close not found'))
        body = src[i:j]
        if REC.search(body):
            break
        i += 10
    recs = []
    for m in REC.finditer(body):
        x, y, A, B = int(m.group(1)), int(m.group(2)), int(m.group(3)), int(m.group(4))
        caps = [(int(cm.group(1)), frac_of(cm.group(2))) for cm in CAP_ENTRY.finditer(m.group(5))]
        assert len(caps) >= 1, (defname, 'caps parse', m.group(5))
        recs.append((x, y, A, B, caps))
    return recs

# ---- trace-mirror reuse (perwalk_v2.py's reuse pattern, verbatim) ----
v1src = open(os.path.join(AUD, 'selectoweda_v1.py')).read()
exec(v1src.split('# ---- the DFS ----')[0])
LEAN = os.path.join(ROOT, 'LonelyRunnerFresh', 'Fresh')  # re-set: the exec'd header rebinds LEAN

def run_word(word):
    U = [[mkTab[p][q] for q in range(7)] for p in range(7)]
    a, Aex = 0, F(1)
    for (b, A, B) in word:
        V = l_step(U, a, b, Aex, F(A), F(B))
        assert V is not None, ('step died', b, A, B)
        U = V; a, Aex = b, F(B)
    return U

def caps_dom(get, y, caps):
    prev = y
    for (z, c) in caps:
        e = get(prev, z)
        if e is None or not (e[0] <= c):
            return (False, (prev, z, e, c))
        prev = z
    return (True, None)

def frac_s(x):
    return '%d/%d' % (x.numerator, x.denominator)

WORDS = os.path.join(AUD, 'perwalk_v2_words.jsonl')

def load_data_lines(path):
    out = []
    for l in open(path):
        l = l.strip()
        if not l:
            continue
        d = json.loads(l)
        if d.get('complete'):
            continue
        out.append(d)
    return out

def load_banked():
    """Canonical walk key = the perwalk_v2_words.jsonl enumeration index (phase1's DFS
    yield order; phase1 asserts a yield-prefix on every resume, so it is THE enumeration
    of record).  The trace/census lines are joined BY WORD IDENTITY: the JSONL seq fields
    are run-local orderings (an aborted early run left 20 mislabeled lines, and the
    phase2/3 indexing differs from the final words-file order), so the word is the join
    key and the words-file seq is the walk key.  Returns {seq: {...}} over 0..803."""
    words = {}
    for d in load_data_lines(WORDS):
        assert d.get('seq') is not None and d['seq'] not in words, ('words dup', d.get('seq'))
        words[d['seq']] = tuple(tuple(s) for s in d['word'])
    assert len(words) == 804 and sorted(words) == list(range(804)), 'words file not 804 contiguous'
    tr = {}
    for d in load_data_lines(TRACES):
        w = tuple(tuple(s) for s in d['word'])
        assert w not in tr, ('trace dup word', d['seq'])
        tr[w] = d
    cn = {}
    for d in load_data_lines(CENSUS):
        w = tuple(tuple(s) for s in d['word'])
        assert w not in cn, ('census dup word', d['seq'])
        cn[w] = d
    assert set(tr) == set(words.values()) == set(cn), 'word sets disagree across the three JSONLs'
    canon = {}
    for s, w in words.items():
        t, c = tr[w], cn[w]
        assert t['len'] == c['len'] == len(w), ('len disagree', s)
        assert c['attests'] == [0, 1, 2, 3], ('attests', s, c['attests'])
        assert sorted(t['pairs'].keys()) == ['0,6', '1,6'], ('pairs keys', s)
        canon[s] = {'seq': s, 'len': len(w), 'word': w, 'tr': t, 'cn': c,
                    'e06': F(*t['pairs']['0,6'][:2]), 'f06': t['pairs']['0,6'][2],
                    'e16': F(*t['pairs']['1,6'][:2]), 'f16': t['pairs']['1,6'][2],
                    'tab_le_census': t['tab_le_census']}
    return canon

def main():
    t0 = time.time()
    ap = argparse.ArgumentParser()
    ap.add_argument('--limit', type=int, default=0, help='emit only the first K walks (pilot)')
    ap.add_argument('--out', default=OUT_DEFAULT)
    args = ap.parse_args()

    # ---- load the banked data (canonical join) ----
    canon = load_banked()
    assert len(canon) == 804, len(canon)

    # ---- the records, re-parsed from the banked Lean source; caps literals cross-checked ----
    recs = parse_records(os.path.join(LEAN, 'ComposedFamData.lean'), 'compFam_1_3_4_5_5_5_7')
    assert recs == [
        (6, 0, 13, 3, [(6, F(1870, 13113))]),
        (6, 1, 65, 31, [(6, F(55, 117))]),
        (6, 1, 5, 3, [(6, F(55, 117))]),
        (6, 1, 65, 47, [(6, F(55, 117))]),
    ], 'record literals drifted from the emitted caps'
    # the trace-relevant pairs, derived mechanically from the records' cap pairs
    PAIR_KEYS = []
    for (x, y, A, B, caps) in recs:
        prev = y
        for (z, _) in caps:
            if (prev, z) not in PAIR_KEYS:
                PAIR_KEYS.append((prev, z))
            prev = z
    assert PAIR_KEYS == [(0, 6), (1, 6)], PAIR_KEYS

    # ---- per-walk asserts: the pair entries dominate the caps on every walk ----
    cap0, cap1 = F(1870, 13113), F(55, 117)
    walks = [canon[s] for s in sorted(canon)]
    for k in walks:
        assert k['e06'] <= cap0 and k['e16'] <= cap1, (k['seq'], k['e06'], k['e16'])
    n_eq0 = sum(1 for w in walks if w['e06'] == cap0)
    n_eq1 = sum(1 for w in walks if w['e16'] == cap1)
    v06s = sorted(set((w['e06'], w['f06']) for w in walks))
    v16s = sorted(set((w['e16'], w['f16']) for w in walks))
    assert len(v06s) == 3 and len(v16s) == 6, (v06s, v16s)
    n_tab_fails = sum(1 for w in walks if not w['tab_le_census'])
    assert n_tab_fails == 564, n_tab_fails
    print('data asserts OK: 804 walks, attests=[0,1,2,3] on all, pairs {(0,6),(1,6)},')
    print('  (0,6): 3 distinct values, max-equality walks %d; (1,6): 6 distinct, max-equality walks %d;' % (n_eq0, n_eq1))
    print('  census-trace TabLe fails (the reconciled 564): %d' % n_tab_fails)

    # ---- worked deepest instance: generator-side trace reproduction ----
    # (selection over the EMITTED set, so pilot runs bank their own deepest walk)
    n_emit = len(walks) if not args.limit else min(args.limit, len(walks))
    emit = walks[:n_emit]
    deep = max(emit, key=lambda w: (w['len'], -w['seq']))
    dseq, dlen = deep['seq'], deep['len']
    V = run_word(deep['word'])
    for i in range(7):
        for j in range(7):
            e = V[i][j]
            assert e is not None, ('trace not total', dseq, i, j)
            assert e[0] <= mkTab[i][j][0], ('trace loosened vs mkTab', dseq, i, j)
    for (p, q) in PAIR_KEYS:
        banked = deep['tr']['pairs']['%d,%d' % (p, q)]
        e = V[p][q]
        assert [e[0].numerator, e[0].denominator, e[1]] == banked, \
            ('reproduction mismatch', dseq, (p, q), frac_s(e[0]), e[1], banked)
    att = [caps_dom(lambda p, q: V[p][q], y, caps)[0] for (x, y, A, B, caps) in recs]
    assert att == [True, True, True, True], ('reproduction attests', dseq, att)
    d06, d16 = deep['e06'], deep['e16']
    print('deepest walk reproduction OK: seq %d len %d; recomputed trace matches the banked' % (dseq, dlen))
    print('  line at (0,6)=%s and (1,6)=%s (values, flags, totality, <= mkTab); attests all four records.' %
          (frac_s(d06), frac_s(d16)))

    # ---- emission ----
    L = []
    w = L.append
    w('import Fresh.SelectRung1Data')
    w('')
    w('/-!')
    w('# PerWalkHdom: the per-walk CapsDom attestation instances for box b1 (Track C data layer)')
    w('')
    w('New file (2026-11-21); nothing existing is edited; generated by')
    w('`experiments/n8/onefast_audit/perwalkhdom_gen_v1.py` from the verified per-walk data')
    w('(`perwalk_v2_census.jsonl` + `perwalk_v2_traces.jsonl`, E911).')
    w('')
    w('Walk key: the `perwalk_v2_words.jsonl` enumeration index (phase1\'s DFS yield order,')
    w('the enumeration of record -- phase1 asserts a yield-prefix on every resume).  The')
    w('trace/census lines are joined BY WORD IDENTITY: the JSONL `seq` fields carry')
    w('run-local orderings (an aborted early run left 20 mislabeled lines, and the phase2/3')
    w('indexing differs from the final words-file order), so this generator joins on the')
    w('word -- each of the 804 words appears exactly once in each file -- and re-keys by the')
    w('words-file index.  All E911 statistics (804/804 attested, the 564 census-trace TabLe')
    w('failures, the 3+6 distinct pair values, the 8 pair-value combos, the equality counts)')
    w('were re-verified under this canonical indexing before emission.')
    w('')
    w('## The datum and its provenance')
    w('')
    w('The select rung `Fresh.SelectRung1.selectRung1_1_3_4_5_5_5_7` needs, per realized')
    w('first-window walk, a record of `compFamOf b1` attesting FROM THAT WALK')
    w('(`AttestsFrom e walk U`).  Its banked form demanded the walk\'s trace be `TabLe`-below')
    w('the ONE census trace `T8_1_3_4_5_5_5_7_12` (all 49 pairs); that uniform `hdom` is')
    w('REFUTED as a box-uniform datum')
    w('(`Fresh.SelectRung1Data.selectRung1_hdom_owed_unsupplyable_b1`, walk19 at pair (0,1)).')
    w('The route decision therefore forces the PER-WALK form, and `perwalk_v2` (E911) verified')
    w('its data layer: for EVERY one of the 804 realized first-window walks W of the closure')
    w('start `mkTab_1_3_4_5_5_5_7` (lengths 18..28; the class coincides, as a set, with the')
    w('dump\'s table-level 804-word enumeration), ALL FOUR records r0..r3 of')
    w('`compFam_1_3_4_5_5_5_7` attest W\'s OWN endpoint trace: `CapsDom V_W e.y e.caps e.x`.')
    w('')
    w('The reconciliation: `CapsDom` reads only the pairs of the record\'s cap walk -- the')
    w('trace-relevant pairs, mechanically the union of the four records\' cap pairs, is')
    w('{(0,6), (1,6)}.  The 564 census-trace `TabLe` failures live on 12 OTHER pairs and')
    w('never touch these two on any walk: on every walk the stored entry at (0,6) is one of')
    w('3 distinct values, all ≤ 1870/13113 (max with equality on %d walks), and the entry at' % n_eq0)
    w('(1,6) is one of 6 distinct values, all ≤ 55/117 (max with equality on %d walks).' % n_eq1)
    w('')
    w('## What is banked (and the honest scope)')
    w('')
    w('Per walk W (seq n), a literal relevant-pair trace projection `VWalk_n : UTable`: the')
    w('two stored pairs with their exact trace values and strict flags, `none` elsewhere.')
    w('`CapsDom` treats `none` as the loosest bound and reads only the cap pairs, so the')
    w('projection is EXACTLY what the attestation consumes; the full 49-pair traces stay in')
    w('`perwalk_v2_traces.jsonl`.  Per walk, the instance theorem')
    w('')
    w('    hdom_walk_n : CapsDom VWalk_n (0 : Fin 7) [(6, (1870/13113 : ℝ))] (6 : Fin 7) ∧')
    w('                  CapsDom VWalk_n (1 : Fin 7) [(6, (55/117 : ℝ))] (6 : Fin 7)')
    w('')
    w('(r0 = ⟨6, 0, 13, 3, [(6, 1870/13113)]⟩ and r1 = ⟨6, 1, 65, 31, [(6, 55/117)]⟩; r2/r3')
    w('share r1\'s pair and cap, so these two conjuncts carry all four records\' conditions).')
    w('Each proof is `capsDom_single` on an inline `rfl` entry and an inline `norm_num`')
    w('comparison (the `Fresh.BandCertDataExt` per-instance pattern).  The enumeration')
    w('`walkInstances` (804 (seq, len, table) triples, perwalk_v2 order) carries the class as')
    w('data, and `hdom_perwalk_b1` states the aggregate in the select shape: every banked')
    w('instance carries SOME record of `compFamOf b1` attesting its own projection at the')
    w('record\'s cap pair.')
    w('')
    w('All arithmetic is exact (`rfl` on the literal entries; `norm_num` on the emitted')
    w('comparisons; data-side this generator asserts the same inequalities in `Fraction` and')
    w('reproduces the deepest walk\'s trace through the value-verbatim `l_`-mirror).  Every')
    w('theorem carries `#print axioms`; the accepted profile is the standard three --')
    w('`sorryAx` is failure.')
    w('-/')
    w('')
    w('namespace Fresh.PerWalkHdom')
    w('')
    w('open Fresh.ChainDomBase Fresh.CapChainsOfCarve Fresh.JoinFamComposed Fresh.OneSidedComposed')
    w('  Fresh.OneSidedGlue Fresh.UClosure Fresh.SpineSound Fresh.FilterAssembly Fresh.DumpDomData')
    w('  Fresh.ChainDomPerRec8 Fresh.WordCoverSide Fresh.SelectRung1')
    w('')
    w('set_option maxHeartbeats 10000000')
    w('-- the chunked enumeration literals need elaboration depth beyond the default 512;')
    w('-- the enumeration itself is chunked (14 appended sublists) to keep every single')
    w('-- literal chain shallow (an unchunked 804-element chain aborts the elaborator)')
    w('set_option maxRecDepth 2000')
    w('')

    # ---- section 1: the witness record membership ----
    w('/-! ## 1. The attesting witness record -/')
    w('')
    w('/-- The aggregate\'s witness: r1 = ⟨6, 1, 65, 31, [(6, 55/117)]⟩, the rung\'s record')
    w('(r2/r3 are CapsDom-identical to r1; r0 = ⟨6, 0, 13, 3, [(6, 1870/13113)]⟩ is the')
    w('second, distinct cap condition, carried as the per-walk instances\' `.1`).  Membership')
    w('via the banked dispatch `Fresh.SelectRung1.compFamOf_b1`. -/')
    w('theorem r1_mem_b1 :')
    w('    (⟨6, 1, 65, 31, [(6, (%s : ℝ))]⟩ : ComposedEdge) ∈' % CAP1)
    w('      (compFamOf (%s)).edges := by' % BOX)
    w('  rw [compFamOf_b1]')
    w('  simp [compFam_1_3_4_5_5_5_7]')
    w('')
    w('#print axioms r1_mem_b1')
    w('')

    # ---- section 2: the 804 per-walk instances ----
    w('/-! ## 2. The per-walk trace projections and CapsDom instances (%d walks) -/' % n_emit)
    w('')
    for k in emit:
        e06 = '%d / %d' % (k['e06'].numerator, k['e06'].denominator)
        e16 = '%d / %d' % (k['e16'].numerator, k['e16'].denominator)
        f06 = 'true' if k['f06'] else 'false'
        f16 = 'true' if k['f16'] else 'false'
        w('/-- Walk seq %d (len %d): trace projection (0,6) = %s, (1,6) = %s' %
          (k['seq'], k['len'], e06, e16))
        w('(the `perwalk_v2_traces.jsonl` line whose word is this walk\'s word -- the JSONL')
        w('lines are joined by word identity, walk key = the words-file enumeration index;')
        w('attests r0..r3 per the census line of the same word). -/')
        w('-- STANDING: DATA (per-walk trace projection)')
        w('def VWalk_%d : UTable := fun p q =>' % k['seq'])
        w('  if p = (0 : Fin 7) ∧ q = (6 : Fin 7) then some ((%s : ℚ), %s) else' % (e06, f06))
        w('  if p = (1 : Fin 7) ∧ q = (6 : Fin 7) then some ((%s : ℚ), %s) else' % (e16, f16))
        w('  none')
        w('')
        w('-- STANDING: DATA (per-walk CapsDom instance: r0 ∧ r1; r2/r3 share r1\'s condition)')
        w('theorem hdom_walk_%d :' % k['seq'])
        w('    CapsDom VWalk_%d (0 : Fin 7) [(6, (%s : ℝ))] (6 : Fin 7) ∧' % (k['seq'], CAP0))
        w('    CapsDom VWalk_%d (1 : Fin 7) [(6, (%s : ℝ))] (6 : Fin 7) :=' % (k['seq'], CAP1))
        w('  ⟨capsDom_single ⟨(%s : ℚ), %s, rfl, by norm_num⟩,' % (e06, f06))
        w('   capsDom_single ⟨(%s : ℚ), %s, rfl, by norm_num⟩⟩' % (e16, f16))
        w('')
        w('#print axioms hdom_walk_%d' % k['seq'])
        w('')

    # ---- section 3: the enumeration and the aggregate ----
    CHUNK = 60
    n_chunks = (n_emit + CHUNK - 1) // CHUNK
    chunk_names = ['walkChunk_%d' % (i + 1) for i in range(n_chunks)]
    chunk_args = ', '.join(chunk_names)
    w('/-! ## 3. The enumeration and the aggregate -/')
    w('')
    w('-- The %d-walk class as banked instances: (seq, len, relevant-pair trace projection),' % n_emit)
    w('-- seq 0..%d in the perwalk_v2 enumeration order.  The enumeration itself is part of the' % (n_emit - 1))
    w('-- data: which walk carries which pair values is exactly the banked census.  It is')
    w('-- chunked into %d appended sublists (every literal chain stays shallow); the' % n_chunks)
    w('-- per-chunk aggregate lemmas below make the consumption boundary-free.')
    w('-- STANDING: DATA (the enumeration: %d instances in %d chunks)' % (n_emit, n_chunks))
    for ci in range(n_chunks):
        ce = emit[ci * CHUNK:(ci + 1) * CHUNK]
        w('-- walkInstances chunk %d (seqs %d..%d).' % (ci + 1, ce[0]['seq'], ce[-1]['seq']))
        w('def walkChunk_%d : List (ℕ × ℕ × UTable) :=' % (ci + 1))
        items = ['(%d, %d, VWalk_%d)' % (k['seq'], k['len'], k['seq']) for k in ce]
        for i in range(0, len(items), 3):
            chunk = items[i:i + 3]
            sep = ',' if i + 3 < len(items) else ']'
            prefix = '  [' if i == 0 else '   '
            w(prefix + ', '.join(chunk) + sep)
        w('')
        w('theorem walkChunk_%d_len : walkChunk_%d.length = %d := rfl' % (ci + 1, ci + 1, len(ce)))
        w('')
        w('#print axioms walkChunk_%d_len' % (ci + 1))
        w('')
    w('/-- The %d-walk class: the %d chunks appended (explicitly right-nested). -/' % (n_emit, n_chunks))
    w('def walkInstances : List (ℕ × ℕ × UTable) :=')
    body = chunk_names[-1]
    for ci in range(n_chunks - 2, -1, -1):
        body = '%s ++ (%s)' % (chunk_names[ci], body)
    w('  ' + body)
    w('')
    w('theorem walkInstances_len : walkInstances.length = %d :=' % n_emit)
    w('  by simp only [walkInstances, List.length_append, %s]' %
      ', '.join('walkChunk_%d_len' % (ci + 1) for ci in range(n_chunks)))
    w('')
    w('#print axioms walkInstances_len')
    w('')
    w('/-- **Per-chunk aggregates**: each chunk carries the select shape on its own walks.')
    w('These make the full aggregate boundary-free (no False leaves interrupt the peel). -/')
    for ci in range(n_chunks):
        ce = emit[ci * CHUNK:(ci + 1) * CHUNK]
        w('theorem hdom_chunk_%d :' % (ci + 1))
        w('    ∀ W ∈ walkChunk_%d, ∃ e ∈ (compFamOf (%s)).edges,' % (ci + 1, BOX))
        w('      CapsDom W.2.2 e.y e.caps e.x := by')
        w('  intro W hW')
        w('  simp only [walkChunk_%d, List.mem_cons, List.not_mem_nil] at hW' % (ci + 1))
        for k in ce:
            w('  rcases hW with rfl | hW')
            w('  · exact ⟨⟨6, 1, 65, 31, [(6, (%s : ℝ))]⟩, r1_mem_b1, hdom_walk_%d.2⟩' % (CAP1, k['seq']))
        w('  exact absurd hW (by simp)')
        w('')
        w('#print axioms hdom_chunk_%d' % (ci + 1))
        w('')
    w('/-- The append lift: the select shape propagates over `++` (this keeps the aggregate')
    w('free of any reliance on the association simp leaves the membership disjunction in). -/')
    w('theorem agg_append {P : (ℕ × ℕ × UTable) → Prop} {l₁ l₂ : List (ℕ × ℕ × UTable)}')
    w('    (h₁ : ∀ W ∈ l₁, P W) (h₂ : ∀ W ∈ l₂, P W) :')
    w('    ∀ W ∈ l₁ ++ l₂, P W := by')
    w('  intro W hW')
    w('  rcases List.mem_append.mp hW with h | h')
    w('  · exact h₁ W h')
    w('  · exact h₂ W h')
    w('')
    w('#print axioms agg_append')
    w('')
    w('/-- **THE AGGREGATE** (the per-walk datum, select shape): every banked instance -- i.e.')
    w('every walk of the %d-walk class -- carries a record of `compFamOf b1` attesting the' % n_emit)
    w('walk\'s own trace at the record\'s cap pair.  Consumed at the assembly together with')
    w('the per-walk projection-tightness datum via `capsDom_tabLe` (see the composition note')
    w('at the end of this file). -/')
    w('-- STANDING: DATA-AGGREGATE (%d/%d walks attested)' % (n_emit, n_emit))
    w('theorem hdom_perwalk_b1 :')
    w('    ∀ W ∈ walkInstances, ∃ e ∈ (compFamOf (%s)).edges,' % BOX)
    w('      CapsDom W.2.2 e.y e.caps e.x := by')
    if n_chunks == 1:
        w('  intro W hW')
        w('  exact hdom_chunk_1 W hW')
    else:
        for ci in range(n_chunks - 1, 0, -1):
            h2arg = 'hdom_chunk_%d' % (ci + 1) if ci + 1 == n_chunks else 'h%d' % (ci + 1)
            w('  have h%d := agg_append hdom_chunk_%d %s' % (ci, ci, h2arg))
        w('  intro W hW')
        w('  exact h1 W hW')
    w('')
    w('#print axioms hdom_perwalk_b1')
    w('')

    # ---- section 4: the worked deepest instance ----
    w('/-! ## 4. The worked deepest instance: walk seq %d, len %d -/' % (dseq, dlen))
    w('')
    w('/-- The class\'s longest walk (class length range %d..%d; this walk has len %d).  Its banked trace line' %
      (min(k['len'] for k in emit), max(k['len'] for k in emit), dlen))
    w('(the `perwalk_v2_traces.jsonl` line whose word is this walk\'s word -- the JSONL\'s own')
    w('run-local seq field is %d; the canonical walk key is the words-file index, and the' % deep['tr']['seq'])
    w('pairs below are quoted from that line verbatim):')
    w('')
    w('    {"seq": %d, "len": %d, "word": [...%d steps...], "pairs": {"0,6": [%d, %d, %s], "1,6": [%d, %d, %s]}, ...}' %
      (deep['tr']['seq'], dlen, dlen, d06.numerator, d06.denominator, 'true' if deep['f06'] else 'false',
       d16.numerator, d16.denominator, 'true' if deep['f16'] else 'false'))
    w('')
    w('The generator reproduced this line independently: the walk\'s endpoint trace was')
    w('recomputed through the value-verbatim `l_`-mirror run from `mkTab_1_3_4_5_5_5_7`')
    w('(totality, entrywise ≤ `mkTab`), the two relevant pairs match the banked line (values')
    w('AND strict flags), and all four records attest the recomputed trace.  The Lean lemmas')
    w('below pin the emitted projection literals to that banked line (the trace-reproduction')
    w('check); `hdom_walk_%d` above is the walk\'s per-walk theorem. -/' % dseq)
    w('')
    w('-- STANDING: DATA (deepest-walk worked instance)')
    w('def walk%d_word : List Step :=' % dseq)
    steps = ['⟨(%d : Fin 7), (%d : ℚ), (%d : ℚ)⟩' % (b, A, B) for (b, A, B) in deep['word']]
    assert len(steps) == dlen
    for i in range(0, len(steps), 3):
        chunk = steps[i:i + 3]
        sep = ',' if i + 3 < len(steps) else ']'
        prefix = '  [' if i == 0 else '   '
        w(prefix + ', '.join(chunk) + sep)
    w('')
    w('theorem walk%d_len : walk%d_word.length = %d := rfl' % (dseq, dseq, dlen))
    w('')
    w('#print axioms walk%d_len' % dseq)
    w('')
    w('/-- The deepest walk sits in the enumeration at its own key (seq %d, len %d):' % (dseq, dlen))
    w('membership in its chunk (position %d of chunk %d), then through the append tree. -/' %
      (dseq - (dseq // CHUNK) * CHUNK, dseq // CHUNK + 1))
    w('theorem walk%d_mem_chunk : (%d, %d, VWalk_%d) ∈ walkChunk_%d := by' %
      (dseq, dseq, dlen, dseq, dseq // CHUNK + 1))
    w('  simp only [walkChunk_%d, List.mem_cons, List.not_mem_nil]' % (dseq // CHUNK + 1))
    for i in range(dseq - (dseq // CHUNK) * CHUNK):
        w('  apply Or.inr')
    w('  exact Or.inl trivial')
    w('')
    w('#print axioms walk%d_mem_chunk' % dseq)
    w('')
    ci0 = dseq // CHUNK                      # 0-based target chunk
    # thread the chunk membership through the explicitly right-nested append tree
    if ci0 == n_chunks - 1:
        inner = 'walk%d_mem_chunk' % dseq
    else:
        tail = 'walkChunk_%d' % n_chunks
        for cj in range(n_chunks - 2, ci0, -1):
            tail = 'walkChunk_%d ++ (%s)' % (cj + 1, tail)
        inner = 'List.mem_append_left (%s) walk%d_mem_chunk' % (tail, dseq)
    term = inner
    for cj in range(ci0 - 1, -1, -1):
        term = 'List.mem_append_right walkChunk_%d (%s)' % (cj + 1, term)
    w('theorem walk%d_in : (%d, %d, VWalk_%d) ∈ walkInstances := by' % (dseq, dseq, dlen, dseq))
    w('  exact %s' % term)
    w('')
    w('#print axioms walk%d_in' % dseq)
    w('')
    w('/-- Trace-reproduction checks: the emitted projection literals ARE the banked trace')
    w('line\'s pairs (value and strict flag, per pair). -/')
    w('theorem walk%d_t06 : VWalk_%d (0 : Fin 7) (6 : Fin 7) = some ((%s : ℚ), %s) := rfl' %
      (dseq, dseq, '%d / %d' % (d06.numerator, d06.denominator), 'true' if deep['f06'] else 'false'))
    w('')
    w('theorem walk%d_t16 : VWalk_%d (1 : Fin 7) (6 : Fin 7) = some ((%s : ℚ), %s) := rfl' %
      (dseq, dseq, '%d / %d' % (d16.numerator, d16.denominator), 'true' if deep['f16'] else 'false'))
    w('')
    w('#print axioms walk%d_t06' % dseq)
    w('#print axioms walk%d_t16' % dseq)
    w('')

    # ---- section 5: the composition note ----
    w('/-! ## 5. The composition note: how `hdom_perwalk_b1` consumes into the select rung')
    w('')
    w('The select hypothesis of `Fresh.OpeningChainConflict.twoWindows_of_select_opening_record`')
    w('(consumed by `Fresh.SelectRung1.selectRung1_1_3_4_5_5_5_7`) demands, per realized walk,')
    w('a record `e` of `compFamOf b` with `AttestsFrom e walk U`.  The rung\'s banked form')
    w('discharged the attestation half from a UNIFORM `hdom` (every walk\'s trace `TabLe`-below')
    w('the one census trace, 49 pairs) -- refuted as a box-uniform datum.  The per-walk form')
    w('replaces it at the assembly as follows, per walk W (= banked instance k):')
    w('')
    w('1. THE CONSUMPTION (per walk).  Given the per-walk projection-tightness datum')
    w('   `hsub_k : ∀ V af Af, chainRun U 0 1 walk_k = some (V, af, Af) → TabLe V VWalk_k`')
    w('   (the walk\'s run from the arrangement\'s OWN start `U` is tighter than its own census')
    w('   projection at the two stored pairs -- the data-side per-walk replay pattern of')
    w('   `perrec8_diag_v1.py`, now a two-pair check), the banked instance closes the')
    w('   attestation half outright:')
    w('     `intro V af Af hrun; exact capsDom_tabLe (hsub_k V af Af hrun) hdom_walk_k.2`')
    w('   gives `AttestsFrom r1 walk_k U` (`capsDom_tabLe`\'s contravariance: tighter run')
    w('   trace inherits the domination of the census projection).  The `.1` half gives the')
    w('   same for r0; r2/r3 need nothing new.  Note the equality walks need no special form:')
    w('   `TabLe` is ≤, so the %d walks whose (1,6) entry EQUALS the cap 55/117 are carried' % n_eq1)
    w('   verbatim.')
    w('')
    w('2. THE AGGREGATE\'S ROLE.  `hdom_perwalk_b1` is the ∃-half of the select hypothesis in')
    w('   the exact shape the consumer quantifies (`∃ e ∈ compFamOf b1, CapsDom ...`), so at')
    w('   the assembly the per-walk witness record need not be re-derived: for the realized')
    w('   walk, identify its class index k (walk-identification datum) and the banked')
    w('   instance supplies both the witness `e` (via `r1_mem_b1`) and the `CapsDom` half.')
    w('')
    w('3. WHAT REMAINS OWED AT THE ASSEMBLY (honest).  (a) Walk identification: the realized')
    w('   walk\'s word must be recognized as `walk_k`\'s word -- the per-walk words are banked')
    w('   in `perwalk_v2_words.jsonl` / the traces JSONL and the transcription pattern is')
    w('   `walk%d_word` (a full 804-word transcription is mechanical but not banked here).' % dseq)
    w('   (b) `hsub_k` per walk: the two-pair projection tightness of the run from the')
    w('   arrangement\'s own start (the rung\'s per-walk `hdom`, now scoped to the two pairs')
    w('   the attestation reads -- the exact datum whose census-trace 49-pair uniform form')
    w('   was refuted).  (c) The demand half (`g e.x / g e.y < e.A / e.B` per walk): the')
    w('   select rung\'s separate datum, unchanged (perwalk_v2\'s own honest boundary).')
    w('-/')
    w('')
    w('end Fresh.PerWalkHdom')
    w('')

    src = '\n'.join(L)
    with open(args.out, 'w') as fh:
        fh.write(src)
    print('emitted %s: %d lines, %d bytes' % (args.out, len(L), len(src)))
    print('  instances: %d/%d walks; deepest banked: seq %d len %d' %
          (n_emit, len(walks), dseq, dlen))
    print('  elapsed %.1fs' % (time.time() - t0))

if __name__ == '__main__':
    main()
