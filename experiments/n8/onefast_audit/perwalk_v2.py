# perwalk_v2.py -- CHECKPOINTED per-walk attestation census for box b1 = ![1,3,4,5,5,5,7].
#
# The question (E893/E898's route-decider; perwalk_v1.py's question, unkillable this time):
#   for EACH of the 804 realized first-window walks W (from mkTab_1_3_4_5_5_5_7), does
#   there EXIST a record e in compFamOf b1 with CapsDom V_W e.y e.caps e.x,
# where V_W is W's OWN endpoint trace (the [T]-validated l_-mirror).
# 804/804 -> the per-walk datum completes the select route's hdom; any unattested walk
# -> the structural finding.  Banked context: 564/804 fail against the ONE census trace
# (TabLe, all 49 pairs); the open question is per-walk SOME-record attestation.
#
# Why v2 exists: perwalk_v1 died silently.  Post-mortem (established today, data-side):
#   (a) v1's parse_records anchors the record body at the first ']>' AFTER the def, but
#       each record's own caps close with ')]>' mid-list, so the body is truncated before
#       any complete record; the find-loop then spins forever (run4 hung there, 0 CPU
#       visible output; killed -> 562 flushed bytes).  FIXED here (anchor '\n  ]>').
#   (b) v1 line 229 reads _os.environ BEFORE 'import os as _os' at its line 242 -- a
#       NameError landmine that would crash any run that got past (a).
#   (c) v1's silent heavy phases: enumeration (~266s per selectoweda_v1.out), then the
#       w0chains2 cross-enum, then the fresh recompute of 804 traces (~53 min per v1's
#       own comment), then the prefix-trie pass (~another 53 min) -- all with no progress
#       output and no intermediate saves; stdout was block-buffered so kills left
#       0-byte logs (runs 1-3).  v2: EVERY phase streams + flushes per walk.
#
# Design (three checkpointed phases; each JSONL is append-only, flush per line, resumable
# per walk by word identity; the .out is rewritten after every phase so kills are safe):
#   Phase 1 (enumeration, checkpointed): selectoweda_v2's enumerate_walks2 re-implemented
#     as a GENERATOR with per-walk yields (verbatim traversal semantics: same r_feasible
#     gates, same l_step gate, same TEETH/no-repeat/maxdepth=95); streams each walk word
#     to perwalk_v2_words.jsonl; progress every 50 yields with elapsed/block timing;
#     DFS node + dead-step counters (v1 counted 1660 nodes / 0 dead with fineness).
#   Phase 2 (traces, checkpointed): per walk, the endpoint trace via run_word (the
#     l_-mirror from mkTab; independent of the DFS's carried state); asserts totality
#     (49 entries) and entrywise <= mkTab; computes TabLe-vs-census on the full trace
#     (banking the 564 cross-check per walk) and stores the trace-relevant pairs = the
#     records' cap pairs (mechanically derived, not hard-coded); streams to
#     perwalk_v2_traces.jsonl.  SKIPPED vs v1: the w0chains2 cross-enum (word-set
#     equality already [T]-banked, selectoweda_v2/E893) and the redundant DFS-carried
#     recompute VALIDATION ([T]-banked); this phase's run_word is the single
#     authoritative trace computation.
#   Phase 3 (the census): per walk, caps_dom against EVERY record of compFamOf b1
#     (4 records, parsed mechanically as in perwalk_v1 with the (a) fix); streams the
#     verdict to perwalk_v2_census.jsonl; aggregate: attested count, per-record carrier
#     distribution, attesting-set shapes, per-cap-condition carriers, endpoint value
#     distributions, and for any unattested walk the diagnostic (trace pairs, per-record
#     first-failure gaps, nearest record).
#
# REUSE (nothing reinvented): selectoweda_v1.py header verbatim (banked tables mkTab/
#   census/t1, the value-verbatim UClosureKill mirror l_*, the ratio-closure r_*, bounds,
#   dom_check); selectoweda_v2.py's enumerate_walks2 traversal semantics; perrec8_gen_v1.py
#   pre-main (DATA + CHOSEN for the record cross-check); perwalk_v1.py's parse_records/
#   parse_steps/caps_dom/frac_s/entry_lit with the (a) fix.  NO calls to w0chains2.
#
# Exact Fractions throughout; floats nowhere; floats steer never count.
# Usage: python3 -I perwalk_v2.py   (env: PERWALK_V2_BLOCK=50 progress interval;
#        PERWALK_V2_SMOKE=K stops Phase 1 after K yields, no complete marker -- smoke test)
import os, re, json, sys, time, signal
from fractions import Fraction as F

AUD = os.path.dirname(os.path.abspath(__file__))
N8 = os.path.dirname(AUD)
LEAN = '/Users/trentpalelei/Desktop/Math Ex/LonelyRunnerFresh/Fresh'
os.chdir(N8)

WORDS_PATH  = os.path.join(AUD, 'perwalk_v2_words.jsonl')
TRACES_PATH = os.path.join(AUD, 'perwalk_v2_traces.jsonl')
CENSUS_PATH = os.path.join(AUD, 'perwalk_v2_census.jsonl')
OUT_PATH    = os.path.join(AUD, 'perwalk_v2.out')

BLOCK = int(os.environ.get('PERWALK_V2_BLOCK', '50'))
SMOKE = int(os.environ.get('PERWALK_V2_SMOKE', '0'))   # 0 = full run

OUTLINES = []
def say(*args):
    s = ' '.join(str(a) for a in args)
    print(s, flush=True)                # flush per line: no more silent phases
    OUTLINES.append(s)

def flush_out():
    with open(OUT_PATH, 'w') as fh:
        fh.write('\n'.join(OUTLINES) + '\n')

def now():
    return time.perf_counter()

class Killed(Exception):
    pass
def _sigterm_handler(sig, frm):
    raise Killed('SIGTERM')
signal.signal(signal.SIGTERM, _sigterm_handler)

# ---- REUSE: selectoweda_v1.py header (tables + l_ mirror + r_ closure + bounds) ----
v1src = open(os.path.join(AUD, 'selectoweda_v1.py')).read()
exec(v1src.split('# ---- the DFS ----')[0])
LEAN = '/Users/trentpalelei/Desktop/Math Ex/LonelyRunnerFresh/Fresh'  # re-set: the exec'd header rebinds LEAN to a file path
# have: F, mkTab, census, t1, l_* mirror, n, faceLo/faceHi, r_add/r_feasible,
#       box_bounds/fineness_bounds/seam_bounds/base_bound, dom_check, parse_table

TEETH = [(F(8 * j - 1), F(8 * j + 1)) for j in range(1, 16)]

def run_word(word):
    U = [[mkTab[p][q] for q in range(7)] for p in range(7)]
    a, Aex = 0, F(1)
    for (b, A, B) in word:
        V = l_step(U, a, b, Aex, F(A), F(B))
        assert V is not None, ('step died', b, A, B)
        U = V; a, Aex = b, F(B)
    return U

def tables_equal(T1, T2):
    return all(T1[i][j] == T2[i][j] for i in range(7) for j in range(7))

# ---- Phase 1 enumerator: selectoweda_v2.py's enumerate_walks2, verbatim traversal ----
# ---- semantics, re-implemented as a generator with per-walk yields + counters.     ----
def iter_walks2(use_fineness=True, maxdepth=95, stats=None):
    if stats is None:
        stats = {'nodes': 0, 'dead': 0}
    base_sys = box_bounds() + (fineness_bounds() if use_fineness else [])
    def dfs(a, Aex, trace, bounds, walk):
        stats['nodes'] += 1
        if r_feasible(bounds + [base_bound(a, Aex)]):
            yield (tuple(walk), trace)
        if len(walk) >= maxdepth: return
        for b in range(1, 7):
            for ji in range(15):
                A, B = TEETH[ji]
                if (b, int(A)) in set(walk): continue
                newb = bounds + seam_bounds(a, Aex, b, A, B)
                if not r_feasible(newb): continue
                V = l_step(trace, a, b, Aex, A, B)
                if V is None:
                    stats['dead'] += 1
                    continue
                yield from dfs(b, B, V, newb, walk + [(b, int(A), int(B))])
    yield from dfs(0, F(1), mkTab, base_sys, [])

# ---- the family records, parsed mechanically from the banked Lean sources ----
# (perwalk_v1's parsers with the (a) fix: anchor the record list at '\n  ]>').
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
        j = src.find('\n  ]⟩', i)   # (a) FIX: ']'>' matches a record's own caps-close ')]>' mid-list
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
        ncaps = len(CAP_ENTRY.findall(m.group(5)))
        assert len(caps) == ncaps and len(caps) >= 1, (defname, 'caps parse', m.group(5))
        recs.append((x, y, A, B, caps))
    n_open = body.count('⟨')
    assert n_open == len(recs) + 1, (defname, 'record count', n_open, len(recs))
    return recs

STEP = re.compile(r'⟨\s*\(\s*(\d+)\s*:\s*Fin 7\s*\)\s*,\s*\(\s*(\d+)\s*:\s*ℚ\s*\)\s*,\s*\(\s*(\d+)\s*:\s*ℚ\s*\)\s*⟩')

def parse_steps(path, name):
    src = open(path).read()
    i = src.index('def %s : List Step' % name)
    j = src.index(']', i)
    return [(int(m.group(1)), int(m.group(2)), int(m.group(3)))
            for m in STEP.finditer(src[i:j])]

# ---- value-level CapsDom mirror (Fresh/CapChainsOfCarve.CapsDom.cons) over a getter ----
def caps_dom(get, y, caps):
    # get(p, q) -> (value, strict_flag) or None.  Returns (ok, first_failure)
    # failure = (prev, z, entry-or-None, cap); entry value must satisfy e[0] <= c.
    prev = y
    for (z, c) in caps:
        e = get(prev, z)
        if e is None or not (e[0] <= c):
            return (False, (prev, z, e, c))
        prev = z
    return (True, None)

def frac_s(x):
    return '%d/%d' % (x.numerator, x.denominator)

def entry_lit(e):
    if e is None:
        return 'none'
    return 'some ((%s : ℚ), %s)' % (frac_s(e[0]), 'true' if e[1] else 'false')

# ================= JSONL checkpoint helpers =================
def load_words(path):
    words, complete, meta = [], False, None
    if not os.path.exists(path):
        return words, complete, meta
    with open(path) as fh:
        for line in fh:
            line = line.strip()
            if not line:
                continue
            d = json.loads(line)
            if d.get('complete'):
                complete = True; meta = d
                continue
            words.append(tuple(tuple(s) for s in d['word']))
    seqs = [json.loads(l).get('seq') for l in open(path) if l.strip() and not json.loads(l).get('complete')]
    assert seqs == list(range(len(seqs))), 'words file seq not contiguous'
    assert len(words) == len(set(words)), 'duplicate words in words file'
    return words, complete, meta

def done_words(path):
    done = set()
    if not os.path.exists(path):
        return done
    with open(path) as fh:
        for line in fh:
            line = line.strip()
            if not line:
                continue
            d = json.loads(line)
            if d.get('complete'):
                continue
            done.add(tuple(tuple(s) for s in d['word']))
    return done

def load_jsonl(path):
    out = []
    if not os.path.exists(path):
        return out
    with open(path) as fh:
        for line in fh:
            line = line.strip()
            if not line:
                continue
            d = json.loads(line)
            if d.get('complete'):
                continue
            out.append(d)
    return out

# ================= Phase 0: sanity (cheap, seconds) =================
say('perwalk_v2 -- CHECKPOINTED per-walk attestation census for box (1,3,4,5,5,5,7)')
say('question: per realized walk W (from mkTab_1_3_4_5_5_5_7), exists e in compFamOf b1')
say('  with CapsDom V_W e.y e.caps e.x?  (V_W = W\'s own endpoint trace, l_-mirror)')
say('phases: 1 enumeration (generator, streamed+checkpointed) -> 2 traces (run_word,')
say('  streamed+checkpointed) -> 3 census (caps_dom per record, streamed+checkpointed).')
say('skipped vs v1: w0chains2 cross-enum ([T]-banked set equality), DFS-trace recompute')
say('  validation ([T]-banked); v1 landmines fixed: parse_records "]>" anchor, _os use')
say('  before import.  Exact Fractions; floats nowhere.')
say('')

t0 = now()
say('SANITY mirror==banked T8_1_3_4_5_5_5_7_1 :', tables_equal(run_word(((6, 7, 9),)), t1))
say('SANITY mirror==banked census T8_..._12  :',
    tables_equal(run_word(((6, 7, 9), (5, 7, 9), (3, 7, 9), (2, 7, 9), (1, 7, 9), (5, 15, 17),
                           (4, 15, 17), (3, 15, 17), (2, 15, 17), (5, 23, 25), (6, 31, 33),
                           (1, 15, 17), (3, 23, 25), (6, 39, 41))), census))

recs_c = parse_records(os.path.join(LEAN, 'ComposedFamData.lean'), 'compFam_1_3_4_5_5_5_7')
recs_d = parse_records(os.path.join(LEAN, 'DumpDomData.lean'), 'dumpFam_1_3_4_5_5_5_7')
say('records compFam_1_3_4_5_5_5_7 == dumpFam_1_3_4_5_5_5_7 (Lean control re-checked):', recs_c == recs_d)

# ---- REUSE: perrec8_gen_v1.py pre-main (DATA + CHOSEN only; w0chains2 NOT called) ----
p8src = open(os.path.join(AUD, 'perrec8_gen_v1.py')).read()
g8 = {'__file__': os.path.join(AUD, 'perrec8_gen_v1.py'), '__name__': 'perrec8reuse'}
exec(p8src.rsplit("if __name__ == '__main__':", 1)[0], g8)
data_norm = []
for (x, y, P, Q, cap) in g8['DATA'][0][2]:
    data_norm.append((x, y, P, Q, [(x, cap)]))
say('records == perrec8_gen_v1.DATA transcription:', recs_c == data_norm)
assert recs_c == recs_d == data_norm
RECS = recs_c

for k, (x, y, A, B, caps) in enumerate(RECS):
    end = y
    for (z, _) in caps: end = z
    assert end == x, (k, 'chainEnd', end, x)
say('records (x, y, A, B, caps [(z, cap)]), chainEnd y caps == x checked:')
for k, (x, y, A, B, caps) in enumerate(RECS):
    pairs = []
    prev = y
    for (z, _) in caps:
        pairs.append((prev, z)); prev = z
    say('  r%d: x=%d y=%d A=%d B=%d caps=%s  (demand %s/%s; cap pairs %s)' %
        (k, x, y, A, B, [(z, frac_s(c)) for (z, c) in caps], A, B, pairs))
say('  start-table entries at the cap pairs: mkTab[0][6] = %s (strict %s), mkTab[1][6] = %s (strict %s)' %
    (frac_s(mkTab[0][6][0]), mkTab[0][6][1], frac_s(mkTab[1][6][0]), frac_s(mkTab[1][6][1]) if mkTab[1][6] else 'none'))
say('  census-trace entries at the cap pairs: census[0][6] = %s (strict %s), census[1][6] = %s (strict %s)' %
    (frac_s(census[0][6][0]), census[0][6][1], frac_s(census[1][6][0]), census[1][6][1]))
say('  note: r1/r2/r3 share caps [(6, 55/117)] at y=1 -> CapsDom-identical conditions;')
say('        r0 is the distinct condition (6, 1870/13113) at y=0.')

# the trace-relevant pairs, derived mechanically from the records' cap pairs
PAIR_KEYS = []
for (x, y, A, B, caps) in RECS:
    prev = y
    for (z, _) in caps:
        if (prev, z) not in PAIR_KEYS:
            PAIR_KEYS.append((prev, z))
        prev = z
say('trace-relevant pairs (union of the records\' cap pairs):', PAIR_KEYS)

# the banked census word + its banked per-record attestations, re-verified data-side
banked_word = parse_steps(os.path.join(LEAN, 'ChainDomPerRecBox1.lean'), 'steps8_1_3_4_5_5_5_7')
chosen_word = tuple(g8['CHOSEN']['1_3_4_5_5_5_7'][1])
say('banked census word steps8_1_3_4_5_5_5_7: %d steps; == CHOSEN chain 0 first %d steps: %s' %
    (len(banked_word), len(banked_word), tuple(banked_word) == chosen_word[:len(banked_word)]))
census_trace = run_word(banked_word)
say('banked census word trace == banked census table (49 entries):', tables_equal(census_trace, census))
banked_att = [caps_dom(lambda p, q: census_trace[p][q], y, caps)[0] for (x, y, A, B, caps) in RECS]
say('capsDom(census trace, r_k) for k=0..3:', banked_att, ' (matches banked attests_1_3_4_5_5_5_7_r0..r3 [T])')
assert all(banked_att)
say('sanity done (%.1fs)' % (now() - t0))
flush_out()

CHOSEN_FULL = chosen_word   # the 18-step banked attesting word; must be in the 804 set

# ================= Phase 1: enumeration (checkpointed, streamed) =================
def phase1():
    t0 = now()
    words, complete, meta = load_words(WORDS_PATH)
    have = set(words)
    say('')
    say('[P1] enumeration start: mode=%s, %d walks already banked in %s' %
        ('complete-resume' if complete else ('partial-resume' if words else 'fresh'), len(have), os.path.basename(WORDS_PATH)))
    if complete:
        say('[P1] complete marker present (%s) -- skipping enumeration' % json.dumps(meta))
        say('[P1] enumeration skipped; banked %d walks (marker meta above)' % len(words))
        return words
    fh = open(WORDS_PATH, 'a')
    stats = {'nodes': 0, 'dead': 0}
    n = 0                      # yields seen this process (deterministic DFS order)
    order = []                 # yields in DFS pre-order (the canonical word order)
    first_t = None
    blk_t = now(); blk_n = 0
    interrupted = False
    try:
        for (w, _tr) in iter_walks2(True, stats=stats):
            n += 1
            order.append(w)
            if first_t is None:
                first_t = now() - t0
                say('[P1] first walk yielded at %.1fs (len %d): %s' % (first_t, len(w), list(w)))
            if SMOKE and n >= SMOKE:
                break
            if w in have:
                continue
            if len(have) != n - 1:
                raise AssertionError('words file is not a yield-prefix (seq %d vs %d banked) -- delete %s and rerun' %
                                     (n - 1, len(have), WORDS_PATH))
            have.add(w)
            fh.write(json.dumps({'seq': n - 1, 'len': len(w), 'word': [list(s) for s in w]}) + '\n')
            blk_n += 1
            if BLOCK and blk_n % BLOCK == 0:
                tn = now()
                say('[P1] %d yields | banked %d | elapsed %.1fs | block %.1fs (%.2fs/walk) | nodes %d dead %d | last len %d' %
                    (n, len(have), tn - t0, tn - blk_t, (tn - blk_t) / BLOCK, stats['nodes'], stats['dead'], len(w)))
                fh.flush()
                flush_out()
                blk_t = tn
    except Killed:
        interrupted = True
    except KeyboardInterrupt:
        interrupted = True
    fh.flush(); fh.close()
    el = now() - t0
    if interrupted:
        say('[P1] INTERRUPTED at %d yields (%d walks banked, %.1fs) -- progress saved; rerun to resume' % (n, len(have), el))
        flush_out()
        raise SystemExit(130)
    if SMOKE:
        say('[P1] SMOKE stop after %d yields (%d banked, %.1fs, nodes %d dead %d) -- no complete marker written' %
            (n, len(have), el, stats['nodes'], stats['dead']))
        flush_out()
        return order
    with open(WORDS_PATH, 'a') as fh2:
        fh2.write(json.dumps({'complete': True, 'count': len(have), 'nodes': stats['nodes'],
                              'dead': stats['dead'], 'elapsed_s': el,
                              'first_walk_s': first_t}) + '\n')
    say('[P1] enumeration done: %d distinct walks | DFS nodes %d (selectoweda_v1: 1660) | dead steps %d (v1: 0) | elapsed %.1fs | first walk at %.1fs' %
        (len(have), stats['nodes'], stats['dead'], el, first_t if first_t is not None else -1))
    assert len(have) == n, ('yield/bank mismatch', n, len(have))
    assert len(have) == 804, ('expected 804 walks', len(have))
    assert CHOSEN_FULL in have, 'banked 18-step census word not in the enumerated set'
    say('[P1] asserts: 804 distinct, banked 18-step census word in set -- OK')
    flush_out()
    return list(have)

# ================= Phase 2: traces (checkpointed, streamed) =================
def phase2(words):
    t0 = now()
    done = done_words(TRACES_PATH)
    say('')
    say('[P2] traces start: %d walks, %d already banked in %s; relevant pairs %s' %
        (len(words), len(done), os.path.basename(TRACES_PATH), PAIR_KEYS))
    fh = open(TRACES_PATH, 'a')
    blk_t = now(); blk_n = 0
    n = 0
    comp = 0                   # traces computed this process (for the ETA)
    interrupted = False
    try:
        for k, w in enumerate(words):
            n += 1
            if w in done:
                continue
            comp += 1
            V = run_word(w)
            for i in range(7):
                for j in range(7):
                    e = V[i][j]
                    assert e is not None, ('trace not total', w, i, j)
                    assert e[0] <= mkTab[i][j][0], ('trace loosened vs mkTab', w, i, j)
            bad = dom_check(V)
            pairs = {}
            for (p, q) in PAIR_KEYS:
                e = V[p][q]
                assert e is not None, ('relevant pair missing', w, p, q)
                pairs['%d,%d' % (p, q)] = [e[0].numerator, e[0].denominator, e[1]]
            fh.write(json.dumps({'seq': k, 'len': len(w), 'word': [list(s) for s in w],
                                 'pairs': pairs, 'tab_le_census': (len(bad) == 0),
                                 'n_bad_pairs': len(bad)}) + '\n')
            blk_n += 1
            if BLOCK and blk_n % BLOCK == 0:
                tn = now()
                el = tn - t0
                rem = (len(words) - n) * (el / max(comp, 1))
                say('[P2] %d/%d traces (%d computed here) | elapsed %.1fs | block %.1fs (%.2fs/walk) | ETA ~%.0fmin' %
                    (n, len(words), comp, el, tn - blk_t, (tn - blk_t) / BLOCK, rem / 60.0))
                fh.flush()
                flush_out()
                blk_t = tn
    except Killed:
        interrupted = True
    except KeyboardInterrupt:
        interrupted = True
    fh.flush(); fh.close()
    el = now() - t0
    if interrupted:
        say('[P2] INTERRUPTED at %d/%d (%.1fs) -- progress saved; rerun to resume' % (n, len(words), el))
        flush_out()
        raise SystemExit(130)
    if SMOKE:
        say('[P2] SMOKE stop: %d traces computed this process (%.1fs) -- no complete marker' % (n - len(done), el))
        flush_out()
        return
    with open(TRACES_PATH, 'a') as fh2:
        fh2.write(json.dumps({'complete': True, 'count': len(words), 'elapsed_s': el}) + '\n')
    say('[P2] traces done: %d computed this process (%d pre-banked) over %d walks | elapsed %.1fs | per-walk avg %.2fs' %
        (comp, len(done), len(words), el, el / max(comp, 1)))
    flush_out()

# ================= Phase 3: the census (checkpointed, streamed) =================
def phase3(words):
    t0 = now()
    traces = {}
    for d in load_jsonl(TRACES_PATH):
        traces[tuple(tuple(s) for s in d['word'])] = d
    done = done_words(CENSUS_PATH)
    say('')
    say('[P3] census start: %d walks, %d traces banked, %d verdicts already banked in %s' %
        (len(words), len(traces), len(done), os.path.basename(CENSUS_PATH)))
    fh = open(CENSUS_PATH, 'a')
    n = 0
    interrupted = False
    try:
        for k, w in enumerate(words):
            n += 1
            if w in done:
                continue
            tr = traces.get(w)
            assert tr is not None, ('no trace for walk', w)
            pairs = {}
            for key, v in tr['pairs'].items():
                p, q = key.split(',')
                pairs[(int(p), int(q))] = (F(v[0], v[1]), v[2])
            get = lambda p, q: pairs.get((p, q))
            att = []
            fails = []
            for rk, (x, y, A, B, caps) in enumerate(RECS):
                ok, badf = caps_dom(get, y, caps)
                if ok:
                    att.append(rk)
                else:
                    fails.append((rk, badf))
            line = {'seq': k, 'len': len(w), 'word': [list(s) for s in w],
                    'attests': att, 'tab_le_census': tr['tab_le_census']}
            if not att:
                gaps = []
                for (rk, (prev, z, e, c)) in fails:
                    gaps.append({'rec': rk, 'pair': [prev, z],
                                 'entry': None if e is None else [e[0].numerator, e[0].denominator],
                                 'cap': [c.numerator, c.denominator],
                                 'excess': None if e is None else [(e[0] - c).numerator, (e[0] - c).denominator]})
                finite = [g for g in gaps if g['excess'] is not None]
                nearest = min(finite, key=lambda g: F(g['excess'][0], g['excess'][1]))['rec'] if finite else None
                line['diag'] = {'gaps': gaps, 'nearest_record': nearest}
            fh.write(json.dumps(line) + '\n')
            if BLOCK and (n % BLOCK == 0):
                fh.flush()
    except Killed:
        interrupted = True
    except KeyboardInterrupt:
        interrupted = True
    fh.flush(); fh.close()
    el = now() - t0
    if interrupted:
        say('[P3] INTERRUPTED at %d/%d (%.1fs) -- progress saved; rerun to resume' % (n, len(words), el))
        flush_out()
        raise SystemExit(130)
    say('[P3] census pass done (%.1fs)' % el)
    flush_out()

def aggregate(words):
    wset = set(words)
    lines = [d for d in load_jsonl(CENSUS_PATH) if tuple(tuple(s) for s in d['word']) in wset]
    assert len(lines) == len(words), ('census lines != walks', len(lines), len(words))
    from collections import Counter
    carrier = Counter()
    cond_carrier = Counter()
    attshapes = Counter()
    tabfails = 0
    natt = 0
    unatt = []
    vals = {}      # distinct cap condition (pair, cap) -> Counter of trace entry values
    for d in lines:
        w = tuple(tuple(s) for s in d['word'])
        att = d['attests']
        if att:
            natt += 1
        else:
            unatt.append(d)
        for rk in att:
            carrier[rk] += 1
        attshapes[tuple(att)] += 1
        if not d['tab_le_census']:
            tabfails += 1
        seen_cond = set()
        tr = traces_by_word[w]
        for rk, (x, y, A, B, caps) in enumerate(RECS):
            if rk not in att:
                continue
            prev = y
            for (z, c) in caps:
                cond = ((prev, z), c)
                if cond not in seen_cond:
                    seen_cond.add(cond)
                    cond_carrier[cond] += 1
                    vals.setdefault(cond, Counter())[F(*tr['pairs']['%d,%d' % (prev, z)][:2])] += 1
                prev = z
    say('')
    say('================ AGGREGATE %s ================' % ('(SMOKE partial set -- not the census verdict)' if SMOKE else ''))
    say('VERDICT: %d/%d walks attested (each by >=1 family record)' % (natt, len(lines)))
    say('per-record carrier distribution: ' + ', '.join('r%d: %d' % (k, carrier.get(k, 0)) for k in range(len(RECS))))
    say('attesting-record-set shapes: ' + '; '.join('%dx%s' % (c, list(s)) for s, c in sorted(attshapes.items(), key=lambda kv: -kv[1])))
    say('distinct cap-condition carriers (walks satisfying each DISTINCT (pair, cap) condition):')
    for ((pair, c), cnt) in sorted(cond_carrier.items(), key=lambda kv: str(kv[0])):
        say('  pair (%d,%d) cap %s : %d walks' % (pair[0], pair[1], frac_s(c), cnt))
    say('TabLe-vs-census fails over the 804 OWN traces (banked cross-check, expect 564):', tabfails)
    say('')
    say('endpoint value structure per distinct cap condition:')
    for ((pair, c), cnts) in sorted(vals.items(), key=lambda kv: str(kv[0])):
        mx = max(cnts)
        mn = min(cnts)
        say('  (%d,%d) cap %s: %d distinct entries; min %s; max %s; walks at max %d; attained-with-equality %d' %
            (pair[0], pair[1], frac_s(c), len(cnts), frac_s(mn), frac_s(mx), cnts[mx], cnts.get(c, 0)))
    say('')
    if unatt:
        say('UNATTESTED WALKS: %d (walks attesting NO record) -- diagnostics:' % len(unatt))
        shown = 0
        for d in unatt:
            if shown >= 10:
                say('  ... (%d more; see perwalk_v2_census.jsonl "diag" fields)' % (len(unatt) - shown))
                break
            shown += 1
            tr = traces_by_word[tuple(tuple(s) for s in d['word'])]
            say('  FAIL walk (len %d): %s' % (d['len'], d['word']))
            for key in sorted(tr['pairs']):
                v = tr['pairs'][key]
                say('    trace (%s) = some ((%d/%d : ℚ), %s)' % (key, v[0], v[1], 'true' if v[2] else 'false'))
            for g in d['diag']['gaps']:
                ex = 'none' if g['excess'] is None else frac_s(F(g['excess'][0], g['excess'][1]))
                say('    r%d first-failure at pair %s: entry %s vs cap %s (excess %s)' %
                    (g['rec'], g['pair'], g['entry'], g['cap'], ex))
            say('    nearest record (min excess): r%s' % d['diag']['nearest_record'])
    else:
        say('UNATTESTED WALKS: none -- no diagnostics needed.')
    say('')
    say('honest boundary: settles ONLY the CapsDom half of per-walk attestation on the')
    say('  verified l_-mirror; the demand half (g e.x/g e.y < e.A/e.B per walk) is the')
    say('  select rung\'s separate datum and is NOT checked here (same boundary as v1).')
    say('banking input: perwalk_v2_census.jsonl (word -> attesting record indices) +')
    say('  perwalk_v2_traces.jsonl (the relevant pair literals per walk).')
    flush_out()

traces_by_word = {}

# ================= main =================
def main():
    words = phase1()
    # require completeness before the expensive phases unless smoke
    if not SMOKE:
        _, complete, meta = load_words(WORDS_PATH)
        assert complete and len(words) == 804, 'Phase 1 not complete -- refusing to proceed (rerun to resume)'
    phase2(words)
    for d in load_jsonl(TRACES_PATH):
        traces_by_word[tuple(tuple(s) for s in d['word'])] = d
    phase3(words)
    aggregate(words)
    say('')
    say('outputs: %s, %s, %s, %s' % (os.path.basename(WORDS_PATH), os.path.basename(TRACES_PATH),
                                      os.path.basename(CENSUS_PATH), os.path.basename(OUT_PATH)))
    flush_out()

try:
    main()
except SystemExit as e:
    if e.code not in (0, 130):
        raise
    raise
except AssertionError as e:
    say('ASSERTION FAILED:', e)
    flush_out()
    raise
