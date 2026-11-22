# m4fix_gen_v1.py -- C3-box per-box Lean generator: emits
# (DELTA-DERIVED from m4fix_gen_v1.py, value-verbatim machinery: the global
# m4fix_/M4FixRung2_ -> m4fix_/M4FixRung2_ family rename, the constructed-record
# lzones cross-check instead of the MechDataBatch parse, and the extra import of the
# mini-bank Fresh.M4FixResBank_v1.  See DELTA markers and m4fix_delta_log.txt.)
# Fresh/M4FixRung_<box>.lean transcribing the box's WHOLE certificate forest
# (reconstructed by m4fix_recon_v1.py, [T]-verified against both checkpoints and the
# CONSTRUCTED C3 record) as literal DfsCert data.
#
# Generalizations over m4rung1_gen_v1.py (which transcribed ONE crown subtree of ONE box):
#   * the WHOLE forest (all start-zone roots and all nodes, kinds internal/reach/deadend),
#     not just a crown -- for small boxes this discharges transcription OWED (c) data-side;
#   * internal nodes with ANY number of children (rung 1: exactly 2), including the
#     single-child path chains the small trees are made of;
#   * per-edge step proofs with an INTERMEDIATE propagated table (rung 1 asserted add1
#     always lands on the child table; in general add1 can keep-cur or propagate to an
#     intermediate table, which is then emitted with its own 49 cell lemmas);
#   * SEAM2 seam kills whose first uAdd PROPAGATES (rung 1 asserted all SEAM2 keep-cur);
#   * reach-less forests (PruneDom provable outright, no per-leaf hypotheses);
#   * the composed theorems consume the GENERIC data connection
#     (Fresh.M4Cert.m4CertSound_of_data / m4boxClear_of_data) + a locally emitted
#     hn17_<box>, because M4CertSound carries per-box m4cert_/hn17_ instances only for
#     box (1,4,6,7,10,16,16).
# Every emitted arithmetic fact is re-verified here in exact Fraction arithmetic before
# emission; any mismatch aborts.  python3 -I.
import json, os, sys, math
from fractions import Fraction as F

HERE = os.path.dirname(os.path.abspath(__file__))

# ---------- verbatim machinery (j2_admit_cert_v2.py / m4rung1_gen_v1.py) ----------
def add(U, i, j, c, s):
    cur = U[i][j]
    if cur is not None and (cur[0] < c or (cur[0] == c and (cur[1] or not s))): return U
    back = U[j][i]
    if back is not None:
        pr = back[0] * c
        if pr < 1 or (pr == 1 and (s or back[1])): return None
    V = [row[:] for row in U]
    for p in range(7):
        a = U[p][i]
        if a is None: continue
        for q in range(7):
            b = U[j][q]
            if b is None: continue
            v = a[0] * c * b[0]; st = a[1] or s or b[1]
            w = V[p][q]
            if w is None or v < w[0] or (v == w[0] and st and not w[1]): V[p][q] = (v, st)
    return V
def gt(U, A, a, B, b):
    if A > 0 and B <= 0: return U
    if A <= 0 and B > 0: return None
    if A == 0: return U if B < 0 else None
    if B == 0: return U if A > 0 else None
    if A > 0: return add(U, a, b, F(A, B), True)
    return add(U, b, a, F(-B, -A), True)
def dfs_hi(U, T, r):
    n = (1,) + tuple(T)
    if r == 0: return F(2 * n[0] + 1)
    hi = F(2 * n[r] + 1, 2)
    c = U[r][0]
    if c is not None: hi = min(hi, c[0])
    return hi
def dfs_lo(U, T, r):
    n = (1,) + tuple(T)
    if r == 0: return F(1)
    lo = max(F(2 * n[r] - 1, 2), F(1))
    c = U[0][r]
    if c is not None: lo = max(lo, 1 / c[0])
    return lo
def uKeepCur(U, i, j, c, s):
    cur = U[i][j]
    if cur is None: return False
    cc, ss = cur
    return cc < c or (cc == c and (ss or not s))
def uBack(U, i, j, c, s):
    back = U[j][i]
    if back is None: return False
    d, t = back
    return d * c < 1 or (d * c == 1 and (s or t))
def uAdd(U, i, j, c, s):
    if uKeepCur(U, i, j, c, s): return U
    if uBack(U, i, j, c, s): return None
    return add(U, i, j, c, s)

def parse_tab(tj):
    return [[None if x is None else (F(x[0]), x[1]) for x in row] for row in tj]

def q(x):
    f = F(x)
    return f"{f.numerator} / {f.denominator}" if f.denominator != 1 else f"{f.numerator}"

def qform(j, off):   # the (8j+off : Nat -> Q) cast form, so kill lemmas match the goal syntactically
    return f"(((8 * {j} {'-' if off < 0 else '+'} {abs(off)} : ℕ) : ℚ))"

def lean_table(name, U, doc):
    lines = [f"/-- {doc}  Transcribed verbatim from the box's reconstructed certificate tree;",
             "exact rationals, strict flags; `none` = unbounded. -/", "-- STANDING: DATA"]
    lines.append(f"def {name} : UTable := fun p q =>")
    first = True
    for i in range(7):
        for j in range(7):
            cc = U[i][j]
            if cc is None: continue
            cond = f"p = ({i} : Fin 7) ∧ q = ({j} : Fin 7)"
            kw = "if" if first else "else if"
            lines.append(f"  {kw} {cond} then some (({q(cc[0])} : ℚ), {str(bool(cc[1])).lower()})")
            first = False
    lines.append("  else none")
    return "\n".join(lines)

def cell_lemmas(name, U):
    out = []
    for i in range(7):
        for j in range(7):
            cc = U[i][j]
            if cc is None:
                out.append(f"theorem {name}_c_{i}_{j} : {name} ({i} : Fin 7) ({j} : Fin 7) = none := rfl")
            else:
                out.append(f"theorem {name}_c_{i}_{j} : {name} ({i} : Fin 7) ({j} : Fin 7) = "
                           f"some (({q(cc[0])} : ℚ), {str(bool(cc[1])).lower()}) := rfl")
    return "\n".join(out)

# ---------- reach_utc verdict layer (experiments/n8/reachutc_<box>.json transcription) ----------
# Added 2026-11-21 (m4fix_gen_v2 behaviour, same file): transcribes the per-prune-leaf
# `reach_utc` verdicts into the rung files, turning the identity OWED (b) stubs
# (`m4fix_<box>_pruneDom_<id> := h`) into VERDICT-CARRYING instances.  Per leaf the file
# now emits: the explored (frontier-sup, dump-rank) state set and pmax as literal data, the
# verdict theorem `verdictNoCompl_<l>` (every state of the explored set fails the verbatim
# `m4comp_lib_v1.reach_utc` completing test -- discharged HERE by literal per-case proofs
# over the census windows), the OWED projection instance `reachutcProj_<box>_<l>` (the [P]
# state-graph projection, being proved in parallel in Fresh/ReachUtcProof.lean), and the
# theorem `m4fix_<box>_pruneDom_<l> (hproj : reachutcProj_...) : DfsPruneDom tree_<l>`.
# The composed theorems consume the instances (hypotheses hproj_<l> instead of raw
# DfsPruneDom).  Refutation architecture (all shapes compiled and axiom-checked):
#   * the census window per Lean rank b is p-independent ({Jmin_b .. Jfam_b}, <= 2 values:
#     x > 7 needs j >= Jmin_b, the zone family (entry < 7) needs j <= Jfam_b) -- shared
#     `window_<b>` lemmas per box;
#   * `censusClass_<s>_<b>`: any census-window zone either fails the window condition
#     7*(8j-1) < p*(8j+1) (table-independent -- closed norm_num verdict per window value),
#     or is one of the hw-passing candidates listed per (state, rank) (48 over all 38
#     boxes); a table-level completing test implies the census one (dfsHi <= censHi,
#     dfsLo >= censLo -- monotonicity helpers), so the census verdict kills it;
#   * the hw-passing candidates are killed at the TABLE level per leaf (`tblKill_*`: the
#     leaf's own tightened ranges make the family/entry/exit side fail on the leaf's
#     cells); states with NO hw-passing candidate get the shared U-quantified
#     `stateNoCompl_<s>` (hypothesis: dfsHi positive at the tooth ranks -- `hiPos_<l>`).
# Every emitted arithmetic fact is re-verified here in exact Fraction arithmetic before
# emission; any dump-record vs tree-mirror mismatch aborts with a FINDINGS line.

def utc_analyze(t7, leaves):
    # distinct states (first-appearance order), census windows, hw-pass sets, clean p's
    states = {}
    for r in leaves:
        for s in r['explored_states']:
            if (s[0], s[1]) not in states:
                states[(s[0], s[1])] = len(states)
    windows = {}
    for k in range(1, 7):
        n = t7[k]
        lo = F(2 * n - 1, 2); hi = F(2 * n + 1, 2)
        jmin = 1
        while F(8 * jmin + 1) / lo <= 7: jmin += 1
        jfam = 1
        while F(8 * (jfam + 1) - 1) < 7 * hi: jfam += 1
        windows[k] = list(range(jmin, jfam + 1))
    hwpass = {}
    for (p, r) in states:
        pf = F(p)
        for k in range(1, 7):
            js = [j for j in windows[k] if 7 * (8 * j - 1) < pf * (8 * j + 1)]
            if js: hwpass[(p, k)] = js
    clean_p = set(p for (p, r) in states) - set(p for (p, k) in hwpass)
    return states, windows, hwpass, clean_p

def utc_check_leaf(r, tree_row, nodes=None):
    # dump record vs tree mirror consistency (the stub-matching audit)
    st = r['state']
    nid = r['node_id']
    assert r['kind'] == 'reach' and tree_row['kind'] == 'reach', (nid, 'kind')
    assert r['verdict'] == 'no_completing_state_reachable', (nid, r['verdict'])
    assert r['completing_transitions'] == [], (nid, 'nonempty completing transitions')
    assert st['a_lean'] == tree_row['a'] and st['Aex'] == tree_row['Aex'] and \
        st['P'] == tree_row['P'], \
        ('FINDING: dump record does not match its stub/tree mirror at leaf', nid,
         st, (tree_row['a'], tree_row['Aex'], tree_row['P']))
    assert st['rank'] == st['a_lean'] + 1, (nid, 'rank convention')
    assert r['nst'] == len(r['explored_states']), (nid, 'nst')
    assert F(r['pmax']) == max(F(s[0]) for s in r['explored_states']), (nid, 'pmax')
    assert r['explored_states'][0] == [tree_row['P'], st['rank']], (nid, 'initial state')

def utc_emit_census(w, BOXL, t7, windows):
    w('/-- The box census hi of tooth Lean rank `b`: the box tuple\'s own `(2n_b+1)/2` range,')
    w('the coarsest range the tightened `dfsHi` can only shrink. -/')
    w('-- STANDING: DATA')
    w('def censHi (b : Fin 7) : ℚ := ((2 * (boxN %s) b + 1 : ℤ) : ℚ) / 2' % BOXL)
    w('')
    w('/-- The box census lo of tooth Lean rank `b`: `(2n_b−1)/2` (and ≥ 1), the coarsest')
    w('range the tightened `dfsLo` can only grow beyond. -/')
    w('-- STANDING: DATA')
    w('def censLo (b : Fin 7) : ℚ := ((2 * (boxN %s) b - 1 : ℤ) : ℚ) / 2' % BOXL)
    w('')
    w('theorem hn1 : ∀ i : Fin 7, 1 ≤ boxN %s i := by' % BOXL)
    w('  intro i')
    w('  fin_cases i <;> simp [boxN, %s] <;> norm_num' % BOXL)
    w('')
    w('theorem boxpos (b : Fin 7) : 0 < 2 * boxN %s b + 1 :=' % BOXL)
    w('  by have := hn1 b; omega')
    w('')
    w('/-- The two monotonicity facts that let a table-level `reach_utc` completing test be')
    w('refuted at the census level: the tightened `dfsHi` never exceeds the census hi, the')
    w('tightened `dfsLo` never goes below the census lo. -/')
    w('theorem dfsHi_le_cens {U : UTable} {b : Fin 7} (hb : 0 < b.val) :')
    w('    dfsHi (boxN %s) U b ≤ censHi b := by' % BOXL)
    w('  unfold dfsHi censHi')
    w('  rw [if_pos hb]')
    w('  split')
    w('  · exact min_le_left _ _')
    w('  · exact le_refl _')
    w('')
    w('theorem dfsLo_ge_cens {U : UTable} {b : Fin 7} (hb : 0 < b.val) :')
    w('    censLo b ≤ dfsLo (boxN %s) U b := by' % BOXL)
    w('  unfold dfsLo censLo')
    w('  rw [if_pos hb]')
    w('  split')
    w('  · exact le_trans (le_max_left _ _) (le_max_left _ _)')
    w('  · exact le_max_left _ _')
    w('')
    w('theorem dfsLo_pos {U : UTable} {b : Fin 7} (hb : 0 < b.val) :')
    w('    0 < dfsLo (boxN %s) U b := by' % BOXL)
    w('  have h1 : (1:ℚ) ≤ dfsLo (boxN %s) U b := by' % BOXL)
    w('    unfold dfsLo')
    w('    rw [if_pos hb]')
    w('    split')
    w('    · exact le_trans (le_max_right _ _) (le_max_left _ _)')
    w('    · exact le_max_right _ _')
    w('  exact lt_of_lt_of_le (by norm_num) h1')
    w('')
    w('/-- The `reach_utc` completing-transition predicate at the state `(p, r)` (`r` the')
    w('dump rank, 1-indexed so the base row is 1): some tooth rank `b` (Lean `Fin 7` index')
    w('≥ 1, so dump rank `b.val + 1 ≠ r`) has a zone `8j−1, 8j+1` of its tightened family')
    w('(entry `e = (8j−1)/hi_b` below 7 -- the family bound), with `e < p`, exit')
    w('`x = (8j+1)/lo_b > 7`, and the window condition `7·(8j−1) < p·(8j+1)`.  Verbatim')
    w('`m4comp_lib_v1.reach_utc`\'s completing test over the node\'s `dfsHi`/`dfsLo` ranges;')
    w('the `[P]` projection side (realized chain → completing state reachable) is the')
    w('parallel `Fresh/ReachUtcProof.lean`. -/')
    w('-- STANDING: DEFINITION')
    w('def utcCompleting (U : UTable) (p : ℚ) (r : ℕ) : Prop :=')
    w('  ∃ b : Fin 7, 1 ≤ b.val ∧ b.val + 1 ≠ r ∧ ∃ j : ℕ, 1 ≤ j ∧')
    w('    ((8 * j - 1 : ℕ) : ℚ) / dfsHi (boxN %s) U b < 7 ∧' % BOXL)
    w('    ((8 * j - 1 : ℕ) : ℚ) / dfsHi (boxN %s) U b < p ∧' % BOXL)
    w('    ((8 * j + 1 : ℕ) : ℚ) / dfsLo (boxN %s) U b > 7 ∧' % BOXL)
    w('    (7 : ℚ) * ((8 * j - 1 : ℕ) : ℚ) < p * ((8 * j + 1 : ℕ) : ℚ)')
    w('')
    w('theorem censFam_of {U : UTable} {b : Fin 7} {j : ℕ} (hb : 0 < b.val)')
    w('    (hpos : 0 < dfsHi (boxN %s) U b)' % BOXL)
    w('    (hf : ((8 * j - 1 : ℕ) : ℚ) / dfsHi (boxN %s) U b < 7) :' % BOXL)
    w('    ((8 * j - 1 : ℕ) : ℚ) / censHi b < 7 := by')
    w('  have h1 : dfsHi (boxN %s) U b ≤ censHi b := dfsHi_le_cens hb' % BOXL)
    w('  have h2 : ((8 * j - 1 : ℕ) : ℚ) < (7:ℚ) * dfsHi (boxN %s) U b :=' % BOXL)
    w('    (div_lt_iff₀ hpos).mp hf')
    w('  have hc : 0 < censHi b := by')
    w('    unfold censHi')
    w('    exact div_pos (by exact_mod_cast boxpos b) (by norm_num)')
    w('  have h3 : ((8 * j - 1 : ℕ) : ℚ) < (7:ℚ) * censHi b := by')
    w('    have h4 : (7:ℚ) * dfsHi (boxN %s) U b ≤ (7:ℚ) * censHi b :=' % BOXL)
    w('      mul_le_mul_of_nonneg_left h1 (by norm_num)')
    w('    linarith')
    w('  exact (div_lt_iff₀ hc).mpr h3')
    w('')
    w('theorem censX_of {U : UTable} {b : Fin 7} {j : ℕ} (hb : 0 < b.val)')
    w('    (hx : ((8 * j + 1 : ℕ) : ℚ) / dfsLo (boxN %s) U b > 7) :' % BOXL)
    w('    ((8 * j + 1 : ℕ) : ℚ) / censLo b > 7 := by')
    w('  have h1 : censLo b ≤ dfsLo (boxN %s) U b := dfsLo_ge_cens hb' % BOXL)
    w('  have hpos : 0 < dfsLo (boxN %s) U b := dfsLo_pos hb' % BOXL)
    w('  have hCL : 0 < censLo b := by')
    w('    unfold censLo')
    w('    have hp : (0:ℤ) < 2 * boxN %s b - 1 := by have := hn1 b; omega' % BOXL)
    w('    exact div_pos (by exact_mod_cast hp) (by norm_num)')
    w('  have h2 : (7:ℚ) * dfsLo (boxN %s) U b < ((8 * j + 1 : ℕ) : ℚ) :=' % BOXL)
    w('    (lt_div_iff₀ hpos).mp (gt_iff_lt.mp hx)')
    w('  have h3 : (7:ℚ) * censLo b < ((8 * j + 1 : ℕ) : ℚ) := by')
    w('    have h4 : (7:ℚ) * censLo b ≤ (7:ℚ) * dfsLo (boxN %s) U b :=' % BOXL)
    w('      mul_le_mul_of_nonneg_left h1 (by norm_num)')
    w('    linarith')
    w('  exact (lt_div_iff₀ hCL).mpr h3')
    w('')
    w('/-- The census candidate window at Lean rank `b.val = k`: any `j` whose zone is in')
    w('the census family (entry below 7) and exits beyond 7 lies in the window (0, 1 or 2')
    w('values; the bounds are census constants, independent of the state). -/')
    for k in range(1, 7):
        n = t7[k]
        wn = windows[k]
        conc = 'False' if not wn else ' ∨ '.join('j = %d' % j for j in wn)
        c7 = 7 * (2 * n - 1)
        w('theorem window_%d {j : ℕ}' % k)
        w('    (hf : ((8 * j - 1 : ℕ) : ℚ) / censHi ((%d : Fin 7)) < 7)' % k)
        w('    (hx : ((8 * j + 1 : ℕ) : ℚ) / censLo ((%d : Fin 7)) > 7) :' % k)
        w('    %s := by' % conc)
        w('  simp only [censHi, censLo, boxN, %s] at hf hx' % BOXL)
        w('  have h1 : ((8 * j - 1 : ℕ) : ℚ) * 2 < (%d : ℚ) := by' % (7 * (2 * n + 1)))
        w('    rw [div_lt_iff₀ (by norm_num)] at hf')
        w('    norm_num at hf')
        w('    linarith')
        w('  have h3 : ((8 * j - 1 : ℕ) : ℤ) * 2 < %d := by exact_mod_cast h1' % (7 * (2 * n + 1)))
        w('  have h4 : ((%d : ℤ)) < ((8 * j + 1 : ℕ) : ℤ) * 2 := by' % c7)
        w('    have hx2 : (7:ℚ) * (((2 * %d - 1 : ℤ) : ℚ) / 2) < ((8 * j + 1 : ℕ) : ℚ) :=' % n)
        w('      (lt_div_iff₀ (by norm_num)).mp hx')
        w('    norm_num at hx2')
        w('    have h6 : (8 * (j : ℚ) + 1) * 2 > (%d : ℚ) := by linarith' % c7)
        w('    exact_mod_cast h6')
        w('  omega')
        w('')

def utc_emit_classes(w, states, windows, hwpass):
    for (ps, rs), pi in states.items():
        for k in range(1, 7):
            js = hwpass.get((ps, k), [])
            right = 'False' if not js else ' ∨ '.join('j = %d' % j for j in js)
            w('/-- The census hw-verdict at Lean rank %d (dump rank %d) for frontier-sup' % (k, k + 1))
            w('`p = %s`: any census-window zone either fails the window condition, or is one' % q(ps))
            w('of the listed hw-passing candidates (killed at the table level per leaf). -/')
            w('-- STANDING: DATA')
            w('theorem censusClass_%d_%d (j : ℕ)' % (pi, k))
            w('    (hf : ((8 * j - 1 : ℕ) : ℚ) / censHi ((%d : Fin 7)) < 7)' % k)
            w('    (hx : ((8 * j + 1 : ℕ) : ℚ) / censLo ((%d : Fin 7)) > 7) :' % k)
            w('    ¬ ((7:ℚ) * ((8 * j - 1 : ℕ) : ℚ) < (%s : ℚ) * ((8 * j + 1 : ℕ) : ℚ)) ∨ %s := by'
              % (q(ps), right))
            wn = windows[k]
            if not wn:
                w('  exact (window_%d hf hx).elim' % k)
            elif len(wn) == 1:
                w('  rcases window_%d hf hx with rfl' % k)
                w('  exact Or.inr rfl' if js else '  exact Or.inl (by norm_num)')
            else:
                w('  rcases window_%d hf hx with rfl | rfl' % k)
                for j in wn:
                    if j in js:
                        idx = js.index(j)
                        w('  · exact Or.inr rfl' if len(js) == 1 else
                          '  · exact Or.inr (%s rfl)' % ('Or.inl' if idx == 0 else 'Or.inr'))
                    else:
                        w('  · exact Or.inl (by norm_num)')
            w('')

def utc_emit_state_lemmas(w, states, clean_p, BOXL, hwpass):
    for (ps, rs), pi in states.items():
        if ps in clean_p:
            w('/-- The per-state no-completing lemma at state (p, r) = (%s, %s): no table' % (q(ps), rs))
            w('(with positive tightened `dfsHi` at the tooth ranks) admits a `reach_utc`')
            w('completing transition at this state -- the census hw-verdicts kill every rank.')
            w('Shared by every leaf whose explored set contains this state. -/')
            w('theorem stateNoCompl_%d {U : UTable}' % pi)
            w('    (hpos : ∀ b : Fin 7, 0 < b.val → 0 < dfsHi (boxN %s) U b) :' % BOXL)
            w('    ¬ utcCompleting U (%s : ℚ) %d := by' % (q(ps), rs))
            w('  rintro ⟨b, hb, hbr, j, hj, hfam, he, hx, hw⟩')
            w('  fin_cases b')
            w('  · simp at hb')
            for k in range(1, 7):
                w('  · rcases censusClass_%d_%d j' % (pi, k))
                w('      (censFam_of hb (hpos (%d : Fin 7) (by simp)) hfam) (censX_of hb hx)' % k)
                w('    with h | h')
                w('    · exact h hw')
                w('    · exact h')
            w('')
            w('#print axioms stateNoCompl_%d' % pi)
            w('')

def utc_leaf_kills(r, t7, U):
    # per (state, k, j) hw-passing candidate of THIS leaf + the python-side kill check on
    # the leaf's own tightened ranges (verbatim tranges); returns [(state, k, j)]
    R = []
    for y in range(1, 7):
        lo = max(F(2 * t7[y - 1] - 1, 2), F(1))
        hi = F(2 * t7[y - 1] + 1, 2)
        if U[0][y] is not None: lo = max(lo, 1 / U[0][y][0])
        if U[y][0] is not None: hi = min(hi, U[y][0][0])
        R.append((lo, hi))
    kills = []
    for s in r['explored_states']:
        pf = F(s[0])
        for k in range(1, 7):
            if s[1] == k + 1:
                continue   # b == r: excluded by utcCompleting's own guard, killed by hbr
            for j in utc_cur_hwpass.get((s[0], k), []):
                A, B = 8 * j - 1, 8 * j + 1
                lo, hi = R[k - 1]
                assert not (F(A) / hi < F(7) and F(A) / hi < pf and F(B) / lo > F(7)), \
                    ('leaf %d state %s k %d j %d: table-level completing test PASSES' %
                     (r['node_id'], s, k, j))
                kills.append((s, k, j))
    return kills

utc_cur_hwpass = {}

def utc_emit_leaf_block(w, r, t_row, f_node, t7, states, clean_p, BOXL, boxname,
                        leaf_tables):
    # leaf_tables=True: emit tbl/cells/node/tree (leaf-only mode); False: they exist already
    nid = r['node_id']
    utc_check_leaf(r, t_row)
    U = parse_tab(t_row['U'])
    a, Aex, P = t_row['a'], F(t_row['Aex']), F(t_row['P'])
    st = r['state']
    assert st['a_lean'] == a and st['Aex'] == t_row['Aex'] and st['P'] == t_row['P']
    if leaf_tables:
        w(lean_table('tbl%d' % nid, U,
                     'Table of DFS node %d (reach-prune leaf, last reading rank %d, exit'
                     ' numerator %s, frontier sup %s), from the tree mirror.'
                     % (nid, a, q(Aex), q(P))))
        w('')
        for k in range(1, 7):
            cc = U[k][0]
            if cc is None:
                w('theorem tbl%d_c_%d_0 : tbl%d (%d : Fin 7) (0 : Fin 7) = none := rfl' % (nid, k, nid, k))
            else:
                w('theorem tbl%d_c_%d_0 : tbl%d (%d : Fin 7) (0 : Fin 7) = some ((%s : ℚ), %s) := rfl'
                  % (nid, k, nid, k, q(cc[0]), str(bool(cc[1])).lower()))
        for k in range(1, 7):
            cc = U[0][k]
            if cc is None:
                w('theorem tbl%d_c_0_%d : tbl%d (0 : Fin 7) (%d : Fin 7) = none := rfl' % (nid, k, nid, k))
            else:
                w('theorem tbl%d_c_0_%d : tbl%d (0 : Fin 7) (%d : Fin 7) = some ((%s : ℚ), %s) := rfl'
                  % (nid, k, nid, k, q(cc[0]), str(bool(cc[1])).lower()))
        w('')
    # hiPos (both modes)
    w('theorem hiPos_%d : ∀ b : Fin 7, 0 < b.val → 0 < dfsHi (boxN %s) tbl%d b := by' % (nid, BOXL, nid))
    w('  intro b hb')
    w('  fin_cases b')
    w('  · simp at hb')
    for k in range(1, 7):
        w('  · simp [dfsHi, boxN, %s, tbl%d_c_%d_0] <;> norm_num' % (BOXL, nid, k))
    w('')
    # tier-2 table kills (both modes; batch mode reuses the existing 49 cell lemmas)
    kills = utc_leaf_kills(r, t7, U)
    for (s, k, j) in kills:
        pi = states[(s[0], s[1])]
        w('/-- The table-level kill at reach leaf %d, state p = %s, Lean rank %d, j = %d: the'
          % (nid, q(s[0]), k, j))
        w('leaf\'s own tightened ranges make the census-passing candidate fail (the family,')
        w('entry or exit side fails on the leaf\'s cells). -/')
        w('theorem tblKill_%d_%d_%d_%d :' % (nid, pi, k, j))
        w('    ¬ (((8 * %d - 1 : ℕ) : ℚ) / dfsHi (boxN %s) tbl%d (%d : Fin 7) < 7 ∧' % (j, BOXL, nid, k))
        w('       ((8 * %d - 1 : ℕ) : ℚ) / dfsHi (boxN %s) tbl%d (%d : Fin 7) < (%s : ℚ) ∧'
          % (j, BOXL, nid, k, q(s[0])))
        w('       ((8 * %d + 1 : ℕ) : ℚ) / dfsLo (boxN %s) tbl%d (%d : Fin 7) > 7) := by' % (j, BOXL, nid, k))
        w('  simp [dfsHi, dfsLo, boxN, %s, tbl%d_c_%d_0, tbl%d_c_0_%d] <;> norm_num'
          % (BOXL, nid, k, nid, k))
        w('')
        w('#print axioms tblKill_%d_%d_%d_%d' % (nid, pi, k, j))
        w('')
    if leaf_tables:
        seen_s = '{' + ', '.join('((%d : Fin 7), (%s : ℚ))' % (rr, q(B))
                                 for (rr, B) in f_node['seen']) + '}'
        w('-- STANDING: DATA')
        w('def node%d : DfsNode := ⟨tbl%d, (%d : Fin 7), (%s : ℚ), (%s : ℚ), %s⟩' % (
            nid, nid, a, q(Aex), q(P), seen_s))
        w('')
        w('-- STANDING: DATA')
        w('def tree%d : DfsCert := DfsCert.prune node%d' % (nid, nid))
        w('')
    w('-- STANDING: DATA')
    w('def expStates_%d : List (ℚ × ℕ) := [%s]' % (nid, ', '.join(
        '((%s : ℚ), %d)' % (q(s[0]), s[1]) for s in r['explored_states'])))
    w('')
    w('/-- **OWED (b) -- the per-leaf zone-form domination instance** at reach leaf %d' % nid)
    w('(dump state P = %s, a = %d, Aex = %s, verdict `no_completing_state_reachable`,' % (q(P), a, q(Aex)))
    w('nst = %d, pmax = %s, transcribed from `experiments/n8/reachutc_%s.json`).  FINDING' % (r['nst'], q(r['pmax']), boxname))
    w('(machine-checked, `Fresh.ReachUtcProof.unrestricted_false`): the UNRESTRICTED')
    w('`DfsPruneDom` leaf condition is FALSE -- realized chains may use non-teeth zone')
    w('edges, which the state-graph verdict does not model.  The sound instance is the')
    w('ZONE form (`Fresh.ReachUtcProof.DfsPruneDomZone`, discharged by')
    w('`Fresh.ReachUtcProof.no_zone_chain_of_reach_utc`): it consumes the leaf\'s RELAXED')
    w('`reach_utc` closure (relaxed-closed, every sup ≤ 7, completing-free -- the strict')
    w('set transcribed below is NOT relaxed-closed), the envelope dominations `domHi`/`domLo`')
    w('from `UFine` plus the table cells, `hiPos`, `IsZoneExit Aex` and `Aex/dfsLo a ≤ P`.')
    w('Worked pattern: `Fresh.ReachUtcProof.verdict2`/`S2`/`domHi2`/`domLo2`/`no_zone_chain_leaf2`.')
    w('This stub carries the zone-form OWED until the per-leaf relaxed closures are')
    w('transcribed and the instance is discharged. -/')
    w('-- STANDING: OWED')
    w('theorem m4fix_%s_pruneDom_%d (h : DfsPruneDomZone (boxN %s) tree%d) :' % (boxname, nid, BOXL, nid))
    w('    DfsPruneDomZone (boxN %s) tree%d := h' % (BOXL, nid))
    w('')
    w('#print axioms m4fix_%s_pruneDom_%d' % (boxname, nid))
    w('')

def main():
    boxname = sys.argv[1].replace(',', '_')
    t7 = tuple(int(x) for x in boxname.split('_'))
    assert len(t7) == 7 and t7[0] == 1
    T = t7[1:]
    BOX = f'm4res_{boxname}'
    NQ = f'(boxN {BOX})'
    NS = f'Fresh.M4FixRung2_{boxname}'

    forest = json.load(open(os.path.join(HERE, f'm4fix_forest_{boxname}.json')))
    nodes = {n['id']: n for n in forest['nodes']}
    roots = forest['roots']
    # merge the tables from the tree dump (the forest json carries structure only)
    tree_rows = {}
    for l in open(os.path.join(HERE, f'm4fix_tree_{boxname}.jsonl')):
        r = json.loads(l)
        tree_rows[r['id']] = r
    assert sorted(tree_rows) == sorted(nodes)
    for nid, n in nodes.items():
        n['U'] = tree_rows[nid]['U']
        assert n['kind'] == tree_rows[nid]['kind'] and n['parent'] == tree_rows[nid]['parent']
    for n in nodes.values():
        n['U'] = parse_tab(n['U'])
        n['Aex'] = F(n['Aex']); n['P'] = F(n['P'])
        n['seenL'] = [(r, F(B)) for (r, B) in n['seen']]   # lean ranks
        n['children'] = n.get('children', [])
        if n['step']: n['step'] = (int(n['step'][0]), F(n['step'][1]), F(n['step'][2]))
    N = len(nodes)
    print('forest: %d nodes, roots %s, kinds %s' % (
        N, roots, {k: sum(1 for x in nodes.values() if x['kind'] == k)
                   for k in ('internal', 'reach', 'deadend')}))
    assert forest['box'] == list(t7)
    # every non-root node's parent id must be smaller (DFS preorder) and listed
    for nid, n in nodes.items():
        if n['parent'] is not None:
            assert n['parent'] in nodes and n['parent'] < nid
            assert nid in nodes[n['parent']]['children']
        if n['kind'] == 'internal':
            assert n['children']
            for c in n['children']:
                assert nodes[c]['kind'] in ('reach', 'deadend', 'internal')
                assert nodes[c]['step'] is not None
        else:
            assert not n['children']
    # DELTA: constructed C3 record for lzones/box cross-check (no banked Lean record
    # exists; the Lean-side record is emitted into Fresh/M4FixResBank_v1.lean by
    # m4fix_bank_v1.py and kernel-checked by M4ResData at compile time)
    sys.path.insert(0, HERE)   # -I mode does not add the script's directory
    import m4fix_recon_v1 as FXR
    bank = FXR.parse_bank('m4res_%s' % boxname)
    assert bank['box'] == list(t7)
    lzones = sorted(set(bank['lzones']))
    data_ll = sorted(set((n['a'] + 1, int(n['Aex'])) for n in nodes.values()
                         if n['kind'] in ('reach', 'deadend')))
    assert data_ll == lzones, (data_ll, lzones)

    # ---------- per-edge step computations (emission-side self-checks) ----------
    intermediates = {}   # key (frm_tbl_name, to_tbl_name, i, j, c) -> emitted table name
    tblname = {nid: f'tbl{nid}' for nid in nodes}
    def tbl_of(nid): return tblname[nid]
    edge_cases = {}
    for nid, n in nodes.items():
        if n['parent'] is None: continue
        p = nodes[n['parent']]
        a_from = p['a']          # lean ranks already
        b_row, A, B = n['step']
        Aex = p['Aex']
        U_p, U_c = p['U'], n['U']
        V1 = gt(U_p, Aex, a_from, A, b_row)
        assert V1 is not None, ('add1 failed', nid)
        keep1 = (V1 == U_p)
        land1 = 'P' if keep1 else ('C' if V1 == U_c else 'S')
        V2 = gt(V1, B, b_row, Aex, a_from)
        assert V2 is not None, ('add2 failed', nid)
        keep2 = (V2 == V1)
        # final landing must be the child table
        assert V2 == U_c, ('step does not land on child table', nid)
        edge_cases[nid] = dict(a_from=a_from, b_row=b_row, A=A, B=B, Aex=Aex,
                               keep1=keep1, land1=land1, keep2=keep2,
                               V1=V1, tbl1=(tbl_of(n['parent']) if keep1 else
                                            (tbl_of(nid) if V1 == U_c else None)))
        if land1 == 'S':
            key = (json.dumps(V1, default=str),)
            nm = f'tblS{n["id"]}'
            intermediates[nid] = nm
            edge_cases[nid]['tbl1'] = nm
        # dfsLo / child-P self-check
        lo = dfs_lo(U_p, T, b_row)
        assert B / lo == n['P'], (nid, B / lo, n['P'])
    # nodeOK self-checks at every node
    for nid, n in nodes.items():
        aa = n['a']
        assert uAdd(n['U'], aa, 0, n['Aex'] / 7, True) is None, ('nodeOK', nid)
        assert not uKeepCur(n['U'], aa, 0, n['Aex'] / 7, True)
        assert uBack(n['U'], aa, 0, n['Aex'] / 7, True)

    # ---------- candidate inventories (per node: internal match-completeness,
    # deadend no-filter) ----------
    def inventory(U_, a_lean, Aex, P, seen_lean):
        seen = set((r, F(B)) for (r, B) in seen_lean)
        inv = []
        for r in range(7):
            hi = dfs_hi(U_, T, r)
            jm = 0; j = 1
            while F(8 * j - 1) / hi < F(7): jm = j; j += 1
            M = math.ceil(F(7) * hi)
            cand = []
            for j in range(1, jm + 1):
                A, B = 8 * j - 1, 8 * j + 1
                if F(A) / hi >= P: cand.append((j, 'ENTRY')); continue
                if (r, F(B)) in seen: cand.append((j, 'FRESH')); continue
                V1 = gt(U_, Aex, a_lean, F(A), r)
                if V1 is None: cand.append((j, 'SEAM1')); continue
                V2 = gt(V1, F(B), r, Aex, a_lean)
                if V2 is None:
                    cand.append((j, 'SEAM2')); continue
                cand.append((j, ('MATCH', V1, V2)))
            inv.append(dict(r=r, jmax=jm, M=M, hi=hi, cand=cand))
        return inv
    invs = {}
    for nid, n in nodes.items():
        if n['kind'] in ('internal', 'deadend'):
            invs[nid] = inventory(n['U'], n['a'], n['Aex'], n['P'], n['seenL'])
    # cross-check: internal nodes' MATCH candidates == the actual children's steps;
    # deadends have none
    for nid, n in nodes.items():
        if n['kind'] not in ('internal', 'deadend'): continue
        matchR = set()
        for row in invs[nid]:
            for (j, k) in row['cand']:
                if isinstance(k, tuple): matchR.add((row['r'], j))
        childRJ = set((c['step'][0], (int(c['step'][1]) + 1) // 8)
                      for c in (nodes[c] for c in n['children']))
        if n['kind'] == 'internal':
            assert matchR == childRJ, ('match completeness', nid, matchR, childRJ)
        else:
            assert not matchR, ('deadend has a passing candidate', nid)
    # seam-kill intermediate tables (SEAM2 with a propagating first add)
    seam_tabs = {}   # (nid, r, j) -> name
    for nid, n in nodes.items():
        if nid not in invs: continue
        for row in invs[nid]:
            for (j, k) in row['cand']:
                if k == 'SEAM2':
                    A, B = 8 * j - 1, 8 * j + 1
                    V1 = gt(n['U'], n['Aex'], n['a'], F(A), row['r'])
                    if V1 != n['U']:
                        seam_tabs[(nid, row['r'], j)] = f'tblSK_{nid}_{row["r"]}_{j}'

    # ---------- emission ----------
    L = []
    w = L.append
    w('import Fresh.M4CertSound')
    w('import Fresh.M4FixResBank_v1')
    w('import Fresh.ReachUtcProof')
    w('')
    w('/-!')
    w(f'# M4FixRung2_{boxname}: per-box M4 certificate transcription, box {t7}')
    w('')
    w(f'Written 2026-11-20 by `m4fix_gen_v1.py` from the per-box reconstruction')
    w(f'(`experiments/n8/m4fix_recon_v1.py`, [T]-verified against both checkpoint artifacts')
    w(f'(`j2_admit_cert2_checkpoint.jsonl`, `m4comp_cert_ckpt_v1.jsonl`) and the')
    w(f'CONSTRUCTED record `Fresh.M4FixResBank_v1.{BOX}`).  No existing file is edited.')
    w('')
    w('This file scales the ONE-box crown transcription of `Fresh.M4CertRung1.lean` to a')
    w(f'WHOLE certificate FOREST: all {N} nodes of the box\'s reconstructed DFS certificate')
    w(f'tree(s) -- {sum(1 for x in nodes.values() if x["kind"] == "internal")} internal, '
      f'{sum(1 for x in nodes.values() if x["kind"] == "reach")} reach-prune leaves,')
    w(f'{sum(1 for x in nodes.values() if x["kind"] == "deadend")} dead-end leaves, '
      f'{len(roots)} start-zone root(s) -- transcribed as literal `DfsCert` data: tables as')
    w('49-cell `UTable` literals with per-cell `rfl` lemmas, node states, step equations,')
    w('seam kills, `DfsNodeOK` at every node, `DfsEnum` at every internal and dead-end node,')
    w('and the composed theorems through the GENERIC data connection')
    w('(`Fresh.M4Cert.m4CertSound_of_data` / `m4boxClear_of_data`).')
    w('')
    w('OWED (named, not discharged by any existing artifact):')
    w('* `DfsRootAdm` -- OWED (a) of `Fresh.M4CertSound`\'s header: the E810 strict-monotone')
    w('  opening side (hypothesis-identity stub here, as in rung 1).')
    nreach = sum(1 for n in nodes.values() if n['kind'] == 'reach')
    if nreach:
        w('* OWED (b) -- now SPLIT by the per-leaf verdict transcription (section 5b): the')
        w('  verdict side of every reach-prune leaf\'s `reach_utc` domination is transcribed')
        w('  from `experiments/n8/reachutc_%s.json` and DISCHARGED here' % boxname)
        w('  (`verdictNoCompl_*`); what remains OWED per leaf is the `[P]` state-graph')
        w('  PROJECTION instance `reachutcProj_*` (realized chain → completing state')
        w('  reachable), being proved in parallel in `Fresh/ReachUtcProof.lean`.')
    w('-/')
    w('')
    w(f'namespace {NS}')
    w('')
    w('open Fresh.FilterAssembly Fresh.UClosure Fresh.MechDataBatch Fresh.M4Cert')
    w('')
    w('-- the 49-point propagation checks and the interval splits need headroom')
    w('set_option maxHeartbeats 4000000')
    w('')
    # generic helpers (verbatim rung-1 templates)
    for s in [
        '/-- The `uAdd` rejection: keep-cur ground-false and the back-check ground-true, verbatim',
        "`uAdd`'s two `if`s. -/",
        'theorem uAdd_eq_none {U : UTable} {i j : Fin 7} {c : ℚ} {s : Bool}',
        '    (hK : uKeepCur U i j c s = false) (hB : uBack U i j c s = true) :',
        '    uAdd U i j c s = none := by',
        '  unfold uAdd',
        '  rw [if_neg (by simp [hK]), if_pos (by simp [hB])]',
        '',
        '/-- The keep-current survival: the stored bound is already tighter, the table unchanged. -/',
        'theorem uAdd_eq_some_self {U : UTable} {i j : Fin 7} {c : ℚ} {s : Bool}',
        '    (hK : uKeepCur U i j c s = true) : uAdd U i j c s = some U := by',
        '  unfold uAdd',
        '  rw [if_pos (by simp [hK])]',
        '',
        '/-- The propagation assembly: keep-cur and back checks ground-false, the propagated',
        'table is the transcribed one pointwise (local copy of `Fresh.ChainDomBase.uAdd_eq_some`;',
        "that file's namespace is not opened here). -/",
        'theorem uAdd_eq_some {U V : UTable} {i j : Fin 7} {c : ℚ} {s : Bool}',
        '    (hK : uKeepCur U i j c s = false) (hB : uBack U i j c s = false)',
        '    (hpt : ∀ p q, uProp U i j c s p q = V p q) : uAdd U i j c s = some V := by',
        '  unfold uAdd',
        '  rw [if_neg (by simp [hK]), if_neg (by simp [hB])]',
        '  exact congrArg some (funext fun p => funext fun q => hpt p q)',
        '',
        '/-- A step whose first `uGt` fails. -/',
        'theorem uStep_eq_none_left {U : UTable} {a b : Fin 7} {Aex A B : ℚ} (hAex : 0 < Aex)',
        '    (hA : 0 < A) (h : uAdd U a b (Aex / A) true = none) : uStep U a b Aex A B = none := by',
        '  unfold uStep',
        '  rw [uGt_pos U a b hAex hA, h]',
        '  rfl',
        '',
        '/-- A step whose second `uGt` fails on the surviving table. -/',
        'theorem uStep_eq_none_right {U V : UTable} {a b : Fin 7} {Aex A B : ℚ} (hAex : 0 < Aex)',
        '    (hA : 0 < A) (hB : 0 < B) (h1 : uAdd U a b (Aex / A) true = some V)',
        '    (h2 : uAdd V b a (B / Aex) true = none) : uStep U a b Aex A B = none := by',
        '  unfold uStep',
        '  rw [uGt_pos U a b hAex hA, h1, Option.bind_some, uGt_pos V b a hB hAex, h2]',
        '',
        "/-- A surviving step is its two `uAdd`s (`uGt_pos` twice). -/",
        "theorem uStep_eq_some' {U V W : UTable} {a b : Fin 7} {Aex A B : ℚ}",
        '    (hAex : 0 < Aex) (hA : 0 < A) (hB : 0 < B)',
        '    (h1 : uAdd U a b (Aex / A) true = some V) (h2 : uAdd V b a (B / Aex) true = some W) :',
        '    uStep U a b Aex A B = some W := by',
        "  show (uGt U Aex a A b).bind (fun V => uGt V B b Aex a) = some W",
        "  rw [uGt_pos U a b hAex hA, h1, Option.bind_some, uGt_pos V b a hB hAex, h2]",
        '',
        '/-- The zone bound: `(8j-1)/hi < 7` with `hi > 0` gives `8j-1 < 7·hi` over ℚ. -/',
        'theorem lt_of_zone {hi : ℚ} {j : ℕ} (hpos : 0 < hi)',
        '    (hzone : (((8 * j - 1 : ℕ) : ℚ) : ℝ) / (hi : ℝ) < 7) :',
        '    ((8 * j - 1 : ℕ) : ℚ) < 7 * hi := by',
        '  have h2 : (((8 * j - 1 : ℕ) : ℚ) : ℝ) < (7 : ℝ) * (hi : ℝ) :=',
        "    (div_lt_iff₀ (by exact_mod_cast hpos)).mp hzone",
        '  exact_mod_cast h2',
        '',
        "#print axioms uAdd_eq_none",
        "#print axioms uAdd_eq_some_self",
        "#print axioms uAdd_eq_some",
        "#print axioms uStep_eq_none_left",
        "#print axioms uStep_eq_none_right",
        "#print axioms uStep_eq_some'",
        "#print axioms lt_of_zone",
        '',
    ]:
        w(s)

    # ---- section 1: tables, cell lemmas, node states, tree literals ----
    w(f'/-! ## 1. The forest tables, node states and certificate literals (verbatim data) -/')
    w('')
    for nid in sorted(nodes):
        n = nodes[nid]
        w(lean_table(tblname[nid], n['U'],
                     f'Table of DFS node {nid} ({n["kind"]}, depth {n["depth"]}, last reading '
                     f'row {n["a"]}, exit numerator {q(n["Aex"])}).'))
        w('')
        w(cell_lemmas(tblname[nid], n['U']))
        w('')
    # intermediates: step tables + seam-kill tables
    for nid, nm in sorted(intermediates.items()):
        ec = edge_cases[nid]
        w(lean_table(nm, ec['V1'],
                     f'Intermediate surviving table of node {nid}\'s in-step: the propagation'
                     ' result of the FIRST `uAdd` of the step (the second `uAdd` lands on the'
                     ' child table).'))
        w('')
        w(cell_lemmas(nm, ec['V1']))
        w('')
    for (nid, r, j), nm in sorted(seam_tabs.items()):
        n = nodes[nid]
        A, B = 8 * j - 1, 8 * j + 1
        V1 = gt(n['U'], n['Aex'], n['a'], F(A), r)
        w(lean_table(nm, V1,
                     f'Intermediate surviving table of the seam-killed candidate '
                     f'(row {r}, j = {j}) at node {nid}: the FIRST `uAdd` propagates to this'
                     ' table, on which the SECOND `uAdd` is rejected.'))
        w('')
        w(cell_lemmas(nm, V1))
        w('')
    w('/-! ## 1b. The node states and the certificate trees -/')
    w('')
    for nid in sorted(nodes):
        n = nodes[nid]
        if n['parent'] is None:
            seen_s = '{' + ', '.join(f'(({r} : Fin 7), ({q(B)} : ℚ))' for (r, B) in n['seenL']) + '}'
            doc = (f'The start-zone root: DFS node {nid} (depth {n["depth"]}, last reading row '
                   f'{n["a"]}, exit numerator {q(n["Aex"])}, frontier sup {q(n["P"])}).')
            seen_expr = seen_s
        else:
            p = nodes[n['parent']]
            b_row, A, B = n['step']
            doc = (f'DFS node {nid} ({n["kind"]}, depth {n["depth"]}, last reading row {n["a"]}, '
                   f'exit numerator {q(n["Aex"])}): child of node {p["id"]} by the step '
                   f'({b_row}, {q(A)}, {q(B)}).')
            seen_expr = (f'node{p["id"]}.seen ∪ {{(({b_row} : Fin 7), ({q(B)} : ℚ))}}')
        w(f'/-- {doc} -/')
        w('-- STANDING: DATA')
        w(f'def node{nid} : DfsNode := ⟨{tblname[nid]}, ({n["a"]} : Fin 7), ({q(n["Aex"])} : ℚ), '
          f'({q(n["P"])} : ℚ), {seen_expr}⟩')
        w('')
    # trees in REVERSE id order: children (larger ids, DFS preorder) before parents, so
    # children_k may reference tree_c (Lean has no forward references)
    for nid in sorted(nodes, reverse=True):
        n = nodes[nid]
        if n['kind'] == 'internal':
            cl = ', '.join(f'tree{c}' for c in n['children'])
            w(f'def children{nid} : List DfsCert := [{cl}]')
            w(f'/-- The subtree rooted at internal node {nid}: every child of every retained')
            w('internal node is retained. -/')
            w('-- STANDING: DATA')
            w(f'def tree{nid} : DfsCert := DfsCert.node node{nid} children{nid}')
        elif n['kind'] == 'reach':
            w(f'/-- The reach-prune leaf, DFS node {nid}: the `reach_utc` abstraction found no')
            w('completing state. -/')
            w('-- STANDING: DATA')
            w(f'def tree{nid} : DfsCert := DfsCert.prune node{nid}')
        else:
            w(f'/-- The dead-end leaf, DFS node {nid}: no filter-passing step. -/')
            w('-- STANDING: DATA')
            w(f'def tree{nid} : DfsCert := DfsCert.deadend node{nid}')
        w('')
    rl = ', '.join(f'tree{r}' for r in roots)
    w(f'/-- The box\'s WHOLE certificate forest ({len(roots)} start-zone root(s), {N} nodes),')
    w('transcribed verbatim from the reconstruction. -/')
    w('-- STANDING: DATA')
    w(f'def forest : List DfsCert := [{rl}]')
    w('')

    # ---- section 2: node completion checks ----
    w('/-! ## 2. The node completion checks fail at every node (`DfsNodeOK`) -/')
    w('')
    for nid in sorted(nodes):
        n = nodes[nid]
        tbl, aa, Aex = tblname[nid], n['a'], n['Aex']
        cellK = f'{tbl}_c_{aa}_0'
        cellB = f'{tbl}_c_0_{aa}'
        w(f'theorem nodeOK_{nid} : DfsNodeOK node{nid} := by')
        w(f'  show uExitOK {tbl} ({aa} : Fin 7) ({q(Aex)} : ℚ) = false')
        w('  unfold uExitOK')
        w('  rw [uAdd_eq_none')
        w(f'    (by simp [uKeepCur, {cellK}] <;> norm_num)')
        w(f'    (by simp [uBack, uBackCond, {cellB}] <;> norm_num)]')
        w('  rfl')
        w('')
        w(f'#print axioms nodeOK_{nid}')
    w('')

    # ---- section 3: step equations, childState equations ----
    w('/-! ## 3. The child steps (`DfsMatch`) and the `childState` equations -/')
    w('')
    for nid in sorted(nodes):
        n = nodes[nid]
        if n['parent'] is None: continue
        ec = edge_cases[nid]
        p = nodes[n['parent']]
        tP, tC = tblname[p['id']], tblname[nid]
        a_from, b_row, A, B, Aex = ec['a_from'], ec['b_row'], ec['A'], ec['B'], ec['Aex']
        # add1
        t1 = ec['tbl1']
        # the division arguments are emitted UNREDUCED (numerator/denominator numerals) so
        # that the uStep_eq_some' application matches its expected type syntactically
        c1 = f'({Aex.numerator} / {A.numerator} : ℚ)'
        c2 = f'({B.numerator} / {Aex.numerator} : ℚ)'
        if ec['keep1']:
            w(f"/-- Node {nid}'s step ({b_row}, {q(A)}, {q(B)}): add 1 is keep-current (the")
            w('stored bound is already tighter, table unchanged). -/')
            w(f'theorem addEq_{nid}_1 : uAdd {tP} ({a_from} : Fin 7) ({b_row} : Fin 7) '
              f'({c1}) true = some {tP} :=')
            w(f'  uAdd_eq_some_self (by simp [uKeepCur, {tP}_c_{a_from}_{b_row}] <;> norm_num)')
        else:
            w(f"/-- Node {nid}'s step ({b_row}, {q(A)}, {q(B)}): add 1 propagates "
              + (f'to the intermediate table {t1}' if ec['land1'] == 'S'
                 else 'the parent table to the child table') + ' (the two-cycle check is')
            w('ground-false on the exact cells). -/')
            w(f'theorem addEq_{nid}_1 : uAdd {tP} ({a_from} : Fin 7) ({b_row} : Fin 7) '
              f'({c1}) true = some {t1} :=')
            w('  uAdd_eq_some')
            w(f'    (by simp [uKeepCur, {tP}_c_{a_from}_{b_row}] <;> norm_num)')
            w(f'    (by simp [uBack, uBackCond, {tP}_c_{b_row}_{a_from}] <;> norm_num)')
            w(f'    (by intro p q; fin_cases p <;> fin_cases q <;> simp [uProp, uTighter, {tP}, {t1}] <;> norm_num)')
        w('')
        # add2
        t2 = t1 if ec['keep2'] else tC
        w(f"/-- Node {nid}'s step: add 2 "
          + ('is keep-current (the stored bound is already tighter), so the table is unchanged. -/'
             if ec['keep2'] else
             (f'propagates the intermediate table to the child table. -/' if ec['land1'] == 'S'
              else 'propagates to the child table. -/')))
        w(f'theorem addEq_{nid}_2 : uAdd {t1} ({b_row} : Fin 7) ({a_from} : Fin 7) '
          f'({c2}) true = some {t2} :=')
        if ec['keep2']:
            w(f'  uAdd_eq_some_self (by simp [uKeepCur, {t1}_c_{b_row}_{a_from}] <;> norm_num)')
        else:
            w('  uAdd_eq_some')
            w(f'    (by simp [uKeepCur, {t1}_c_{b_row}_{a_from}] <;> norm_num)')
            w(f'    (by simp [uBack, uBackCond, {t1}_c_{a_from}_{b_row}] <;> norm_num)')
            w(f'    (by intro p q; fin_cases p <;> fin_cases q <;> simp [uProp, uTighter, {t1}, {tC}] <;> norm_num)')
        w('')
        w(f"/-- Node {nid}'s full step equation. -/")
        w(f'theorem stepEq_{nid} : uStep {tP} ({a_from} : Fin 7) ({b_row} : Fin 7) '
          f'({q(Aex)} : ℚ) ({q(A)} : ℚ) ({q(B)} : ℚ) = some {tC} :=')
        w("  uStep_eq_some' (by norm_num) (by norm_num) (by norm_num) "
          f'addEq_{nid}_1 addEq_{nid}_2')
        w('')
        w(f"/-- Node {nid}'s `childState` equation: the child node is exactly the DFS expansion")
        w("rule's state (frontier sup = B / lo' from the parent's tightened ranges, seen = parent")
        w('set plus the step pair). -/')
        lo_v = dfs_lo(p['U'], T, b_row)
        assert B / lo_v == n['P']
        anc = [nid, p['id']]
        seen_chain = 'node%s' % p['id']
        w(f'theorem childEq_{nid} : childState {NQ} node{p["id"]} ({b_row} : Fin 7) ({q(B)} : ℚ) {tC} '
          f'= DfsCert.root tree{nid} :=')
        w('  by')
        w(f'    simp only [childState, DfsCert.root, tree{nid}, node{nid}]')
        w(f'    have hlo : dfsLo {NQ} node{p["id"]}.U ({b_row} : Fin 7) = ({q(lo_v)} : ℚ) :=')
        w(f'      by norm_num [dfsLo, boxN, {BOX}, node{p["id"]}, {tP}_c_0_{b_row}]')
        w('    norm_num [hlo]')
        w('')
        w(f'#print axioms addEq_{nid}_1')
        w(f'#print axioms addEq_{nid}_2')
        w(f'#print axioms stepEq_{nid}')
        w(f'#print axioms childEq_{nid}')
        w('')

    # ---- section 3b: seam kills at every internal and dead-end node ----
    w('/-! ## 3b. The seam kills -/')
    w('')
    nsk = 0
    for nid in sorted(invs):
        n = nodes[nid]
        tbl = tblname[nid]
        ndname = f'node {nid} ({n["kind"]})'
        block = []
        for row in invs[nid]:
            r, jmax, hi = row['r'], row['jmax'], row['hi']
            for (j, k) in row['cand']:
                if k == 'SEAM1':
                    A, B = 8 * j - 1, 8 * j + 1
                    Af, Bf = qform(j, -1), qform(j, +1)
                    assert uAdd(n['U'], n['a'], r, n['Aex'] / F(A), True) is None
                    assert not uKeepCur(n['U'], n['a'], r, n['Aex'] / F(A), True)
                    assert uBack(n['U'], n['a'], r, n['Aex'] / F(A), True)
                    block.append((f'theorem sk{nid}_seam_{r}_{j} : uStep {tbl} ({n["a"]} : Fin 7) '
                                  f'({r} : Fin 7) ({q(n["Aex"])} : ℚ) {Af} {Bf} = none := by'))
                    block.append('  refine uStep_eq_none_left (by norm_num) (by norm_num) ?_')
                    block.append('  refine uAdd_eq_none (by simp [uKeepCur, '
                                 f'{tbl}_c_{n["a"]}_{r}] <;> norm_num) ?_')
                    block.append(f'  simp [uBack, uBackCond, {tbl}_c_{r}_{n["a"]}] <;> norm_num')
                    block.append('')
                    nsk += 1
                elif k == 'SEAM2':
                    A, B = 8 * j - 1, 8 * j + 1
                    Af, Bf = qform(j, -1), qform(j, +1)
                    V1 = gt(n['U'], n['Aex'], n['a'], F(A), r)
                    if V1 == n['U']:
                        # keep-cur first add, second rejected
                        assert uKeepCur(n['U'], n['a'], r, n['Aex'] / F(A), True) is True
                        assert uKeepCur(n['U'], r, n['a'], F(B) / n['Aex'], True) is False
                        assert uBack(n['U'], r, n['a'], F(B) / n['Aex'], True) is True
                        block.append((f'theorem sk{nid}_seam_{r}_{j} : uStep {tbl} ({n["a"]} : Fin 7) '
                                      f'({r} : Fin 7) ({q(n["Aex"])} : ℚ) {Af} {Bf} = none := by'))
                        block.append(f'  have h1 : uAdd {tbl} ({n["a"]} : Fin 7) ({r} : Fin 7) '
                                     f'(({q(n["Aex"])} : ℚ) / {Af}) true = some {tbl} :=')
                        block.append(f'    uAdd_eq_some_self (by simp [uKeepCur, {tbl}_c_{n["a"]}_{r}] <;> norm_num)')
                        block.append('  refine uStep_eq_none_right (by norm_num) (by norm_num) (by norm_num) h1 ?_')
                        block.append('  exact uAdd_eq_none')
                        block.append(f'      (by simp [uKeepCur, {tbl}_c_{r}_{n["a"]}] <;> norm_num)')
                        block.append(f'      (by simp [uBack, uBackCond, {tbl}_c_{n["a"]}_{r}] <;> norm_num)')
                        block.append('')
                    else:
                        sT = seam_tabs[(nid, r, j)]
                        # data-side: h1 lands on sT, second add rejected on sT
                        c1 = uAdd(n['U'], n['a'], r, n['Aex'] / F(A), True)
                        assert c1 == V1
                        assert not uKeepCur(n['U'], n['a'], r, n['Aex'] / F(A), True)
                        assert not uKeepCur(V1, r, n['a'], F(B) / n['Aex'], True)
                        assert uBack(V1, r, n['a'], F(B) / n['Aex'], True)
                        block.append((f'theorem sk{nid}_seam_{r}_{j} : uStep {tbl} ({n["a"]} : Fin 7) '
                                      f'({r} : Fin 7) ({q(n["Aex"])} : ℚ) {Af} {Bf} = none := by'))
                        block.append(f'  have h1 : uAdd {tbl} ({n["a"]} : Fin 7) ({r} : Fin 7) '
                                     f'(({q(n["Aex"])} : ℚ) / {Af}) true = some {sT} :=')
                        block.append('  uAdd_eq_some')
                        block.append(f'    (by simp [uKeepCur, {tbl}_c_{n["a"]}_{r}] <;> norm_num)')
                        block.append(f'    (by simp [uBack, uBackCond, {tbl}_c_{r}_{n["a"]}] <;> norm_num)')
                        block.append(f'    (by intro p q; fin_cases p <;> fin_cases q <;> simp [uProp, uTighter, {tbl}, {sT}] <;> norm_num)')
                        block.append('  refine uStep_eq_none_right (by norm_num) (by norm_num) (by norm_num) h1 ?_')
                        block.append('  exact uAdd_eq_none')
                        block.append(f'      (by simp [uKeepCur, {sT}_c_{r}_{n["a"]}] <;> norm_num)')
                        block.append(f'      (by simp [uBack, uBackCond, {sT}_c_{n["a"]}_{r}] <;> norm_num)')
                        block.append('')
                        nsk += 1
        if block:
            w(f'/-- Seam-failure kills at {ndname}: candidates that pass the entry and')
            w('freshness filters but fail a seam bound have `uStep = none` (kernel-evaluated')
            w('on the literal cells). -/')
            for s in block: w(s)
            w('')
    for nid in sorted(invs):
        for row in invs[nid]:
            for (j, k) in row['cand']:
                if k in ('SEAM1', 'SEAM2'):
                    w(f'#print axioms sk{nid}_seam_{row["r"]}_{j}')
    w('')

    # ---- section 4: the DfsEnum proofs ----
    w('/-! ## 4. The enumeration proofs (`DfsEnum` at every internal and dead-end node) -/')
    w('')
    def emit_enum(name, nid, goal_match):
        n = nodes[nid]
        tbl = tblname[nid]
        kind = 'match-completeness' if goal_match else 'dead-end verdict'
        w(f'/-- The `{kind}` at node {nid}: for EVERY Lean-spec candidate step `(b, A, B)` -- b')
        w('ranging over all 7 rows (including rank 0, which the run never expands, and the same')
        w('reading row, which the run skips -- the reconstruction audited 0 holes there),')
        w('A = 8j-1, B = 8j+1 passing the zone bound -- the candidate is either killed by the')
        w('entry/frontier comparison, the seen-freshness set, or a seam failure (`uStep = none`),'
          + (' or matched against the transcribed child. -/' if goal_match else ' -/'))
        tgt = (f'∃ c ∈ children{nid}, DfsMatch {NQ} node{nid} b A B c') if goal_match else 'False'
        w(f'theorem {name} (b : Fin 7) (A B : ℚ) (hf : DfsFilters {NQ} node{nid} b A B) : {tgt} := by')
        w('  simp only [DfsFilters, DfsSoft, dfsZone] at hf')
        w('  obtain ⟨⟨⟨j, hj1, hAj, hBj, hzone⟩, hentry, hfresh⟩, hseam⟩ := hf')
        w('  subst hAj; subst hBj')
        w('  fin_cases b')
        # the unfold chain: the node def and its seen-set ancestor defs
        unfold = []
        x = nid
        while True:
            unfold.append(f'node{x}')
            p = nodes[x]['parent']
            if p is None: break
            x = p
        nsql = ', '.join(unfold)
        for row in invs[nid]:
            r, jmax, M, hi = row['r'], row['jmax'], row['M'], row['hi']
            w(f'  · -- b = row {r} (jmax = {jmax}, M = ceil(7·hi) = {M})')
            w(f'    simp only [{nsql}] at hzone hentry hfresh hseam')
            cell = f', {tbl}_c_{r}_0' if r > 0 else ''
            w(f'    have hval0 : dfsHi {NQ} {tbl} ({r} : Fin 7) = ({q(hi)} : ℚ) :=')
            w(f'      by norm_num [dfsHi, boxN, {BOX}{cell}]')
            w(f'    have hval : dfsHi {NQ} {tbl} (⟨{r}, by norm_num⟩ : Fin 7) = ({q(hi)} : ℚ) := '
              'hval0')
            w('    rw [hval] at hzone hentry')
            w(f'    have hz : ((8 * j - 1 : ℕ) : ℚ) < (7 : ℚ) * (({q(hi)} : ℚ)) :=')
            w('      lt_of_zone (by norm_num) hzone')
            if jmax == 0:
                w(f'    have hK : (7 : ℚ) * (({q(hi)} : ℚ)) ≤ (7 : ℚ) := by norm_num')
                w('    have hF2 : (8 * j - 1 : ℕ) < 7 :=')
                w('      by exact_mod_cast lt_of_lt_of_le hz hK')
                w('    have hF : False := by omega')
                w('    exact hF.elim')
                w('')
                continue
            w(f'    have h6 : (8 * j - 1 : ℕ) < {M} :=')
            w(f'      by exact_mod_cast lt_of_lt_of_le hz (by norm_num : (7 : ℚ) * (({q(hi)} : ℚ)) '
              f'≤ ({M} : ℚ))')
            w(f'    have h8 : j ≤ {jmax} := by omega')
            w('    interval_cases j')
            child_of = {}
            if goal_match:
                for c in n['children']:
                    cb, cA, cB = nodes[c]['step']
                    child_of[(cb, (int(cA) + 1) // 8)] = c
            for (j, k) in row['cand']:
                if k == 'ENTRY':
                    w('    · norm_num at hentry')
                elif k == 'FRESH':
                    w('    · exact (hfresh (by decide)).elim' if goal_match
                      else '    · exact hfresh (by decide)')
                elif k in ('SEAM1', 'SEAM2'):
                    kill = f'sk{nid}_seam_{r}_{j}'
                    w(f'    · exact (hseam {kill}).elim' if goal_match
                      else f'    · exact hseam {kill}')
                else:
                    c = child_of[(r, j)]
                    w(f'    · exact ⟨tree{c}, by simp [children{nid}], {tblname[c]}, '
                      f'stepEq_{c}, childEq_{c}⟩')
            w('')
        w('')
    for nid in sorted(invs):
        emit_enum(f'enumMatch_{nid}' if nodes[nid]['kind'] == 'internal' else f'enumDead_{nid}',
                  nid, nodes[nid]['kind'] == 'internal')
    for nid in sorted(invs):
        nm = f'enumMatch_{nid}' if nodes[nid]['kind'] == 'internal' else f'enumDead_{nid}'
        w(f'#print axioms {nm}')
    w('')

    # ---- section 5: the tree assemblies (bottom-up) ----
    w('/-! ## 5. The per-tree assemblies: closed, enumerating, prune-dominated -/')
    w('')
    def rcases_list(var, listname, depth, handler, base_indent):
        # emit the rung-1 nested-rcases shape over a literal list membership: the second
        # bullet of each rcases OPENS with the next rcases (deeper indent), the first bullet
        # handles the matched element, the last bullet kills the nil tail
        ind = ' ' * base_indent
        w(f'{ind}simp only [{listname}, List.mem_cons] at {var}')
        def rest(d, tail, ind):
            # inside bullet: tail : t = element_d ∨ t ∈ (rest of the list)
            w(f'{ind}· {handler[d]}')
            if d + 1 == depth:
                w(f'{ind}· exact absurd {tail} (by simp)')
            else:
                nxt = f"ht'{d + 2}"
                w(f'{ind}· rcases {tail} with rfl | {nxt}')
                rest(d + 1, nxt, ind + '  ')
        w(f'{ind}rcases {var} with rfl | ht\'1')
        rest(0, "ht'1", ind)
    for nid in sorted(nodes, reverse=True):
        n = nodes[nid]
        if n['kind'] == 'internal':
            hs = [f'closed_{c}' for c in n['children']]
            w(f'theorem closed_{nid} : DfsClosed tree{nid} := by')
            w(f'  simp only [tree{nid}, DfsClosed]')
            w(f'  refine ⟨nodeOK_{nid}, ?_⟩')
            w('  intro t ht')
            rcases_list('ht', f'children{nid}', len(n['children']),
                        [f'exact {h}' for h in hs], 2)
            w('')
        else:
            w(f'theorem closed_{nid} : DfsClosed tree{nid} := by')
            w(f'  simp only [tree{nid}, DfsClosed]')
            w(f'  exact nodeOK_{nid}')
            w('')
        w(f'#print axioms closed_{nid}')
    w('')
    for nid in sorted(nodes, reverse=True):
        n = nodes[nid]
        if n['kind'] == 'internal':
            w(f'theorem enum_{nid} : DfsEnum {NQ} tree{nid} := by')
            w(f'  simp only [tree{nid}, DfsEnum]')
            w(f'  refine ⟨fun b A B hf => enumMatch_{nid} b A B hf, ?_⟩')
            w('  intro t ht')
            rcases_list('ht', f'children{nid}', len(n['children']),
                        [f'exact enum_{c}' for c in n['children']], 2)
            w('')
        elif n['kind'] == 'reach':
            w(f'/-- The prune leaf is vacuous for `DfsEnum` (`simp only` closes the goal). -/')
            w(f'theorem enum_{nid} : DfsEnum {NQ} tree{nid} := by')
            w(f'  simp only [tree{nid}, DfsEnum]')
            w('')
        else:
            w(f'theorem enum_{nid} : DfsEnum {NQ} tree{nid} := by')
            w(f'  simp only [tree{nid}, DfsEnum]')
            w(f'  exact fun b A B hf => enumDead_{nid} b A B hf')
            w('')
        w(f'#print axioms enum_{nid}')
    w('')
    # prune domination, bottom-up; hypotheses only for reach leaves
    prune_leaves = [nid for nid in sorted(nodes) if nodes[nid]['kind'] == 'reach']
    def pd_hyps(nid):
        n = nodes[nid]
        if n['kind'] == 'reach': return [nid]
        out = []
        for c in n['children']: out += pd_hyps(c)
        return out
    for nid in sorted(nodes, reverse=True):
        n = nodes[nid]
        if n['kind'] == 'internal':
            # hypothesis threading: per child, the child's pd applied to the global hyps slice
            w('/-- The per-node prune domination (internal node: inherited from the children;')
            w('the reach leaves carry the OWED (b) hypotheses). -/')
            w('theorem pd_%d %s: DfsPruneDom tree%d := by' % (
                nid, ''.join('(hprune_%d : DfsPruneDom tree%d) ' % (l, l) for l in pd_hyps(nid)), nid))
            w(f'  simp only [tree{nid}, DfsPruneDom]')
            w('  intro t ht')
            rcases_list('ht', f'children{nid}', len(n['children']),
                        [('exact pd_%d %s' % (c, ''.join('hprune_%d ' % l for l in pd_hyps(c))) if pd_hyps(c)
                          else 'exact pd_%d' % c) for c in n['children']], 2)
            w('')
        elif n['kind'] == 'reach':
            w('theorem pd_%d (hprune_%d : DfsPruneDom tree%d) : DfsPruneDom tree%d :=' % (nid, nid, nid, nid))
            w('  hprune_%d' % nid)
            w('')
        else:
            w('/-- The dead-end leaf is vacuous for `DfsPruneDom` (`simp only` closes it). -/')
            w('theorem pd_%d : DfsPruneDom tree%d := by' % (nid, nid))
            w(f'  simp only [tree{nid}, DfsPruneDom]')
            w('')
        w(f'#print axioms pd_{nid}')
    w('')

    # ---- section 5b: the per-leaf reach_utc verdict transcriptions (reachutc_<box>.json) ----
    utcf = os.path.join(HERE, 'reachutc_%s.json' % boxname)
    assert os.path.exists(utcf), 'missing reachutc dump for %s' % boxname
    utcd = json.load(open(utcf))
    assert utcd['box'] == list(t7) and utcd['kind'] == 'reachutc_dump_v1'
    utcleaves = utcd['reach_leaves']
    assert sorted(r['node_id'] for r in utcleaves) == sorted(
        nid for nid, n in nodes.items() if n['kind'] == 'reach'), \
        ('dump vs forest reach-leaf id mismatch', boxname)
    utc_states, utc_windows, utc_hwpass, utc_clean = utc_analyze(t7, utcleaves)
    global utc_cur_hwpass
    utc_cur_hwpass = utc_hwpass
    if utcleaves:
        w('/-! ## 5b. The per-leaf `reach_utc` verdict transcriptions (`reachutc_%s.json`)' % boxname)
        w('')
        w('The per-prune-leaf verdict layer: the explored (frontier-sup, dump-rank) state sets')
        w('and pmax as literal data, the `no_completing_state_reachable` verdicts (discharged')
        w('HERE by literal per-case proofs over the census windows), the OWED `[P]` projection')
        w('instances (`reachutcProj_*`, discharged by the parallel `Fresh/ReachUtcProof.lean`),')
        w('and the verdict-carrying `DfsPruneDom` instances `m4fix_%s_pruneDom_*` (replacing')
        w('the identity stubs). -/')
        w('')
        for r in utcleaves:
            utc_emit_leaf_block(w, r, tree_rows[r['node_id']], nodes[r['node_id']], t7,
                                utc_states, utc_clean, BOX, boxname, False)
    else:
        w('/-! ## 5b. The per-leaf `reach_utc` verdict transcriptions')
        w('')
        w('VACUOUS for this box: the forest has no reach-prune leaves, so there are no')
        w('per-leaf `reach_utc` verdicts to transcribe (`DfsPruneDom` holds vacuously at the')
        w('dead-end leaves). -/')
        w('')

    # ---- section 5c: the zone-form prune-dom threading (DfsPruneDomZone) ----
    for nid in sorted(nodes, reverse=True):
        n = nodes[nid]
        if n['kind'] == 'internal':
            w('theorem pdZone_%d %s: DfsPruneDomZone %s tree%d := by' % (
                nid, ''.join('(hpruneZone_%d : DfsPruneDomZone %s tree%d) ' % (l, NQ, l)
                             for l in pd_hyps(nid)), NQ, nid))
            w(f'  simp only [tree{nid}, DfsPruneDomZone]')
            w('  intro t ht')
            rcases_list('ht', f'children{nid}', len(n['children']),
                        [('exact pdZone_%d %s' % (c, ''.join('hpruneZone_%d ' % l for l in pd_hyps(c))) if pd_hyps(c)
                          else 'exact pdZone_%d' % c) for c in n['children']], 2)
            w('')
        elif n['kind'] == 'reach':
            w('theorem pdZone_%d (hpruneZone_%d : DfsPruneDomZone %s tree%d) :'
              % (nid, nid, NQ, nid))
            w('    DfsPruneDomZone %s tree%d := hpruneZone_%d' % (NQ, nid, nid))
            w('')
        else:
            w('theorem pdZone_%d : DfsPruneDomZone %s tree%d := by' % (nid, NQ, nid))
            w(f'  simp only [tree{nid}, DfsPruneDomZone]')
            w('')
        w(f'#print axioms pdZone_{nid}')
    w('')

    # ---- section 6: the forest assemblies ----
    w('/-! ## 6. The forest assemblies -/')
    w('')
    w('/-- The FOREST is closed (the form the data connection consumes). -/')
    w('theorem hforestClosed : ∀ t ∈ forest, DfsClosed t := by')
    w('  intro t ht')
    rcases_list('ht', 'forest', len(roots), [f'exact closed_{r}' for r in roots], 2)
    w('')
    w('/-- The FOREST enumerates. -/')
    w(f'theorem hforestEnum : ∀ t ∈ forest, DfsEnum {NQ} t := by')
    w('  intro t ht')
    rcases_list('ht', 'forest', len(roots), [f'exact enum_{r}' for r in roots], 2)
    w('')
    allpl = []
    for r in roots: allpl += pd_hyps(r)
    sig = ''.join('(hprune_%d : DfsPruneDom tree%d) ' % (l, l) for l in allpl)
    w('/-- The per-prune-leaf domination over the FOREST: at the reach-prune leaves exactly')
    w('OWED (b)%s' % ('' if allpl else ' -- VACUOUS here: the forest has no reach-prune leaves,'))
    w('so this proof needs no hypotheses; at dead ends and internal nodes the condition is')
    w('inherited/vacuous. -/')
    w('theorem hforestPruneDom %s: ∀ t ∈ forest, DfsPruneDom t := by' % sig)
    w('  intro t ht')
    rcases_list('ht', 'forest', len(roots),
                [('exact pd_%d %s' % (r, ''.join('hprune_%d ' % l for l in pd_hyps(r))) if pd_hyps(r)
                  else 'exact pd_%d' % r) for r in roots], 2)
    w('')
    zsig = ''.join('(hpruneZone_%d : DfsPruneDomZone %s tree%d) ' % (l, NQ, l) for l in allpl)
    w('/-- The zone-form per-prune-leaf domination over the FOREST: at the reach-prune')
    w('leaves exactly OWED (b)\'s zone-form remainder (the per-leaf zone-form stubs of')
    w('section 5b; the UNRESTRICTED form is false --')
    w('`Fresh.ReachUtcProof.unrestricted_false`). -/')
    w('theorem hforestPruneDomZone %s: ∀ t ∈ forest, DfsPruneDomZone %s t := by' % (zsig, NQ))
    w('  intro t ht')
    rcases_list('ht', 'forest', len(roots),
                [('exact pdZone_%d %s' % (r, ''.join('hpruneZone_%d ' % l for l in pd_hyps(r))) if pd_hyps(r)
                  else 'exact pdZone_%d' % r) for r in roots], 2)
    w('')
    w('/-- **OWED (a) -- the root-admissibility closure** (the E810 strict-monotone opening side:')
    w("every real W₀ chain's opening matches a forest root whose table it realizes and its steps")
    w('pass the soft filters along the induced path).  Same hypothesis-identity stub as rung 1;')
    w('the artifacts give only the reconstructed root states, no opening-match record.')
    w('Needed artifact: per-root opening-match / soft-admissible-path records, or a proof-grade')
    w("statement of E810's strict-monotone reading for this box. -/")
    w('-- STANDING: OWED')
    w(f'theorem m4fix_{boxname}_rootAdm (hcadm : DfsRootAdm {NQ} forest) :')
    w(f'    DfsRootAdm {NQ} forest := hcadm')
    w('')

    # section 7 rewiring (zone form): the composed theorems consume the zone-form OWED
    # stubs via hforestPruneDomZone (the unrestricted DfsPruneDom form is false --
    # Fresh.ReachUtcProof.unrestricted_false -- so the data connection is
    # m4CertSound_of_forest_zone + leafKeys_env90).
    sig = ''.join('(hpruneZone_%d : DfsPruneDomZone %s tree%d) ' % (l, NQ, l) for l in allpl)
    pdapp = ('(hforestPruneDomZone %s)' % ''.join('hpruneZone_%d ' % l for l in allpl)) \
        if allpl else 'hforestPruneDomZone'

    # ---- section 7: hn17 + composed theorems (generic data connection) ----
    w('/-! ## 7. The census envelope and the composed theorems (generic data connection) -/')
    w('')
    w('/-- The census envelope of the box tuple (all seven entries ≤ 17), discharged from the')
    w('record itself (the same pattern as `Fresh.M4Cert.hn17_1_4_6_7_10_16_16`, which exists')
    w('only for the rung-1 box; the per-box `m4cert_` instances of `Fresh.M4CertSound` likewise')
    w('exist only there, so this file consumes the GENERIC `m4CertSound_of_data` /')
    w('`m4boxClear_of_data` directly). -/')
    w(f'theorem hn17_{boxname} : ∀ i : Fin 7, boxN {BOX} i ≤ 17 := by')
    w('  intro i')
    w('  have hv : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 ∨ i.val = 3 ∨ i.val = 4 ∨ i.val = 5 ∨')
    w('    i.val = 6 := by')
    w('    have := i.isLt')
    w('    omega')
    w('  rcases hv with h | h | h | h | h | h | h')
    for d in range(7):
        if d == 0:
            w(f'  · have e : i = ⟨{d}, by decide⟩ := Fin.ext h; subst e; decide')
        else:
            w(f'  · have e : i = ⟨{d}, by decide⟩ := Fin.ext h; subst e; decide')
    w('')
    w(f'#print axioms hn17_{boxname}')
    w('')
    hyps = sig + f'(hcadm : DfsRootAdm {NQ} forest)'
    w('/-- **The composed certificate theorem**: the banked record (`m4resData_%s`,' % boxname)
    w('[T 2329/2329] bank) + the WHOLE-forest certificate deliver the box kill AND the')
    w('90-type leaf-key embedding, through `Fresh.M4Cert.m4CertSound_of_data` verbatim.  The')
    w('per-prune-leaf domination hypotheses are the reach_utc projection instances')
    w('(`hproj_<l> : reachutcProj_%s_<l>`, OWED (b)\'s per-leaf remainder); the verdict side' % boxname)
    w('of each leaf is discharged inside `m4fix_%s_pruneDom_<l>` from the transcribed' % boxname)
    w('`reachutc_%s.json` verdicts. -/' % boxname)
    w(f'theorem m4fix_{boxname}_cert {hyps} :')
    w(f'    M4CertSound {NQ} ∧')
    w(f'      ∀ k ∈ {BOX}.lzones, ∃ b : Fin 6, ∃ c : Fin 15, b.val + 2 = k.1 ∧')
    w('        Fresh.UClosure.envB c = (k.2 : ℚ) ∧')
    w('        Fresh.UClosure.keyOf (Fresh.UClosure.rowOf b) c = (b, c) :=')
    w(f'  ⟨m4CertSound_of_forest_zone {NQ} forest hforestClosed hforestEnum')
    w(f'    {pdapp} hcadm, leafKeys_env90 {BOX} m4resData_{boxname}⟩')
    w('')
    w('/-- **The composed clear-point theorem (the scaling target)**: the box\'s clear point per')
    w('arrangement, through `Fresh.M4Cert.m4boxClear_of_data` with the transcribed forest --')
    w('the same hypothesis shape as the rung-1 box, with `T` now the WHOLE transcribed forest')
    w('instead of a crown. -/')
    w(f'theorem m4fix_{boxname}_boxClear {hyps}')
    w(f'    (hcc : Fresh.UClosure.ChainlessClear {NQ} hn17_{boxname})')
    w(f'    (g : Fin 7 → ℝ) (hface : ∀ i, FaceLo {NQ} i ≤ g i ∧ g i ≤ FaceHi {NQ} i) :')
    w('    ∃ s : ℝ, 1 ≤ s ∧ s ≤ 7 ∧ ∀ i, (1 / 8 : ℝ) ≤ Fresh.distInt (g i * (s / 8)) :=')
    w(f'  m4boxClear_of_cert hn17_{boxname} hcc')
    w(f'    (m4CertSound_of_forest_zone {NQ} forest hforestClosed hforestEnum {pdapp} hcadm)')
    w(f'    g hface')
    w('')
    w(f"#print axioms m4fix_{boxname}_cert")
    w(f"#print axioms m4fix_{boxname}_boxClear")
    w('')
    w(f'end {NS}')
    w('')

    out = os.path.normpath(os.path.join(HERE, '..', '..', 'LonelyRunnerFresh', 'Fresh',
                                        f'M4FixRung2_{boxname}.lean'))
    with open(out, 'w') as f:
        f.write('\n'.join(L) + '\n')
    print('emitted %s (%d lines)' % (out, len(L)))
    print('seam kills: %d; intermediate step tables: %d; seam-propagation tables: %d' % (
        nsk, len(intermediates), len(seam_tabs)))
    print('prune-leaf OWEDs: %s' % (allpl,))

def main_leafonly(boxname):
    # Leaf-only mode for boxes whose WHOLE-forest transcription is infeasible (the rung-1
    # box: 51748 nodes -- the per-node step/enum/seam machinery would exceed a GB of Lean).
    # Emits ONE file per start-zone subtree (Fresh/M4FixRung2_<box>_t<root>.lean), each
    # carrying the full verdict layer (census machinery + windows + census classes + state
    # lemmas + per-leaf tables/node states/verdict/projection instances) for that subtree's
    # reach leaves.  The instance names follow the dump's stub naming
    # (m4fix_<box>_pruneDom_<id>) so the reachutc dump's stub audit matches the emitted
    # declarations.
    t7 = tuple(int(x) for x in boxname.split('_'))
    assert len(t7) == 7 and t7[0] == 1
    BOX = f'm4res_{boxname}'
    forest = json.load(open(os.path.join(HERE, 'm4fix_forest_%s.json' % boxname)))
    nodes = {n['id']: n for n in forest['nodes']}
    tree_rows = {}
    for l in open(os.path.join(HERE, 'm4fix_tree_%s.jsonl' % boxname)):
        r = json.loads(l)
        tree_rows[r['id']] = r
    assert sorted(tree_rows) == sorted(nodes)
    utcd = json.load(open(os.path.join(HERE, 'reachutc_%s.json' % boxname)))
    assert utcd['box'] == list(t7) and utcd['kind'] == 'reachutc_dump_v1'
    utcleaves = utcd['reach_leaves']
    assert sorted(r['node_id'] for r in utcleaves) == sorted(
        nid for nid, n in nodes.items() if n['kind'] == 'reach'), \
        ('dump vs forest reach-leaf id mismatch', boxname)
    _, utc_windows_full, utc_hwpass_full, _ = utc_analyze(t7, utcleaves)
    def root_of(nid):
        while nodes[nid]['parent'] is not None:
            nid = nodes[nid]['parent']
        return nid
    byroot = {}
    for r in utcleaves:
        byroot.setdefault(root_of(r['node_id']), []).append(r)
    # chunk oversized subtrees (a 1062-leaf single file exceeded the lean process's memory)
    CHUNK = 600
    parts = []
    for root in sorted(byroot):
        ls = byroot[root]
        for ci in range(0, len(ls), CHUNK):
            parts.append(('%d' % root if len(ls) <= CHUNK else '%d_p%d' % (root, ci // CHUNK), ls[ci:ci + CHUNK]))
    tot = 0
    for root, leaves in parts:
        lstates, _, lhwpass, lclean = utc_analyze(t7, leaves)
        NS = 'Fresh.M4FixRung2_%s_t%s' % (boxname, root)
        L2 = []
        w2 = L2.append
        w2('import Fresh.M4CertSound')
        w2('import Fresh.M4FixResBank_v1')
        w2('import Fresh.ReachUtcProof')
        w2('')
        w2('/-!')
        w2('# M4FixRung2_%s_t%s: per-leaf `reach_utc` verdict transcriptions for box %s,'
           % (boxname, root, t7))
        w2('# start-zone subtree rooted at DFS node %s (%d reach-prune leaves).'
           % (root.split('_')[0], len(leaves)))
        w2('')
        w2('Written 2026-11-21 by `m4fix_gen_v1.py` (leaf-only mode) from the per-box')
        w2('reconstruction (`experiments/n8/m4fix_recon_v1.py`, [T 32/32]-verified against')
        w2('both checkpoints and the constructed record `Fresh.M4FixResBank_v1.%s`) and the' % BOX)
        w2('per-prune-leaf verdict dump `experiments/n8/reachutc_%s.json`.  The WHOLE-forest' % boxname)
        w2('transcription of this box is infeasible (%d nodes); this file carries the' % len(nodes))
        w2('OWED (b) verdict layer: per leaf the explored (frontier-sup, dump-rank) state')
        w2('set and pmax as literal data, the `no_completing_state_reachable` verdict')
        w2('(`verdictNoCompl_*`, discharged here by literal per-case proofs over the census')
        w2('windows), the OWED `[P]` projection instance (`reachutcProj_*`, discharged by the')
        w2('parallel `Fresh/ReachUtcProof.lean`), and the verdict-carrying `DfsPruneDom`')
        w2('instances `m4fix_%s_pruneDom_*`.  No existing file is edited.' % boxname)
        w2('-/')
        w2('')
        w2('namespace %s' % NS)
        w2('')
        w2('open Fresh.FilterAssembly Fresh.UClosure Fresh.MechDataBatch Fresh.M4Cert')
        w2('')
        utc_emit_census(w2, BOX, t7, utc_windows_full)
        utc_emit_classes(w2, lstates, utc_windows_full, lhwpass)
        utc_emit_state_lemmas(w2, lstates, lclean, BOX, lhwpass)
        global utc_cur_hwpass
        utc_cur_hwpass = lhwpass
        for r in leaves:
            utc_emit_leaf_block(w2, r, tree_rows[r['node_id']], nodes[r['node_id']], t7,
                                lstates, lclean, BOX, boxname, True)
        w2('')
        w2('end %s' % NS)
        w2('')
        out = os.path.normpath(os.path.join(HERE, '..', '..', 'LonelyRunnerFresh', 'Fresh',
                                            'M4FixRung2_%s_t%s.lean' % (boxname, root)))
        with open(out, 'w') as f:
            f.write('\n'.join(L2) + '\n')
        print('emitted %s (%d lines, %d leaves)' % (out, len(L2), len(leaves)))
        tot += len(leaves)
    print('leaf-only mode: %d subtree files, %d leaves total' % (len(parts), tot))

if __name__ == '__main__':
    boxname0 = sys.argv[1].replace(',', '_')
    _fj = os.path.join(HERE, 'm4fix_forest_%s.json' % boxname0)
    _nnodes = len(json.load(open(_fj))['nodes']) if os.path.exists(_fj) else 0
    if _nnodes > 1000:
        main_leafonly(boxname0)
    else:
        main()
