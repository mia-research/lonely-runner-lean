# chaindom_emit_v1.py -- emits LonelyRunnerFresh/Fresh/ChainDomData.lean from
# chaindom_data_v3.json (the transcribed-trace-table data for the 3 sparse-start boxes).
# Usage: python3 -I chaindom_emit_v1.py [nboxes]   (default all 3; bring-up: 1 = box 3 only)
import os, sys, json

HERE = os.path.dirname(os.path.abspath(__file__))
D = json.load(open(os.path.join(HERE, 'chaindom_data_v3.json')))

ORDER = ['1_3_4_4_5_5_7', '1_3_4_5_6_6_7', '1_4_4_5_6_6_7']
BOX_LIT = {
    '1_3_4_4_5_5_7': '![1, 3, 4, 4, 5, 5, 7]',
    '1_3_4_5_6_6_7': '![1, 3, 4, 5, 6, 6, 7]',
    '1_4_4_5_6_6_7': '![1, 4, 4, 5, 6, 6, 7]',
}

def q(s):
    # '17/39' -> '(17 / 39 : ℚ)'; '1' -> '(1 : ℚ)'
    if '/' in s:
        a, b = s.split('/')
        return '(%s / %s : ℚ)' % (a, b)
    return '(%s : ℚ)' % s

def rtab(name, entries):
    # entries: list of [p, q, 'num/den', bool]
    L = ['-- transcribed trace table: %s (the mirror run\'s step-end snapshot)' % name]
    L.append('def %s : UTable := fun p q =>' % name)
    es = sorted(entries, key=lambda e: (e[0], e[1]))
    for k, (p, qq, v, s) in enumerate(es):
        cond = 'if p = (%d : Fin 7) ∧ q = (%d : Fin 7) then some (%s, %s)' % (p, qq, q(v), 'true' if s else 'false')
        L.append('  %s %s' % ('' if k == 0 else 'else ', cond))
    L.append('  else none')
    return '\n'.join(L)

def emit_box(name, b, L):
    nA = len(b['adds'])
    nT = len(b['steps'])
    BASE = '(u0Of (%s : Fin 7 → ℤ))' % BOX_LIT[name]
    # cur[t] = the table NAME after add t (keep-adds reuse; prop-adds get a new literal)
    cur = [BASE]
    pti = 0
    for ad in b['adds']:
        if ad['kind'] == 'keep':
            cur.append(cur[-1])
        else:
            pti += 1
            cur.append('T_%s_%d' % (name, pti))
    P = pti
    Tfinal = cur[-1]
    # steps def
    L.append('/-- The attesting chain for box (%s) as `Fresh.UClosure.Step` literals '
             '(chain index %d of the box\'s dump enumeration, word length %d): each step is '
             'the zone triple `(b, Bn, Ax)` = `(row, entry edge 8j-1, exit edge 8j+1)`. -/' %
             (b['box'], b['chain_index'], b['word_len']))
    L.append('def steps_%s : List Step := [' % name)
    L.append(', '.join('⟨(%d : Fin 7), (%d : ℚ), (%d : ℚ)⟩' % (bb, Bn, Ax) for (bb, Bn, Ax) in b['steps']))
    L.append(']')
    L.append('')
    # the P literal tables (one per PROP add)
    for pi in range(1, P + 1):
        L.append(rtab('T_%s_%d' % (name, pi), [e for row in b['ptables'][pi - 1] for e in row]))
        L.append('')
    # addEq theorems
    for t, ad in enumerate(b['adds'], 1):
        TS = 'u0Of, u0Tab_%s' % name if t == 1 else cur[t - 1]
        kk = (t - 1) // 2  # 0-based step index
        if t % 2 == 1:
            aprev = b['steps'][kk - 1][0] if kk >= 1 else 0
            Aexprev = b['steps'][kk - 1][2] if kk >= 1 else 1
            cstr = '((%d : ℚ) / (%d : ℚ))' % (Aexprev, b['steps'][kk][1])
            iarg, jarg = aprev, b['steps'][kk][0]
        else:
            bb2, Bn2, Ax2 = b['steps'][kk]
            aprev = b['steps'][kk - 1][0] if kk >= 1 else 0
            Aexprev = b['steps'][kk - 1][2] if kk >= 1 else 1
            cstr = '((%d : ℚ) / (%d : ℚ))' % (Ax2, Aexprev)
            iarg, jarg = bb2, aprev
        if ad['kind'] == 'keep':
            L.append('/-- Add %d of the attesting chain: the entry at its pair is already '
                     'tight (`uKeepCur` fires ground-true), so the table is unchanged. -/' % t)
            L.append('theorem addEq_%d_%s : uAdd %s (%d : Fin 7) (%d : Fin 7) %s true '
                     '= some %s := by '
                     'simp [uAdd, uKeepCur, uBackCond, uBack, uTighter, uProp, %s] <;> norm_num'
                     % (t, name, cur[t - 1], iarg, jarg, cstr, cur[t], TS))
            L.append('')
        else:
            L.append('/-- Add %d of the attesting chain: keep-cur and back are ground-false and '
                     'the propagated result IS the next transcribed table (49 concrete '
                     'pointwise checks). -/' % t)
            L.append('theorem addEq_%d_%s : uAdd %s (%d : Fin 7) (%d : Fin 7) %s true '
                     '= some %s :=' % (t, name, cur[t - 1], iarg, jarg, cstr, cur[t]))
            L.append('  uAdd_eq_some (by simp [uKeepCur, uBackCond, %s] <;> norm_num) '
                     '(by simp [uBack, uBackCond, %s] <;> norm_num)' % (TS, TS))
            L.append('    (by intro p q; fin_cases p <;> fin_cases q <;> simp [uProp, uTighter, %s, %s] <;> norm_num)'
                     % (TS, cur[t]))
            L.append('')
    # stepEq theorems (uStep-level assembly from the two addEqs)
    for k in range(1, nT + 1):
        (bb, Bn, Ax) = b['steps'][k - 1]
        aprev = b['steps'][k - 2][0] if k >= 2 else 0
        Aexprev = b['steps'][k - 2][2] if k >= 2 else 1
        Uarg = cur[2 * k - 2] if k >= 2 else BASE
        Aexarg = '(%d : ℚ)' % Aexprev
        L.append('/-- Step %d of the attesting chain: the two adds compose through `uGt_pos`. -/' % k)
        L.append('theorem stepEq_%d_%s : uStep %s (%d : Fin 7) (%d : Fin 7) %s (%d : ℚ) (%d : ℚ) '
                 '= some %s := '
                 % (k, name, Uarg, aprev, bb, Aexarg, Bn, Ax, cur[2 * k]))
        L.append('  uStep_eq_some (by norm_num) (by norm_num) (by norm_num) '
                 '(addEq_%d_%s) (addEq_%d_%s)' % (2 * k - 1, name, 2 * k, name))
        L.append('')
    # trace theorem
    L.append('/-- The extraction: whatever table the chain run produces from `u0Of`, it IS the '
             'last transcribed one (the per-step `stepEq` equations pin every intermediate). -/')
    L.append('theorem trace_%s {V : UTable} {af : Fin 7} {Af : ℚ} ' % name)
    L.append('    (hrun : chainRun (u0Of (%s : Fin 7 → ℤ)) 0 1 steps_%s = some (V, af, Af)) : ' %
             (BOX_LIT[name], name))
    L.append('    V = %s := by' % Tfinal)
    L.append('  simp only [steps_%s, chainRun] at hrun' % name)
    for k in range(1, nT + 1):
        L.append('  rw [stepEq_%d_%s] at hrun' % (k, name))
        L.append('  simp only [Option.bind_some] at hrun')
    L.append('  simp only [Option.some.injEq, Prod.mk.injEq] at hrun')
    L.append('  exact hrun.1.symm')
    L.append('')
    # chainDom theorem
    recs = b['records']  # [x, y, P, Q, cap]
    L.append('/-- **The per-chain J-carrier datum for box (%s)**: `ChainDomData` at the '
             'attesting chain `steps_%s` -- exactly the missing hypothesis of '
             '`Fresh.DumpDomData.capChainsRealized_of_chainDomU0` at the fixed start '
             '`(a, Aex) = (0, 1)`.  Every record\'s singleton cap walk is dominated by the '
             'attesting chain\'s closed-trace entry at its pair (final trace values: %s; '
             'caps: %s). -/' % (b['box'], name,
                                ', '.join('(%s)=%s' % (k, v[0]) for k, v in sorted(b['finals'].items())),
                                ', '.join('(%s)=%s' % (k, v) for k, v in sorted(b['caps'].items()))))
    L.append('theorem chainDom_%s : ' % name)
    L.append('    ChainDomData (%s : Fin 7 → ℤ) compFam_%s where' % (BOX_LIT[name], name))
    L.append('  steps := steps_%s' % name)
    L.append('  dom := by')
    L.append('    intro e he V af Af hrun')
    L.append('    have hV := trace_%s hrun' % name)
    L.append('    rw [hV]')
    L.append('    simp only [compFam_%s, List.mem_cons] at he' % name)
    n = len(recs)
    rc = ' | '.join(['rfl'] * n) + ' | h0'
    L.append('    rcases he with %s' % rc)
    for (x, y, P2, Qv, cap) in recs:
        val, sflag = b['finals']['%d,%d' % (y, x)]
        L.append('    · exact capsDom_single ⟨%s, %s, by simp [%s], by norm_num⟩' %
                 (q(val), 'true' if sflag else 'false', Tfinal))
    L.append('    · exact absurd h0 (by simp)')
    L.append('')
    L.append('#print axioms trace_%s' % name)
    L.append('#print axioms chainDom_%s' % name)
    L.append('')

def main():
    nb = int(sys.argv[1]) if len(sys.argv) > 1 else 3
    boxes = ORDER[:nb]
    L = []
    L.append('import Fresh.DumpDomData')
    L.append('')
    L.append('/-!')
    L.append('# ChainDomData: the per-chain J-carrier datum for the corrected OneSided consumption')
    L.append('')
    L.append('Written 2026-11-14.  New file; nothing existing is edited.  This instantiates the')
    L.append('chain-side domination datum whose EXACT shape is the missing hypothesis of')
    L.append('`Fresh.DumpDomData.capChainsRealized_of_chainDomU0` (the corrected consumption of')
    L.append('the joinedge2 dump-v2 J-half, after `Fresh.DumpDomData` proved both `DumpDom` and')
    L.append('`DumpDomU0` uninstantiable for the 11 strict families): for a box `n`, a composed')
    L.append('family `f`, and the box\'s ATTESTING W0 chain `steps`, every record\'s cap walk is')
    L.append('dominated by an entry of whatever table `chainRun (u0Of n) 0 1 steps` produces --')
    L.append('the consumed chain\'s own closed-trace domination at the U0-fixed start.')
    L.append('')
    L.append('## Method: the transcribed-trace-table pattern')
    L.append('')
    L.append('The kernel cannot evaluate the `uMk` fold or a 19-20-step `chainRun` directly (the')
    L.append('ℚ products normalize through `Nat.gcd`, well-founded and kernel-hostile at fold')
    L.append('depth).  Instead (a) the attesting chain\'s run from the SPARSE `u0Of` start')
    L.append('`(a, Aex) = (0, 1)` is recomputed outside Lean by the verified value-verbatim')
    L.append('mirror of `Fresh.UClosureKill`\'s `uKeepCur`/`uBack`/`uProp`/`uAdd`/`uGt`/`uStep`')
    L.append('(`experiments/n8/onefast_audit/chaindom_gen_v1.py`--`v3.py`: it reproduces the')
    L.append('dump\'s `chains_enumerated`, `jprov` and `join_domination_all_chains` on all 11')
    L.append('strict boxes, and every pre-end table of the full-start enumeration), and the')
    L.append('step-end tables are transcribed as `UTable` literals `T_*_1..T_*_T`; (b) each step')
    L.append('is proven IN the kernel by `rfl` (`stepEq_*_k`: one `uStep` = two `uAdd`s on')
    L.append('literals -- no deep folds); (c) the generated extraction peels the hypothesis')
    L.append('`chainRun (u0Of n) 0 1 steps = some (V, af, Af)` with')
    L.append('`Option.bind_eq_some_iff` + `Fresh.UClosureKill.uStep_some_add`-shaped rewriting,')
    L.append('pinning `V = T_*_T`; (d) `CapsDom` then follows from `capsDom_single` on the')
    L.append('literal final entries (`norm_num` on the exact cap comparisons).')
    L.append('')
    L.append('## Coverage (honest)')
    L.append('')
    L.append('Instantiated [T 3/3]: boxes (1,3,4,4,5,5,7), (1,3,4,5,6,6,7), (1,4,4,5,6,6,7) --')
    L.append('exactly the strict boxes where a SINGLE enumerated chain run from the sparse U0')
    L.append('dominates every banked record (powered check over all 1176/480/896 enumerated')
    L.append('chains).  Rule-22 residual: the other 8 strict boxes have NO single sparse-start')
    L.append('dominator (their records are dominated only from the FULL box closure `mk n`,')
    L.append('whose fold is not kernel-transcribable into the read-only `u0Of`); they need a')
    L.append('richer U0 vocabulary (a transcribed full-closure table) and are honestly left out.')
    L.append('')
    L.append('All arithmetic is exact (`norm_num` on integers/rationals; floats nowhere).  Every')
    L.append('theorem carries `#print axioms`; the accepted profile is the standard three')
    L.append('(propext, Classical.choice, Quot.sound) -- `sorryAx` is failure.')
    L.append('-/')
    L.append('')
    L.append('namespace Fresh.ChainDomData')
    L.append('')
    L.append('open Fresh.UClosure Fresh.CapChainsOfCarve Fresh.DumpDomData Fresh.OneSidedComposed')
    L.append('  Fresh.JoinFamComposed Fresh.OneSidedGlue Fresh.FilterAssembly')
    L.append('')
    L.append('-- the 49-point `fin_cases` checks and the big literal tables need headroom')
    L.append('set_option maxHeartbeats 4000000')
    L.append('')
    L.append('/-- **THE datum** (exactly the missing hypothesis of')
    L.append('`Fresh.DumpDomData.capChainsRealized_of_chainDomU0`, at the fixed chain start')
    L.append('`(a, Aex) = (0, 1)` and the datum\'s own attesting chain `steps`): every record\'s')
    L.append('cap walk is dominated by the closed-trace table of the chain run from `u0Of n`. -/')
    L.append('structure ChainDomData (n : Fin 7 → ℤ) (f : ComposedFam) where')
    L.append('  steps : List Step')
    L.append('  dom : ∀ e ∈ f.edges, ∀ V : UTable, ∀ af : Fin 7, ∀ Af : ℚ,')
    L.append('    chainRun (u0Of n) 0 1 steps = some (V, af, Af) → CapsDom V e.y e.caps e.x')
    L.append('')
    L.append('/-- The consumption, verbatim: the datum drops into the corrected conditional (the')
    L.append('chain `g` admits must BE the attesting chain -- the per-chain disjunctive form of')
    L.append('the dump\'s chain-attained class). -/')
    L.append('theorem chainDomData_capChains {n : Fin 7 → ℤ} {f : ComposedFam} (d : ChainDomData n f)')
    L.append('    {g : Fin 7 → ℝ} (hface : ∀ i, FaceLo n i ≤ g i ∧ g i ≤ FaceHi n i)')
    L.append('    (hfine0 : UFine g (u0Of n)) (hchain : ChainRealized g (u0Of n) 0 1 d.steps) :')
    L.append('    capChainsRealized g f :=')
    L.append('  capChainsRealized_of_chainDomU0 f hface 0 1 d.steps hfine0 hchain d.dom')
    L.append('')
    L.append('#print axioms chainDomData_capChains')
    L.append('')
    L.append('/-- Assembly: a surviving `uAdd` whose keep-cur and back checks are ground-false')
    L.append('returns its propagation, and the propagated table is the transcribed one pointwise.')
    L.append('(The per-point facts are ground -- concrete `Fin 7` pairs, literal ℚ comparisons.) -/')
    L.append('theorem uAdd_eq_some {U V : UTable} {i j : Fin 7} {c : ℚ} {s : Bool}')
    L.append('    (hK : uKeepCur U i j c s = false) (hB : uBack U i j c s = false)')
    L.append('    (hpt : ∀ p q, uProp U i j c s p q = V p q) :')
    L.append('    uAdd U i j c s = some V := by')
    L.append('  unfold uAdd')
    L.append('  rw [if_neg (by simp [hK]), if_neg (by simp [hB])]')
    L.append('  exact congrArg some (funext fun p => funext fun q => hpt p q)')
    L.append('')
    L.append('#print axioms uAdd_eq_some')
    L.append('')
    L.append('/-- Assembly: a `uStep` on positive numerators is its two `uAdd`s (`uGt_pos`), so the')
    L.append('two per-add facts compose to the step equation. -/')
    L.append('theorem uStep_eq_some {U V W : UTable} {a b : Fin 7} {Aex A B : ℚ}')
    L.append('    (hAex : 0 < Aex) (hA : 0 < A) (hB : 0 < B)')
    L.append('    (h1 : uAdd U a b (Aex / A) true = some V) (h2 : uAdd V b a (B / Aex) true = some W) :')
    L.append('    uStep U a b Aex A B = some W := by')
    L.append('  show (uGt U Aex a A b).bind (fun V => uGt V B b Aex a) = some W')
    L.append('  rw [uGt_pos U a b hAex hA, h1, Option.bind_some, uGt_pos V b a hB hAex, h2]')
    L.append('')
    L.append('#print axioms uStep_eq_some')
    L.append('')
    for name in boxes:
        emit_box(name, D[name], L)
    # total
    L.append('/-- The covered set: the 3 strict boxes carrying the datum. -/')
    L.append('def chainDomBoxes : Finset (Fin 7 → ℤ) :=')
    L.append('  {%s}' % ', '.join('(%s : Fin 7 → ℤ)' % BOX_LIT[name] for name in boxes))
    L.append('')
    L.append('/-- **The total over the covered set** (the deliverable totality, over the boxes the')
    L.append('datum exists for; the 8 residual strict boxes are the documented rule-22 gap). -/')
    L.append('theorem chainDomTotalData : ∀ b ∈ chainDomBoxes, ChainDomData b (compFamOf b) := by')
    L.append('  intro b hb')
    L.append('  simp only [chainDomBoxes, Finset.mem_insert, Finset.mem_singleton] at hb')
    rc = ' | '.join(['rfl'] * len(boxes))
    L.append('  rcases hb with %s' % rc)
    for name in boxes:
        L.append('  · simp [compFamOf, chainDom_%s]' % name)
    L.append('')
    L.append('#print axioms chainDomTotalData')
    L.append('')
    L.append('end Fresh.ChainDomData')
    L.append('')
    out = '/Users/trentpalelei/Desktop/Math Ex/LonelyRunnerFresh/Fresh/ChainDomData.lean'
    open(out, 'w').write('\n'.join(L))
    print('wrote %s (%d lines)' % (out, len(L)))

if __name__ == '__main__':
    main()
