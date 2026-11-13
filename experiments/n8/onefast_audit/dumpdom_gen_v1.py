# dumpdom_gen_v1.py -- generates Fresh/DumpDomData.lean (the dump-v2 DumpDom instantiation
# for the 11 fully strict-ready boxes) + dumpdom_bridge_mirror_v1.lean (bridge test mirror).
#
# Data: joinedge2_perbox_v1.jsonl (73 records; the 11 census "strict-complete on every
# death row" boxes).  Per row the strict-complete primary witness gives the composed edge
# (y, x, A, B, caps) = (y1-1, x1-1, P, Q, walk caps), each hop dominated (dump dom_box /
# dom_J tags) by a certified table entry.
#
# HONEST SHAPE (rule 22): literal Fresh.CapChainsOfCarve.DumpDom quantifies over ARBITRARY
# realized opening tables U and ALL real chains; the dump certifies domination from the
# box-closure/join entries at the standard opening only.  Literal DumpDom is FALSE (the
# file carries the counterexample theorem not_dumpDom_1_3_4_4_5_5_7).  What is banked is
# the certified-opening restriction: chains opened at uj_<box> (the certified tightening
# of the box closure at the family's hop pairs) have their closed trace dominate every
# record's caps, consuming capChainsRealized_of_domData's trace disjunct verbatim.
#
# New files only; nothing existing is modified.  Exact rationals; floats nowhere.
import json, os
from fractions import Fraction as F

HERE = os.path.dirname(os.path.abspath(__file__))
FRESH = os.path.abspath(os.path.join(HERE, '..', '..', '..', 'LonelyRunnerFresh', 'Fresh'))

READY = [(1,3,4,4,5,5,7),(1,3,4,5,5,5,7),(1,3,4,5,6,6,7),(1,3,4,5,7,7,9),(1,4,4,5,6,6,7),
         (1,4,5,5,5,6,7),(1,4,5,5,6,7,9),(1,4,5,6,6,7,8),(1,5,5,5,6,7,8),(1,5,5,6,6,7,8),
         (1,5,5,6,7,8,8)]

def boxname(b):
    return '_'.join(str(k) for k in b)

def q(v):  # Fraction -> Lean rational literal
    return '(%d/%d : \u211a)' % (v.numerator, v.denominator)

def qcast(v):
    return '((%d/%d : \u211a) : \u211d)' % (v.numerator, v.denominator)

# ---------------- load data ----------------
recs = {}
for l in open(os.path.join(HERE, 'joinedge2_perbox_v1.jsonl')):
    r = json.loads(l); recs[tuple(r['box'])] = r

BOXES = {}
for b in READY:
    r = recs[b]
    U0 = {}
    for e in r['U0_entries']:
        U0[(e[0], e[1])] = (F(e[2]), bool(e[3]))
    assert len(U0) == 49, (b, len(U0))
    pairdom = {}
    rows = []
    for row in r['death_rows']:
        stricts = [c for c in row['caps'] if c['complete_strict']]
        assert stricts, (b, row)
        c0 = stricts[0]
        w = r['witnesses'][str(c0['witness'])]
        hops = w['hops']
        caps = [F(h['value']) for h in hops]
        nodes = [h['v'] for h in hops]
        prod = F(1)
        for c in caps: prod *= c
        assert F(row['P'], row['Q']) * prod <= 1, (b, row)
        for h in hops:
            u, v, val = h['u'], h['v'], F(h['value'])
            cands = []
            if h['dom_J']: cands.append((F(h['dom_J'][2]), bool(h['dom_J'][3]), 'J'))
            if h['dom_box']: cands.append((F(h['dom_box'][2]), bool(h['dom_box'][3]), 'box'))
            assert cands, (b, row, h)
            best = min(cands, key=lambda t: t[0])
            old = pairdom.get((u, v))
            if old is None or best[0] < old[0]:
                pairdom[(u, v)] = best
        rows.append({'kind': row['kind'], 'x1': row['x1'], 'y1': row['y1'],
                     'P': row['P'], 'Q': row['Q'], 'nodes': nodes, 'caps': caps})
    for row in rows:
        cur = row['y1'] - 1
        for v, c in zip(row['nodes'], row['caps']):
            assert pairdom[(cur, v)][0] <= c, (b, row, cur, v)
            cur = v
        assert cur == row['x1'] - 1, (b, row)
    tight = {}
    for (u, v), (val, st, src) in pairdom.items():
        u0v = U0.get((u, v))
        if u0v is None or val < u0v[0]:
            tight[(u, v)] = (val, st, src)
        else:
            assert u0v[0] <= val, (b, (u, v))
    BOXES[b] = {'U0': U0, 'tight': tight, 'pairdom': pairdom, 'rows': rows, 'w0n': r['w0n']}

CBBOX = (1,3,4,4,5,5,7)
cbrow = None
for row in BOXES[CBBOX]['rows']:
    if row['kind'] == 'end' and row['x1'] == 4 and row['y1'] == 1:
        cbrow = row; break
assert cbrow is not None and cbrow['nodes'] == [3] and cbrow['caps'] == [F(7,31)]

def sortkey(row):
    return (row['kind'], row['x1'], row['y1'], row['P'], row['Q'])

_LIMIT = [None]

def fam_rows(b):
    rows = sorted(BOXES[b]['rows'], key=sortkey)
    if b == CBBOX:
        rows = [cbrow] + [r for r in rows if r is not cbrow]
    if _LIMIT[0]:
        rows = rows[:_LIMIT[0]]
    return rows

# ---------------- Lean emitters ----------------
def emit_u0(b):
    name = 'u0_%s' % boxname(b)
    L = ['/-- The box closure `U0` of box (%s): verbatim `joinedge2_perbox_v1.jsonl` `U0_entries`\n'
         '(the `mkp`-style face table: diagonal 1, face_hi `(2n+1)/2` on `(y,0)`, face_lo\n'
         '`2/(2n-1)` and the strict `1` on `(0,y)` (whichever is tighter), ordination `1` on\n'
         '`(y,y+1)`, plus the propagated compositions).  49 entries, exact rationals. -/' %
         ', '.join(str(k) for k in b),
         'def %s : UTable := fun i j =>' % name,
         '  match i.val, j.val with']
    for (u, v) in sorted(BOXES[b]['U0']):
        val, st = BOXES[b]['U0'][(u, v)]
        L.append('  | %d, %d => some (%s, %s)' % (u, v, q(val), 'true' if st else 'false'))
    L.append('  | _, _ => none')
    return '\n'.join(L)

def emit_uj(b):
    name = 'uj_%s' % boxname(b)
    tight = BOXES[b]['tight']
    L = ['/-- The certified opening of box (%s): the box closure tightened at the family\'s hop\n'
         'pairs to the dump\'s certified dominating values (the `dom_J` join-entry value where\n'
         'present, else the `dom_box` closure value; the census verifies `<=` every hop value\n'
         'at its pair).  Mirrors the dump\'s one-sided DFS opening `UJ = U0 (+) J` restricted\n'
         'to the pairs the strict witnesses use. -/' % ', '.join(str(k) for k in b),
         'def %s : UTable := fun i j =>' % name,
         '  match i.val, j.val with']
    for (u, v) in sorted(tight):
        val, st, src = tight[(u, v)]
        L.append('  | %d, %d => some (%s, %s)  -- %s' % (u, v, q(val), 'true' if st else 'false', src))
    L.append('  | _, _ => %s i j' % ('u0_%s' % boxname(b)))
    return '\n'.join(L)

def emit_bnd(b):
    name = 'bnd_%s' % boxname(b)
    return ('/-- The certified-bound function: the certified opening\'s own entry value at each\n'
            'pair (0 = unconstrained). -/\n'
            'def %s : Fin 7 \u2192 Fin 7 \u2192 \u211a := fun i j =>\n'
            '  match %s i j with\n'
            '  | some (c, _) => c\n'
            '  | none => 0' % (name, 'uj_%s' % boxname(b)))

def emit_caps_list(row):
    out = []
    for v, c in zip(row['nodes'], row['caps']):
        out.append('(%d, %s)' % (v, qcast(c)))
    return '[' + ', '.join(out) + ']'

def emit_edge(row):
    return '\u27e8%d, %d, %d, %d, %s\u27e9' % (row['x1'] - 1, row['y1'] - 1, row['P'], row['Q'],
                                              emit_caps_list(row))

def capsB_term(row, b):
    tag = '[bnd_%s, uj_%s, u0_%s]' % (boxname(b), boxname(b), boxname(b))
    depth = len(row['caps'])
    s = 'rfl'
    for i in range(depth - 1, -1, -1):
        s = '\u27e8by norm_num %s, by norm_num %s, %s\u27e9' % (tag, tag, s)
    return s

def emit_fam(b):
    name = 'fam_%s' % boxname(b)
    rows = fam_rows(b)
    total = sum(len(r['caps']) for r in rows)
    note = ''
    if b == CBBOX:
        note = ('  The FIRST edge is the rule-22 falsity witness of `not_dumpDom_%s`\n'
                '(row `end`, x1=4, y1=1, demand 41/15, cap 7/31 at pair (0,3), J-class). -/\n' % boxname(b))
    else:
        note = ' -/\n'
    L = ['/-- The strict-class composed family of box (%s): every death row\'s strict-complete\n'
         'primary witness from `joinedge2_perbox_v1.jsonl` (census: EVERY row of this box is\n'
         'strict-complete), as a `ComposedEdge` `(y1-1, x1-1, P, Q, walk)` carrying the\n'
         'witness\'s cap walk (hop product = the row\'s cap exactly; `P*cap <= Q` datum holds;\n'
         '%d rows, %d hops; w0n=%d chains enumerated).%s' %
         (', '.join(str(k) for k in b), len(rows), total, BOXES[b]['w0n'], note),
         'def %s : ComposedFam :=\n  \u27e8[' % name]
    edges = [emit_edge(r) for r in rows]
    L.append('    ' + ',\n    '.join(edges))
    L.append('  ]\u27e9')
    return '\n'.join(L)

def emit_certbelow(b):
    name = 'certBelow_%s' % boxname(b)
    return ('/-- The certified opening dominates its own certified-bound function. -/\n'
            'theorem %s : CertBelow (bnd_%s) (uj_%s) := by\n'
            '  intro i j hne\n'
            '  cases hj : uj_%s i j with\n'
            '  | none =>\n'
            '    exfalso\n'
            '    simp only [bnd_%s, hj] at hne\n'
            '    exact absurd rfl hne\n'
            '  | some p =>\n'
            '    obtain \u27e8c, s\u27e9 := p\n'
            '    refine \u27e8c, s, rfl, ?_\u27e9\n'
            '    simp only [bnd_%s, hj]\n'
            '    exact le_refl _' % (name, boxname(b), boxname(b), boxname(b), boxname(b), boxname(b)))

def emit_capsB(b):
    name = 'capsB_%s' % boxname(b)
    rows = fam_rows(b)
    L = ['/-- Per-record certified domination: every hop of every record\'s walk is bounded below\n'
         'by the certified value (`CapsB`), i.e. the dump\'s dom_box/dom_J census, kernel-checked. -/',
         'theorem %s : \u2200 e \u2208 (fam_%s).edges, CapsB (bnd_%s) e.caps e.y e.x := by' %
         (name, boxname(b), boxname(b)),
         '  intro e he',
         '  simp only [fam_%s, List.mem_cons] at he' % boxname(b),
         '  rcases he with ' + ' | '.join(['rfl'] * len(rows)) + ' | h0']
    for r in rows:
        L.append('  \u00b7 exact ' + capsB_term(r, b))
    L.append('  \u00b7 exact absurd h0 (by simp)')
    return '\n'.join(L)

def emit_dumpDomData(b):
    nb = boxname(b)
    bstr = ', '.join(str(k) for k in b)
    doc = ('/-- The certified-opening dump-v2 datum of box (%s): for every in-box `g`, every real\n'
           'W\u2080 chain opened at the certified opening `uj_%s` has its closed trace dominate every\n'
           'record\'s caps, hence the family\'s cap chains are realized on `g`\n'
           '(`Fresh.CapChainsOfCarve.capChainsRealized_of_domData`\'s trace disjunct).  This is\n'
           'the certified-opening restriction of `Fresh.CapChainsOfCarve.DumpDom` (which\n'
           'quantifies over arbitrary openings and is FALSE; see `not_dumpDom_%s`). -/\n' % (bstr, nb, nb))
    L = [doc,
         'theorem dumpDomData_%s {g : Fin 7 \u2192 \u211d}' % nb,
         '    (hface : \u2200 i, FaceLo (![%s] : Fin 7 \u2192 \u2124) i \u2264 g i \u2227' % bstr,
         '      g i \u2264 FaceHi (![%s] : Fin 7 \u2192 \u2124) i)' % bstr,
         '    (a : Fin 7) (Aex : \u211a) (steps : List Step)',
         '    (hfine0 : UFine g (uj_%s)) (hchain : ChainRealized g (uj_%s) a Aex steps) :' % (nb, nb),
         '    capChainsRealized g (fam_%s) :=' % nb,
         '  capChainsRealized_of_domData (fam_%s) hface (uj_%s) a Aex steps hfine0 hchain (by' % (nb, nb),
         '    intro e he',
         '    have hpos : ∀ k, 0 < g k := fun k => face_pos hface k',
         '    refine Or.inr (fun V afn Af hrun => ?_)',
         '    exact capsDom_of_capsB (certBelow_chainRun hpos (certBelow_%s) hchain V afn Af hrun)' % nb,
         '      e.caps e.y e.x (capsB_%s e he))' % nb]
    return '\n'.join(L)

ENGINE = r'''/-! ## 1. The certified-bound engine (the data-side vocabulary) -/

/-- The certified-bound datum: at every pair where the bound function `bnd` prescribes a
nonzero bound, the table `U` stores an entry whose value is at most that bound.  This is
the data-side certificate the dump's strict witnesses carry per hop (dom_box / dom_J
values, census-verified `<=` the hop value), lifted to a whole table. -/
-- STANDING: DEFINITION
def CertBelow (bnd : Fin 7 → Fin 7 → ℚ) (U : UTable) : Prop :=
  ∀ i j, bnd i j ≠ 0 → ∃ c₀ : ℚ, ∃ s : Bool, U i j = some (c₀, s) ∧
    ((c₀ : ℚ) : ℝ) ≤ ((bnd i j : ℚ) : ℝ)

/-- The `uTighter` rule always stores SOME entry. -/
theorem uTighter_some {old : UBound} {v : ℚ} {t : Bool} :
    ∃ w : ℚ, ∃ tw : Bool, uTighter (v, t) old = some (w, tw) := by
  cases old with
  | none => exact ⟨v, t, rfl⟩
  | some p =>
    obtain ⟨c₀, s₀⟩ := p
    simp only [uTighter]
    split
    · exact ⟨_, _, rfl⟩
    · exact ⟨_, _, rfl⟩

/-- The `uTighter` rule never increases the stored value. -/
theorem uTighter_le {old : UBound} {v : ℚ} {t : Bool} {c₀ : ℚ} {s₀ : Bool}
    (hold : old = some (c₀, s₀)) :
    ∀ w : ℚ, ∀ tw : Bool, uTighter (v, t) old = some (w, tw) →
      ((w : ℚ) : ℝ) ≤ ((c₀ : ℚ) : ℝ) := by
  intro w tw h
  cases hold
  simp only [uTighter] at h ⊢
  split at h
  · rename_i hc
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨e1, _⟩ := h
    subst e1
    rcases Bool.or_eq_true_iff.mp hc with hv | hand
    · exact le_of_lt (by exact_mod_cast (Bool.of_decide_eq_true hv))
    · have heq : v = c₀ := Bool.of_decide_eq_true (Bool.and_eq_true_iff.mp hand).1
      rw [heq]
      exact le_refl _
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨e1, _⟩ := h
    subst e1
    exact le_refl _

#print axioms uTighter_some
#print axioms uTighter_le

/-- **Certified bounds are preserved by every surviving `add`**: `uAdd` never increases a
stored entry (the `uTighter` replace rule keeps the smaller value) and never deletes one,
so a table dominating `bnd` has its surviving `add` result still dominating `bnd`.  No
constraint on the added bound `c` — the preservation is unconditional. -/
theorem certBelow_uAdd {bnd : Fin 7 → Fin 7 → ℚ} {U : UTable} {i j : Fin 7} {c : ℚ} {s : Bool}
    {V : UTable} (hc : CertBelow bnd U) (h : uAdd U i j c s = some V) : CertBelow bnd V := by
  intro p q hpq
  unfold uAdd at h
  split at h
  · simp only [Option.some.injEq] at h
    subst h
    exact hc p q hpq
  · split at h
    · exact absurd h (by simp)
    · simp only [Option.some.injEq] at h
      subst h
      cases hpi : U p i with
      | none => simp only [uProp, hpi]; exact hc p q hpq
      | some aa =>
        cases hpj : U j q with
        | none => simp only [uProp, hpi, hpj]; exact hc p q hpq
        | some bb =>
          obtain ⟨c₀, s₀, hV, hcle⟩ := hc p q hpq
          obtain ⟨w, tw, hw⟩ := uTighter_some (v := aa.1 * c * bb.1) (t := aa.2 || s || bb.2)
              (old := U p q)
          refine ⟨w, tw, ?_, ?_⟩
          · simp only [uProp, hpi, hpj]
            rw [hV] at hw ⊢
            exact hw
          · exact le_trans (uTighter_le hV w tw hw) hcle

#print axioms certBelow_uAdd

/-- **Certified bounds survive a chain step** (on positive zone numerators, where each
`uGt` is the strict `uAdd` — `uGt_pos`): the step's two `add`s each preserve the
certificate, so the stepped table is again certified. -/
theorem certBelow_uStep {bnd : Fin 7 → Fin 7 → ℚ} {U V : UTable} {a b : Fin 7} {Aex A B₀ : ℚ}
    (hAex : 0 < Aex) (hA : 0 < A) (hB₀ : 0 < B₀)
    (hc : CertBelow bnd U) (h : uStep U a b Aex A B₀ = some V) : CertBelow bnd V := by
  unfold uStep at h
  rw [uGt_pos (U := U) (a := a) (b := b) (A := Aex) (B := A) hAex hA] at h
  cases hb1 : uAdd U a b (Aex / A) true with
  | none => rw [hb1] at h; simp at h
  | some W =>
    rw [hb1] at h
    simp only [Option.bind_some] at h
    rw [uGt_pos (U := W) (a := b) (b := a) (A := B₀) (B := Aex) hB₀ hAex] at h
    exact certBelow_uAdd (certBelow_uAdd hc hb1) h

#print axioms certBelow_uStep

/-- **Certified bounds survive the whole chain run**: the closed trace table of any real
chain (each step's numerators positive, per `ChainRealized`) opened at a certified table
is again certified — the engine behind the trace disjunct of
`Fresh.CapChainsOfCarve.capChainsRealized_of_domData`. -/
theorem certBelow_chainRun {bnd : Fin 7 → Fin 7 → ℚ} {g : Fin 7 → ℝ} {U : UTable}
    {a : Fin 7} {Aex : ℚ} {steps : List Step}
    (hpos : ∀ k, 0 < g k) (hc : CertBelow bnd U) :
    ChainRealized g U a Aex steps → ∀ W : UTable, ∀ af : Fin 7, ∀ Af : ℚ,
      chainRun U a Aex steps = some (W, af, Af) → CertBelow bnd W := by
  induction steps generalizing U a Aex with
  | nil =>
    intro hchain W af Af h
    simp only [ChainRealized] at hchain
    simp only [chainRun, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact hc
  | cons st rest ih =>
    intro hchain W af Af h
    simp only [ChainRealized] at hchain
    obtain ⟨V₀, hstep, hA, hB, sat1, _, hrest⟩ := hchain
    have hci : 0 < (Aex / st.A : ℚ) := bpos_of_holds (div_pos (hpos a) (hpos st.b)) sat1
    have hAex' : 0 < Aex := by
      have h1 : Aex = (Aex / st.A) * st.A := by field_simp
      rw [h1]
      exact mul_pos hci hA
    simp only [chainRun] at h
    rw [hstep] at h
    simp only [Option.bind_some] at h
    exact ih (certBelow_uStep hAex' hA hB hc hstep) hrest W af Af h

#print axioms certBelow_chainRun

/-- The walk-shaped certified domination: each hop's cap is at least the certified bound
of its pair (with the pair certified, i.e. nonzero).  The `CapsDom` mirror of the dump's
per-hop census. -/
-- STANDING: DEFINITION
def CapsB (bnd : Fin 7 → Fin 7 → ℚ) : List (Fin 7 × ℝ) → Fin 7 → Fin 7 → Prop
  | [], y, x => y = x
  | (z, c) :: l, y, x => bnd y z ≠ 0 ∧ ((bnd y z : ℚ) : ℝ) ≤ c ∧ CapsB bnd l z x

/-- Certified walks are dominated walks: a certified trace table realizes every certified
walk as a `CapsDom` chain (each step's stored entry value is squeezed between the
certified bound and the cap). -/
theorem capsDom_of_capsB {bnd : Fin 7 → Fin 7 → ℚ} {V : UTable} (hc : CertBelow bnd V) :
    ∀ (caps : List (Fin 7 × ℝ)) (y x : Fin 7), CapsB bnd caps y x → CapsDom V y caps x := by
  intro caps
  induction caps with
  | nil => intro y x h; cases h; exact CapsDom.nil _
  | cons p l ih =>
    intro y x h
    obtain ⟨hnz, hcap, hrest⟩ := h
    obtain ⟨z, c⟩ := p
    obtain ⟨c₀, s₀, hV, hcle⟩ := hc y z hnz
    exact CapsDom.cons y z c l x ⟨c₀, s₀, hV, le_trans hcle hcap⟩ (ih z x hrest)

#print axioms capsDom_of_capsB
'''

def counterexample_block():
    return r'''/-! ## 3. Rule 22 — literal `DumpDom` is false (the honest residual) -/

/-- The counterexample box (1, 3, 4, 4, 5, 5, 7) as an explicit function (so `simp` reduces
its values). -/
def box134455_7 : Fin 7 → ℤ := fun i =>
  match i.val with
  | 0 => 1 | 1 => 3 | 2 => 4 | 3 => 4 | 4 => 5 | 5 => 5 | 6 => 7 | _ => 0

/-- The counterexample readings: an interior point of the box (kernel-checked in
`not_dumpDom_1_3_4_4_5_5_7`). -/
def gbad_134455_7 : Fin 7 → ℝ := fun i =>
  ((match i.val with
    | 0 => (32 : ℚ) / 25
    | 1 => (13 : ℚ) / 4
    | 2 => (17 : ℚ) / 4
    | 3 => (171 : ℚ) / 40
    | 4 => (9 : ℚ) / 2
    | 5 => (21 : ℚ) / 4
    | 6 => (29 : ℚ) / 4
    | _ => 0 : ℚ) : ℝ)

/-- The all-`none` opening table: realized by ANY readings (all entries vacuous). -/
def uNone : UTable := fun _ _ => none

theorem uNone_fine (g : Fin 7 → ℝ) : UFine g uNone := fun _ _ _ _ hb => absurd hb (by simp [uNone])

#print axioms uNone_fine

/-- The counterexample's one chain step survives on `uNone`: no stored entries means the
keep/back tests fail and the propagation has no paths to compose, so both `uAdd`s return
`some uNone`. -/
theorem uProp_uNone (i j : Fin 7) (c : ℚ) (s : Bool) : uProp uNone i j c s = uNone := by
  funext p q
  simp [uProp, uNone]

theorem uAdd_uNone_none (i j : Fin 7) (c : ℚ) (s : Bool) :
    uAdd uNone i j c s = some uNone := by
  simp [uAdd, uKeepCur, uBack, uNone, uProp_uNone]

theorem uStep_none_none : uStep uNone 3 4 23 23 25 = some uNone := by
  unfold uStep
  rw [uGt_pos (U := uNone) (a := 3) (b := 4) (A := 23) (B := 23) (by norm_num) (by norm_num)]
  simp only [uAdd_uNone_none, Option.bind_some]
  rw [uGt_pos (U := uNone) (a := 4) (b := 3) (A := 25) (B := 23) (by norm_num) (by norm_num)]
  exact uAdd_uNone_none 4 3 (25 / 23) true

#print axioms uStep_none_none

/-- The counterexample chain is REAL: each step's two strict seam bounds and the exit
bound hold at `gbad_134455_7` (kernel-checked), the step survives on `uNone`. -/
theorem chain_bad_134455_7 : ChainRealized gbad_134455_7 uNone 3 23 [⟨4, 23, 25⟩] := by
  refine ⟨uNone, uStep_none_none, by norm_num, by norm_num, ?_, ?_, ?_⟩
  · simp only [BHolds, gbad_134455_7]; push_cast; norm_num
  · simp only [BHolds, gbad_134455_7]; push_cast; norm_num
  · simp only [ChainRealized, BHolds, gbad_134455_7]; push_cast; norm_num

#print axioms chain_bad_134455_7

/-- The counterexample chain's closed trace: `uNone` itself (no entries created). -/
theorem hrun_bad : chainRun uNone 3 23 [⟨4, 23, 25⟩] = some (uNone, (4 : Fin 7), (25 : ℚ)) := by
  simp only [chainRun, uStep_none_none, Option.bind_some]

#print axioms hrun_bad

/-- A `CapsDom` claim against the all-`none` table is absurd at any nonempty walk: the
first hop needs a stored entry. -/
theorem capsDom_uNone_false {y z : Fin 7} {c : ℝ} {l : List (Fin 7 × ℝ)} {x : Fin 7}
    (h : CapsDom uNone y ((z, c) :: l) x) : False := by
  cases h with
  | cons _ _ _ _ _ hentry _ =>
    obtain ⟨_, _, hn, _⟩ := hentry
    simp [uNone] at hn

#print axioms capsDom_uNone_false

/-- The counterexample edge: the family's first record (J-side cap `7/31` at pair `(0,3)`,
demand `41/15`). -/
theorem mem_cb_edge :
    ⟨3, 0, 41, 15, [(3, ((7/31 : ℚ) : ℝ))]⟩ ∈ (fam_1_3_4_4_5_5_7).edges := by
  simp only [fam_1_3_4_4_5_5_7, List.mem_cons]
  exact Or.inl rfl

#print axioms mem_cb_edge

/-- **Rule 22 (the falsity witness).**  Literal `Fresh.CapChainsOfCarve.DumpDom` for the
strict family of box (1, 3, 4, 4, 5, 5, 7) is FALSE: the all-`none` opening `uNone` is
realized by the interior readings `gbad_134455_7`, the one-step chain `chain_bad_134455_7`
is real with closed trace `uNone` (`hrun_bad`), and BOTH of `DumpDom`'s disjuncts fail on
the family's first record — its cap's certifying entries live in the box closure / join
tables, not in an arbitrary opening or a short chain's trace.  The dump's certification
(domination by the box closure or the enumerated join, per hop) is therefore strictly
weaker than the quantifier shape `DumpDom` carries, and the bankable form is the
certified-opening restriction `dumpDomData_*` of this file. -/
theorem not_dumpDom_1_3_4_4_5_5_7 :
    ¬ DumpDom box134455_7 fam_1_3_4_4_5_5_7 := by
  intro h
  have hg : ∀ i, FaceLo box134455_7 i ≤ gbad_134455_7 i ∧
      gbad_134455_7 i ≤ FaceHi box134455_7 i := by
    intro i
    fin_cases i
    all_goals (simp only [FaceLo, FaceHi, box134455_7, gbad_134455_7]; push_cast; norm_num)
  have hsp := h gbad_134455_7 hg uNone 3 23 [⟨4, 23, 25⟩] (uNone_fine _) chain_bad_134455_7
  rcases hsp ⟨3, 0, 41, 15, [(3, ((7/31 : ℚ) : ℝ))]⟩ mem_cb_edge with h1 | h2
  · exact capsDom_uNone_false h1
  · exact capsDom_uNone_false (h2 uNone 4 25 hrun_bad)

#print axioms not_dumpDom_1_3_4_4_5_5_7
'''

def totals_block():
    return r'''/-! ## 4. The strict set and the certified-opening totality (the deliverable) -/

/-- The 11 fully DumpDom-ready boxes (census item 7: every death row of the box carries a
strict-complete cap). -/
def strictSet : Finset (Fin 7 → ℤ) :=
  { (![1, 3, 4, 4, 5, 5, 7] : Fin 7 → ℤ), (![1, 3, 4, 5, 5, 5, 7] : Fin 7 → ℤ),
    (![1, 3, 4, 5, 6, 6, 7] : Fin 7 → ℤ), (![1, 3, 4, 5, 7, 7, 9] : Fin 7 → ℤ),
    (![1, 4, 4, 5, 6, 6, 7] : Fin 7 → ℤ), (![1, 4, 5, 5, 5, 6, 7] : Fin 7 → ℤ),
    (![1, 4, 5, 5, 6, 7, 9] : Fin 7 → ℤ), (![1, 4, 5, 6, 6, 7, 8] : Fin 7 → ℤ),
    (![1, 5, 5, 5, 6, 7, 8] : Fin 7 → ℤ), (![1, 5, 5, 6, 6, 7, 8] : Fin 7 → ℤ),
    (![1, 5, 5, 6, 7, 8, 8] : Fin 7 → ℤ) }

/-- The certified opening per strict box. -/
def ujOf (b : Fin 7 → ℤ) : UTable :=
  if b = (![1, 3, 4, 4, 5, 5, 7] : Fin 7 → ℤ) then uj_1_3_4_4_5_5_7
  else if b = (![1, 3, 4, 5, 5, 5, 7] : Fin 7 → ℤ) then uj_1_3_4_5_5_5_7
  else if b = (![1, 3, 4, 5, 6, 6, 7] : Fin 7 → ℤ) then uj_1_3_4_5_6_6_7
  else if b = (![1, 3, 4, 5, 7, 7, 9] : Fin 7 → ℤ) then uj_1_3_4_5_7_7_9
  else if b = (![1, 4, 4, 5, 6, 6, 7] : Fin 7 → ℤ) then uj_1_4_4_5_6_6_7
  else if b = (![1, 4, 5, 5, 5, 6, 7] : Fin 7 → ℤ) then uj_1_4_5_5_5_6_7
  else if b = (![1, 4, 5, 5, 6, 7, 9] : Fin 7 → ℤ) then uj_1_4_5_5_6_7_9
  else if b = (![1, 4, 5, 6, 6, 7, 8] : Fin 7 → ℤ) then uj_1_4_5_6_6_7_8
  else if b = (![1, 5, 5, 5, 6, 7, 8] : Fin 7 → ℤ) then uj_1_5_5_5_6_7_8
  else if b = (![1, 5, 5, 6, 6, 7, 8] : Fin 7 → ℤ) then uj_1_5_5_6_6_7_8
  else if b = (![1, 5, 5, 6, 7, 8, 8] : Fin 7 → ℤ) then uj_1_5_5_6_7_8_8
  else fun _ _ => none

/-- The strict family per strict box. -/
def famOf (b : Fin 7 → ℤ) : ComposedFam :=
  if b = (![1, 3, 4, 4, 5, 5, 7] : Fin 7 → ℤ) then fam_1_3_4_4_5_5_7
  else if b = (![1, 3, 4, 5, 5, 5, 7] : Fin 7 → ℤ) then fam_1_3_4_5_5_5_7
  else if b = (![1, 3, 4, 5, 6, 6, 7] : Fin 7 → ℤ) then fam_1_3_4_5_6_6_7
  else if b = (![1, 3, 4, 5, 7, 7, 9] : Fin 7 → ℤ) then fam_1_3_4_5_7_7_9
  else if b = (![1, 4, 4, 5, 6, 6, 7] : Fin 7 → ℤ) then fam_1_4_4_5_6_6_7
  else if b = (![1, 4, 5, 5, 5, 6, 7] : Fin 7 → ℤ) then fam_1_4_5_5_5_6_7
  else if b = (![1, 4, 5, 5, 6, 7, 9] : Fin 7 → ℤ) then fam_1_4_5_5_6_7_9
  else if b = (![1, 4, 5, 6, 6, 7, 8] : Fin 7 → ℤ) then fam_1_4_5_6_6_7_8
  else if b = (![1, 5, 5, 5, 6, 7, 8] : Fin 7 → ℤ) then fam_1_5_5_5_6_7_8
  else if b = (![1, 5, 5, 6, 6, 7, 8] : Fin 7 → ℤ) then fam_1_5_5_6_6_7_8
  else if b = (![1, 5, 5, 6, 7, 8, 8] : Fin 7 → ℤ) then fam_1_5_5_6_7_8_8
  else ⟨[]⟩

/-- **The certified-opening totality (deliverable)**: for every box in `strictSet`, every
in-box arrangement admitting a real W₀ chain OPENED AT THE CERTIFIED OPENING realizes the
box's whole strict family.  This is the certified-opening restriction of the (false,
rule-22) shape `∀ b ∈ strictSet, DumpDom b (famOf b)`; see
`not_dumpDom_1_3_4_4_5_5_7` for why the unrestricted quantifier cannot hold. -/
theorem dumpDomTotalCert : ∀ b ∈ strictSet, ∀ g : Fin 7 → ℝ,
    (∀ i, FaceLo b i ≤ g i ∧ g i ≤ FaceHi b i) → ∀ a : Fin 7, ∀ Aex : ℚ, ∀ steps : List Step,
    UFine g (ujOf b) → ChainRealized g (ujOf b) a Aex steps → capChainsRealized g (famOf b) := by
  intro b hb g hface a Aex steps hfine0 hchain
  simp only [strictSet, Finset.mem_insert, Finset.mem_singleton] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simp only [ujOf, famOf]
    exact dumpDomData_1_3_4_4_5_5_7 hface a Aex steps hfine0 hchain
  · simp only [ujOf, famOf]
    exact dumpDomData_1_3_4_5_5_5_7 hface a Aex steps hfine0 hchain
  · simp only [ujOf, famOf]
    exact dumpDomData_1_3_4_5_6_6_7 hface a Aex steps hfine0 hchain
  · simp only [ujOf, famOf]
    exact dumpDomData_1_3_4_5_7_7_9 hface a Aex steps hfine0 hchain
  · simp only [ujOf, famOf]
    exact dumpDomData_1_4_4_5_6_6_7 hface a Aex steps hfine0 hchain
  · simp only [ujOf, famOf]
    exact dumpDomData_1_4_5_5_5_6_7 hface a Aex steps hfine0 hchain
  · simp only [ujOf, famOf]
    exact dumpDomData_1_4_5_5_6_7_9 hface a Aex steps hfine0 hchain
  · simp only [ujOf, famOf]
    exact dumpDomData_1_4_5_6_6_7_8 hface a Aex steps hfine0 hchain
  · simp only [ujOf, famOf]
    exact dumpDomData_1_5_5_5_6_7_8 hface a Aex steps hfine0 hchain
  · simp only [ujOf, famOf]
    exact dumpDomData_1_5_5_6_6_7_8 hface a Aex steps hfine0 hchain
  · simp only [ujOf, famOf]
    exact dumpDomData_1_5_5_6_7_8_8 hface a Aex steps hfine0 hchain

#print axioms dumpDomTotalCert
'''

# ---------------- Fresh-span extraction for the bridge mirror ----------------
def span(path, start_marker, end_marker, include_end=True):
    s = open(path).read()
    i = s.index(start_marker)
    j = s.index(end_marker, i)
    if include_end:
        j = j + len(end_marker)
    return s[i:j]

def build_mirror():
    _LIMIT[0] = 14  # keep the mirror under the bridge's 120s: all tactic forms still exercised
    uc = os.path.join(FRESH, 'UClosureKill.lean')
    jf = os.path.join(FRESH, 'JoinFamComposed.lean')
    og = os.path.join(FRESH, 'OneSidedGlue.lean')
    cc = os.path.join(FRESH, 'CapChainsOfCarve.lean')
    fa = os.path.join(FRESH, 'FilterAssembly.lean')
    faces = span(fa, '/-- The per-coordinate raw-box face', 'noncomputable def FaceHi (n : Fin 7 → ℤ) (i : Fin 7) : ℝ := ((2 * n i + 1 : ℤ) : ℝ) / 2')
    ucspan = span(uc, 'namespace Fresh.UClosure', '#print axioms chain_fine_of_realized')
    ucspan = ucspan.replace('open Fresh.FilterAssembly Fresh.KTaxonomy', 'open Fresh.FilterAssembly')
    ucspan += '\nend Fresh.UClosure\n'
    jspan = (span(jf, 'inductive ChainReal (g : Fin 7 → ℝ)',
                  '(hrest : ChainReal g v l w) : ChainReal g u ((v, c) :: l) w') + '\n\n'
             + span(jf, '/-- One composed record:',
                    'structure ComposedEdge where\n  x : Fin 7\n  y : Fin 7\n  A : ℤ\n  B : ℤ\n  caps : List (Fin 7 × ℝ)') + '\n'
             + span(jf, '/-- The walk end of a cap chain',
                    'caps.foldl (fun _ p => p.1) y') + '\n\n'
             + span(jf, '/-- Datum-level validity',
                    'def ComposedFamData (f : ComposedFam) : Prop := ∀ e ∈ f.edges, ComposedEdgeValid e'))
    sp = os.path.join(FRESH, 'SpineSound.lean')
    sspan = span(sp, '/-- The box faces are positive', '#print axioms face_pos')
    ospan = span(og, '-- STANDING: DEFINITION\ndef capChainsRealized', 'def capChainsRealized (g : Fin 7 → ℝ) (f : ComposedFam) : Prop :=\n  ∀ e ∈ f.edges, ChainReal g e.y e.caps e.x')
    cspan1 = span(cc, 'inductive CapsDom', '#print axioms chainReal_of_capsDom')
    cspan2 = span(cc, '/-- The faithful two-sided form', '#print axioms capChainsRealized_of_domData')
    cspan3 = span(cc, '-- STANDING: OWED', 'chainRun U a Aex steps = some (V, af, Af) \u2192 CapsDom V e.y e.caps e.x)')
    parts = ['import Mathlib\n']
    parts.append('namespace Fresh.FilterAssembly\n' + faces + '\nend Fresh.FilterAssembly\n')
    parts.append(ucspan)
    parts.append('namespace Fresh.SpineSound\nopen Fresh.FilterAssembly\n' + sspan + '\nend Fresh.SpineSound\n')
    parts.append('namespace Fresh.JoinFamComposed\n' + jspan + '\nend Fresh.JoinFamComposed\n')
    parts.append('namespace Fresh.OneSidedGlue\nopen Fresh.JoinFamComposed\n' + ospan + '\nend Fresh.OneSidedGlue\n')
    parts.append('namespace Fresh.CapChainsOfCarve\nopen Fresh.FilterAssembly Fresh.SpineSound Fresh.JoinFamComposed Fresh.OneSidedGlue Fresh.UClosure\n'
                 + cspan1 + '\n' + cspan2 + '\n' + cspan3 + '\nend Fresh.CapChainsOfCarve\n')
    parts.append('open Fresh.UClosure Fresh.JoinFamComposed Fresh.OneSidedGlue Fresh.CapChainsOfCarve Fresh.FilterAssembly Fresh.SpineSound\n')
    parts.append(ENGINE)
    blocks = []
    for mb in [MBOX, CBBOX]:
        blocks += [emit_u0(mb), emit_uj(mb), emit_bnd(mb),
                   emit_certbelow(mb) + '\n\n#print axioms certBelow_%s' % boxname(mb),
                   emit_fam(mb), emit_capsB(mb) + '\n\n#print axioms capsB_%s' % boxname(mb),
                   emit_dumpDomData(mb) + '\n\n#print axioms dumpDomData_%s' % boxname(mb)]
    parts.append('\n' + '\n\n'.join(blocks))
    parts.append('\n' + counterexample_block())
    return '\n'.join(parts)

MBOX = (1, 5, 5, 6, 7, 8, 8)  # mirror box: 146 rows, all 1-hop

if __name__ == '__main__':
    mirror = build_mirror()
    open(os.path.join(HERE, 'dumpdom_bridge_mirror_v1.lean'), 'w').write(mirror)
    print('mirror lines:', mirror.count('\n'))
    for b in BOXES:
        print(boxname(b), 'rows=%d tight=%d' % (len(BOXES[b]['rows']), len(BOXES[b]['tight'])))

