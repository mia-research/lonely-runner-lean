#!/usr/bin/env python3
"""bandrep_offplane_gen_v1.py -- the OFF-PLANE tranche emitter (Track B, sub-
deliverable B): the 1,018 h3 side regions of tail_h3_offplane_dump_v1.jsonl as
`SideWindowCertV` records (schema class 6 of BandCertData6).

Sibling of bandrep_gen_v1.py (E916's inventory: the 1,018 off-plane regions are
emission-ready as the VERTEX-form certificates; the interval-hull form fails 29/33).
Nothing existing is edited.

## What is verified data-side before anything is emitted (exact Fractions)

Per region (box = the D = 512 cell `n = [n0..n5]` over rho_2..rho_7, rho_1 = 1
pinned; region = the closed half-cell `cell ∩ {side}` of the h3 plane
`25·rho_7 = 89·rho_5`):

  1. The 15 recorded inequality pairs are parsed with the instrument's convention
     (pair ((A,s),(B,t)) means A·u[t] ≤ B·u[s], u[None] = 1) and asserted to have the
     five SideWindowCertV family shapes; from them: na, ka, nb, kb and the laps
     `(8j_i+1)` per reading.
  2. The Lean families hv1..hv5 (SideWindowCertV's fields, Lean indices = artifact+1,
     j_0 = 0 for the pinned ρ1) are verified on the FULL SideVertex set of the parent
     cell with the region's plane vector:
       - 64 box corners with linForm ≤ 0 (SideVertex case 1),
       - the plane crossings of the box's edges in the two plane coordinates
         (SideVertex case 2 with interior index in {s,t}; 32 corner-assignments each),
       - case-2 points with interior index outside {s,t} hold automatically: the
         plane vector vanishes on that coordinate, so each family is constant along
         the edge segment and its endpoints are checked corners.
     SideVertex is exactly the vertex set of `{faces ∧ side ≤ 0}` and the families
     are linear, so their verification there makes each family a linear consequence
     of faces + side — what the per-region `linarith` proofs consume.
  3. CROSS-CHECK: the 15 recorded pairs are re-verified on the same vertex set
     (my set ⊆ the instrument's region vertices, so this must pass; a failure is a
     convention bug, not a data finding).

## Emission (per verified box, two regions)

  offBox<n>Lo/Hi  the parent cell faces (ρ1 pinned to the point 1)
  offj<n><s>      the seven gap indices (j 0 = 0)
  offBox<n>FaceV  the 12 literal face bounds of a side vertex (+ the pinned v 0 = 1)
  offc<n><s>      the SideWindowCertV record (hv1..hv5 by linarith over the faces,
                  the side, and the pinned ρ1 — the swc3739 pattern)
  offbox<n><s>_swv / _noCarve       per-region consumption (schema class 6 / NoCarve)
  offbox<n>_swv / _noCarve          per-box discharge (the two closed sides cover the
                                    cell — `sideRegions_cover_closed`'s data shape)
and per chunk a totality theorem over a right-nested box disjunction (maxRecDepth
discipline: per-chunk grouping, `set_option maxRecDepth 800000 in`).  The grand file
composes the 509-box tranche totality and states the schema-6 slice:
`bandCertData6_offplane_slice : (box disjunction) → BandSideWindowV g` — the
hypothesis-carrying instance feeding BandCertData6 (the bandPinch_tranche_discharged
pattern; the band-wide covering claim stays data-side, as E916 recorded).
"""
import json, os, sys, time
from fractions import Fraction as F
from itertools import product

N8 = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(N8))
FRESH = os.path.join(ROOT, "LonelyRunnerFresh", "Fresh")

H3MINUS = (6, 4, 25, 89)   # pairL 6 4 25 89: 25·ρ7 - 89·ρ5 ≤ 0  (hval ≤ 0 side)
H3PLUS = (4, 6, 89, 25)    # pairL 4 6 89 25: 89·ρ5 - 25·ρ7 ≤ 0  (hval ≥ 0 side)


def parse_region(reg, n, D):
    """Parse one region record; returns the emission record or None with a reason."""
    path = reg["path"]
    if path not in ("h3-", "h3+"):
        return None, f"path {path}"
    ineqs = reg["ineqs"]
    if len(ineqs) != 15:
        return None, "not 15 pairs"
    # pair convention: ((A, s), (B, t)) means A·u[t] ≤ B·u[s], u[None] = 1
    (A1, s1), (B1, t1) = ineqs[0]                     # hv1: 1·u[ka] ≤ na·1
    (A3, s3), (B3, t3) = ineqs[1]                     # hv3: nb·1 ≤ 7·u[kb]
    (A2, s2), (B2, t2) = ineqs[2]                     # hv2: na·u[kb] ≤ nb·u[ka]
    if not (A1 == 1 and s1 is None and B3 == 7 and t3 is None):
        return None, "hv1/hv3 shape"
    if not (A2 == B1 and s2 == t1 and B2 == A3 and t2 == s3):
        return None, "hv2 shape"
    na, ka, nb, kb = B1, t1, A3, s3
    laps = []
    for i in range(6):
        (A4, s4), (B4, t4) = ineqs[3 + 2 * i]         # hv4_i: (8j+1)·u[ka] ≤ na·u[i]
        (A5, s5), (B5, t5) = ineqs[4 + 2 * i]         # hv5_i: nb·u[i] ≤ (8j+7)·u[kb]
        if not (s4 == i and t4 == ka and B4 == na and s5 == kb and t5 == i and A5 == nb):
            return None, f"hv4/hv5 shape at reading {i}"
        if (A4 - 1) % 8 != 0 or (B5 - 7) % 8 != 0 or (A4 - 1) // 8 != (B5 - 7) // 8:
            return None, f"lap consistency at reading {i}"
        laps.append((A4 - 1) // 8)
    # the Lean window data
    return {
        "path": path, "na": na, "kaL": ka + 1, "nb": nb, "kbL": kb + 1,
        "j": [0] + laps,                      # Lean Fin 7: j 0 = 0 (ρ1 pinned)
        "n": n, "D": D,
    }, None


def linform(vec, v):
    """pairL (s,t,A,B) at v: A·v[s] - B·v[t]."""
    s, t, A, B = vec
    return A * v[s] - B * v[t]


def families_ok(na, kaL, nb, kbL, j, v):
    """The five SideWindowCertV families at the point v (Lean-indexed dict)."""
    if not v[kaL] <= na:                                  # hv1: 1·v ka ≤ na·v 0
        return False
    if not na * v[kbL] <= nb * v[kaL]:                    # hv2
        return False
    if not nb * v[0] <= 7 * v[kbL]:                       # hv3
        return False
    for i in range(7):                                    # hv4_i
        if not (8 * j[i] + 1) * v[kaL] <= na * v[i]:
            return False
    for i in range(7):                                    # hv5_i
        if not nb * v[i] <= (8 * j[i] + 7) * v[kbL]:
            return False
    return True


def recorded_pairs_ok(ineqs, v):
    """Cross-check: the 15 recorded pairs at the point v (Lean index = artifact+1)."""
    for (A, s), (B, t) in ineqs:
        vs = v[s + 1] if s is not None else v[0]
        vt = v[t + 1] if t is not None else v[0]
        if A * vt > B * vs:
            return False
    return True


def verify_region(rec, vec=None):
    """Verify the five Lean families on the full SideVertex set of the parent cell
    with the region's plane vector.  Returns (ok, reason)."""
    n, D = rec["n"], rec["D"]
    lo = {0: F(1)}
    hi = {0: F(1)}
    for i in range(6):
        lo[i + 1] = F(n[i], D)
        hi[i + 1] = F(n[i] + 1, D)
    if vec is None:
        vec = H3MINUS if rec["path"] == "h3-" else H3PLUS
    s, t, A, B = vec
    na, kaL, nb, kbL, j = rec["na"], rec["kaL"], rec["nb"], rec["kbL"], rec["j"]

    def check(v):
        return families_ok(na, kaL, nb, kbL, j, v)

    # case 1: the 64 corners on the closed side
    for bits in product((0, 1), repeat=6):
        v = {0: F(1)}
        for i in range(6):
            v[i + 1] = lo[i + 1] if bits[i] == 0 else hi[i + 1]
        if linform(vec, v) <= 0 and not check(v):
            return False, f"corner {bits}"
    # case 2: edge crossings in the two plane coordinates
    for i0 in (s, t):
        others = [i for i in range(1, 7) if i != i0]
        for bits in product((0, 1), repeat=5):
            v = {0: F(1)}
            for o, b in zip(others, bits):
                v[o] = lo[o] if b == 0 else hi[o]
            if i0 == s:
                sol = B * v[t] / A            # A·v s = B·v t
            else:
                sol = A * v[s] / B            # B·v t = A·v s
            if not (lo[i0] < sol < hi[i0]):
                continue
            v[i0] = sol
            if not check(v):
                return False, f"crossing i0={i0} bits={bits}"
    # case 2 with interior index outside {s,t}: the plane vector vanishes there, so
    # every family is constant along the edge segment and its endpoints are checked
    # corners — covered by the case-1 sweep.
    return True, "ok"


def sidevertex_ok_pairs(vec, n, D, ineqs):
    """The recorded pairs on the SideVertex set of (parent cell, vec)."""
    lo = {0: F(1)}
    hi = {0: F(1)}
    for i in range(6):
        lo[i + 1] = F(n[i], D)
        hi[i + 1] = F(n[i] + 1, D)
    s, t, A, B = vec
    for bits in product((0, 1), repeat=6):
        v = {0: F(1)}
        for i in range(6):
            v[i + 1] = lo[i + 1] if bits[i] == 0 else hi[i + 1]
        if linform(vec, v) <= 0 and not recorded_pairs_ok(ineqs, v):
            return False
    for i0 in (s, t):
        others = [i for i in range(1, 7) if i != i0]
        for bits in product((0, 1), repeat=5):
            v = {0: F(1)}
            for o, b in zip(others, bits):
                v[o] = lo[o] if b == 0 else hi[o]
            if i0 == s:
                sol = B * v[t] / A
            else:
                sol = A * v[s] / B
            if not (lo[i0] < sol < hi[i0]):
                continue
            v[i0] = sol
            if not recorded_pairs_ok(ineqs, v):
                return False
    return True


def determine_side(n, D, ineqs):
    """Which closed h3 side the region's recorded certificate lives on (the dump's
    path labels are swapped relative to the sides' sign conventions — the walk
    labels sides()'s pos side `h3-`; determined here from the certificate itself,
    never from the label).  Returns (vec, label_is_swapped)."""
    ok_minus = sidevertex_ok_pairs(H3MINUS, n, D, ineqs)
    ok_plus = sidevertex_ok_pairs(H3PLUS, n, D, ineqs)
    if ok_minus and not ok_plus:
        return H3MINUS, None
    if ok_plus and not ok_minus:
        return H3PLUS, None
    if ok_minus and ok_plus:
        return None, "ambiguous (both sides)"
    return None, "neither side"


def crosscheck_region(rec, ineqs, vec):
    """The recorded pairs must hold on the same vertex set (convention cross-check)."""
    n, D = rec["n"], rec["D"]
    lo = {0: F(1)}
    hi = {0: F(1)}
    for i in range(6):
        lo[i + 1] = F(n[i], D)
        hi[i + 1] = F(n[i] + 1, D)
    s, t, A, B = vec
    for bits in product((0, 1), repeat=6):
        v = {0: F(1)}
        for i in range(6):
            v[i + 1] = lo[i + 1] if bits[i] == 0 else hi[i + 1]
        if linform(vec, v) <= 0 and not recorded_pairs_ok(ineqs, v):
            return False, f"corner {bits}"
    for i0 in (s, t):
        others = [i for i in range(1, 7) if i != i0]
        for bits in product((0, 1), repeat=5):
            v = {0: F(1)}
            for o, b in zip(others, bits):
                v[o] = lo[o] if b == 0 else hi[o]
            if i0 == s:
                sol = B * v[t] / A
            else:
                sol = A * v[s] / B
            if not (lo[i0] < sol < hi[i0]):
                continue
            v[i0] = sol
            if not recorded_pairs_ok(ineqs, v):
                return False, f"crossing i0={i0}"
    return True, "ok"


def rat_lit(fr):
    fr = F(fr)
    return str(fr.numerator) if fr.denominator == 1 else f"{fr.numerator}/{fr.denominator}"


def face_lits(n, D):
    lo = [rat_lit(F(n[i], D)) for i in range(6)]
    hi = [rat_lit(F(n[i] + 1, D)) for i in range(6)]
    return lo, hi


def emit_box(out, bidx, n, D, recs_m, recs_p, j_shared, jname_m, jname_p, vec_m, vec_p):
    """Emit one box's definitions + certificates + consumption theorems."""
    A = out.append
    lo, hi = face_lits(n, D)
    A(f"/-- Box {bidx} (line {bidx} of the dump): cells ρ2..ρ7 = {n}, D = {D};")
    A(f"the h3- and h3+ closed half-cells are the two recorded side regions. -/")
    A(f"noncomputable def offBox{bidx}Lo : Fin 7 → ℝ := ![1, {', '.join(lo)}]")
    A("")
    A(f"noncomputable def offBox{bidx}Hi : Fin 7 → ℝ := ![1, {', '.join(hi)}]")
    A("")
    def emit_j(jn, jvals):
        A(f"def {jn} : Fin 7 → ℤ := ![{', '.join(map(str, jvals))}]")
        A("")
        for k in range(7):
            A(f"theorem {jn}_k{k} : {jn} {k} = {jvals[k]} := rfl")
        A("")
        return [f"{jn}_k{k}" for k in range(7)]
    if j_shared:
        jn = f"offj{bidx}"
        jk = emit_j(jn, recs_m["j"])
        jn_m = jn_p = jn
        jkl_m = jkl_p = jk
    else:
        jn_m, jn_p = f"offj{bidx}m", f"offj{bidx}p"
        jkl_m = emit_j(jn_m, recs_m["j"])
        jkl_p = emit_j(jn_p, recs_p["j"])
    A(f"theorem offBox{bidx}FaceV (a : Fin 7 → ℝ) (v : Fin 7 → ℝ)")
    A(f"    (hv : SideVertex offBox{bidx}Lo offBox{bidx}Hi a v) :")
    A(f"    (1 : ℝ) ≤ v 0 ∧ v 0 ≤ 1 ∧ ({lo[0]} : ℝ) ≤ v 1 ∧ v 1 ≤ {hi[0]} ∧")
    A(f"      ({lo[1]} : ℝ) ≤ v 2 ∧ v 2 ≤ {hi[1]} ∧ ({lo[2]} : ℝ) ≤ v 3 ∧ v 3 ≤ {hi[2]} ∧")
    A(f"      ({lo[3]} : ℝ) ≤ v 4 ∧ v 4 ≤ {hi[3]} ∧ ({lo[4]} : ℝ) ≤ v 5 ∧ v 5 ≤ {hi[4]} ∧")
    A(f"      ({lo[5]} : ℝ) ≤ v 6 ∧ v 6 ≤ {hi[5]} := by")
    A(f"  have hb := sideVertex_box (by")
    A(f"    intro i")
    A(f"    fin_cases i <;>")
    A(f"      norm_num [offBox{bidx}Lo, offBox{bidx}Hi, Matrix.cons_val_zero,")
    A(f"        Matrix.cons_val_succ]) hv")
    A(f"  have h0 := sideVertex_pinned ⟨rfl, rfl⟩ hv")
    A(f"  refine ⟨by linarith, by linarith, (hb 1).1, (hb 1).2, (hb 2).1, (hb 2).2,")
    A(f"    (hb 3).1, (hb 3).2, (hb 4).1, (hb 4).2, (hb 5).1, (hb 5).2, (hb 6).1,")
    A(f"    (hb 6).2⟩")
    A("")
    for side, rec, vec, jn, jkl in (("m", recs_m, vec_m, jn_m, jkl_m),
                                    ("p", recs_p, vec_p, jn_p, jkl_p)):
        sL, tL, Aco, Bco = vec
        na, kaL, nb, kbL = rec["na"], rec["kaL"], rec["nb"], rec["kbL"]
        vstr = f"pairL {sL} {tL} {Aco} {Bco}"
        sgn = "h3+" if vec == H3PLUS else "h3-"
        A(f"/-- The {sgn} side-window-vertex certificate of box {bidx}:")
        A(f"window X = {na}/ρ{kaL}, Y = {nb}/ρ{kbL}, laps (8j+1) =")
        A(f"{[8 * x + 1 for x in rec['j']]}, on the closed side `{vstr} · g ≤ 0` (the")
        A(f"families hold on the side region's vertex set — verified exact data-side). -/")
        A(f"noncomputable def offc{bidx}{side} : SideWindowCertV :=")
        A(f"  {{ lo := offBox{bidx}Lo")
        A(f"    hi := offBox{bidx}Hi")
        A(f"    a := {vstr}")
        A(f"    na := {na}")
        A(f"    ka := {kaL}")
        A(f"    nb := {nb}")
        A(f"    kb := {kbL}")
        A(f"    j := {jn}")
        A(f"    hp0 := ⟨rfl, rfl⟩")
        A(f"    hlo := by")
        A(f"      intro i")
        A(f"      fin_cases i <;>")
        A(f"        norm_num [offBox{bidx}Lo, offBox{bidx}Hi, Matrix.cons_val_zero,")
        A(f"          Matrix.cons_val_succ]")
        A(f"    hposka := by")
        A(f"      rw [show offBox{bidx}Lo {kaL} = ({lo[kaL-1]} : ℝ) from rfl]")
        A(f"      norm_num")
        A(f"    hposkb := by")
        A(f"      rw [show offBox{bidx}Lo {kbL} = ({lo[kbL-1]} : ℝ) from rfl]")
        A(f"      norm_num")
        A(f"    hposlo := by")
        A(f"      intro i")
        A(f"      fin_cases i <;>")
        A(f"        norm_num [offBox{bidx}Lo, Matrix.cons_val_zero, Matrix.cons_val_succ]")
        for fam, extra_rw in (("hv1", True), ("hv2", False), ("hv3", True)):
            A(f"    {fam} := by")
            A(f"      intro v hvx")
            A(f"      have h0 := sideVertex_pinned ⟨rfl, rfl⟩ hvx")
            A(f"      have hs := sideVertex_side hvx")
            A(f"      rw [linForm_pairL] at hs")
            A(f"      obtain ⟨f0l, f0h, f1l, f1h, f2l, f2h, f3l, f3h, f4l, f4h, f5l, f5h,")
            A(f"        f6l, f6h⟩ := offBox{bidx}FaceV ({vstr}) v hvx")
            if extra_rw:
                A(f"      rw [h0]")
            A(f"      linarith")
        for fam in ("hv4", "hv5"):
            A(f"    {fam} := by")
            A(f"      intro v hvx")
            A(f"      have h0 := sideVertex_pinned ⟨rfl, rfl⟩ hvx")
            A(f"      have hs := sideVertex_side hvx")
            A(f"      rw [linForm_pairL] at hs")
            A(f"      obtain ⟨f0l, f0h, f1l, f1h, f2l, f2h, f3l, f3h, f4l, f4h, f5l, f5h,")
            A(f"        f6l, f6h⟩ := offBox{bidx}FaceV ({vstr}) v hvx")
            A(f"      refine swc_forallFin7 ?_ ?_ ?_ ?_ ?_ ?_ ?_")
            A(f"      all_goals norm_num [{', '.join(jkl)}, Matrix.cons_val_zero,")
            A(f"        Matrix.cons_val_succ]")
            A(f"      all_goals linarith")
        A(f"  }}")
        A("")
        A(f"/-- Region {bidx}{side} (the {sgn} side of box {bidx}): schema class 6 for")
        A(f"arrangements in the cell on the closed side. -/")
        A(f"theorem offbox{bidx}{side}_swv (g : Fin 7 → ℝ)")
        A(f"    (hbox : ∀ i, offBox{bidx}Lo i ≤ g i ∧ g i ≤ offBox{bidx}Hi i)")
        A(f"    (hs : linForm ({vstr}) g ≤ 0) : BandSideWindowV g :=")
        A(f"  ⟨offc{bidx}{side}, hbox, hs⟩")
        A("")
        A(f"theorem offbox{bidx}{side}_noCarve (g : Fin 7 → ℝ)")
        A(f"    (hbox : ∀ i, offBox{bidx}Lo i ≤ g i ∧ g i ≤ offBox{bidx}Hi i)")
        A(f"    (hs : linForm ({vstr}) g ≤ 0) : Fresh.Certs.NoCarve g :=")
        A(f"  sideWindowCertV_noCarve offc{bidx}{side} g hbox hs")
        A("")
    pv = "(pairL %d %d %d %d)" % vec_p
    mv = "(pairL %d %d %d %d)" % vec_m
    A(f"/-- Box {bidx} discharged: the two closed h3 sides cover the cell (with ρ1")
    A(f"pinned to 1) — `sideRegions_cover_closed`'s data shape.  (The dump's path")
    A(f"labels are swapped relative to the sides' sign conventions — the side of each")
    A(f"record is determined from its certificate, not the label.) -/")
    A(f"theorem offbox{bidx}_swv (g : Fin 7 → ℝ)")
    A(f"    (hbox : ∀ i, offBox{bidx}Lo i ≤ g i ∧ g i ≤ offBox{bidx}Hi i) :")
    A(f"    BandSideWindowV g := by")
    A(f"  rcases le_or_gt (linForm {pv} g) 0 with hp | hn")
    A(f"  · exact offbox{bidx}p_swv g hbox hp")
    A(f"  · refine offbox{bidx}m_swv g hbox ?_")
    A(f"    rw [linForm_pairL] at hn ⊢")
    A(f"    linarith")
    A("")
    A(f"theorem offbox{bidx}_noCarve (g : Fin 7 → ℝ)")
    A(f"    (hbox : ∀ i, offBox{bidx}Lo i ≤ g i ∧ g i ≤ offBox{bidx}Hi i) :")
    A(f"    Fresh.Certs.NoCarve g :=")
    A(f"  noCarve_of_sideWindowV (offbox{bidx}_swv g hbox)")
    A("")


def emit_chunk(bidxs, boxes, chunk_no, verify_stats):
    L = []
    A = L.append
    A("import Fresh.BandCertDataExt")
    A("")
    A("/-!")
    A(f"# The off-plane tranche, chunk {chunk_no} of 4: boxes {bidxs[0]}-{bidxs[-1]} of the")
    A(f"509-box h3 straddler closure (E846's 1,018 side regions)")
    A("")
    A("Generated by `experiments/n8/bandrep_offplane_gen_v1.py` from")
    A("`tail_h3_offplane_dump_v1.jsonl` (schema 6 per E846; D = 512).  Each box's two")
    A("closed h3 half-cells carry a `SideWindowCertV` on the parent cell faces (ρ1")
    A("pinned to the point 1): the five families hold on the side region's vertex set,")
    A(f"verified exact data-side for all {2*len(bidxs)} regions of this chunk")
    A("(cross-checked against the dump's own recorded pairs).  The per-box discharge")
    A("composes the two closed sides (`sideRegions_cover_closed`'s shape) and the chunk")
    A("totality is the right-nested box disjunction (maxRecDepth discipline).  Nothing")
    A("existing is edited.")
    A("-/")
    A("")
    A("namespace Fresh.BandRepOff_%d" % chunk_no)
    A("")
    A("open Fresh.BandNoCarve")
    A("")
    for bidx in bidxs:
        emit_box(L, bidx, *boxes[bidx])
    A("set_option maxRecDepth 800000 in")
    A("/-- The chunk's box-union totality (schema class 6): the %d boxes' disjunction" % len(bidxs))
    A("gives `BandSideWindowV`. -/")
    A("theorem offchunk%d_swv (g : Fin 7 → ℝ)" % chunk_no)
    A("    (h : %s) : BandSideWindowV g :=" % disj_text(bidxs))
    A("  by")
    peel = []
    for k, bidx in enumerate(bidxs):
        last = k == len(bidxs) - 1
        ind = "    " + "  " * k
        if last:
            peel.append(f"{ind}exact offbox{bidx}_swv g h")
        else:
            peel.append(f"{ind}rcases h with hb | h")
            peel.append(f"{ind}· exact offbox{bidx}_swv g hb")
            peel.append(f"{ind}·")
    A("\n".join(peel))
    A("")
    A("theorem offchunk%d_noCarve (g : Fin 7 → ℝ)" % chunk_no)
    A("    (h : %s) : Fresh.Certs.NoCarve g :=" % disj_text(bidxs))
    A("  noCarve_of_sideWindowV (offchunk%d_swv g h)" % chunk_no)
    A("")
    A("#print axioms offchunk%d_swv" % chunk_no)
    A("#print axioms offchunk%d_noCarve" % chunk_no)
    A("")
    A("end Fresh.BandRepOff_%d" % chunk_no)
    out_path = os.path.join(FRESH, "BandRepOff_%d.lean" % chunk_no)
    with open(out_path, "w") as f:
        f.write("\n".join(L) + "\n")
    return out_path


def disj_text(bidxs):
    """Right-nested disjunction over the boxes' cell-face memberships."""
    term = lambda b: f"(∀ i, offBox{b}Lo i ≤ g i ∧ g i ≤ offBox{b}Hi i)"
    if len(bidxs) == 1:
        return term(bidxs[0])
    out = term(bidxs[-1])
    for b in reversed(bidxs[:-1]):
        out = f"({term(b)} ∨ {out})"
    return out


def emit_grand(all_bidxs, chunk_of):
    """The grand totality, HIERARCHICAL (the maxRecDepth discipline): the four
    chunk totalities (each ≤128-deep, already compiled) composed by a 4-case top.
    A single 509-deep rcases peel aborts the native stack (measured)."""
    groups = chunk_of
    L = []
    A = L.append
    for c in (1, 2, 3, 4):
        A(f"import Fresh.BandRepOff_{c}")
    A("")
    A("/-!")
    A("# The off-plane tranche totality and the BandCertData6 wiring (E846's 1,018")
    A("# side regions over the 509-box h3 straddler closure)")
    A("")
    A("Generated by `experiments/n8/bandrep_offplane_gen_v1.py`.  The grand totality")
    A("composes the four chunk totalities by a 4-case top — the HIERARCHICAL form of")
    A("the `bandPinch_tranche_discharged` pattern (a single 509-deep rcases peel")
    A("aborts the native stack; the chunk-then-top composition is the working")
    A("granularity, matching the per-window grouping discipline of the pinch")
    A("tranche).  Stated in both the schema-6 form (`BandSideWindowV`) and the")
    A("`NoCarve` form.  The covering claim — that every normalized arrangement in")
    A("the band's off-plane part satisfies the disjunction — is the data-side")
    A("obligation E916 priced; no covering claim is made here (rule 7(b)): every")
    A("theorem is an implication over the recorded boxes' faces.  The dump's path")
    A("labels are swapped relative to the sides' sign conventions (the walk labels")
    A("sides()'s pos side `h3-`); each region's side was determined from its")
    A("certificate, not the label.  Nothing existing is edited.")
    A("-/")
    A("")
    A("namespace Fresh.BandRepOffGrand")
    A("")
    A("open Fresh.BandNoCarve Fresh.BandRepOff_1 Fresh.BandRepOff_2 Fresh.BandRepOff_3")
    A("  Fresh.BandRepOff_4")
    A("")
    A("set_option maxRecDepth 800000 in")
    A("/-- The tranche's grand totality (schema class 6): the 509-box disjunction,")
    A("grouped by chunk, gives `BandSideWindowV`. -/")
    A("theorem offplane_tranche_swv (g : Fin 7 → ℝ)")
    A("    (h : %s) : BandSideWindowV g :=" % grand_disj_text(groups))
    A("  by")
    A("  rcases h with h1 | h2 | h3 | h4")
    for c in (1, 2, 3, 4):
        A(f"  · exact offchunk{c}_swv g h{c}")
    A("")
    A("/-- The tranche's grand totality in the `NoCarve` form. -/")
    A("theorem offplane_tranche_noCarve (g : Fin 7 → ℝ)")
    A("    (h : %s) : Fresh.Certs.NoCarve g :=" % grand_disj_text(groups))
    A("  noCarve_of_sideWindowV (offplane_tranche_swv g h)")
    A("")
    A("/-- **The BandCertData6 wiring**: the tranche's schema-6 slice — the")
    A("hypothesis-carrying instance consumed by `BandCertData6`'s `BandSideWindowV`")
    A("class (the `bandPinch_tranche_discharged` pattern feeding schema 4). -/")
    A("theorem bandCertData6_offplane_slice (g : Fin 7 → ℝ)")
    A("    (h : %s) : BandSideWindowV g :=" % grand_disj_text(groups))
    A("  offplane_tranche_swv g h")
    A("")
    A("#print axioms offplane_tranche_swv")
    A("#print axioms offplane_tranche_noCarve")
    A("#print axioms bandCertData6_offplane_slice")
    A("")
    A("end Fresh.BandRepOffGrand")
    out_path = os.path.join(FRESH, "BandRepOffGrand.lean")
    with open(out_path, "w") as f:
        f.write("\n".join(L) + "\n")
    return out_path


def grand_disj_text(groups):
    """The 4-deep top over the chunk-level box disjunctions (right-nested)."""
    terms = [disj_text(grp) for grp in groups]
    out = terms[-1]
    for t in reversed(terms[:-1]):
        out = f"({t} ∨ {out})"
    return out


def main():
    mode = sys.argv[1] if len(sys.argv) > 1 else "verify"
    t0 = time.time()
    boxes = {}          # bidx -> (n, D, recs_m, recs_p, j_shared, jname_m, jname_p)
    stats = {"regions": 0, "verified": 0, "failed": [], "crossfail": [],
             "labelswap": 0}
    with open(os.path.join(N8, "tail_h3_offplane_dump_v1.jsonl")) as f:
        for bidx, line in enumerate(f, start=1):
            d = json.loads(line)
            regions = d["regions"]
            if len(regions) != 2:
                stats["failed"].append((bidx, "not 2 regions"))
                continue
            rec_m, err_m = parse_region(regions[0], d["n"], d["D"])
            rec_p, err_p = parse_region(regions[1], d["n"], d["D"])
            if rec_m is None or rec_p is None:
                stats["failed"].append((bidx, err_m or err_p))
                continue
            stats["regions"] += 2
            vec_m, why_m = determine_side(d["n"], d["D"], regions[0]["ineqs"])
            vec_p, why_p = determine_side(d["n"], d["D"], regions[1]["ineqs"])
            if vec_m is None or vec_p is None:
                stats["crossfail"].append((bidx, why_m or why_p))
                continue
            # the label-swap census: the dump labels sides()'s pos side `h3-`
            lab_m = "h3+" if vec_m == H3PLUS else "h3-"
            lab_p = "h3+" if vec_p == H3PLUS else "h3-"
            if regions[0]["path"] != lab_m:
                stats["labelswap"] += 1
            if regions[1]["path"] != lab_p:
                stats["labelswap"] += 1
            ok_m, fw_m = verify_region(rec_m, vec_m)
            ok_p, fw_p = verify_region(rec_p, vec_p)
            cc_m, ccm_why = crosscheck_region(rec_m, regions[0]["ineqs"], vec_m)
            cc_p, ccp_why = crosscheck_region(rec_p, regions[1]["ineqs"], vec_p)
            if not cc_m or not cc_p:
                stats["crossfail"].append((bidx, ccm_why if not cc_m else ccp_why))
                continue
            if ok_m and ok_p:
                stats["verified"] += 2
                j_shared = rec_m["j"] == rec_p["j"]
                boxes[bidx] = (d["n"], d["D"], rec_m, rec_p, j_shared, None, None,
                               vec_m, vec_p)
            else:
                stats["failed"].append((bidx, fw_m if not ok_m else fw_p))
    print(f"regions: {stats['regions']}, vertex-form verified: {stats['verified']}, "
          f"failed: {len(stats['failed'])}, cross-check failures: {len(stats['crossfail'])}, "
          f"label-vs-geometry swaps: {stats['labelswap']}")
    for b, w in stats["failed"][:10]:
        print("  FAIL box", b, w)
    for b, w in stats["crossfail"][:10]:
        print("  CROSSFAIL box", b, w)
    print(f"verified boxes: {len(boxes)}  ({time.time()-t0:.1f} s)")

    if mode == "verify":
        return
    bidxs = sorted(boxes)
    if mode == "pilot":
        sel = bidxs[:3]
        out_path = emit_chunk(sel, {b: boxes[b] for b in sel}, 1, stats)
        print(f"emitted pilot ({len(sel)} boxes) -> {out_path}")
    elif mode == "chunks":
        groups = [bidxs[i:i + 128] for i in range(0, len(bidxs), 128)]
        for c, grp in enumerate(groups, start=1):
            out_path = emit_chunk(grp, {b: boxes[b] for b in grp}, c, stats)
            print(f"emitted chunk {c} ({len(grp)} boxes) -> {out_path}")
        out_path = emit_grand(bidxs, groups)
        print(f"emitted grand totality -> {out_path}")
    else:
        sys.exit("unknown mode (verify | pilot | chunks)")

    with open(os.path.join(N8, "bandrep_offplane_gen_v1.out"), "a") as f:
        f.write(f"mode={mode} regions={stats['regions']} verified={stats['verified']} "
                f"failed={len(stats['failed'])} crossfail={len(stats['crossfail'])} "
                f"labelswap={stats['labelswap']} "
                f"boxes={len(boxes)} ({time.time()-t0:.1f} s)\n")


if __name__ == "__main__":
    main()
