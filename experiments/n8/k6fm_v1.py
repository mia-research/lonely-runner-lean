# k6fm_v1 -- the INTERSECTION-FORM LEMMA's certificate instrument (the surgical strike on gamma).
# The mathematics: within a ratio-partition cell of the two boundary readings, the K6
# combinatorics is CONSTANT (all component endpoints are zone-edge values (8j±1)/r_i for
# FIXED (i, j)), so every loneliness condition -- s covers component [a,b] at lap j iff
# (8j-1) <= s*a and s*b <= (8j+1), with a, b linear in 1/rhoL, 1/rhoR -- is a LINEAR
# inequality in (rhoL, rhoR, s). The chamber-uniform death claim for the cell is then the
# INFEASIBILITY of a small linear system over cell x [25,50). Certificate: exact
# Fourier-Motzkin elimination; if the projection is NONEMPTY, the witness (rhoL, rhoR, s)
# is a live tuple -- the decisive negative finding.
# Exact Fractions throughout.
import json, sys, time
from fractions import Fraction as F

def fm_project(vars, sys_, elim_var):
    """Fourier-Motzkin: eliminate elim_var from sys_ (list of (coeff_dict, op, rhs) with
    op in {'<=','='}; homogeneous form: sum c_i x_i <= rhs). Returns new system."""
    pos, neg, eqs = [], [], []
    rest = []
    for (c, op, r) in sys_:
        if c.get(elim_var, F(0)) == 0:
            rest.append((c, op, r)); continue
        if op == '=':
            eqs.append((c, op, r))
        elif c[elim_var] > 0: pos.append((c, op, r))
        else: neg.append((c, op, r))
    out = list(rest)
    # normalize equalities into two inequalities
    for (c, op, r) in eqs:
        cc = dict(c); cc[elim_var] = cc.get(elim_var, F(0)) * 2
        out.append((cc, '<=', r * 2 + F(1, 1000000)))  # split not needed if we handle below
        out.append((dict(c), '>=', r))  # treat via negation into pos/neg below
    # simpler: treat '=' as two inequalities
    out = list(rest)
    for (c, op, r) in eqs:
        cpos = dict(c); cout_pos = r
        # x-var coefficient positive: c*x <= r  and  -c*x <= -r
        cneg = {k: -v for k, v in c.items()}
        pos.append((cpos, '<=', r)); neg.append((cneg, '<=', -r))
    if not pos or not neg:
        return out if not pos else out, None, None  # var unbounded above/below: keep rest, note free
    # combine every pos with every neg:  sum_neg <= 0 <= sum_pos  ==> sum_neg * pos <= ...
    newcons = []
    for (cp, rp) in [(c, r) for (c, op, r) in pos]:
        for (cn, rn) in [(c, r) for (c, op, r) in neg]:
            # cp[elim]*e <= rp  and  cn[elim]*e <= rn  (cn[elim] < 0)
            # e <= rp/cp[elim];  e >= rn/cn[elim]  ==>  combine: cn[elim]*rp/cp[elim] ... standard:
            # multiply first by |cn[elim]|, second by cp[elim], add:
            k1 = abs(cn[elim_var]); k2 = cp[elim_var]
            nc = {}
            for v in set(list(cp.keys()) + list(cn.keys())):
                if v == elim_var: continue
                s = cp.get(v, F(0)) * k1 + cn.get(v, F(0)) * k2
                if s != 0: nc[v] = s
            nr = rp * k1 + rn * k2
            newcons.append((nc, '<=', nr))
    return out + newcons, None, None

def fm_empty(vars_, sys_, box):
    """Eliminate all vars in vars_; detect infeasibility (a constraint 0 <= negative)."""
    sys_ = list(sys_)
    for v in vars_:
        sys_, _, _ = fm_project(vars_, sys_, v)
        # feasibility check: any constraint with empty coeff dict and negative rhs => infeasible
        for (c, op, r) in sys_:
            if not c and r < 0: return False, ('0 <= ' + str(r))
    return True, None

def solve_point(sys_, assign):
    """check a full assignment against the system"""
    for (c, op, r) in sys_:
        val = sum(c.get(v, F(0)) * assign.get(v, F(0)) for v in c)
        if op == '<=' and val > r: return False
        if op == '=' and val != r: return False
    return True

def main():
    # The worked chamber: skel P,P,G1,G1,S2; kL=kR=2; component (a,b) = (85/76, 75/58)
    # readings: Fin 5 -> Q = [rho2, rho3, rho4, rho5, rho6]; boundary: rhoL = idx 3 (rho5), rhoR = idx 4 (rho6)
    # windows (from the K=32 refinement): rhoL in [15, 76/5], rhoR in [58/5, 986/75]
    # others fixed at the recorded representative values (from the probe dump; rho2=1-ish P cell, rho3, rho4 in G1)
    # For the worked instance we use the datasheet's rhoEx convention scaled to this chamber:
    # rhoL=15 (the low corner!), rhoR=986/75 (the high corner) -- the OPEN corner tuples.
    L1, L2 = F(15), F(76, 5)
    R1, R2 = F(58, 5), F(986, 75)
    print('rhoL window:', L1, L2, ' rhoR window:', R1, R2)
    # The other readings: fix at the chamber's cell midpoints (G1 cells: rho3, rho4; P cell: rho2).
    # From the recorded representative we don't have them in this file; use G1 mid=12, 12 and P mid=4:
    # honest scope: the 2D slice fixes rho2, rho3, rho4; the 5D generalization is the scale-out.
    f2, f3, f4 = F(4), F(12), F(12)
    # Components: compute K6Comps at a sample point to get the combinatorics; then FIX the
    # endpoint formulas per the cell (each endpoint is (8j±1)/rho_i for the owning reading).
    # For the prototype we derive the endpoint ownership at the sample point:
    def zones_of(r, maxj=15):
        return [(F(8*j-1)/r, F(8*j+1)/r, j) for j in range(1, maxj+1)]
    def merged(all_):
        all_s = sorted(all_)
        out = []
        for (a, b, tag) in all_s:
            if out and a <= out[-1][1]:
                if b > out[-1][1]: out[-1] = (out[-1][0], b, out[-1][2] + [(a, b, tag)])
                else: out[-1] = (out[-1][0], out[-1][1], out[-1][2] + [(a, b, tag)])
            else: out.append((a, b, [(a, b, tag)]))
        return [(a, b, t) for (a, b, t) in out]
    def comps_at(rhoL, rhoR):
        zs = []
        zs += [(a, b, ('r2', j)) for (a, b, j) in zones_of(f2) if b >= 1 and a <= 7]
        zs += [(a, b, ('r3', j)) for (a, b, j) in zones_of(f3) if b >= 1 and a <= 7]
        zs += [(a, b, ('r4', j)) for (a, b, j) in zones_of(f4) if b >= 1 and a <= 7]
        zs += [(a, b, ('rL', j)) for (a, b, j) in zones_of(rhoL) if b >= 1 and a <= 7]
        zs += [(a, b, ('rR', j)) for (a, b, j) in zones_of(rhoR) if b >= 1 and a <= 7]
        m = merged([(a, b, t) for (a, b, t) in zs])
        comps = []
        cur = F(1)
        for (a, b, t) in m:
            if a > cur: comps.append((cur, a, t))
            cur = max(cur, b)
        if cur < 7: comps.append((cur, F(7), []))
        return comps
    # sample the corner to get the combinatorics
    corner = comps_at(L1, R2)
    print('corner components:', [(str(a), str(b)) for (a, b, t) in corner])
    # Build the linear loneliness system for the corner combinatorics:
    # each component's endpoints are zone edges (8j±1)/rho_i for owning reading i (or 1 / 7 constants).
    # Component [a, b] with a = (8ja-1)/rho_ia (or const), b = (8jb+1)/rho_ib (or const):
    # coverage by s at lap j: (8j-1)*rho_ia/(8ja-1) <= s  and  s*(8jb+1)/rho_ib <= (8j+1)
    #   ==> linear in (rhoL, rhoR, s) after clearing.
    # We emit the system symbolically: each endpoint = num/den * (1/rho_own) or constant.
    def endpoint_form(x, at):
        """return ('var', own, num) if x = num/rho_own at this sample, or ('const', x)."""
        for own in ('rL', 'rR', 'r2', 'r3', 'r4'):
            r = {'rL': rhoL if False else 1, 'rR': 1}
        # determine ownership by testing x * rho = (8j±1) at the sample values
        return None
    # Simpler: emit per-component constraints directly at the corner's ownership:
    # For each component, find its endpoint owners by scanning which (reading, j) reproduces the endpoint at the corner.
    def owner(x, samples):
        for own, rv in samples.items():
            for j in range(1, 16):
                for sgn_num, sgn in ((8*j-1, -1), (8*j+1, 1)):
                    if rv != 0 and x * rv == sgn_num:
                        return (own, sgn_num)
        return None
    samples = {'rL': 1/rhoL_lo if rhoL_lo != 0 else 1, 'rR': 1, 'r2': f2, 'r3': f3, 'r4': f4, 'one': 1}
    # ownership test at the corner tuple rhoL=L1, rhoR=R2:
    cornerL, cornerR = L1, R2
    samp2 = {'rL': cornerL, 'rR': cornerR, 'r2': f2, 'r3': f3, 'r4': f4, 'one': 1}
    syscons = []   # linear constraints in (rL, rR, s): coefficients dict + rhs (a*x + b*y + c*s <= rhs)
    comp_specs = []
    for (a, b, tags) in corner:
        oa = owner(a, samp2); ob = owner(b, samp2)
        comp_specs.append((oa, ob))
        print('component', str(a), str(b), 'owners:', oa, ob)
    # Coverage of component (oa, ob) by s at lap j:
    #   a = Na/rL' (own rL' in {rL, rR, r2..}), so (8j-1) <= s*a  ==>  (8j-1)*rho_own <= Na*s (if Na = 8ja∓1 over own)
    #   generic: Na/rho_own <= s*... let's write a = Na/rho_own; s*a >= 8j-1  ==> s*Na >= (8j-1)*rho_own
    #   b = Nb/rho_own2; s*b <= 8j+1  ==> s*Nb <= (8j+1)*rho_own2
    # Each: linear. Build the loneliness system: for each component, for each lap j in 1..15, the two
    # inequalities; TupleLonely at s requires for EVERY component SOME j covering: the disjunction.
    # Disjunctions make FM non-trivial: we enumerate the LAP-ASSIGNMENT (which lap covers which component).
    # The assignment count: components^laps -- too big; instead: FM per assignment, emptiness of the UNION
    # = infeasibility of EACH assignment-system (loneliness requires one assignment to hold fully).
    # So: chamber-uniform death  <=>  for EVERY lap-assignment A, the system (A's cover constraints +
    #     cell bounds + s in [25,50)) is INFEASIBLE.  Certificate: per assignment an FM contradiction.
    import itertools
    comp_laps = list(range(1, 16))
    ncomp = len(corner)
    # bound the per-component lap ranges: j must satisfy (8j-1) <= s * a with s <= 50: 8j-1 <= 50*a -> j <= (50*a+1)/8
    jranges = []
    for (a, b, tags) in corner:
        jmax = int((50 * a + 1) / 8) + 1
        jmin = max(1, int((25 * b - 1) / 8))  # 8j+1 >= 25*b -> j >= (25b-1)/8
        jranges.append(list(range(max(1, jmin), jmax + 1)))
    print('per-component lap ranges:', [len(r) for r in jranges], 'total assignments:', 
          __import__('math').prod(len(r) for r in jranges))
    # For each assignment tuple (j_1..j_m): the loneliness system:
    # per component i with owners (oa_i, ob_i) and lap j_i:
    #   (8 j_i - 1) * rho_oa_i <= Na_i * s     [Na_i = the owner numerator of a_i]
    #   Nb_i * s <= (8 j_i + 1) * rho_ob_i
    # plus: rhoL in [L1,L2], rhoR in [R1,R2], s in [25,50].
    # If FM finds it infeasible for every assignment: the cell is column-dead CERTIFIED.
    # Owner coefficients: a = Na / rho_own  (Na = the numerator at the corner, e.g. 7/1 for endpoint 7/r).
    def owner_num(x, own, rho_at):
        # x = Num / rho_own at the corner sample: Num = x * rho_at[own]
        return x * rho_at[own]
    rho_at_corner = {'rL': cornerL, 'rR': cornerR, 'r2': f2, 'r3': f3, 'r4': f4}
    assignments = list(itertools.product(*jranges))
    infeas_count = 0; feas_witness = None
    for ai, assign in enumerate(assignments):
        sysc = []
        for i, ((a, b, tags), j) in enumerate(zip(corner, assign)):
            oa, ob = comp_specs[i][0], comp_specs[i][1]
            if oa is None or ob is None: continue
            Na = a * rho_at_corner[oa]
            Nb = b * rho_at_corner[ob]
            # (8j-1) * rho_oa <= Na * s
            sysc.append(({oa: F(8*j-1), 's': -Na}, '<=', F(0)))
            # Nb * s <= (8j+1) * rho_ob
            sysc.append(({ob: -Nb, 's': F(1)}, '<=', F(0)))
        sysc.append({'rL': F(1), '<': 0} and ({'rL': F(-1)}, '<=', -L1))
        sysc.append(({'rL': F(1)}, '<=', L2))
        sysc.append(({'rR': F(-1)}, '<=', -R1))
        sysc.append(({'rR': F(1)}, '<=', R2))
        sysc.append(({'s': F(-1)}, '<=', F(-25)))
        sysc.append(({'s': F(1)}, '<=', F(50)))
        vars_ = ['rL', 'rR', 's']
        s2 = list(sysc)
        ok = True
        for v in ['s', 'rL', 'rR']:
            s2, _, _ = fm_project(vars_, s2, v)
            for (c, op, r) in s2:
                if not c and r < 0: ok = False; break
            if not ok: break
        if ok: feas_witness = assign; break
        infeas_count += 1
    print('assignments:', len(assignments), '| infeasible (cell dead):', infeas_count, '| FEASIBLE (live!):', 
          'YES assignment=' + str(feas_witness) if feas_witness else 'none')
    if feas_witness is None:
        print('==> the corner cell is CERTIFIED column-dead: the intersection-form certificate exists (FM per assignment).')
    else:
        print('==> LIVE WITNESS at assignment', feas_witness, '-- carve candidate, decisive negative finding')

if __name__ == '__main__':
    main()
