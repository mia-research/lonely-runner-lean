# v3_sliver_lines_v2 -- the sliver-closing lines, tested on the CORRECT population: tuples whose
# whole rho7-column [25,50] is dead (column_state) WITH a boundary component (a=1 or b=7) as the
# certifying component (its own feasible_set empty -- the 'note' certificates of boxcheck2's
# 'boundary' tally, 5,747,771 cases).  The lines:
#   START (a=1): dead over [25,50]  <=>  b >= 33/31   (b = the component's right edge)
#   END   (b=7): dead over [25,50]  <=>  a <= 1225/177 (a = the component's left edge)
# Both directions are checked against the direct feasible_set computation (which, on this
# population, IS the certificate: the component's empty set is what made column_state declare
# COMP-DEAD).  Violations in either direction are reported with exact witnesses.
from fractions import Fraction as F
import sys, time, itertools, json
sys.path.insert(0, '.')
from conjT3_enum_v1 import k6_components, race_certificate, column_state, skels, feasible_set
CELLBOUNDS = {'P': (F(1),F(7)), 'S1': (F(7),F(9)), 'G1': (F(9),F(15)), 'S2': (F(15),F(17)), 'E': (F(17),F(17))}
RLO, RHI = F(25), F(50)
LINE_START = F(33, 31)
LINE_END = F(1225, 177)

def main(deadline, outpath):
    t0 = time.time()
    n_s = n_e = v_s_hi = v_s_lo = v_e_hi = v_e_lo = 0
    ex = {}
    outf = open(outpath, 'a')
    for si, s in enumerate(skels):
        if time.time() > deadline:
            outf.write(json.dumps(dict(status='BUDGET', skel_index=si, n_s=n_s, n_e=n_e,
                                       v_s_hi=v_s_hi, v_s_lo=v_s_lo, v_e_hi=v_e_hi, v_e_lo=v_e_lo)) + "\n")
            outf.close(); return
        vals = []
        for c in s:
            lo, hi = CELLBOUNDS[c]
            cand = sorted(set([lo, hi] + ([F(2*(int(lo*5)+i),10) for i in range(int(hi*5)-int(lo*5)+1)] if lo != hi else [])))
            vals.append(cand)
        for rho in itertools.product(*vals):
            if any(rho[i] > rho[i+1] for i in range(4)): continue
            dead, info = column_state(list(rho), RLO, RHI)
            if not dead or info is None or info['kind'] != 'COMP-DEAD': continue
            cert = info['cert']
            if cert is None or 'note' not in cert: continue
            comps = k6_components(list(rho))
            a, b = comps[info['idx']]
            if a == F(1):
                n_s += 1
                line_says_dead = (b >= LINE_START)
                if line_says_dead != (len(feasible_set(a, b, RLO, RHI)) == 0):
                    v_s_hi += line_says_dead; v_s_lo += (not line_says_dead)
                    ex.setdefault('START', (s, [str(x) for x in rho], info['idx'], str(a), str(b)))
            if b == F(7):
                n_e += 1
                line_says_dead = (a <= LINE_END)
                if line_says_dead != (len(feasible_set(a, b, RLO, RHI)) == 0):
                    v_e_hi += line_says_dead; v_e_lo += (not line_says_dead)
                    ex.setdefault('END', (s, [str(x) for x in rho], info['idx'], str(a), str(b)))
        outf.write(json.dumps(dict(skel_index=si, skel=list(s), n_s=n_s, n_e=n_e,
                                   v_s_hi=v_s_hi, v_s_lo=v_s_lo, v_e_hi=v_e_hi, v_e_lo=v_e_lo)) + "\n")
        outf.flush()
    outf.write(json.dumps(dict(status='DONE', secs=round(time.time()-t0,1), n_s=n_s, n_e=n_e,
                               v_s_hi=v_s_hi, v_s_lo=v_s_lo, v_e_hi=v_e_hi, v_e_lo=v_e_lo)) + "\n"); outf.close()
    print(json.dumps(dict(status='DONE', secs=round(time.time()-t0,1), n_start=n_s, n_end=n_e,
                          viol_start_dead_but_live=v_s_hi, viol_start_live_but_dead=v_s_lo,
                          viol_end_dead_but_live=v_e_hi, viol_end_live_but_dead=v_e_lo,
                          examples=ex)))

if __name__ == '__main__':
    secs = int(sys.argv[1]) if len(sys.argv) > 1 else 2700
    main(time.time() + secs, 'v3_sliver_lines_v3_stream.jsonl')
