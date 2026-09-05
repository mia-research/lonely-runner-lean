#!/usr/bin/env python3
"""
kden_ramanujan_comb_v1.py -- H2b (PRIMARY) + H2a of PREREG_kden_ramanujan_comb_v1.md.

Tests HYP-G: the level set L_q = {off in [0,A) : k_den(off;A,M) = q} is exactly the union of
phi(q) intervals, one centred on each j/q with gcd(j,q)=1.

ORDERING (anti-T-1, prereg section 8): predict_levelsets() derives interval endpoints in CLOSED FORM
from (A,M,q,j) ONLY -- it never minimises |d*off - k*A| over d for a given off.  The endpoint table
is written and SHA-256'd BEFORE k_den is computed for that configuration.

EXACTNESS: signal path is 100% int / fractions.Fraction.  No float anywhere in this file.
"""
import sys
import hashlib
from fractions import Fraction
from math import gcd


# ------------------------------------------------------------------ the source object (verbatim)
def k_den_sequence(A, M):
    """k_den(off) for off in [0,A).  Identical logic to band_residual() in lift_band_spectral_v1.py:
       k = (2*den*off + A)//(2*A) (nearest, ties up); minimise e=|den*off-k*A|; strict '<' => smallest den."""
    two = 2 * A
    out = [0] * A
    for off in range(A):
        best_e = None
        best_den = 1
        for den in range(1, M + 1):
            k = (2 * den * off + A) // two
            e = den * off - k * A
            if e < 0:
                e = -e
            if best_e is None or e < best_e:
                best_e = e
                best_den = den
        out[off] = best_den
    return out


# ------------------------------------------------------------------ closed-form prediction
def _bounds(q, j, M):
    """Exact Fractions (eta_right, xi_left) from prereg section 0.4, plus the binding-d sets.

    theta = (j+eta)/q.  q beats d iff q*|eta| (< or <=) min(u_d + d*eta, q - u_d - d*eta),
    STRICT for d<q (d scanned first), NON-STRICT for d>q.  d a multiple of q never binds.
    Returns (eta_right, right_binders, xi_left, left_binders); binders = set of d achieving the min.
    """
    if q == 1:
        # Degenerate: every d is a multiple of q, so the u_d algebra is empty.  Directly:
        # theta = eta near 0, ||d*eta|| = d*eta while d*eta <= 1/2, then 1 - d*eta.  q=1 holds
        # until eta = 1/(M+1) (binding d = M > q, hence NON-strict => endpoint belongs to q=1).
        b = Fraction(1, M + 1)
        return b, {M}, b, {M}
    eta_r = None
    xi_l = None
    rb = set()
    lb = set()
    for d in range(1, M + 1):
        if d % q == 0:
            continue
        u = (d * j) % q                       # in [1,q-1] since gcd(j,q)=1 and q does not divide d
        # ---- right side (eta >= 0)
        cands_r = [Fraction(q - u, q + d)]
        if d < q:
            cands_r.append(Fraction(u, q - d))
        for c in cands_r:
            if eta_r is None or c < eta_r:
                eta_r = c
                rb = {d}
            elif c == eta_r:
                rb.add(d)
        # ---- left side (eta = -xi, xi >= 0)
        cands_l = [Fraction(u, q + d)]
        if d < q:
            cands_l.append(Fraction(q - u, q - d))
        for c in cands_l:
            if xi_l is None or c < xi_l:
                xi_l = c
                lb = {d}
            elif c == xi_l:
                lb.add(d)
    if eta_r is None:                          # q == 1 and M == 1: no competitor
        eta_r = Fraction(1, 2)
        xi_l = Fraction(1, 2)
    return eta_r, rb, xi_l, lb


def predict_levelsets(A, M, centre_mode='primitive', width_num=1, width_den=1):
    """Closed-form predicted intervals.  Returns (rows, assign) where
         rows   = list of (q, j, off_lo_int, off_hi_int, n_int, boundary_flags)
         assign = dict off -> q  (predicted value; absent => unassigned)
       centre_mode: 'primitive' (HYP-G) | 'all_j' (W1-plant) | 'half' (W2-plant)
       width_num/width_den scales both bounds (W3-plant uses 1/2).
    """
    rows = []
    assign = {}
    boundary = set()
    scale = Fraction(width_num, width_den)
    for q in range(1, M + 1):
        js = range(q) if centre_mode == 'all_j' else [j for j in range(q) if gcd(j, q) == 1]
        for j in js:
            # W1-plant fix (DEVIATION D1): at a NON-primitive centre the u_d=0 term collapses the
            # derived half-widths to zero, so 'all_j' with per-j bounds silently reproduces the
            # primitive prediction and cannot act as a wrong-prediction control.  Give every centre
            # the width of a primitive one, so the plant genuinely predicts q intervals not phi(q).
            jb = j if gcd(j, q) == 1 else 1
            eta_r, rb, xi_l, lb = _bounds(q, jb, M)
            eta_r = eta_r * scale
            xi_l = xi_l * scale
            # centre in off-units
            if centre_mode == 'half':
                centre = Fraction((2 * j + 1) * A, 2 * q)
            else:
                centre = Fraction(j * A, q)
            lo = centre - Fraction(A, q) * xi_l
            hi = centre + Fraction(A, q) * eta_r
            # integers strictly inside are accepted by the exact bounds themselves
            lo_i = lo.numerator // lo.denominator
            if Fraction(lo_i) < lo:
                lo_i += 1                                   # ceil
            hi_i = hi.numerator // hi.denominator            # floor
            accepted = []
            flags = []
            for off in range(lo_i, hi_i + 1):
                fo = Fraction(off)
                if fo == lo:
                    # equality: q keeps it iff every binding d on the left is > q (non-strict there)
                    if all(d > q for d in lb):
                        accepted.append(off); flags.append(True); boundary.add(off % A)
                elif fo == hi:
                    if all(d > q for d in rb):
                        accepted.append(off); flags.append(True); boundary.add(off % A)
                else:
                    accepted.append(off); flags.append(False)
            if accepted:
                for off in accepted:
                    assign[off % A] = q
                rows.append((q, j, accepted[0], accepted[-1], len(accepted), flags))
    return rows, assign, boundary


def phi(n):
    r = n
    m = n
    p = 2
    while p * p <= m:
        if m % p == 0:
            while m % p == 0:
                m //= p
            r -= r // p
        p += 1
    if m > 1:
        r -= r // m
    return r


def circular_runs(seq):
    """dict q -> number of maximal CIRCULAR runs of value q (prereg section 2.1)."""
    A = len(seq)
    if len(set(seq)) == 1:
        return {seq[0]: 1}
    starts = [i for i in range(A) if seq[i] != seq[(i - 1) % A]]
    out = {}
    for i in starts:
        out[seq[i]] = out.get(seq[i], 0) + 1
    return out


# ------------------------------------------------------------------ driver
CONFIGS = [('W1', 17, 31), ('W2', 17, 36), ('W3', 19, 41), ('W4', 19, 60),
           ('T1', 12, 43), ('T2', 12, 45), ('T3', 14, 101), ('T4', 14, 100)]


def run(cid, bexp, M, hashfile):
    A = 1 << (bexp - 1)
    # ---- STEP 1: prediction FIRST, written + hashed, before k_den exists
    rows, assign, boundary = predict_levelsets(A, M)
    lines = ["%d\t%d\t%d\t%d\t%d" % (q, j, lo, hi, n) for (q, j, lo, hi, n, f) in rows]
    blob = "\n".join(lines).encode()
    h = hashlib.sha256(blob).hexdigest()
    with open("endpoints_%s.tsv" % cid, "w") as fh:
        fh.write("\n".join(lines) + "\n")
    hashfile.write("%s\tbexp=%d\tM=%d\tintervals=%d\tsha256=%s\n" % (cid, bexp, M, len(rows), h))
    hashfile.flush()

    # ---- STEP 2: now compute the observed sequence
    seq = k_den_sequence(A, M)

    # ---- H2b: exact off-by-off identity
    mism_int = []
    mism_bnd = []
    for off in range(A):
        pred = assign.get(off, 0)
        if pred != seq[off]:
            (mism_bnd if off in boundary else mism_int).append((off, pred, seq[off]))

    # ---- H2a: run counts
    robs = circular_runs(seq)
    rhat = {}
    for (q, j, lo, hi, n, f) in rows:
        rhat[q] = rhat.get(q, 0) + 1
    Qsafe = [q for q in range(1, M + 1) if q * (q + M) <= A]
    safe_cells = [q for q in Qsafe if phi(q) >= 2]
    unsafe = [q for q in range(1, M + 1) if q not in Qsafe]
    safe_hit = sum(1 for q in safe_cells if robs.get(q, 0) == phi(q))
    tight_cells = [q for q in unsafe if q > 2]
    tight_hit = sum(1 for q in tight_cells if robs.get(q, 0) == rhat.get(q, 0))
    n_int = sum(n for (_, _, _, _, n, _) in rows)

    print("\n== %s  bexp=%d A=%d M=%d ==" % (cid, bexp, A, M))
    print("   predicted intervals = %d   (sum phi(q) = %d)   covered offsets = %d / %d"
          % (len(rows), sum(phi(q) for q in range(1, M + 1)), n_int, A))
    print("   H2b  mismatch_interior = %d   mismatch_boundary = %d   TOTAL = %d"
          % (len(mism_int), len(mism_bnd), len(mism_int) + len(mism_bnd)))
    for off, pr, ob in mism_int[:8]:
        print("        interior mismatch off=%d predicted=%d observed=%d" % (off, pr, ob))
    for off, pr, ob in mism_bnd[:8]:
        print("        boundary mismatch off=%d predicted=%d observed=%d" % (off, pr, ob))
    print("   H2a-safe   r_q == phi(q)  : %d / %d informative safe cells" % (safe_hit, len(safe_cells)))
    print("   H2a-tight  r_q == rhat_q  : %d / %d informative deficiency cells"
          % (tight_hit, len(tight_cells)))
    if len(safe_cells) and safe_hit < len(safe_cells):
        bad = [q for q in safe_cells if robs.get(q, 0) != phi(q)][:8]
        for q in bad:
            print("        safe-cell miss q=%d  r_obs=%d  phi=%d  rhat=%d"
                  % (q, robs.get(q, 0), phi(q), rhat.get(q, 0)))
    if len(tight_cells) and tight_hit < len(tight_cells):
        bad = [q for q in tight_cells if robs.get(q, 0) != rhat.get(q, 0)][:8]
        for q in bad:
            print("        deficiency-cell miss q=%d  r_obs=%d  rhat=%d  phi=%d"
                  % (q, robs.get(q, 0), rhat.get(q, 0), phi(q)))
    return dict(cid=cid, A=A, M=M, rows=len(rows), mint=len(mism_int), mbnd=len(mism_bnd),
                safe=(safe_hit, len(safe_cells)), tight=(tight_hit, len(tight_cells)),
                seq=seq, assign=assign, n_int=n_int)


def plants(cid, bexp, M, seq):
    """Section 4.1 wrong-prediction controls -- each MUST produce mismatch > 0."""
    A = 1 << (bexp - 1)
    out = []
    for name, kw in [("W1-plant(all j)", dict(centre_mode='all_j')),
                     ("W2-plant(half-shift)", dict(centre_mode='half')),
                     ("W3-plant(half-width)", dict(width_num=1, width_den=2))]:
        _, asg, _ = predict_levelsets(A, M, **kw)
        mm = sum(1 for off in range(A) if asg.get(off, 0) != seq[off])
        out.append((name, mm))
    return out


if __name__ == '__main__':
    only = sys.argv[1:] if len(sys.argv) > 1 else None
    print("=" * 88)
    print("H2b/H2a -- PREREG_kden_ramanujan_comb_v1.md  (prediction hashed BEFORE k_den computed)")
    print("=" * 88)
    tot_int = tot_bnd = 0
    tot_safe = [0, 0]
    tot_tight = [0, 0]
    tot_rows = 0
    with open("kden_endpoint_hashes.txt", "w") as hf:
        for cid, bexp, M in CONFIGS:
            if only and cid not in only:
                continue
            r = run(cid, bexp, M, hf)
            tot_int += r['mint']; tot_bnd += r['mbnd']; tot_rows += r['rows']
            tot_safe[0] += r['safe'][0]; tot_safe[1] += r['safe'][1]
            tot_tight[0] += r['tight'][0]; tot_tight[1] += r['tight'][1]
            for name, mm in plants(cid, bexp, M, r['seq']):
                print("   PLANT %-22s mismatch = %-8d %s" % (name, mm, "FIRES" if mm > 0 else "*** FAILED -> VOID ***"))
    print("\n" + "=" * 88)
    print("POOLED  intervals=%d   mismatch_interior=%d   mismatch_boundary=%d" % (tot_rows, tot_int, tot_bnd))
    print("POOLED  H2a-safe  %d/%d informative safe cells" % (tot_safe[0], tot_safe[1]))
    print("POOLED  H2a-tight %d/%d informative deficiency cells" % (tot_tight[0], tot_tight[1]))
    print("KDEN_DONE")
