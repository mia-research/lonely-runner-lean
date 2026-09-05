"""
lrc_gap_investigation_v3.py  — corrected enumeration setup
============================================================
Bugs fixed from v2:
  A.5: was dropping TWO elements from {1,...,n-1} (d + drop2). Correct: only drop d.
       E_full = {1,...,n-1,n} \ {d}  (canonical small-L tuple for Proposition 11.3)
  A.4: L_0 should be lcm(E_non ∪ {n}), not lcm(E_non).
       Free runner M must be explicitly included in E_full.
       E_full = E_non ∪ {n, M} with L = L_0 * M (gcd(M, L_0)=1).
"""
import sys, math, itertools
from fractions import Fraction
from collections import defaultdict

def euler_phi(n):
    r, t = n, n
    p = 2
    while p*p <= t:
        if t % p == 0:
            while t % p == 0: t //= p
            r -= r // p
        p += 1
    if t > 1: r -= r // t
    return r

def extended_gcd(a, b):
    if a == 0: return b, 0, 1
    g, x, y = extended_gcd(b % a, a)
    return g, y - (b // a)*x, x

def mod_inv(a, n):
    g, x, _ = extended_gcd(a % n, n)
    assert g == 1
    return x % n

def lcm_list(lst):
    r = 1
    for x in lst: r = math.lcm(r, x)
    return r

def is_prime(n):
    if n < 2: return False
    for p in range(2, int(n**0.5)+1):
        if n % p == 0: return False
    return True

# ── safe-fibre computation ──────────────────────────────────────────────────

def x0_and_classify(E_full, n, dropped_unit):
    """Return (x0, safe_list, L) classifying each safe fibre by mechanism."""
    d = dropped_unit
    L = lcm_list(E_full)
    N = n * L

    d_inv = mod_inv(d, n)
    r_d   = (-d_inv) % n           # Sole Cover residue (exposed on I_d)
    s_d   = (d_inv - 1) % n       # Dual Sole residue  (exposed on J)

    # Interval bounds (rational)
    I_lo = Fraction(L, n);     I_hi = Fraction(L, n-1)
    J_lo = Fraction((n-2)*L, n-1); J_hi = Fraction((n-1)*L, n)

    # Floor-reset lookup: {b_exact: (e_u, m)} for unit e_u in E_full
    reset_map = {}
    for e_u in E_full:
        if math.gcd(e_u, n) != 1: continue
        for m in range(1, e_u):
            num = m * L
            if num % e_u == 0:
                reset_map[num // e_u] = (e_u, m)

    lo, hi = L, (n-1)*L
    safe_list = []
    for k in range(N):
        if not all(lo <= (e*k) % N <= hi for e in E_full):
            continue
        bf = Fraction(k)
        if I_lo <= bf < I_hi:
            mech = "SOLE_COVER"
            det  = f"r_d={r_d}(=-{d}^-1); d_inv={d_inv}"
        elif J_lo <= bf <= J_hi:
            mech = "DUAL_SOLE"
            det  = f"s_d={s_d}(={d_inv}-1 mod {n})"
        elif k in reset_map:
            e_u, m = reset_map[k]
            dep = (-(m-1)*mod_inv(e_u,n)) % n
            mech = "FLOOR_RESET"
            det  = f"e_u={e_u} m={m} dep={dep}"
        else:
            # Describe gap
            covered = set()
            for e in E_full:
                t = (e*k)//L
                g = math.gcd(e, n)
                for jneg in (t, t+1):
                    j = (-jneg) % n
                    if j % g == 0:
                        eg, ng, jg = e//g, n//g, j//g
                        r0 = (jg * mod_inv(eg,ng)) % ng
                        for kk in range(g): covered.add(r0 + kk*ng)
            uncov = sorted(set(range(n)) - covered)
            floors = {e: (e*k)//L for e in E_full}
            mech = "OTHER"
            det  = f"uncovered={uncov} floors={floors}"
        safe_list.append((k, mech, det))

    return len(safe_list), safe_list, L

# ── A.5 ────────────────────────────────────────────────────────────────────

def run_A5(verbose=False):
    print("\n"+"="*72)
    print("A.5 INVESTIGATION  (composite n≤12, canonical tuple, small L)")
    print("  Correct setup: E_full = {1,...,n-1,n} \\ {d}")
    print("="*72)

    composite_ns = [n for n in range(4,13) if not is_prime(n)]
    all_ext = []

    for n in composite_ns:
        phi_n  = euler_phi(n)
        thresh = n*(n-1)*(phi_n//2 + 1)
        units  = [a for a in range(1,n) if math.gcd(a,n)==1]
        print(f"\n── n={n}  φ={phi_n}  threshold L<{thresh} ──")

        cases, extremal = [], []
        for d in units:
            E_full = [r for r in range(1, n+1) if r != d]
            L = lcm_list(E_full)
            if L >= thresh or L <= 2*n:
                continue
            x0, sf, L_act = x0_and_classify(E_full, n, d)
            rec = dict(n=n, L=L_act, d=d, E_full=sorted(E_full),
                       x0=x0, phi_n=phi_n, safe_fibres=sf)
            cases.append(rec)
            if x0 < phi_n:
                print(f"  *** FAILURE x0={x0}<phi={phi_n}  d={d}  E={sorted(E_full)}  L={L_act}")
            elif x0 == phi_n:
                extremal.append(rec)

        all_ext.extend(extremal)
        if cases:
            x0s = [r['x0'] for r in cases]
            print(f"  cases={len(cases)}  fails={sum(x<phi_n for x in x0s)}  "
                  f"x0∈[{min(x0s)},{max(x0s)}]  extremal={len(extremal)}")
        else:
            print("  no cases in range")
        if extremal:
            _mech_summary(extremal, f"A.5 n={n}", verbose)

    print(f"\nTotal extremal (x0=phi(n)) across all composite n: {len(all_ext)}")
    if all_ext: _mech_summary(all_ext, "A.5 ALL", verbose)

# ── A.4 ────────────────────────────────────────────────────────────────────

def run_A4(verbose=False):
    print("\n"+"="*72)
    print("A.4 INVESTIGATION  (prime n≤30, small M, free runner included)")
    print("  Correct setup: L_0=lcm(E_non∪{n}), E_full=E_non∪{n,M}, L=L_0*M")
    print("="*72)

    prime_ns = [n for n in range(5,31) if is_prime(n)]
    all_ext = []

    for n in prime_ns:
        phi_n = n - 1
        all_res = list(range(1, n))
        print(f"\n── n={n} (prime)  φ={phi_n} ──")

        cases, extremal, has_small_M = [], [], False

        for d1, d2 in itertools.combinations(all_res, 2):
            E_non = [a for a in all_res if a != d1 and a != d2]
            L_0   = lcm_list(E_non + [n])          # CORRECT: include n
            M_0   = math.ceil(n*n*(n-1) / (L_0*(n-2)))

            if M_0 <= 1: continue
            has_small_M = True

            for M in range(1, M_0):
                if math.gcd(M, L_0) != 1: continue  # need gcd(M,L_0)=1 for L=L_0*M
                # Dropped unit for Sole Cover analysis: use d1 (first dropped unit)
                # (d2 may be unit or non-unit for prime n, but both are units)
                for d in (d1, d2):  # try both dropped units as the "Sole Cover dropped"
                    E_full = E_non + [n, M]
                    if len(set(E_full)) != len(E_full): continue  # no duplicates
                    x0, sf, L_act = x0_and_classify(E_full, n, d)
                    rec = dict(n=n, L=L_act, L_0=L_0, M=M, M_0=M_0,
                               d=d, d_other=d2 if d==d1 else d1,
                               E_non=sorted(E_non), E_full=sorted(E_full),
                               x0=x0, phi_n=phi_n, safe_fibres=sf)
                    cases.append(rec)
                    if x0 < phi_n:
                        print(f"  *** FAILURE x0={x0}<phi={phi_n}  d={d}  "
                              f"E_non={sorted(E_non)} M={M} L={L_act}")
                    elif x0 == phi_n:
                        extremal.append(rec)

        all_ext.extend(extremal)
        if not has_small_M:
            print("  M_0=1 for all configs — fully analytic.")
        elif cases:
            x0s = [r['x0'] for r in cases]
            M0s = sorted(set(r['M_0'] for r in cases))
            print(f"  cases={len(cases)}  fails={sum(x<phi_n for x in x0s)}  "
                  f"x0∈[{min(x0s)},{max(x0s)}]  extremal={len(extremal)}  M_0 values={M0s}")
        if extremal:
            _mech_summary(extremal, f"A.4 n={n}", verbose)

    print(f"\nTotal extremal across all primes: {len(all_ext)}")
    if all_ext: _mech_summary(all_ext, "A.4 ALL", verbose)

# ── printer ────────────────────────────────────────────────────────────────

def _mech_summary(cases, label, verbose=False):
    print(f"\n  ┌─ {label}: {len(cases)} extremal (x0=phi(n)) ─┐")
    tally = defaultdict(int)
    sole=dual=reset=mixed=other_cnt=0
    for c in cases:
        mechs = {m for (_,m,_) in c['safe_fibres']}
        for m in mechs: tally[m] += 1
        if   mechs=={'SOLE_COVER'}:    sole  += 1
        elif mechs=={'DUAL_SOLE'}:     dual  += 1
        elif mechs=={'FLOOR_RESET'}:   reset += 1
        elif 'OTHER' in mechs:         other_cnt += 1
        else:                          mixed += 1
    for mech, cnt in sorted(tally.items()):
        print(f"  │  {mech:14s}  in {cnt}/{len(cases)} cases")
    print(f"  │  pure: sole={sole} dual={dual} reset={reset} mixed={mixed} OTHER={other_cnt}")
    if other_cnt:
        print("  │  *** OTHER safe fibres — need investigation ***")
        for c in cases:
            oth = [(k,d) for (k,m,d) in c['safe_fibres'] if m=='OTHER']
            if oth:
                print(f"  │    n={c['n']} L={c['L']} d={c['d']} E={c['E_full']}")
                for k,d in oth: print(f"  │      k={k}: {d}")
    if verbose:
        print("  │  Detailed:")
        for c in cases:
            tag = f"M={c['M']}" if 'M' in c else f"L={c['L']}"
            print(f"  │    n={c['n']} {tag} d={c['d']} E={c.get('E_full',c.get('E_non'))} x0={c['x0']}")
            for (k,m,d) in c['safe_fibres']:
                print(f"  │      k={k:6d}  {m:14s}  {d}")
    print(f"  └{'─'*52}┘")

if __name__ == "__main__":
    verbose = "-v" in sys.argv or "--verbose" in sys.argv
    do_a4   = "--a4" in sys.argv
    do_a5   = "--a5" in sys.argv
    if not do_a4 and not do_a5: do_a4=do_a5=True

    if do_a5: run_A5(verbose=verbose)
    if do_a4: run_A4(verbose=verbose)
