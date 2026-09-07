"""
rate_bad_states_v1.py

(1) Re-derive BAD(rho0) for the five-runner unit-complete configuration at n=8.
(2) Test the "octant line" idea: the seven fibres b = c*L/8, c = 1..7.

Exact integer arithmetic only.  No floating point anywhere.

Setting
-------
n = 8, L = lcm(E), 8 | L.  E_non = five speeds e_1,e_3,e_5,e_7,e_{rho0}
with e_rho = rho (mod 8), rho0 in {2,4,6}.

t_e(b) = floor(e*b/L)
Sol(e,j,8) = { r in Z/8 : e*r = j (mod 8) }
bad(e,t,8) = Sol(e,-t,8) union Sol(e,-(t+1),8)

Only e mod 8 and t mod 8 matter, so the blocked configuration is a function of
T(b) = (t_1,t_3,t_5,t_7,t_{rho0}) mod 8 in (Z/8)^5.
"""

from itertools import product

RHOS_UNIT = (1, 3, 5, 7)


def sol(e_mod8, j):
    """{ r in Z/8 : e*r = j (mod 8) } -- exact, brute force over Z/8."""
    return frozenset(r for r in range(8) if (e_mod8 * r) % 8 == j % 8)


def bad_set(e_mod8, t):
    """bad(e,t,8) = Sol(e,-t,8) u Sol(e,-(t+1),8)."""
    return sol(e_mod8, -t) | sol(e_mod8, -(t + 1))


# ---- sanity on the structural claims quoted in the setting -------------------

def check_structure():
    msgs = []
    for e in (1, 3, 5, 7):
        assert (e * e) % 8 == 1, "units of Z/8 are not self-inverse"
        for t in range(8):
            bs = bad_set(e, t)
            assert bs == {(-t * e) % 8, (-(t + 1) * e) % 8}, (e, t)
            assert len(bs) == 2
            assert sum(1 for r in bs if r % 2 == 1) == 1, (e, t, bs)
    msgs.append("units: bad(e,t) = {-t*e, -(t+1)*e}, always 1 odd + 1 even  OK")

    H2 = frozenset({0, 4})
    H4 = frozenset({0, 2, 4, 6})
    for e in (2, 6):
        for t in range(8):
            bs = bad_set(e, t)
            assert len(bs) == 2, (e, t, bs)
            assert len({r % 2 for r in bs}) == 1, (e, t, bs)
            # coset of H2
            r0 = min(bs)
            assert bs == frozenset((r0 + h) % 8 for h in H2)
    msgs.append("rho0 in {2,6}: bad is a single coset of H2={0,4}, 2 elements, one parity  OK")
    for t in range(8):
        bs = bad_set(4, t)
        assert len(bs) in (0, 4), (t, bs)
        if bs:
            assert bs in (H4, frozenset({1, 3, 5, 7})), (t, bs)
    msgs.append("rho0 = 4: bad is empty or a full parity class (coset of H4)  OK")
    return msgs


# ---- BAD(rho0) enumeration ---------------------------------------------------

def build_bad(rho0):
    """Set of T in (Z/8)^5 (tuple order 1,3,5,7,rho0) whose blocked union is Z/8."""
    rhos = RHOS_UNIT + (rho0,)
    tabs = [[bad_set(r, t) for t in range(8)] for r in rhos]
    full = frozenset(range(8))
    bad = set()
    for T in product(range(8), repeat=5):
        u = set()
        for i in range(5):
            u |= tabs[i][T[i]]
            if len(u) == 8:
                break
        if len(u) == 8:
            bad.add(T)
    return bad


# ---- the octant line ---------------------------------------------------------
#
# Every e in E divides L, and b = c*L/8 is an integer for c = 0..8 because 8 | L.
# For c = 1..7 we have L/8 <= b <= 7L/8, i.e. b in B_div.
#
# Write e_rho = 8*a_rho + rho  (a_rho = (e_rho - rho)/8 >= 0 an integer).
# Then  t_rho(c*L/8) = floor(c*e_rho/8) = c*a_rho + floor(c*rho/8).
#
# So T(c*L/8) = c*A + F(c)  in (Z/8)^5, where A = (a_rho mod 8) and
# F(c) = (floor(c*rho/8))_rho is explicit.

def octant_state(A, c, rho0):
    rhos = RHOS_UNIT + (rho0,)
    return tuple((c * A[i] + (c * rhos[i]) // 8) % 8 for i in range(5))


def octant_check(rho0, bad, cs=range(1, 8)):
    """Return list of A in (Z/8)^5 for which EVERY c in cs gives a BAD state."""
    fails = []
    for A in product(range(8), repeat=5):
        if all(octant_state(A, c, rho0) in bad for c in cs):
            fails.append(A)
    return fails


def main():
    for m in check_structure():
        print("  " + m)
    print()

    expected = {2: 1152, 4: 1600, 6: 1152}
    bads = {}
    ok = True
    for rho0 in (2, 4, 6):
        B = build_bad(rho0)
        bads[rho0] = B
        got, exp = len(B), expected[rho0]
        print(f"|BAD(rho0={rho0})| = {got}   expected {exp}   "
              f"{'MATCH' if got == exp else '*** MISMATCH ***'}")
        ok &= (got == exp)
    print(f"state space |(Z/8)^5| = {8**5}")
    print("re-derivation:", "AGREES" if ok else "DISAGREES -- STOP")
    print()

    if not ok:
        return

    print("Octant-line check: b = c*L/8, c = 1..7, over all A in (Z/8)^5")
    for rho0 in (2, 4, 6):
        f = octant_check(rho0, bads[rho0])
        print(f"  rho0={rho0}: A with all 7 octant fibres BAD: {len(f)} / {8**5}")
        for a in f[:20]:
            print("      A =", a)


if __name__ == "__main__":
    main()
