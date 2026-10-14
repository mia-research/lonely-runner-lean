"""
rate_certificate_v1.py

Shrink the exhaustive 32768-case octant check to a hand-auditable certificate.

c = 1 gives T = A exactly (because floor(rho/8) = 0 for rho < 8), so the only A
that need any further work are A in BAD(rho0).  Then c = 2, then c = 3.
Prints the nested residuals and the final witness table.

Exact integer arithmetic only.
"""
from itertools import product
from rate_bad_states_v1 import build_bad, RHOS_UNIT


def F(c, rho0):
    rhos = RHOS_UNIT + (rho0,)
    return tuple((c * r) // 8 % 8 for r in rhos)


def state(A, c, rho0):
    f = F(c, rho0)
    return tuple((c * A[i] + f[i]) % 8 for i in range(5))


def main():
    for rho0 in (2, 4, 6):
        bad = build_bad(rho0)
        print(f"===== rho0 = {rho0} =====")
        print(f"  F(c) offsets: " + "  ".join(f"c={c}:{F(c,rho0)}" for c in (1, 2, 3)))

        R1 = [A for A in product(range(8), repeat=5) if state(A, 1, rho0) in bad]
        # sanity: state(A,1) == A
        assert all(state(A, 1, rho0) == A for A in product(range(8), repeat=5))
        print(f"  c=1 : T = A.  survivors (A in BAD)            = {len(R1):5d}  (= |BAD|)")

        R2 = [A for A in R1 if state(A, 2, rho0) in bad]
        print(f"  c=2 : T = 2A + {F(2,rho0)}.  survivors        = {len(R2):5d}")

        R3 = [A for A in R2 if state(A, 3, rho0) in bad]
        print(f"  c=3 : T = 3A + {F(3,rho0)}.  survivors        = {len(R3):5d}")
        if R3:
            print("        *** residual non-empty -- {1,2,3} does not suffice ***")
        else:
            print("        residual EMPTY: c in {1,2,3} suffices for every A.")

        # full witness table for the c=2 survivors
        print(f"  witness table for the {len(R2)} A that survive c=1 and c=2 "
              f"(all cleared by c=3):")
        for A in R2:
            print(f"      A={A}  ->  T(3L/8) = {state(A,3,rho0)}  SAFE")
        print()


if __name__ == "__main__":
    main()
