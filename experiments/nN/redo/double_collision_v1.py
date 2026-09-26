"""E103's double grid collisions (d_min = 1, readings 16 and 24 both on multiples of 8*d_min, in the subject's slot at
the bound).  Move one collider off the grid, then the other, then both together, in exact steps of 1/16 across
(-1, 1) (a collider stays in the slot at the bound while within 1 of its multiple of 8), and follow the cascade's
isolation: the instant t*, R* = 8 d_min t*, and the runner e and lap K whose opening it is.  Every speed positive,
exact (Fraction), BSM."""
from fractions import Fraction as F
from arrangement_lib import nd
from lap1_reopen_v1 import cascade, landing

SETS = [(1, 2, 3, 4, 15, 16, 24), (1, 2, 3, 4, 16, 22, 24), (1, 2, 3, 4, 16, 23, 24), (1, 2, 3, 10, 15, 16, 24)]
STEPS = [F(j, 16) for j in range(-15, 16)]

def run(T):
    t = cascade(T); e, K = landing(T, t)
    return t, 8 * T[0] * t, e, K

def show(T, moved):
    print(f"\n{T}: moving {moved}")
    prev = None
    for dl in STEPS:
        U = tuple(sorted(d + dl if d in moved else d for d in T))
        t, R, e, K = run(U)
        tag = (e - (dl if e - dl in moved else 0), K)
        mark = '' if tag == prev else '   <- setter changes'
        prev = tag
        print(f"  delta={str(dl):>6}  R*={str(R):>10} = {float(R):.4f}  setter {e} lap {K}{mark}")

if __name__ == '__main__':
    for T in SETS:
        show(T, {16}); show(T, {24}); show(T, {16, 24})
