"""
lrc_v15_lemma0_verify.py

Verifies Lemma 0(c): the defect-gap Δ(m) = A_(m,1)_left − t*(m) is strictly positive
for all m >= 1, where:

    A_(m,1)_left = (110m + 87) / (121m + 99)    [left endpoint of earliest dangerous window]
    t*(m)        = (55m + 1) / (121m)            [staircase bound]

Also computes the exact numerator of Δ(m) to give the closed-form formula.
"""

from fractions import Fraction

def a_left(m):
    """Left endpoint of earliest dangerous window A_(m,1)."""
    return Fraction(110*m + 87, 121*m + 99)

def t_star(m):
    """Staircase bound t*(m) = (55m+1)/(121m)."""
    return Fraction(55*m + 1, 121*m)

def delta(m):
    """Gap Δ(m) = A_(m,1)_left - t*(m)."""
    return a_left(m) - t_star(m)

print("=" * 70)
print("LEMMA 0(c) VERIFICATION: Δ(m) = A_(m,1)_left - t*(m) > 0")
print("=" * 70)
print()
print(f"{'m':>4}  {'A_(m,1)_left':>20}  {'t*(m)':>20}  {'Δ(m)':>25}  {'Δ>0?':>6}")
print("-" * 85)

all_positive = True
for m in range(1, 21):
    al = a_left(m)
    ts = t_star(m)
    d  = delta(m)
    pos = d > 0
    all_positive = all_positive and pos
    print(f"{m:>4}  {str(al):>20}  {str(ts):>20}  {str(d):>25}  {'YES' if pos else 'NO':>6}")

print()
print(f"All Δ(m) > 0 for m=1,...,20: {'YES ✓' if all_positive else 'FAIL ✗'}")
print()

# Compute the closed-form numerator
print("=" * 70)
print("CLOSED-FORM ANALYSIS")
print("=" * 70)
print()
print("Numerator of Δ(m) (before simplification by GCD):")
print()
print("  Δ(m) = (110m+87)/(121m+99) - (55m+1)/(121m)")
print("       = [121m(110m+87) - (55m+1)(121m+99)] / [121m(121m+99)]")
print()

# Compute symbolically for small m to identify the numerator polynomial
import sympy
m = sympy.Symbol('m')
num = 121*m*(110*m + 87) - (55*m + 1)*(121*m + 99)
num_expanded = sympy.expand(num)
print(f"  Numerator polynomial: {num_expanded}")
print()

# Factor it
num_factored = sympy.factor(num_expanded)
print(f"  Factored: {num_factored}")
print()
print("  Denominator: 121m(121m+99)")
print()

# Verify sign
print("  Since coefficients of m^2 and m are positive and constant term is negative,")
print("  we check the minimum over m >= 1:")
for m_val in range(1, 5):
    n = int(num_expanded.subs(sympy.Symbol('m'), m_val))
    print(f"    m={m_val}: numerator = {n} {'> 0 ✓' if n > 0 else '<= 0 ✗'}")
print()

# Show the minimum (derivative = 0)
m_sym = sympy.Symbol('m', positive=True)
num_sym = sympy.expand(121*m_sym*(110*m_sym + 87) - (55*m_sym + 1)*(121*m_sym + 99))
deriv = sympy.diff(num_sym, m_sym)
print(f"  Derivative of numerator w.r.t. m: {deriv}")
print("  (Positive linear, so numerator is increasing for m >= 1)")
print()
print(f"  Minimum at m=1: numerator = {int(num_sym.subs(m_sym, 1))}")
print(f"  Minimum Δ(1) = {delta(1)} = {float(delta(1)):.6f}")
print()
print("CONCLUSION: Δ(m) > 0 for all m >= 1.")
print("The staircase bound t*(m) strictly precedes every dangerous window.")
print("The dynamic front is closed (modulo Lemma D3's envelope proof).")
