"""Generate the 4 q in [30,36) sliver lemmas for the half-window read-off branches.
Each enumerates (q,p), derives r from the relation, and closes valid triples via
exc_Rkill with an explicit witness m (else absurd hcop / omega)."""
from math import gcd
from fractions import Fraction as F

def fract(x): return x - (x.numerator // x.denominator)

def witness(p, q, r):
    for m in range(q):
        X = fract(F(r) / q * (F(m) + F(1,2)))
        A = fract(F(p) / q * (F(m) + F(1,2)))
        if F(1,6) <= X <= F(1,2) and F(1,6) <= A <= F(1,3):
            return m
    return None

# name, iota, gamma, relation-string (Lean, in p,q,r)
BRANCHES = [
    ("2_3_c4",   2,  4, "3 * r = 2 * p + 4 * q"),
    ("2_neg3_c4",-2, 4, "3 * r + 2 * p = 4 * q"),
    ("4_3_c3",   4,  3, "3 * r = 4 * p + 3 * q"),
    ("4_neg3_c5",-4, 5, "3 * r + 4 * p = 5 * q"),
]

def gen(name, iota, gamma, rel):
    L = []
    L.append(f"/-- **Sliver `q ∈ [30,36)` for the half-window `{name}` branch.** Each surviving")
    L.append(f"    triple has an explicit `R`-witness (`exc_Rkill`); the rest are ruled out by")
    L.append(f"    coprimality or the cone. -/")
    L.append(f"lemma bhk_prop11_exc_{name}_lo (p q r : ℕ) (hq30 : 30 ≤ q) (hq36 : q < 36)")
    L.append(f"    (hcop : Nat.Coprime p q) (hp : 0 < p) (h3p : 3 * p < q)")
    L.append(f"    (hrq : q < r) (hr32 : 2 * r < 3 * q) (hr3 : {rel})")
    L.append(f"    (h_nogood : ∀ l : ℤ,")
    L.append(f"      ¬ (Int.fract ((r : ℝ) / q * ((l : ℝ) + 1 / 2)) ∈ Set.Icc (1 / 6 : ℝ) (1 / 2) ∧")
    L.append(f"         Int.fract ((p : ℝ) / q * ((l : ℝ) + 1 / 2)) ∈ Set.Icc (1 / 6 : ℝ) (1 / 3))) :")
    L.append(f"    False := by")
    L.append(f"  interval_cases q")
    for q in range(30, 36):
        pmax = (q - 1) // 3
        L.append(f"  · have hpb : p ≤ {pmax} := by omega")
        L.append(f"    interval_cases p")
        for p in range(1, pmax + 1):
            num = iota * p + gamma * q
            if gcd(p, q) != 1:
                L.append(f"    · exact absurd hcop (by decide)")
            elif num <= 0 or num % 3 != 0:
                L.append(f"    · omega")
            else:
                r = num // 3
                if not (q < r and 2 * r < 3 * q):
                    L.append(f"    · omega")
                else:
                    m = witness(p, q, r)
                    assert m is not None, (p, q, r)
                    L.append(f"    · have hr : r = {r} := by omega")
                    L.append(f"      subst hr")
                    L.append(f"      exact bhk_prop11_exc_Rkill {p} {q} {r} {m} (by norm_num) h_nogood "
                             f"(by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])")
    return "\n".join(L)

print("\n\n".join(gen(*b) for b in BRANCHES))
