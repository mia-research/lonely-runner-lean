"""
n=6 BHK (1,-2)S pentagon kill — EXACT witnesses for the narrow-window tail.

The wide-window pentkill (bhk_prop11_exc_1_neg2_pentkill) covers every instance
with  hwb : 36*s <= r*(5*s - 4*r).  The narrow tail is its complement:
    36*s > r*(5*s - 4*r)   <=>   s < 4 r^2 / (5r - 36).

Constraints (from the lemma hypotheses), (i,j)=(1,-2), rigidity 2r+p=3q:
    q >= 18, p>0, gcd(p,q)=1, 3p<q, q<r, 2r<3q, r<s, p=3q-2r.
Even q force p even (p=3q-2r) hence gcd(p,q)>1, so only ODD q survive; and the
slant bound holds for q>=25, so the narrow set is q in {19,21,23}.

For each narrow instance we find an integer witness l such that the cone point
    X = frac(r*(2l+1)/(2q)),  Y = frac(p*(2l+1)/(2q))
satisfies pent_no_good's six conditions EXACTLY (Fraction arithmetic), and we
emit X,Y in lowest terms plus the integer parts Kx,Ky (floors) so the Lean
`Int.fract = ...` proofs are pure transcription.
"""
from fractions import Fraction as F
from math import gcd, floor


def conds(X, Y, p, q, r, s):
    M = F(s - q, 3 * q * s)
    return [
        ("h39",  X - (F(1, 6) - r * M)),                      # X >= 1/6 - r M
        ("h40",  Y - (F(1, 6) - p * M)),                      # Y >= 1/6 - p M
        ("h41",  (F(1, 3) + (q - p) * M) - Y),                # Y <= 1/3 + (q-p) M
        ("hxle", F(5, 6) - X),                                # X <= 5/6
        ("h42a", (F(5, 6) - X) / r + (Y - F(1, 6)) / p - F(1, 3 * s)),
        ("h42b", (F(5, 6) - X) / r + (F(1, 3) - Y) / (q - p) - F(1, 3 * s)),
    ]


def narrow_instances():
    out = []
    for q in (19, 21, 23):
        for p in range(1, q, 2):
            if 3 * p >= q or gcd(p, q) != 1 or (3 * q - p) % 2 != 0:
                continue
            r = (3 * q - p) // 2
            if not (q < r and 2 * r < 3 * q):
                continue
            for s in range(r + 1, 3 * q + 1):
                # narrow tail: width bound FAILS
                if 36 * s > r * (5 * s - 4 * r):
                    out.append((p, q, r, s))
    return out


def fract_exact(num, den):
    """frac(num/den) with num,den ints, den>0: returns (K, frac) with frac in lowest terms."""
    K = floor(F(num, den))
    fr = F(num, den) - K
    return K, fr


def best_witness(p, q, r, s):
    """Return (l, X, Y, Kx, Ky, minmargin) for the l with the largest min-condition margin."""
    best = None
    for l in range(-2 * q, 2 * q + 1):
        Kx, X = fract_exact(r * (2 * l + 1), 2 * q)
        Ky, Y = fract_exact(p * (2 * l + 1), 2 * q)
        cs = conds(X, Y, p, q, r, s)
        m = min(v for _, v in cs)
        if m >= 0:
            if best is None or m > best[-1]:
                best = (l, X, Y, Kx, Ky, m)
    return best


def main():
    inst = narrow_instances()
    print(f"narrow instances: {len(inst)}")
    print("=" * 70)
    for (p, q, r, s) in inst:
        w = best_witness(p, q, r, s)
        assert w is not None, f"NO WITNESS for q={q} p={p} r={r} s={s}"
        l, X, Y, Kx, Ky, m = w
        # sanity: X in (1/4,3/4) branch => Y = 3/2 - 2X
        branch_ok = (Y == F(3, 2) - 2 * X)
        cs = conds(X, Y, p, q, r, s)
        print(f"q={q} p={p} r={r} s={s} | l={l}")
        print(f"    X = {X}  (= {r}*(2*{l}+1)/(2*{q}) - {Kx})   Kx={Kx}")
        print(f"    Y = {Y}  (= {p}*(2*{l}+1)/(2*{q}) - {Ky})   Ky={Ky}   Y=3/2-2X: {branch_ok}")
        print(f"    min margin = {m}  (~{float(m):.5f})")
        for name, v in cs:
            print(f"      {name:5s} = {v}  (~{float(v):.5f}) {'OK' if v >= 0 else 'FAIL'}")
        print("-" * 70)


if __name__ == "__main__":
    main()
