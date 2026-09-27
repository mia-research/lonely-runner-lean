"""End-to-end witness extraction: walk the certificate for a given shape, produce an explicit R,
and check R independently with core.is_clear.  Exact arithmetic throughout."""
import pickle, bisect
from fractions import Fraction as F
from verify import T, inter_closed
from core import is_clear

class Cert:
    def __init__(self, path):
        c = pickle.load(open(path, "rb"))
        self.Rhi = F(c["Rhi"])
        self.top = [(F(a), F(b), self._conv(t)) for a, b, t in c["top"]]

    def _conv(self, node):
        if node is None:
            return None
        return [(F(a), F(b), self._conv(sub)) for a, b, sub in node]

    @staticmethod
    def _find(node, x):
        for (a, b, sub) in node:
            if a <= x <= b:
                return a, b, sub
        raise ValueError("coordinate not covered")

    def witness(self, s):
        """s = [1, s1..s6] sorted, 7<=s6<=9. Returns an explicit R."""
        assert s[0] == 1 and all(s[i] <= s[i + 1] for i in range(6)) and 7 <= s[6] <= 9
        S = [(F(1), F(7)), (F(9), self.Rhi)]
        a, b, node = self._find(self.top, s[6])
        # locate in top cell's own partition
        cells = node
        for L in (6, 5, 4, 3, 2):
            a, b, sub = self._find(cells, s[L])
            S = inter_closed(S, T(a, b, S[0][0], S[-1][1]))
            cells = sub
        x = s[1]
        for (p, q) in S:
            k = max(0, (x * p - 7) // 8)
            while (8 * k + 1) / x <= q:
                lo = max(p, F(8 * k + 1) / x); hi = min(q, F(8 * k + 7) / x)
                if lo <= hi:
                    return lo
                k += 1
        return None

if __name__ == "__main__":
    import sys
    C = Cert(sys.argv[1])
    s = [F(v) for v in sys.argv[2:]]
    R = C.witness(s)
    print("R =", R, float(R), "clear:", is_clear(s, R))
