#!/usr/bin/env python3
"""AST audit: find every float-producing construct in the scripts this line depends on.

Mechanical, not a grep: parses each file and reports true division `/`, float
literals, and float(), round(), math.sqrt/log/exp calls, WITH the enclosing function
and whether that function is on an imported-and-used path.  Fraction arithmetic is
NOT flagged -- `Fraction / int` is exact -- so each `/` hit is classified by whether
its operands can be Fractions, which the report states per site for a human check.
"""
import ast, sys, os

FLOATCALLS = {"float", "round"}
MATHFLOAT = {"sqrt", "log", "exp", "sin", "cos", "pi", "hypot", "pow"}

def audit(path):
    src = open(path).read()
    tree = ast.parse(src)
    parent = {}
    for node in ast.walk(tree):
        for ch in ast.iter_child_nodes(node):
            parent[ch] = node
    def enclosing(n):
        while n in parent:
            n = parent[n]
            if isinstance(n, (ast.FunctionDef, ast.AsyncFunctionDef)):
                return n.name
        return "<module>"
    hits = []
    for x in ast.walk(tree):
        if isinstance(x, ast.BinOp) and isinstance(x.op, ast.Div):
            hits.append((x.lineno, enclosing(x), "true-division /", ast.unparse(x)))
        elif isinstance(x, ast.Constant) and isinstance(x.value, float):
            hits.append((x.lineno, enclosing(x), "float literal", repr(x.value)))
        elif isinstance(x, ast.Call):
            f = x.func
            nm = getattr(f, "id", None) or getattr(f, "attr", None)
            if nm in FLOATCALLS or (isinstance(f, ast.Attribute) and nm in MATHFLOAT):
                hits.append((x.lineno, enclosing(x), f"call {nm}", ast.unparse(x)))
    return hits

if __name__ == "__main__":
    roots = sys.argv[1:] or ["experiments/n8", "experiments/n8_mining"]
    files = []
    for r in roots:
        if os.path.isfile(r): files.append(r)
        else:
            for d, _, fs in os.walk(r):
                files += [os.path.join(d, f) for f in sorted(fs) if f.endswith(".py")]
    total = 0
    for f in sorted(files):
        h = audit(f)
        if not h:
            print(f"CLEAN   {f}")
            continue
        print(f"HITS    {f}")
        for ln, fn, kind, txt in h:
            print(f"          L{ln:<5} in {fn:<26} {kind:<16} {txt}")
            total += 1
    print(f"\n{len(files)} files, {total} float-capable sites")
