#!/usr/bin/env python3
"""
No-float guard (CLAUDE.md, rule tightened 2026-08-27).

Float is banned EVERYWHERE in this folder's scripts, not just the signal path.
AST-based, so comments/strings are ignored and only real operations are flagged.

Usage:
    python check_no_float.py                 # scan every *.py in this folder
    python check_no_float.py f1.py f2.py     # scan the named files
    python check_no_float.py --summary       # one line per file, counts only

A flagged line PASSES only if it carries a JUSTIFIED note:
    <code>   # noqa: float — <reason>
The reason is mandatory; a bare "# noqa: float" is itself a violation.
A discrete/algebraic DECISION in float (perfect-square, vanishing, equality,
root-of-unity, multiplicity, integrality) has NO valid exemption — do it exactly.
"""
import ast, sys, os, re, glob

NP_FLOAT = {  # numpy/scipy float-producing calls we flag (np.<name> / numpy.<name>)
    "mean", "std", "var", "average", "roots", "angle", "allclose", "isclose",
    "sqrt", "exp", "log", "log2", "log10", "sin", "cos", "tan", "abs", "absolute",
    "dot", "linalg", "corrcoef", "cov", "fft", "real", "imag", "float64", "float32",
    "arctan", "arctan2", "power", "exp2", "median", "percentile", "quantile",
}
NOTE_RE = re.compile(r"#\s*noqa:\s*float\s*[—:\-]\s*\S")  # requires a reason after the token


def _root_name(node):
    while isinstance(node, ast.Attribute):
        node = node.value
    return node.id if isinstance(node, ast.Name) else None


def violations(path):
    src = open(path).read().splitlines()
    tree = ast.parse("\n".join(src), filename=path)
    out = []

    def noted(ln):  # a justified note on that source line exempts it
        return 1 <= ln <= len(src) and NOTE_RE.search(src[ln - 1]) is not None

    def bare_noqa(ln):
        return 1 <= ln <= len(src) and ("# noqa: float" in src[ln - 1]) and not noted(ln)

    for node in ast.walk(tree):
        ln = getattr(node, "lineno", None)
        if ln is None:
            continue
        msg = None
        if isinstance(node, ast.BinOp) and isinstance(node.op, ast.Div):
            msg = "true division '/'  (use // or Fraction)"
        elif isinstance(node, ast.BinOp) and isinstance(node.op, ast.Pow) and \
                isinstance(node.right, ast.Constant) and isinstance(node.right.value, float):
            msg = f"** {node.right.value!r} (fractional power)"
        elif isinstance(node, ast.Call) and isinstance(node.func, ast.Name) and node.func.id in ("float", "round"):
            msg = f"{node.func.id}(...) call"
        elif isinstance(node, ast.Call) and isinstance(node.func, ast.Attribute):
            root, attr = _root_name(node.func), node.func.attr
            if attr == "astype":
                a = node.args[0] if node.args else None
                if (isinstance(a, ast.Name) and a.id == "float") or (isinstance(a, ast.Constant) and a.value is float):
                    msg = ".astype(float)"
            elif root in ("math", "cmath"):
                msg = f"{root}.{attr}(...)  (float math)"
            elif root in ("np", "numpy") and attr in NP_FLOAT:
                msg = f"{root}.{attr}(...)  (numpy float)"
        elif isinstance(node, ast.Attribute) and node.attr in ("real", "imag"):
            msg = f".{node.attr}  (complex-float part)"
        elif isinstance(node, ast.Constant) and isinstance(node.value, float):
            msg = f"float literal {node.value!r}"

        if msg and not noted(ln):
            out.append((ln, msg))
        if bare_noqa(ln):
            out.append((ln, "bare '# noqa: float' with NO reason (justification required)"))
    return sorted(set(out))


def main(argv):
    summary = "--summary" in argv
    paths = [a for a in argv if not a.startswith("--")]
    if not paths:
        here = os.path.dirname(os.path.abspath(__file__))
        paths = sorted(glob.glob(os.path.join(here, "*.py")))
    bad = 0
    nbad = 0
    for p in paths:
        try:
            v = violations(p)
        except (FileNotFoundError, SyntaxError) as e:
            print(f"SKIP ({type(e).__name__}): {p}")
            continue
        if v:
            bad = 1
            nbad += 1
            if summary:
                print(f"FLOAT-RISK ({len(v):>3}): {os.path.basename(p)}")
            else:
                print(f"FLOAT-RISK in {os.path.basename(p)}:")
                for ln, m in v:
                    print(f"  line {ln}: {m}")
        elif not summary:
            print(f"OK: {os.path.basename(p)}")
    print(f"\n{nbad}/{len(paths)} files have un-noted float.")
    return bad


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
