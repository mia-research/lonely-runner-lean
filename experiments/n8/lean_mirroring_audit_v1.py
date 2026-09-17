"""How much of the structural Lean is the same theorem twice?

Owner, 2026-09-17: "I think there might be more lean mirroring than we suspect."

Two kinds are looked for:
  A. IDENTICAL STATEMENTS -- the same proposition declared more than once, possibly in
     different namespaces, which the kernel will not complain about.
  B. SAME SHAPE -- statements identical after normalising the bound variable names and
     numerals, i.e. one is the other at different parameters.
"""
import re, pathlib, collections, hashlib

C = pathlib.Path("LonelyRunner/LonelyRunner/LRC/Cascade")
GEN = {"PinnedBatch1","PinnedBatch2","PinnedBatch3","PinnedBatch4","CensusBatch","CensusFamilies"}

decls = []
for f in sorted(C.glob("*.lean")):
    if f.stem in GEN: continue
    txt = f.read_text()
    ns = None
    for m in re.finditer(r'^(?:namespace (\S+)|(?:theorem|lemma) ([A-Za-z_][A-Za-z0-9_\']*)([\s\S]*?):=)', txt, re.M):
        if m.group(1): ns = m.group(1); continue
        name, body = m.group(2), m.group(3)
        stmt = re.sub(r'\s+', ' ', body).strip()
        decls.append((f.stem, ns, name, stmt))

print(f"structural declarations parsed : {len(decls)}")

# A. identical statements
by_stmt = collections.defaultdict(list)
for mod, ns, name, stmt in decls:
    by_stmt[stmt].append((mod, ns, name))
dupes = {k: v for k, v in by_stmt.items() if len(v) > 1}
print()
print(f"A. IDENTICAL STATEMENTS: {len(dupes)} propositions declared more than once")
for stmt, where in sorted(dupes.items(), key=lambda kv: -len(kv[1])):
    names = ", ".join(f"{m}.{n}" for m, _, n in where)
    print(f"   x{len(where)}  {names}")
    print(f"        {stmt[:120]}")

# B. same shape after normalising identifiers and numerals
def shape(s):
    s = re.sub(r'\b[a-z][A-Za-z0-9_\']*\b', 'v', s)
    s = re.sub(r'\b\d+\b', 'N', s)
    return re.sub(r'\s+', ' ', s)
by_shape = collections.defaultdict(list)
for mod, ns, name, stmt in decls:
    by_shape[shape(stmt)].append(f"{mod}.{name}")
fam = {k: v for k, v in by_shape.items() if len(v) > 1}
print()
print(f"B. SAME SHAPE (identifiers and numerals normalised): {len(fam)} families covering "
      f"{sum(len(v) for v in fam.values())} declarations")
for sh, names in sorted(fam.items(), key=lambda kv: -len(kv[1]))[:10]:
    print(f"   x{len(names):<3} {', '.join(names[:6])}{' ...' if len(names)>6 else ''}")

print()
print("=" * 72)
print("ADJUDICATION -- what the mechanical pass finds, and what it CANNOT find.")
print()
print("A1. Irrational.clear_of_ratio declared TWICE, lines 17 and 125, statement AND proof")
print("    byte-identical, in namespaces IrrationalDemo and IrrationalCascade. The kernel")
print("    accepts it because the namespaces differ. Genuine duplication.")
print()
print("A2/A3. SmallOrders.three_first_isolation = VersionB.order_three, and the four_ pair.")
print("    VersionB's own header says it is a SECOND development of the proved cases --")
print("    'Version B for the proved cases' -- so these are deliberate alternatives, not")
print("    accidents. Worth knowing they are the same proposition; not a defect.")
print()
print("B. The five same-shape families are mostly small-order statements at different n")
print("   (two_diffs / three_diffs / four_diffs). Same shape, different content.")
print()
print("THE LIMIT, and it is the important one. This pass compares TEXT. It cannot see a")
print("mirror written in different types. The clearest example is one created on 2026-09-17:")
print()
print("   clear_of_residue_band   naturals, band as  m*(n*k+1) mod (n*e) in [e, (n-1)*e]")
print("   clear_at_opening_of_band  reals, band as   exists M, n*M+1 <= (d/e)*(n*k+1) <= n*M+n-1")
print()
print("   'x mod m in [a,b]' and 'exists M, m*M+a <= x <= m*M+b' are the SAME condition, so")
print("   the second is a generalisation of the first. It was proved from scratch that day")
print("   without checking whether the tree already had it. The detector scores them as")
print("   unrelated because the types and the spelling differ.")
print()
print("So the count below is a LOWER BOUND on the mirroring, and the cases it misses are")
print("exactly the ones worth finding -- same mathematics, different dress.")
