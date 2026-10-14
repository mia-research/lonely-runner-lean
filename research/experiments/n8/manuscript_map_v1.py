"""The manuscript interaction map: section -> declarations -> sections, and the open-item register.

Built so an edit can be TRACED rather than hoped about. Run it on the frozen version to get a baseline,
run it on a successor, and diff: anything that leaves the open register, any citation that stops
resolving, any section reference that dangles, shows up as a difference rather than as an impression.

It checks four invariants, and reports rather than asserts:
  I1  every section reference (see-section-X) resolves to a real heading
  I2  every backticked identifier that LOOKS like a declaration resolves in the Lean tree
  I3  every open item is located, with its section and line
  I4  the grade tally per section

Usage:  python3 manuscript_map_v1.py <manuscript.md> [out.json]
"""
import json, re, subprocess, sys, os
from collections import defaultdict, Counter

LEAN_ROOT = 'LonelyRunner/LonelyRunner'

def lean_declarations():
    """every declaration name in the Lean tree, bare and namespace-qualified"""
    out = subprocess.run(
        ['grep', '-rhnE', r'^\s*(private |protected |noncomputable )*(theorem|lemma|def|abbrev|instance) +[A-Za-z_][A-Za-z0-9_.\']*',
         LEAN_ROOT], capture_output=True, text=True).stdout
    bare = set()
    for line in out.splitlines():
        toks = line.split()
        for i, t in enumerate(toks):
            if t in ('theorem', 'lemma', 'def', 'abbrev', 'instance') and i + 1 < len(toks):
                bare.add(toks[i + 1]); break
    return bare

def parse(path, lean):
    text = open(path).read().split('\n')
    sec = 'PREAMBLE'; secline = 0
    secs = {}                      # name -> dict
    order = []
    for i, l in enumerate(text, 1):
        m = re.match(r'^(#{2,4})\s+(.+?)\s*$', l)
        if m:
            sec = m.group(2); secline = i
            if sec not in secs:
                secs[sec] = dict(line=secline, level=len(m.group(1)), decls=set(),
                                 notation=set(), refs=set(), grades=[], opens=[], vrefs=set())
                order.append(sec)
            continue
        if sec not in secs:
            secs[sec] = dict(line=0, level=0, decls=set(), notation=set(), refs=set(),
                             grades=[], opens=[], vrefs=set())
            order.append(sec)
        S = secs[sec]
        for tok in re.findall(r'`([^`]+)`', l):
            if re.fullmatch(r"[A-Za-z_][A-Za-z0-9_.']{3,}", tok):
                (S['decls'] if tok in lean or tok.split('.')[-1] in lean else S['notation']).add(tok)
        # A reference qualified by a version ("v7 section 7.4") points at an EARLIER manuscript, not
        # at this one, and must not be reported as dangling. Nine such references in v9.1 were flagged
        # as defects by the first version of this check; all nine were version-qualified.
        for m2 in re.finditer(r'§\s*([0-9]+(?:\.[0-9]+)?[A-Za-z]?)', l):
            before = l[max(0, m2.start() - 22):m2.start()]
            # `\bv[0-9]` does not match `SKETCH_v7`: `_` is a word character, so there is no boundary
            # before the `v`. Match the version marker without requiring one, and the sketch by name.
            if re.search(r'v[0-9]|SKETCH', before) or sec.startswith('B.') or sec.startswith('Appendix B'):
                S.setdefault('vrefs', set()).add(m2.group(1)); continue
            S['refs'].add(m2.group(1))
        g = re.search(r'`\[([A-Z][A-Za-z]+)', l)
        if g: S['grades'].append(g.group(1))
        if re.search(r'`\[OPEN', l):
            S['opens'].append(dict(line=i, text=l.strip()[:160]))
    return order, secs

def section_number(name):
    m = re.match(r'^([0-9]+(?:\.[0-9]+)?[A-Za-z]?)\.?\s', name)
    return m.group(1) if m else None

def main():
    path = sys.argv[1] if len(sys.argv) > 1 else 'docs/n8/MANUSCRIPT_v9_1.md'
    lean = lean_declarations()
    order, secs = parse(path, lean)
    numbers = {}
    for s in order:
        nb = section_number(s)
        if nb: numbers.setdefault(nb, s)

    # I1 dangling section references
    dangling = []
    for s in order:
        for r in secs[s]['refs']:
            if r not in numbers and r.rstrip('ABC') not in numbers:
                dangling.append((s, r))
    # I2 declarations that do not resolve
    unresolved = sorted({d for s in order for d in secs[s]['decls'] if d not in lean and d.split('.')[-1] not in lean})
    # reverse index
    rev = defaultdict(set)
    for s in order:
        for d in secs[s]['decls']: rev[d].add(s)
    # who cites whom
    cited_by = defaultdict(set)
    for s in order:
        for r in secs[s]['refs']:
            tgt = numbers.get(r) or numbers.get(r.rstrip('ABC'))
            if tgt and tgt != s: cited_by[tgt].add(s)

    print(f"manuscript: {path}")
    print(f"  sections {len(order)}   Lean declarations known: {len(lean)}")
    nv = sum(len(secs[s].get('vrefs', ())) for s in order)
    print(f"\nI1 dangling section references: {len(dangling)}   (version-qualified refs excluded: {nv})")
    for s, r in dangling[:10]: print(f"     {s[:44]:44} -> section {r} (no such heading)")
    print(f"\nI2 backticked identifiers that do not resolve in the tree: {len(unresolved)}")
    for u in unresolved[:12]: print(f"     {u}")
    opens = [(s, o) for s in order for o in secs[s]['opens']]
    print(f"\nI3 open items located: {len(opens)}")
    for s, o in opens: print(f"     line {o['line']:5}  §{section_number(s) or '-':6} {s[:34]:34} {o['text'][:74]}")
    print(f"\nI4 grade tally: {dict(Counter(g for s in order for g in secs[s]['grades']).most_common())}")
    print(f"\nhubs -- sections most cited by others:")
    for s, c in sorted(cited_by.items(), key=lambda kv: -len(kv[1]))[:8]:
        print(f"     §{section_number(s) or '-':6} {s[:40]:40} cited by {len(c)}: {sorted(section_number(x) or x[:10] for x in c)}")
    print(f"\ndeclarations named in more than one section (a change touches each):")
    multi = sorted(((d, v) for d, v in rev.items() if len(v) > 1), key=lambda kv: -len(kv[1]))
    for d, v in multi[:10]:
        print(f"     {d:38} {sorted(section_number(x) or x[:12] for x in v)}")

    out = sys.argv[2] if len(sys.argv) > 2 else None
    if out:
        json.dump(dict(path=path,
                       sections={s: dict(line=secs[s]['line'], decls=sorted(secs[s]['decls']),
                                         notation=sorted(secs[s]['notation']),
                                         refs=sorted(secs[s]['refs']), grades=secs[s]['grades'],
                                         opens=secs[s]['opens']) for s in order},
                       order=order,
                       reverse_index={d: sorted(v) for d, v in rev.items()},
                       cited_by={s: sorted(v) for s, v in cited_by.items()},
                       dangling=dangling, unresolved=unresolved), open(out, 'w'), indent=1)
        print(f"\nwritten {out}")

if __name__ == '__main__':
    main()
