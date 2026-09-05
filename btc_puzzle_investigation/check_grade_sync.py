#!/usr/bin/env python3
"""
check_grade_sync.py -- grade-drift detector (proposal S2).

Single source of truth for claim grades = CLAIMS_LEDGER.md.
This script emits a DECIDABLE ARTIFACT (a table of grade comparisons), not a judgment.

Per ledger row it does two mechanical checks:

  1. FILE-INTEGRITY: the authoritative file exists and the cited line is in range (WARN if not).
     Whether a bracketed grade sits near the cited line is reported as an INFO note only
     (some RESULT files grade in prose).

  2. MASTER-DRIFT: for each pinned master-ref `file:line`, validate the pin by requiring the
     row's `anchor` keyword within a small window (else STALE-REF -- the line moved under an
     edit). Then read the strongest grade in that window and compare to the ledger grade:
       master stronger than ledger  -> OVERCLAIM  (exit 1; blocks master promotion)
       master weaker / different    -> MISMATCH   (warning)
       same                          -> ok

Pins (not token-grep) are used deliberately: short labels like "L2"/"P13" are overloaded across
the master, so grep produces false positives. A pin names the exact assertion site; the anchor
guards against the pin going stale.

No floating point anywhere (text only) -- the project signal-path rule is vacuously satisfied.

Usage:
    python3 check_grade_sync.py                 # default ledger CLAIMS_LEDGER.md
    python3 check_grade_sync.py --ledger PATH
    python3 check_grade_sync.py --window N      # anchor/grade window half-size (default 4)

Exit code: 1 if any OVERCLAIM, 2 on fatal setup error, else 0.
"""
import argparse
import os
import re
import sys

# Higher rank = stronger claim. A master grade ranked above the ledger's = overclaim.
RANK = {
    "PROVED": 6,
    "VERIFIED": 4,
    "CITED": 3,
    "EMPIRICAL": 2,
    "CONDITIONAL": 2,
    "UNREVIEWED": 2,
    "PROVISIONAL": 2,
    "HEURISTIC": 1,
    "ASSERTED": 1,
    "GAP": 1,
    "VOID": 0,
    "CONTAMINATED": 0,
}
GRADE_RE = re.compile(
    r"\[(" + "|".join(sorted(RANK, key=len, reverse=True)) + r")\b[^\]]*\]"
)


def strongest_grade(text):
    """Highest-ranked recognized grade token in a block of text, or None."""
    best = None
    for m in GRADE_RE.finditer(text):
        tok = m.group(1)
        if best is None or RANK[tok] > RANK[best]:
            best = tok
    return best


def parse_ledger(path):
    with open(path, encoding="utf-8") as fh:
        lines = fh.read().splitlines()
    rows, header = [], None
    for ln in lines:
        s = ln.strip()
        if not s.startswith("|"):
            continue
        cells = [c.strip() for c in s.strip("|").split("|")]
        if set("".join(cells)) <= set("-: "):  # |---|---| separator
            continue
        if header is None:
            header = cells
            continue
        if len(cells) == len(header):
            rows.append(dict(zip(header, cells)))
    return header, rows


def read_lines(path):
    with open(path, encoding="utf-8") as fh:
        return fh.read().splitlines()


def window_text(lines, lineno, half):
    lo = max(0, lineno - 1 - half)
    hi = min(len(lines), lineno + half)
    return "\n".join(lines[lo:hi])


def grade_at(lines, lineno, half):
    """Grade on the EXACT pinned line if present (avoids bleeding into an adjacent claim's
    grade); else the strongest grade in the surrounding window (tolerates a wrapped tag)."""
    exact = strongest_grade(lines[lineno - 1]) if 0 < lineno <= len(lines) else None
    return exact if exact is not None else strongest_grade(window_text(lines, lineno, half))


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--ledger", default="CLAIMS_LEDGER.md")
    ap.add_argument("--root", default=None,
                    help="dir the file:line refs resolve against (default: the ledger's dir)")
    ap.add_argument("--window", type=int, default=4)
    args = ap.parse_args()

    if not os.path.exists(args.ledger):
        print(f"FATAL: ledger not found: {args.ledger}", file=sys.stderr)
        return 2
    root = args.root or os.path.dirname(os.path.abspath(args.ledger)) or "."

    header, rows = parse_ledger(args.ledger)
    need = {"claim-id", "grade", "master-refs", "anchor", "authoritative"}
    missing_cols = need - set(header or [])
    if missing_cols:
        print(f"FATAL: ledger missing columns: {sorted(missing_cols)}", file=sys.stderr)
        return 2

    print(f"Ledger: {args.ledger}  ({len(rows)} claims parsed)")
    print("=" * 80)

    overclaims, mismatches, warnings, notes = [], [], [], []
    file_cache = {}

    def get_lines(path):
        if path not in file_cache:
            file_cache[path] = read_lines(path) if os.path.exists(path) else None
        return file_cache[path]

    for r in rows:
        cid = r["claim-id"]
        led = r["grade"].strip().upper()
        anchor = r["anchor"].strip()
        led_rank = RANK.get(led, -1)
        if led not in RANK:
            warnings.append(f"[{cid}] ledger grade '{led}' not in vocabulary")

        # ---- 1. file-integrity ----
        af, _, aline = r["authoritative"].strip().partition(":")
        af_lines = get_lines(os.path.join(root, af))
        if af_lines is None:
            warnings.append(f"[{cid}] authoritative file MISSING: {af}")
        elif aline.isdigit():
            n = int(aline)
            if n > len(af_lines):
                warnings.append(f"[{cid}] authoritative line {n} > {len(af_lines)} in {af}")
            elif strongest_grade(window_text(af_lines, n, args.window)) is None:
                notes.append(f"[{cid}] no bracketed grade near {af}:{n} (prose-graded?)")

        # ---- 2. master-drift ----
        refs = r["master-refs"].strip()
        if refs in ("", "—", "-"):
            print(f"[{cid:14}] ledger={led:12} RESULT-only (no master asserts it)")
            continue

        for ref in [x.strip() for x in refs.split(";") if x.strip()]:
            mf, _, mline = ref.partition(":")
            ml = get_lines(os.path.join(root, mf))
            base = os.path.basename(mf)
            if ml is None:
                warnings.append(f"[{cid}] master-ref file MISSING: {mf}")
                continue
            if not mline.isdigit() or int(mline) > len(ml):
                warnings.append(f"[{cid}] master-ref line out of range: {ref}")
                continue
            win = window_text(ml, int(mline), args.window)
            if anchor and anchor.lower() not in win.lower():
                warnings.append(
                    f"[{cid}] STALE-REF {base}:{mline} -- anchor '{anchor}' not near the "
                    f"pinned line (master edited? re-point the ledger)"
                )
                print(f"[{cid:14}] ledger={led:12} {base}:{mline} -> STALE-REF")
                continue
            mgrade = grade_at(ml, int(mline), args.window)
            if mgrade is None:
                print(f"[{cid:14}] ledger={led:12} {base}:{mline} -> no grade in window")
                notes.append(f"[{cid}] no bracketed grade near master-ref {ref}")
                continue
            mr = RANK[mgrade]
            if mr > led_rank:
                verdict = "OVERCLAIM"
                overclaims.append(
                    f"[{cid}] {base}:{mline} asserts [{mgrade}] > ledger [{led}]"
                )
            elif mgrade != led:
                verdict = "MISMATCH"
                mismatches.append(
                    f"[{cid}] {base}:{mline} says [{mgrade}], ledger [{led}]"
                )
            else:
                verdict = "ok"
            print(f"[{cid:14}] ledger={led:12} {base}:{mline} [{mgrade}] -> {verdict}")

    print("=" * 80)
    for label, items, mark in [
        ("NOTES (informational)", notes, "-"),
        ("WARNINGS", warnings, "!"),
        ("MISMATCH (master weaker/different -- sync, not overclaim)", mismatches, "~"),
    ]:
        if items:
            print(f"\n{label} ({len(items)}):")
            for x in items:
                print(f"  {mark} {x}")
    if overclaims:
        print(f"\nOVERCLAIM drift ({len(overclaims)})  <-- blocks master promotion:")
        for x in overclaims:
            print(f"  X {x}")
        print("\nRESULT: FAIL")
        return 1
    print("\nRESULT: PASS (no overclaim drift)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
