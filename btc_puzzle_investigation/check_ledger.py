#!/usr/bin/env python3
"""
Ledger currency guard  (CLAUDE.md: CLAIMS.md is the only current-state document).

FAILS when any claim-bearing document is newer than CLAIMS.md — i.e. when findings
exist that the ledger does not yet carry. That backlog is the disease this guards:
on 2026-09-01 the master was 5 days stale with 16 unmerged documents, and a banked
result (M21, 1171 cells) was re-derived from scratch because nothing surfaced it.

Usage:
    python3 check_ledger.py            # fail on any unmerged doc
    python3 check_ledger.py --list     # list them, exit 0
    python3 check_ledger.py --touch    # after folding them in: restamp CLAIMS.md

Run at SESSION START and before reporting any result.
"""
import os, sys, glob, time

HERE = os.path.dirname(os.path.abspath(__file__))
LEDGER = os.path.join(HERE, "CLAIMS.md")
STATE = os.path.join(HERE, ".claims_ledger_state")
# claim-bearing prefixes: these assert or move a claim's status
PREFIXES = ("RESULT_", "NOTE_", "CORRECTION_", "AUDIT_", "CONFIRMED_", "RETRACTION_")
# frozen lineage: superseded by CLAIMS.md, never counts as backlog
FROZEN = ("POSITIVE_FINDINGS_MASTER_v", "POSITIVE_FINDINGS_ADDENDUM_",
          "POSITIVE_FINDINGS_HANDOVER_")


def unmerged():
    if not os.path.exists(LEDGER):
        print("FAIL: CLAIMS.md does not exist. It is the only current-state document.")
        sys.exit(2)
    t_ledger = os.path.getmtime(LEDGER)
    out = []
    for path in glob.glob(os.path.join(HERE, "*.md")):
        name = os.path.basename(path)
        if name == "CLAIMS.md" or name.startswith(FROZEN):
            continue
        if not name.startswith(PREFIXES):
            continue
        t = os.path.getmtime(path)
        if t > t_ledger:
            out.append((t, name))
    return t_ledger, sorted(out)


def stamp(t):
    return time.strftime("%Y-%m-%d %H:%M", time.localtime(t))


def main():
    arg = sys.argv[1] if len(sys.argv) > 1 else ""
    t_ledger, back = unmerged()

    if arg == "--touch":
        # Refuse to restamp unless CLAIMS.md's CONTENT actually changed since the last
        # touch. Without this, a --touch after a FAILED edit produces a false "OK" and
        # silently buries the backlog (hit 2026-09-01: an assertion failed, --touch ran
        # on the next line anyway, and the guard reported clean).
        import hashlib
        h = hashlib.sha256(open(LEDGER, "rb").read()).hexdigest()
        prev = None
        if os.path.exists(STATE):
            prev = open(STATE).read().strip() or None
        if prev == h and back:
            print("REFUSED: CLAIMS.md is byte-identical to the last --touch, but "
                  f"{len(back)} document(s) still postdate it:")
            for t, name in back:
                print(f"  {stamp(t)}  {name}")
            print("Fold them in (actually edit the ledger), then --touch.")
            return 2
        open(STATE, "w").write(h + "\n")
        os.utime(LEDGER, None)
        print(f"CLAIMS.md restamped {stamp(time.time())} "
              f"(content hash {h[:12]}) — acknowledged {len(back)} document(s).")
        return 0

    print(f"CLAIMS.md last compiled: {stamp(t_ledger)}")
    if not back:
        print("OK: ledger is current. No claim-bearing document postdates it.")
        return 0

    print(f"\n{len(back)} claim-bearing document(s) NEWER than the ledger:\n")
    for t, name in back:
        print(f"  {stamp(t)}  {name}")
    print("\nFAIL: the ledger is stale. Fold these into CLAIMS.md, then "
          "`python3 check_ledger.py --touch`.")
    print("Do not report a result while this fails — that is how M21 got "
          "re-derived at 1/167 the coverage.")
    return 1 if arg != "--list" else 0


if __name__ == "__main__":
    sys.exit(main())
