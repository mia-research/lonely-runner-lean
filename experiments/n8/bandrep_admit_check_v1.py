#!/usr/bin/env python3
"""bandrep_admit_check_v1.py -- independent admissibility re-check of the Track B
emissions (the E916 verification protocol): for each emitted Lean file, recompile it
from scratch and scan the log for (a) errors, (b) sorryAx axiom footprints, (c) any
axiom footprint outside [propext, Classical.choice, Quot.sound].  Sibling script;
edits nothing; runs the workspace compile command verbatim.
"""
import re, os, subprocess, sys, time

ROOT = os.path.join(os.path.dirname(os.path.dirname(os.path.dirname(
    os.path.abspath(__file__)))), "LonelyRunnerFresh")
FILES = sys.argv[1:] or [
    "BandReplayBulkCore.lean",
    "BandReplayBulkT1.lean",
    "BandReplayBulkCompressed.lean",
    "BandRepOff_1.lean",
    "BandRepOff_2.lean",
    "BandRepOff_3.lean",
    "BandRepOff_4.lean",
    "BandRepOffGrand.lean",
]
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
ENV = dict(os.environ)


def lean_path():
    repo = os.path.join(os.path.dirname(ROOT), "LonelyRunner")
    lp = subprocess.run(["bash", "-c",
                         f'cd "{repo}" && lake env printenv LEAN_PATH'],
                        capture_output=True, text=True).stdout.strip()
    parts = [p for p in lp.split(":") if p and "LonelyRunner/.lake/build/lib/lean" not in p]
    return ":".join(parts)


def check(fn, lp):
    cmd = ["bash", "-c",
           f'cd "{ROOT}" && LEAN_PATH="{ROOT}/build:{lp}" lean Fresh/{fn} -R . '
           f'-o build/Fresh/{fn[:-5]}.olean']
    t0 = time.time()
    r = subprocess.run(cmd, capture_output=True, text=True)
    dt = time.time() - t0
    if r.returncode != 0:
        print(f"    [debug] rc!=0, first 300 chars: {(r.stdout + r.stderr)[:300]!r}")
    log = r.stdout + r.stderr
    nerr = len(re.findall(r"error", log))
    foot = re.findall(r"'([\w.]+)' depends on axioms: \[([^\]]*)\]", log)
    bad, nsorry, nclean = [], 0, 0
    for name, ax in foot:
        axs = {a.strip() for a in ax.split(",") if a.strip()}
        if "sorryAx" in axs:
            nsorry += 1
            bad.append((name, ax))
        elif axs - ALLOWED:
            bad.append((name, ax))
        else:
            nclean += 1
    verdict = "ADMISSIBLE" if (r.returncode == 0 and nerr == 0 and nsorry == 0 and not bad) \
        else "FAIL"
    print(f"{fn}: exit={r.returncode} errors={nerr} footprints={len(foot)} "
          f"(clean {nclean}, sorryAx {nsorry}, other-bad {len(bad)-nsorry}) "
          f"{dt:.1f} s  -> {verdict}")
    for name, ax in bad[:10]:
        print(f"    BAD: {name}: [{ax}]")
    return verdict == "ADMISSIBLE"


def main():
    lp = lean_path()
    print(f"LEAN_PATH isolated (LonelyRunner build excluded), {len(FILES)} files")
    allok = True
    for fn in FILES:
        allok &= check(fn, lp)
    print("ALL ADMISSIBLE" if allok else "ADMISSIBILITY FAILURE")


if __name__ == "__main__":
    main()
