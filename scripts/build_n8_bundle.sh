#!/usr/bin/env bash
# Build the distributable n=8 bundle. EVERYTHING IS COMPUTED, nothing hand-picked:
# the first bundle was assembled by judgement and shipped 10 MB of unrelated n=7 build logs,
# omitted Spec/Target.lean entirely, and dangled nine citations. Each list below is derived.
set -uo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT" || exit 2
OUT="${1:-$HOME/Desktop/lrc_n8_bundle_$(date +%Y-%m-%d).tar.gz}"
B=$(mktemp -d)/lrc_n8_bundle_$(date +%Y-%m-%d)
# Find the CURRENT manuscript, never a hardcoded version. A hardcoded name here shipped
# v9.3 in a bundle built for v9.4, and the same mistake had already been fixed in the gate.
MAN=$(ls docs/n8/MANUSCRIPT_v*.md 2>/dev/null | sort -V | tail -1)
[ -n "$MAN" ] || { echo "  no MANUSCRIPT_v*.md found"; exit 2; }
echo "  manuscript: $MAN"
mkdir -p "$B/docs" "$B/experiments" "$B/lean"

# [1] the Lean tree: the transitive import closure of the artefact plus the frozen target
python3 - "$B" <<'PY'
import re, pathlib, shutil, sys, os
B = pathlib.Path(sys.argv[1])
os.chdir("LonelyRunner")
root = pathlib.Path("LonelyRunner")
seeds = list((root/"LRC"/"Cascade").glob("*.lean")) + [root/"LRC"/"Spec"/"Target.lean"]
seen, q = set(), list(seeds)
while q:
    f = q.pop()
    if f in seen or not f.exists(): continue
    seen.add(f)
    for m in re.findall(r'^import\s+(LonelyRunner[A-Za-z0-9_.]*)', f.read_text(), re.M):
        p = pathlib.Path(m.replace(".", "/") + ".lean")
        if p.exists() and p not in seen: q.append(p)
for f in seen:
    d = B/"lean"/f.parent; d.mkdir(parents=True, exist_ok=True)
    shutil.copy2(f, d/f.name)
for extra in ("lakefile.toml", "lake-manifest.json", "lean-toolchain"):
    if pathlib.Path(extra).exists(): shutil.copy2(extra, B/"lean"/extra)
(B/"lean"/"scripts"/"cascade").mkdir(parents=True, exist_ok=True)
shutil.copy2("scripts/cascade/gate.sh", B/"lean"/"scripts"/"cascade"/"gate.sh")
print(f"  lean: {len(seen)} source files (computed import closure)")
PY

# a root scoped to the artefact: the repo's own root pulls in the general-n line, which
# still contains `sorry` and is not part of the n=8 result
cat > "$B/lean/LonelyRunner.lean" <<'EOF'
/-!
# LonelyRunner — the n = 8 artefact

This root is specific to the distributed bundle: it imports the cascade artefact and the
frozen target, and nothing else. The full repository's root additionally imports the
general-`n` line (`Theorem52_Weyl`, `Theorem121_Main`, …), which is separate work and still
contains `sorry`. Excluding it is why every file here is `sorry`-free.

The real check is `scripts/cascade/gate.sh`, not `lake build`.
-/
import LonelyRunner.LRC.Cascade.All
import LonelyRunner.LRC.Spec.Target
EOF

# [2] every document the manuscript or the corrections cite, by name
cp "$MAN" docs/n8/CORRECTIONS_2026_09_17_v2.md "$B/"
for d in $(grep -ohE '`[A-Z][A-Z0-9_]+(_[0-9_]+)?_v[0-9]+`' "$MAN" docs/n8/CORRECTIONS_2026_09_17_v2.md \
           | tr -d '`' | sort -u); do
  [ -f "docs/n8/$d.md" ] && cp "docs/n8/$d.md" "$B/docs/"
done
cp docs/n8/CORRECTIONS_2026_09_17_v2.md docs/n8/MANUSCRIPT_v9_2.md "$B/docs/" 2>/dev/null
echo "  docs: $(ls "$B/docs" | wc -l | tr -d ' ') (every cited name that exists on disk)"

# [3] the experiments the manuscript or corrections CITE BY NAME, with their deposits.
# Not every tracked file: experiments/n8 holds 596 of them, the project's whole working
# history. A first version copied all of them and quadrupled the archive for no reader.
for b in $(grep -ohE '[A-Za-z0-9_]+_v[0-9]+' "$MAN" docs/n8/CORRECTIONS_2026_09_17_v2.md | sort -u); do
  for ext in py out; do
    [ -f "experiments/n8/$b.$ext" ] && cp "experiments/n8/$b.$ext" "$B/experiments/"
  done
  # Some deposits are DIRECTORIES -- several scripts and their outputs for one investigation.
  # A flat-file-only loop dropped them with no message, which is the same defect as
  # hand-picking: the list looks derived and silently is not. Added 2026-09-18.
  [ -d "experiments/n8/$b" ] && cp -R "experiments/n8/$b" "$B/experiments/"
done
echo "  experiments: $(find "$B/experiments" -type f | wc -l | tr -d ' ') files in $(ls "$B/experiments" | wc -l | tr -d ' ') entries (cited by name, with deposits)"

# [4] the README: the entry point. Regenerated so its figures cannot drift from the tree.
T_N=$(grep -hE '^theorem |^lemma ' LonelyRunner/LonelyRunner/LRC/Cascade/*.lean | wc -l | tr -d ' ')
T_M=$(ls LonelyRunner/LonelyRunner/LRC/Cascade/*.lean | wc -l | tr -d ' ')
T_D=$(cd LonelyRunner/LonelyRunner/LRC/Cascade && shasum -a 256 *.lean | sort -k2 | shasum -a 256 | cut -d' ' -f1)
T_C=$(cd LonelyRunner && git log -1 --format=%h -- LonelyRunner/LRC/Cascade)
C=LonelyRunner/LonelyRunner/LRC/Cascade
T_G=$(grep -hcE '^theorem |^lemma ' $C/PinnedBatch*.lean $C/CensusBatch.lean $C/CensusFamilies.lean | paste -sd+ - | bc)
T_S=$((T_N - T_G))
sed -e "s/@THEOREMS@/$T_N/g" -e "s/@MODULES@/$T_M/g" -e "s/@DIGEST@/$T_D/g" -e "s/@COMMIT@/$T_C/g" \
    -e "s/@STRUCTURAL@/$T_S/g" -e "s/@GENERATED@/$T_G/g" \
    docs/n8/BUNDLE_README_template.md > "$B/README.md"
echo "  README: regenerated ($T_N theorems = $T_S structural + $T_G generated, $T_M modules, digest ${T_D:0:8}, commit $T_C)"

tar -czf "$OUT" -C "$(dirname "$B")" "$(basename "$B")"
echo "  archive: $OUT  ($(du -h "$OUT" | cut -f1))"
echo "$B" > /tmp/n8_bundle_dir
