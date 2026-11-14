#!/bin/bash
# Compile the kernel in import order with plain `lean` and print every `#print axioms` line.
# Needs LEAN_PATH to reach a built Mathlib (rev 5e932f97, Lean v4.29.1).  On the owner's machine:
#   LEAN_PATH="$(cd ../../../../LonelyRunner && lake env printenv LEAN_PATH)" ./check_kernel.sh
# Elsewhere: `lake update && lake exe cache get && lake build` with the lakefile here does the same job.
set -u
cd "$(dirname "$0")"; mkdir -p build/Fresh
export LEAN_PATH="$PWD/build:${LEAN_PATH:-}"
fail=0
for m in Framework Cascade KTaxonomy Localisation OneMoverA CascadeLanding FrontierFamilyCap FilterSkeleton \
         CarveExclusionCerts FilterAssembly PinchCert SpineSound SpineTotalData BandNoCarve BandPinchData KernelProbe; do
  echo "== $m"
  lean "Fresh/$m.lean" -R . -o "build/Fresh/$m.olean" 2>&1 || { echo "FAILED $m"; fail=1; }
done
echo "== sorry scan (comments stripped)"
python3 - <<'PY'
import re,glob
for f in sorted(glob.glob("Fresh/*.lean")):
    s=open(f).read(); s=re.sub(r"/-.*?-/","",s,flags=re.S); s=re.sub(r"--[^\n]*","",s)
    print("  %-34s sorry=%d native_decide=%d axiom=%d"%(f,len(re.findall(r"\bsorry\b",s)),len(re.findall(r"\bnative_decide\b",s)),len(re.findall(r"^\s*axiom\b",s,re.M))))
PY
echo "exit=$fail"; exit $fail
