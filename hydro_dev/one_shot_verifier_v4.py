#!/usr/bin/env python3
"""
HYDRO KERNEL VERIFICATION: ONE-SHOT REAL COMPILER TEST
------------------------------------------------------
This script performs a 100% genuine, un-mocked verification of the
`four_fast_coprime_reduction` theorem against your local Lean 4 / Mathlib toolchain.

Requirements:
  - Run from inside or alongside the `lonely-runner-lean` repository.
  - Requires `lake` and `lean` installed via elan.
"""

import os
import sys
import shutil
import tempfile
import subprocess

# ---------------------------------------------------------------------------
# 1. THE VERIFIED LEAN 4 SOURCE
# Corrected for Mathlib:
#   - Replaces hallucinated 'Nat.gcd_div_gcd_div_gcd' with 'Nat.coprime_div_gcd_div_gcd'
#   - Drops the invalid 'Real.norm_eq_abs' rewrite
#   - Closes the ring factor calculation via symmetric 'Nat.mul_div_cancel''
# ---------------------------------------------------------------------------
LEAN_SOURCE = r"""import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open Real

/-!
# Four-Fast Coprime Reduction (Verified Mathlib Implementation)
Given p, q > 0 with |p*u - q*v| ≤ bound, the primitive quotients
p0 = p/g and q0 = q/g satisfy Nat.Coprime p0 q0 and |p0*u - q0*v| ≤ bound/g.
-/

theorem four_fast_coprime_reduction
    (p q : ℕ) (u v : ℝ) (bound : ℝ)
    (hp : p > 0)
    (_hq : q > 0)
    (h_bound : |(p : ℝ) * u - (q : ℝ) * v| ≤ bound) :
    let g := Nat.gcd p q
    let p0 := p / g
    let q0 := q / g
    Nat.Coprime p0 q0 ∧ |(p0 : ℝ) * u - (q0 : ℝ) * v| ≤ bound / (g : ℝ) := by
  intro g p0 q0
  -- 1. Strict positivity of gcd
  have hg_pos : g > 0 := Nat.gcd_pos_of_pos_left q hp
  have hg_real_pos : (g : ℝ) > 0 := Nat.cast_pos.mpr hg_pos

  -- 2. Coprimality of quotients using canonical Mathlib lemma
  have h_coprime : Nat.Coprime p0 q0 := Nat.coprime_div_gcd_div_gcd hg_pos
  refine ⟨h_coprime, ?_⟩

  -- 3. Exact algebraic cancellation: g * p0 = p and g * q0 = q
  have hp_cancel : g * p0 = p := Nat.mul_div_cancel' (Nat.gcd_dvd_left p q)
  have hq_cancel : g * q0 = q := Nat.mul_div_cancel' (Nat.gcd_dvd_right p q)

  -- 4. Factoring g out of the linear combination
  have h_factor : (p : ℝ) * u - (q : ℝ) * v = ((p0 : ℝ) * u - (q0 : ℝ) * v) * (g : ℝ) := by
    rw [← hp_cancel, ← hq_cancel]
    push_cast
    ring

  -- 5. Scaling the absolute value bound
  rw [h_factor, abs_mul, abs_of_pos hg_real_pos] at h_bound
  exact (le_div_iff₀ hg_real_pos).mpr h_bound

#print axioms four_fast_coprime_reduction
"""

def find_lake_dir():
    """Locates the directory containing lakefile.lean or lakefile.toml."""
    candidates = [
        os.getcwd(),
        os.path.join(os.getcwd(), "lonely-runner-lean"),
        os.path.join(os.getcwd(), "mia-research", "lonely-runner-lean"),
        os.path.expanduser("~/lonely-runner-lean"),
        os.path.expanduser("~/Downloads/lonely-runner-lean"),
    ]
    for c in candidates:
        if os.path.isdir(c) and (
            os.path.exists(os.path.join(c, "lakefile.lean"))
            or os.path.exists(os.path.join(c, "lakefile.toml"))
        ):
            return os.path.abspath(c)
    return None

def main():
    print("=" * 72)
    print(" HYDRO LEAN 4: KERNEL ELABORATION & AXIOM AUDIT TEST")
    print("=" * 72)

    # 1. Find repo directory
    lake_dir = find_lake_dir()
    if not lake_dir:
        print("[!] ERROR: Could not find a Lean project directory with lakefile.")
        print("    Please run this script from inside your 'lonely-runner-lean' repo.")
        sys.exit(1)
    print(f"[*] Target Lean Project : {lake_dir}")

    # 2. Find Lake binary
    lake_bin = shutil.which("lake")
    if not lake_bin:
        elan_lake = os.path.expanduser("~/.elan/bin/lake")
        if os.path.exists(elan_lake):
            lake_bin = elan_lake
        else:
            print("[!] ERROR: 'lake' executable not found in PATH or ~/.elan/bin/lake.")
            sys.exit(1)
    print(f"[*] Lake Binary Executable: {lake_bin}")

    # 3. Write source to temporary file
    with tempfile.NamedTemporaryFile("w", suffix=".lean", delete=False) as tf:
        tf.write(LEAN_SOURCE)
        temp_lean = tf.name

    print(f"[*] Emitted Lean Source to: {temp_lean}")
    print("[*] Invoking: lake env lean <temp_file> ...")
    print("-" * 72)

    try:
        proc = subprocess.run(
            [lake_bin, "env", "lean", temp_lean],
            cwd=lake_dir,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
            timeout=120
        )
    except subprocess.TimeoutExpired:
        print("[!] Execution timed out after 120 seconds.")
        sys.exit(1)
    finally:
        if os.path.exists(temp_lean):
            os.remove(temp_lean)

    stdout = proc.stdout.strip()
    stderr = proc.stderr.strip()

    # 4. Parse Compiler Errors and Axioms
    all_output = (stdout + "\n" + stderr).strip()
    errors = [l for l in all_output.splitlines() if ": error:" in l]
    warnings = [l for l in all_output.splitlines() if ": warning:" in l]
    has_sorry = "sorryAx" in all_output or "declaration uses 'sorry'" in all_output

    print("COMPILER STDOUT:")
    print(stdout if stdout else "  (empty)")
    print("\nCOMPILER STDERR:")
    print(stderr if stderr else "  (empty)")
    print("-" * 72)

    # 5. Output Definitive Audit Verdict
    if proc.returncode == 0 and len(errors) == 0 and not has_sorry:
        import re as _re
        axm = _re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", all_output)
        print("🟢 VERDICT: COMPILED & KERNEL VERIFIED")
        print("   - Return code : 0")
        print(f"   - Errors      : 0")
        print(f"   - Warnings    : {len(warnings)}")
        print("   - Proof Debt  : 0 sorryAx")
        if axm:
            for name, lst in axm:
                print(f"   - {name} depends on axioms: [{lst}] (parsed from kernel output)")
        else:
            print("   - Axioms Used : (no #print axioms output found in kernel stdout)")
        print("=" * 72)
        sys.exit(0)
    else:
        print("🔴 VERDICT: VERIFICATION FAILED")
        print(f"   - Return code : {proc.returncode}")
        print(f"   - Errors      : {len(errors)}")
        print(f"   - Has sorryAx : {has_sorry}")
        for err in errors:
            print(f"     -> {err}")
        print("=" * 72)
        sys.exit(1)

if __name__ == "__main__":
    main()