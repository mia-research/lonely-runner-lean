import Fresh.ThreeBlockBypassOverlap

/-! Rules:1–4,8–18. Original-input overlap comparison updated to the wider
all-subject grid kernel bound g+h≤2. The native subject family has no such
opposite-gap bound. No exclusion after arbitrary physical reparameterization
or from every other proved class is asserted. -/
namespace Fresh.ThreeBlockBypassWideOverlap

theorem unbounded_native_beyond_wide (n : ℤ) (hn : 7 ≤ n) :
    (2 : ℝ) < 1/24+((8*(n : ℝ)+1)/25-1/24) := by
  have hnR : (7 : ℝ) ≤ n := by exact_mod_cast hn
  linarith

#print axioms unbounded_native_beyond_wide
end Fresh.ThreeBlockBypassWideOverlap
