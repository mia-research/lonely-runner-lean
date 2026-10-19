import LonelyRunner.LRC.Spec.OrderSevenU5SoundN
import LonelyRunner.LRC.Spec.OrderSevenU5C30N
import LonelyRunner.LRC.Spec.OrderSevenU5C31N
import LonelyRunner.LRC.Spec.OrderSevenU5C32N
import LonelyRunner.LRC.Spec.OrderSevenU5C33N
import LonelyRunner.LRC.Spec.OrderSevenU5C34N
import LonelyRunner.LRC.Spec.OrderSevenU5C35N
import LonelyRunner.LRC.Spec.OrderSevenU5C36N
import LonelyRunner.LRC.Spec.OrderSevenU5C37N
import LonelyRunner.LRC.Spec.OrderSevenU5C38N
import LonelyRunner.LRC.Spec.OrderSevenU5C39N

set_option maxRecDepth 100000

namespace LRC.O7U5

theorem root_2006 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 2006) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_2006_0, decode 300 d_2006_1, decode 300 d_2006_2, decode 300 d_2006_3, decode 300 d_2006_4, decode 300 d_2006_5, decode 300 d_2006_6, decode 142 d_2006_7] (fun x hx => bits_full_and hx) cov_2006 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_2006_0, ch_2006_1, ch_2006_2, ch_2006_3, ch_2006_4, ch_2006_5, ch_2006_6, ch_2006_7])

theorem root_2008 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 2008) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_2008_0, decode 300 d_2008_1, decode 300 d_2008_2, decode 300 d_2008_3, decode 300 d_2008_4, decode 300 d_2008_5, decode 300 d_2008_6, decode 141 d_2008_7] (fun x hx => bits_full_and hx) cov_2008 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_2008_0, ch_2008_1, ch_2008_2, ch_2008_3, ch_2008_4, ch_2008_5, ch_2008_6, ch_2008_7])

theorem root_2011 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 2011) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_2011_0, decode 300 d_2011_1, decode 300 d_2011_2, decode 300 d_2011_3, decode 300 d_2011_4, decode 300 d_2011_5, decode 78 d_2011_6] (fun x hx => bits_full_and hx) cov_2011 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_2011_0, ch_2011_1, ch_2011_2, ch_2011_3, ch_2011_4, ch_2011_5, ch_2011_6])

theorem root_2014 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 2014) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_2014_0, decode 300 d_2014_1, decode 300 d_2014_2, decode 300 d_2014_3, decode 300 d_2014_4, decode 300 d_2014_5, decode 40 d_2014_6] (fun x hx => bits_full_and hx) cov_2014 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_2014_0, ch_2014_1, ch_2014_2, ch_2014_3, ch_2014_4, ch_2014_5, ch_2014_6])

theorem root_2015 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 2015) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_2015_0, decode 300 d_2015_1, decode 300 d_2015_2, decode 300 d_2015_3, decode 300 d_2015_4, decode 300 d_2015_5, decode 40 d_2015_6] (fun x hx => bits_full_and hx) cov_2015 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_2015_0, ch_2015_1, ch_2015_2, ch_2015_3, ch_2015_4, ch_2015_5, ch_2015_6])

theorem root_2022 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 2022) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_2022_0, decode 300 d_2022_1, decode 300 d_2022_2, decode 300 d_2022_3, decode 300 d_2022_4, decode 300 d_2022_5, decode 300 d_2022_6, decode 158 d_2022_7] (fun x hx => bits_full_and hx) cov_2022 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_2022_0, ch_2022_1, ch_2022_2, ch_2022_3, ch_2022_4, ch_2022_5, ch_2022_6, ch_2022_7])

theorem root_2023 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 2023) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_2023_0, decode 300 d_2023_1, decode 300 d_2023_2, decode 300 d_2023_3, decode 300 d_2023_4, decode 300 d_2023_5, decode 300 d_2023_6, decode 141 d_2023_7] (fun x hx => bits_full_and hx) cov_2023 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_2023_0, ch_2023_1, ch_2023_2, ch_2023_3, ch_2023_4, ch_2023_5, ch_2023_6, ch_2023_7])

theorem root_2024 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 2024) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_2024_0, decode 300 d_2024_1, decode 300 d_2024_2, decode 300 d_2024_3, decode 300 d_2024_4, decode 300 d_2024_5, decode 300 d_2024_6, decode 141 d_2024_7] (fun x hx => bits_full_and hx) cov_2024 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_2024_0, ch_2024_1, ch_2024_2, ch_2024_3, ch_2024_4, ch_2024_5, ch_2024_6, ch_2024_7])

theorem root_2035 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 2035) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_2035_0, decode 300 d_2035_1, decode 300 d_2035_2, decode 300 d_2035_3, decode 300 d_2035_4, decode 300 d_2035_5, decode 300 d_2035_6, decode 158 d_2035_7] (fun x hx => bits_full_and hx) cov_2035 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_2035_0, ch_2035_1, ch_2035_2, ch_2035_3, ch_2035_4, ch_2035_5, ch_2035_6, ch_2035_7])

theorem root_2036 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 2036) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_2036_0, decode 300 d_2036_1, decode 300 d_2036_2, decode 300 d_2036_3, decode 300 d_2036_4, decode 300 d_2036_5, decode 300 d_2036_6, decode 158 d_2036_7] (fun x hx => bits_full_and hx) cov_2036 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_2036_0, ch_2036_1, ch_2036_2, ch_2036_3, ch_2036_4, ch_2036_5, ch_2036_6, ch_2036_7])

theorem root_2044 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 2044) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_2044_0, decode 300 d_2044_1, decode 300 d_2044_2, decode 300 d_2044_3, decode 300 d_2044_4, decode 300 d_2044_5, decode 300 d_2044_6, decode 158 d_2044_7] (fun x hx => bits_full_and hx) cov_2044 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_2044_0, ch_2044_1, ch_2044_2, ch_2044_3, ch_2044_4, ch_2044_5, ch_2044_6, ch_2044_7])

theorem root_2045 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 2045) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_2045_0, decode 300 d_2045_1, decode 300 d_2045_2, decode 300 d_2045_3, decode 300 d_2045_4, decode 300 d_2045_5, decode 300 d_2045_6, decode 141 d_2045_7] (fun x hx => bits_full_and hx) cov_2045 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_2045_0, ch_2045_1, ch_2045_2, ch_2045_3, ch_2045_4, ch_2045_5, ch_2045_6, ch_2045_7])

theorem root_2048 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 2048) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_2048_0, decode 300 d_2048_1, decode 300 d_2048_2, decode 300 d_2048_3, decode 300 d_2048_4, decode 300 d_2048_5, decode 300 d_2048_6, decode 142 d_2048_7] (fun x hx => bits_full_and hx) cov_2048 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_2048_0, ch_2048_1, ch_2048_2, ch_2048_3, ch_2048_4, ch_2048_5, ch_2048_6, ch_2048_7])

theorem root_2049 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 2049) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_2049_0, decode 300 d_2049_1, decode 300 d_2049_2, decode 300 d_2049_3, decode 300 d_2049_4, decode 300 d_2049_5, decode 300 d_2049_6, decode 142 d_2049_7] (fun x hx => bits_full_and hx) cov_2049 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_2049_0, ch_2049_1, ch_2049_2, ch_2049_3, ch_2049_4, ch_2049_5, ch_2049_6, ch_2049_7])

theorem root_2060 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 2060) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_2060_0, decode 300 d_2060_1, decode 300 d_2060_2, decode 300 d_2060_3, decode 300 d_2060_4, decode 300 d_2060_5, decode 300 d_2060_6, decode 158 d_2060_7] (fun x hx => bits_full_and hx) cov_2060 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_2060_0, ch_2060_1, ch_2060_2, ch_2060_3, ch_2060_4, ch_2060_5, ch_2060_6, ch_2060_7])

theorem root_2061 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 2061) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_2061_0, decode 300 d_2061_1, decode 300 d_2061_2, decode 300 d_2061_3, decode 300 d_2061_4, decode 300 d_2061_5, decode 300 d_2061_6, decode 158 d_2061_7] (fun x hx => bits_full_and hx) cov_2061 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_2061_0, ch_2061_1, ch_2061_2, ch_2061_3, ch_2061_4, ch_2061_5, ch_2061_6, ch_2061_7])

theorem root_2062 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 2062) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_2062_0, decode 300 d_2062_1, decode 300 d_2062_2, decode 300 d_2062_3, decode 300 d_2062_4, decode 300 d_2062_5, decode 300 d_2062_6, decode 158 d_2062_7] (fun x hx => bits_full_and hx) cov_2062 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_2062_0, ch_2062_1, ch_2062_2, ch_2062_3, ch_2062_4, ch_2062_5, ch_2062_6, ch_2062_7])

theorem root_2063 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 2063) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_2063_0, decode 300 d_2063_1, decode 300 d_2063_2, decode 300 d_2063_3, decode 300 d_2063_4, decode 300 d_2063_5, decode 300 d_2063_6, decode 141 d_2063_7] (fun x hx => bits_full_and hx) cov_2063 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_2063_0, ch_2063_1, ch_2063_2, ch_2063_3, ch_2063_4, ch_2063_5, ch_2063_6, ch_2063_7])

theorem root_2070 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 2070) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_2070_0, decode 300 d_2070_1, decode 300 d_2070_2, decode 300 d_2070_3, decode 300 d_2070_4, decode 300 d_2070_5, decode 300 d_2070_6, decode 142 d_2070_7] (fun x hx => bits_full_and hx) cov_2070 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_2070_0, ch_2070_1, ch_2070_2, ch_2070_3, ch_2070_4, ch_2070_5, ch_2070_6, ch_2070_7])

theorem roots_30_ok (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    ∀ k ∈ roots_30, Claim (FULL &&& MT k) 3 := by
  intro k hk
  simp only [roots_30, List.mem_cons, List.mem_nil_iff, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [root_2006 hB hC hCl hCB, root_2008 hB hC hCl hCB, root_2011 hB hC hCl hCB, root_2014 hB hC hCl hCB, root_2015 hB hC hCl hCB, root_2022 hB hC hCl hCB, root_2023 hB hC hCl hCB, root_2024 hB hC hCl hCB, root_2035 hB hC hCl hCB, root_2036 hB hC hCl hCB, root_2044 hB hC hCl hCB, root_2045 hB hC hCl hCB, root_2048 hB hC hCl hCB, root_2049 hB hC hCl hCB, root_2060 hB hC hCl hCB, root_2061 hB hC hCl hCB, root_2062 hB hC hCl hCB, root_2063 hB hC hCl hCB, root_2070 hB hC hCl hCB]

theorem root_2071 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 2071) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_2071_0, decode 300 d_2071_1, decode 300 d_2071_2, decode 300 d_2071_3, decode 300 d_2071_4, decode 300 d_2071_5, decode 300 d_2071_6, decode 142 d_2071_7] (fun x hx => bits_full_and hx) cov_2071 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_2071_0, ch_2071_1, ch_2071_2, ch_2071_3, ch_2071_4, ch_2071_5, ch_2071_6, ch_2071_7])

theorem root_2076 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 2076) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_2076_0, decode 300 d_2076_1, decode 300 d_2076_2, decode 300 d_2076_3, decode 300 d_2076_4, decode 300 d_2076_5, decode 300 d_2076_6, decode 158 d_2076_7] (fun x hx => bits_full_and hx) cov_2076 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_2076_0, ch_2076_1, ch_2076_2, ch_2076_3, ch_2076_4, ch_2076_5, ch_2076_6, ch_2076_7])

theorem root_2077 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 2077) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_2077_0, decode 300 d_2077_1, decode 300 d_2077_2, decode 300 d_2077_3, decode 300 d_2077_4, decode 300 d_2077_5, decode 300 d_2077_6, decode 158 d_2077_7] (fun x hx => bits_full_and hx) cov_2077 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_2077_0, ch_2077_1, ch_2077_2, ch_2077_3, ch_2077_4, ch_2077_5, ch_2077_6, ch_2077_7])

theorem root_2078 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 2078) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_2078_0, decode 300 d_2078_1, decode 300 d_2078_2, decode 300 d_2078_3, decode 300 d_2078_4, decode 300 d_2078_5, decode 300 d_2078_6, decode 158 d_2078_7] (fun x hx => bits_full_and hx) cov_2078 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_2078_0, ch_2078_1, ch_2078_2, ch_2078_3, ch_2078_4, ch_2078_5, ch_2078_6, ch_2078_7])

theorem root_2087 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 2087) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_2087_0, decode 300 d_2087_1, decode 300 d_2087_2, decode 300 d_2087_3, decode 300 d_2087_4, decode 300 d_2087_5, decode 300 d_2087_6, decode 62 d_2087_7] (fun x hx => bits_full_and hx) cov_2087 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_2087_0, ch_2087_1, ch_2087_2, ch_2087_3, ch_2087_4, ch_2087_5, ch_2087_6, ch_2087_7])

theorem root_2093 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 2093) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_2093_0, decode 300 d_2093_1, decode 300 d_2093_2, decode 300 d_2093_3, decode 300 d_2093_4, decode 300 d_2093_5, decode 276 d_2093_6] (fun x hx => bits_full_and hx) cov_2093 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_2093_0, ch_2093_1, ch_2093_2, ch_2093_3, ch_2093_4, ch_2093_5, ch_2093_6])

theorem root_2097 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 2097) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_2097_0, decode 300 d_2097_1, decode 300 d_2097_2, decode 300 d_2097_3, decode 300 d_2097_4, decode 300 d_2097_5, decode 300 d_2097_6, decode 141 d_2097_7] (fun x hx => bits_full_and hx) cov_2097 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_2097_0, ch_2097_1, ch_2097_2, ch_2097_3, ch_2097_4, ch_2097_5, ch_2097_6, ch_2097_7])

theorem root_2098 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 2098) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_2098_0, decode 300 d_2098_1, decode 300 d_2098_2, decode 300 d_2098_3, decode 300 d_2098_4, decode 300 d_2098_5, decode 300 d_2098_6, decode 141 d_2098_7] (fun x hx => bits_full_and hx) cov_2098 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_2098_0, ch_2098_1, ch_2098_2, ch_2098_3, ch_2098_4, ch_2098_5, ch_2098_6, ch_2098_7])

theorem root_2099 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 2099) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_2099_0, decode 300 d_2099_1, decode 300 d_2099_2, decode 300 d_2099_3, decode 300 d_2099_4, decode 300 d_2099_5, decode 300 d_2099_6, decode 141 d_2099_7] (fun x hx => bits_full_and hx) cov_2099 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_2099_0, ch_2099_1, ch_2099_2, ch_2099_3, ch_2099_4, ch_2099_5, ch_2099_6, ch_2099_7])

theorem root_2111 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 2111) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_2111_0, decode 300 d_2111_1, decode 300 d_2111_2, decode 300 d_2111_3, decode 300 d_2111_4, decode 300 d_2111_5, decode 300 d_2111_6, decode 141 d_2111_7] (fun x hx => bits_full_and hx) cov_2111 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_2111_0, ch_2111_1, ch_2111_2, ch_2111_3, ch_2111_4, ch_2111_5, ch_2111_6, ch_2111_7])

theorem root_2112 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 2112) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_2112_0, decode 300 d_2112_1, decode 300 d_2112_2, decode 300 d_2112_3, decode 300 d_2112_4, decode 300 d_2112_5, decode 300 d_2112_6, decode 141 d_2112_7] (fun x hx => bits_full_and hx) cov_2112 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_2112_0, ch_2112_1, ch_2112_2, ch_2112_3, ch_2112_4, ch_2112_5, ch_2112_6, ch_2112_7])

theorem root_2116 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 2116) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_2116_0, decode 300 d_2116_1, decode 300 d_2116_2, decode 300 d_2116_3, decode 300 d_2116_4, decode 300 d_2116_5, decode 300 d_2116_6, decode 158 d_2116_7] (fun x hx => bits_full_and hx) cov_2116 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_2116_0, ch_2116_1, ch_2116_2, ch_2116_3, ch_2116_4, ch_2116_5, ch_2116_6, ch_2116_7])

theorem root_2120 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 2120) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_2120_0, decode 300 d_2120_1, decode 300 d_2120_2, decode 300 d_2120_3, decode 300 d_2120_4, decode 300 d_2120_5, decode 300 d_2120_6, decode 141 d_2120_7] (fun x hx => bits_full_and hx) cov_2120 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_2120_0, ch_2120_1, ch_2120_2, ch_2120_3, ch_2120_4, ch_2120_5, ch_2120_6, ch_2120_7])

theorem root_2121 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 2121) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_2121_0, decode 300 d_2121_1, decode 300 d_2121_2, decode 300 d_2121_3, decode 300 d_2121_4, decode 300 d_2121_5, decode 300 d_2121_6, decode 141 d_2121_7] (fun x hx => bits_full_and hx) cov_2121 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_2121_0, ch_2121_1, ch_2121_2, ch_2121_3, ch_2121_4, ch_2121_5, ch_2121_6, ch_2121_7])

theorem root_2123 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 2123) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_2123_0, decode 300 d_2123_1, decode 300 d_2123_2, decode 300 d_2123_3, decode 300 d_2123_4, decode 300 d_2123_5, decode 300 d_2123_6, decode 158 d_2123_7] (fun x hx => bits_full_and hx) cov_2123 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_2123_0, ch_2123_1, ch_2123_2, ch_2123_3, ch_2123_4, ch_2123_5, ch_2123_6, ch_2123_7])

theorem root_2130 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 2130) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_2130_0, decode 300 d_2130_1, decode 300 d_2130_2, decode 300 d_2130_3, decode 300 d_2130_4, decode 300 d_2130_5, decode 300 d_2130_6, decode 141 d_2130_7] (fun x hx => bits_full_and hx) cov_2130 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_2130_0, ch_2130_1, ch_2130_2, ch_2130_3, ch_2130_4, ch_2130_5, ch_2130_6, ch_2130_7])

theorem root_2131 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 2131) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_2131_0, decode 300 d_2131_1, decode 300 d_2131_2, decode 300 d_2131_3, decode 300 d_2131_4, decode 300 d_2131_5, decode 300 d_2131_6, decode 142 d_2131_7] (fun x hx => bits_full_and hx) cov_2131 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_2131_0, ch_2131_1, ch_2131_2, ch_2131_3, ch_2131_4, ch_2131_5, ch_2131_6, ch_2131_7])

theorem root_2132 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 2132) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_2132_0, decode 300 d_2132_1, decode 300 d_2132_2, decode 300 d_2132_3, decode 300 d_2132_4, decode 300 d_2132_5, decode 300 d_2132_6, decode 142 d_2132_7] (fun x hx => bits_full_and hx) cov_2132 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_2132_0, ch_2132_1, ch_2132_2, ch_2132_3, ch_2132_4, ch_2132_5, ch_2132_6, ch_2132_7])

theorem roots_31_ok (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    ∀ k ∈ roots_31, Claim (FULL &&& MT k) 3 := by
  intro k hk
  simp only [roots_31, List.mem_cons, List.mem_nil_iff, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [root_2071 hB hC hCl hCB, root_2076 hB hC hCl hCB, root_2077 hB hC hCl hCB, root_2078 hB hC hCl hCB, root_2087 hB hC hCl hCB, root_2093 hB hC hCl hCB, root_2097 hB hC hCl hCB, root_2098 hB hC hCl hCB, root_2099 hB hC hCl hCB, root_2111 hB hC hCl hCB, root_2112 hB hC hCl hCB, root_2116 hB hC hCl hCB, root_2120 hB hC hCl hCB, root_2121 hB hC hCl hCB, root_2123 hB hC hCl hCB, root_2130 hB hC hCl hCB, root_2131 hB hC hCl hCB, root_2132 hB hC hCl hCB]

theorem root_2146 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 2146) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_2146_0, decode 300 d_2146_1, decode 300 d_2146_2, decode 300 d_2146_3, decode 300 d_2146_4, decode 300 d_2146_5, decode 25 d_2146_6] (fun x hx => bits_full_and hx) cov_2146 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_2146_0, ch_2146_1, ch_2146_2, ch_2146_3, ch_2146_4, ch_2146_5, ch_2146_6])

theorem root_2153 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 2153) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_2153_0, decode 300 d_2153_1, decode 300 d_2153_2, decode 300 d_2153_3, decode 300 d_2153_4, decode 300 d_2153_5, decode 36 d_2153_6] (fun x hx => bits_full_and hx) cov_2153 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_2153_0, ch_2153_1, ch_2153_2, ch_2153_3, ch_2153_4, ch_2153_5, ch_2153_6])

theorem root_2157 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 2157) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_2157_0, decode 300 d_2157_1, decode 300 d_2157_2, decode 300 d_2157_3, decode 300 d_2157_4, decode 300 d_2157_5, decode 300 d_2157_6, decode 141 d_2157_7] (fun x hx => bits_full_and hx) cov_2157 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_2157_0, ch_2157_1, ch_2157_2, ch_2157_3, ch_2157_4, ch_2157_5, ch_2157_6, ch_2157_7])

theorem root_2158 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 2158) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_2158_0, decode 300 d_2158_1, decode 300 d_2158_2, decode 300 d_2158_3, decode 300 d_2158_4, decode 300 d_2158_5, decode 300 d_2158_6, decode 141 d_2158_7] (fun x hx => bits_full_and hx) cov_2158 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_2158_0, ch_2158_1, ch_2158_2, ch_2158_3, ch_2158_4, ch_2158_5, ch_2158_6, ch_2158_7])

theorem root_2162 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 2162) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_2162_0, decode 300 d_2162_1, decode 300 d_2162_2, decode 300 d_2162_3, decode 300 d_2162_4, decode 300 d_2162_5, decode 300 d_2162_6, decode 141 d_2162_7] (fun x hx => bits_full_and hx) cov_2162 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_2162_0, ch_2162_1, ch_2162_2, ch_2162_3, ch_2162_4, ch_2162_5, ch_2162_6, ch_2162_7])

theorem root_2163 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 2163) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_2163_0, decode 300 d_2163_1, decode 300 d_2163_2, decode 300 d_2163_3, decode 300 d_2163_4, decode 300 d_2163_5, decode 300 d_2163_6, decode 141 d_2163_7] (fun x hx => bits_full_and hx) cov_2163 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_2163_0, ch_2163_1, ch_2163_2, ch_2163_3, ch_2163_4, ch_2163_5, ch_2163_6, ch_2163_7])

theorem root_2164 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 2164) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_2164_0, decode 300 d_2164_1, decode 300 d_2164_2, decode 300 d_2164_3, decode 300 d_2164_4, decode 300 d_2164_5, decode 300 d_2164_6, decode 141 d_2164_7] (fun x hx => bits_full_and hx) cov_2164 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_2164_0, ch_2164_1, ch_2164_2, ch_2164_3, ch_2164_4, ch_2164_5, ch_2164_6, ch_2164_7])

theorem root_2165 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 2165) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_2165_0, decode 300 d_2165_1, decode 300 d_2165_2, decode 300 d_2165_3, decode 300 d_2165_4, decode 300 d_2165_5, decode 300 d_2165_6, decode 141 d_2165_7] (fun x hx => bits_full_and hx) cov_2165 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_2165_0, ch_2165_1, ch_2165_2, ch_2165_3, ch_2165_4, ch_2165_5, ch_2165_6, ch_2165_7])

theorem root_2171 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 2171) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_2171_0, decode 300 d_2171_1, decode 300 d_2171_2, decode 300 d_2171_3, decode 300 d_2171_4, decode 300 d_2171_5, decode 300 d_2171_6, decode 141 d_2171_7] (fun x hx => bits_full_and hx) cov_2171 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_2171_0, ch_2171_1, ch_2171_2, ch_2171_3, ch_2171_4, ch_2171_5, ch_2171_6, ch_2171_7])

theorem root_2181 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 2181) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_2181_0, decode 300 d_2181_1, decode 300 d_2181_2, decode 300 d_2181_3, decode 300 d_2181_4, decode 300 d_2181_5, decode 300 d_2181_6, decode 141 d_2181_7] (fun x hx => bits_full_and hx) cov_2181 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_2181_0, ch_2181_1, ch_2181_2, ch_2181_3, ch_2181_4, ch_2181_5, ch_2181_6, ch_2181_7])

theorem root_2182 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 2182) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_2182_0, decode 300 d_2182_1, decode 300 d_2182_2, decode 300 d_2182_3, decode 300 d_2182_4, decode 300 d_2182_5, decode 300 d_2182_6, decode 141 d_2182_7] (fun x hx => bits_full_and hx) cov_2182 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_2182_0, ch_2182_1, ch_2182_2, ch_2182_3, ch_2182_4, ch_2182_5, ch_2182_6, ch_2182_7])

theorem root_2186 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 2186) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_2186_0, decode 300 d_2186_1, decode 300 d_2186_2, decode 300 d_2186_3, decode 300 d_2186_4, decode 300 d_2186_5, decode 13 d_2186_6] (fun x hx => bits_full_and hx) cov_2186 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_2186_0, ch_2186_1, ch_2186_2, ch_2186_3, ch_2186_4, ch_2186_5, ch_2186_6])

theorem root_2187 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 2187) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_2187_0, decode 300 d_2187_1, decode 300 d_2187_2, decode 300 d_2187_3, decode 300 d_2187_4, decode 300 d_2187_5, decode 13 d_2187_6] (fun x hx => bits_full_and hx) cov_2187 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_2187_0, ch_2187_1, ch_2187_2, ch_2187_3, ch_2187_4, ch_2187_5, ch_2187_6])

theorem root_2188 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 2188) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_2188_0, decode 300 d_2188_1, decode 300 d_2188_2, decode 300 d_2188_3, decode 300 d_2188_4, decode 263 d_2188_5] (fun x hx => bits_full_and hx) cov_2188 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_2188_0, ch_2188_1, ch_2188_2, ch_2188_3, ch_2188_4, ch_2188_5])

theorem root_2194 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 2194) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_2194_0, decode 300 d_2194_1, decode 300 d_2194_2, decode 300 d_2194_3, decode 300 d_2194_4, decode 300 d_2194_5, decode 300 d_2194_6, decode 141 d_2194_7] (fun x hx => bits_full_and hx) cov_2194 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_2194_0, ch_2194_1, ch_2194_2, ch_2194_3, ch_2194_4, ch_2194_5, ch_2194_6, ch_2194_7])

theorem root_2197 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 2197) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_2197_0, decode 300 d_2197_1, decode 300 d_2197_2, decode 300 d_2197_3, decode 300 d_2197_4, decode 300 d_2197_5, decode 300 d_2197_6, decode 141 d_2197_7] (fun x hx => bits_full_and hx) cov_2197 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_2197_0, ch_2197_1, ch_2197_2, ch_2197_3, ch_2197_4, ch_2197_5, ch_2197_6, ch_2197_7])

theorem root_2198 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 2198) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_2198_0, decode 300 d_2198_1, decode 300 d_2198_2, decode 300 d_2198_3, decode 300 d_2198_4, decode 300 d_2198_5, decode 300 d_2198_6, decode 141 d_2198_7] (fun x hx => bits_full_and hx) cov_2198 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_2198_0, ch_2198_1, ch_2198_2, ch_2198_3, ch_2198_4, ch_2198_5, ch_2198_6, ch_2198_7])

theorem root_2201 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 2201) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_2201_0, decode 300 d_2201_1, decode 300 d_2201_2, decode 300 d_2201_3, decode 300 d_2201_4, decode 300 d_2201_5, decode 79 d_2201_6] (fun x hx => bits_full_and hx) cov_2201 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_2201_0, ch_2201_1, ch_2201_2, ch_2201_3, ch_2201_4, ch_2201_5, ch_2201_6])

theorem root_2204 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 2204) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_2204_0, decode 300 d_2204_1, decode 300 d_2204_2, decode 300 d_2204_3, decode 300 d_2204_4, decode 300 d_2204_5, decode 79 d_2204_6] (fun x hx => bits_full_and hx) cov_2204 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_2204_0, ch_2204_1, ch_2204_2, ch_2204_3, ch_2204_4, ch_2204_5, ch_2204_6])

theorem root_2208 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 2208) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_2208_0, decode 300 d_2208_1, decode 300 d_2208_2, decode 300 d_2208_3, decode 300 d_2208_4, decode 300 d_2208_5, decode 10 d_2208_6] (fun x hx => bits_full_and hx) cov_2208 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_2208_0, ch_2208_1, ch_2208_2, ch_2208_3, ch_2208_4, ch_2208_5, ch_2208_6])

theorem roots_32_ok (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    ∀ k ∈ roots_32, Claim (FULL &&& MT k) 3 := by
  intro k hk
  simp only [roots_32, List.mem_cons, List.mem_nil_iff, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [root_2146 hB hC hCl hCB, root_2153 hB hC hCl hCB, root_2157 hB hC hCl hCB, root_2158 hB hC hCl hCB, root_2162 hB hC hCl hCB, root_2163 hB hC hCl hCB, root_2164 hB hC hCl hCB, root_2165 hB hC hCl hCB, root_2171 hB hC hCl hCB, root_2181 hB hC hCl hCB, root_2182 hB hC hCl hCB, root_2186 hB hC hCl hCB, root_2187 hB hC hCl hCB, root_2188 hB hC hCl hCB, root_2194 hB hC hCl hCB, root_2197 hB hC hCl hCB, root_2198 hB hC hCl hCB, root_2201 hB hC hCl hCB, root_2204 hB hC hCl hCB, root_2208 hB hC hCl hCB]

theorem root_2209 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 2209) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_2209_0, decode 300 d_2209_1, decode 300 d_2209_2, decode 300 d_2209_3, decode 300 d_2209_4, decode 300 d_2209_5, decode 10 d_2209_6] (fun x hx => bits_full_and hx) cov_2209 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_2209_0, ch_2209_1, ch_2209_2, ch_2209_3, ch_2209_4, ch_2209_5, ch_2209_6])

theorem root_2210 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 2210) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_2210_0, decode 300 d_2210_1, decode 300 d_2210_2, decode 300 d_2210_3, decode 300 d_2210_4, decode 300 d_2210_5, decode 10 d_2210_6] (fun x hx => bits_full_and hx) cov_2210 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_2210_0, ch_2210_1, ch_2210_2, ch_2210_3, ch_2210_4, ch_2210_5, ch_2210_6])

theorem root_2211 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 2211) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_2211_0, decode 300 d_2211_1, decode 300 d_2211_2, decode 300 d_2211_3, decode 300 d_2211_4, decode 300 d_2211_5, decode 81 d_2211_6] (fun x hx => bits_full_and hx) cov_2211 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_2211_0, ch_2211_1, ch_2211_2, ch_2211_3, ch_2211_4, ch_2211_5, ch_2211_6])

theorem root_2212 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 2212) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_2212_0, decode 300 d_2212_1, decode 300 d_2212_2, decode 300 d_2212_3, decode 300 d_2212_4, decode 300 d_2212_5, decode 81 d_2212_6] (fun x hx => bits_full_and hx) cov_2212 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_2212_0, ch_2212_1, ch_2212_2, ch_2212_3, ch_2212_4, ch_2212_5, ch_2212_6])

theorem root_2216 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 2216) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_2216_0, decode 300 d_2216_1, decode 300 d_2216_2, decode 300 d_2216_3, decode 300 d_2216_4, decode 300 d_2216_5, decode 15 d_2216_6] (fun x hx => bits_full_and hx) cov_2216 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_2216_0, ch_2216_1, ch_2216_2, ch_2216_3, ch_2216_4, ch_2216_5, ch_2216_6])

theorem root_2220 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 2220) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_2220_0, decode 300 d_2220_1, decode 300 d_2220_2, decode 300 d_2220_3, decode 300 d_2220_4, decode 300 d_2220_5, decode 40 d_2220_6] (fun x hx => bits_full_and hx) cov_2220 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_2220_0, ch_2220_1, ch_2220_2, ch_2220_3, ch_2220_4, ch_2220_5, ch_2220_6])

theorem root_2225 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 2225) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_2225_0, decode 300 d_2225_1, decode 300 d_2225_2, decode 300 d_2225_3, decode 300 d_2225_4, decode 300 d_2225_5, decode 300 d_2225_6, decode 141 d_2225_7] (fun x hx => bits_full_and hx) cov_2225 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_2225_0, ch_2225_1, ch_2225_2, ch_2225_3, ch_2225_4, ch_2225_5, ch_2225_6, ch_2225_7])

theorem root_2226 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 2226) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_2226_0, decode 300 d_2226_1, decode 300 d_2226_2, decode 300 d_2226_3, decode 300 d_2226_4, decode 300 d_2226_5, decode 300 d_2226_6, decode 141 d_2226_7] (fun x hx => bits_full_and hx) cov_2226 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_2226_0, ch_2226_1, ch_2226_2, ch_2226_3, ch_2226_4, ch_2226_5, ch_2226_6, ch_2226_7])

theorem root_2227 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 2227) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_2227_0, decode 300 d_2227_1, decode 300 d_2227_2, decode 300 d_2227_3, decode 300 d_2227_4, decode 300 d_2227_5, decode 300 d_2227_6, decode 141 d_2227_7] (fun x hx => bits_full_and hx) cov_2227 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_2227_0, ch_2227_1, ch_2227_2, ch_2227_3, ch_2227_4, ch_2227_5, ch_2227_6, ch_2227_7])

theorem root_2228 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 2228) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_2228_0, decode 300 d_2228_1, decode 300 d_2228_2, decode 300 d_2228_3, decode 300 d_2228_4, decode 300 d_2228_5, decode 300 d_2228_6, decode 141 d_2228_7] (fun x hx => bits_full_and hx) cov_2228 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_2228_0, ch_2228_1, ch_2228_2, ch_2228_3, ch_2228_4, ch_2228_5, ch_2228_6, ch_2228_7])

theorem root_2233 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 2233) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_2233_0, decode 300 d_2233_1, decode 300 d_2233_2, decode 300 d_2233_3, decode 300 d_2233_4, decode 300 d_2233_5, decode 300 d_2233_6, decode 141 d_2233_7] (fun x hx => bits_full_and hx) cov_2233 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_2233_0, ch_2233_1, ch_2233_2, ch_2233_3, ch_2233_4, ch_2233_5, ch_2233_6, ch_2233_7])

theorem root_2234 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 2234) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_2234_0, decode 300 d_2234_1, decode 300 d_2234_2, decode 300 d_2234_3, decode 300 d_2234_4, decode 300 d_2234_5, decode 300 d_2234_6, decode 141 d_2234_7] (fun x hx => bits_full_and hx) cov_2234 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_2234_0, ch_2234_1, ch_2234_2, ch_2234_3, ch_2234_4, ch_2234_5, ch_2234_6, ch_2234_7])

theorem root_2238 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 2238) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_2238_0, decode 300 d_2238_1, decode 300 d_2238_2, decode 300 d_2238_3, decode 300 d_2238_4, decode 300 d_2238_5, decode 300 d_2238_6, decode 141 d_2238_7] (fun x hx => bits_full_and hx) cov_2238 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_2238_0, ch_2238_1, ch_2238_2, ch_2238_3, ch_2238_4, ch_2238_5, ch_2238_6, ch_2238_7])

theorem root_2239 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 2239) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_2239_0, decode 300 d_2239_1, decode 300 d_2239_2, decode 300 d_2239_3, decode 300 d_2239_4, decode 300 d_2239_5, decode 300 d_2239_6, decode 141 d_2239_7] (fun x hx => bits_full_and hx) cov_2239 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_2239_0, ch_2239_1, ch_2239_2, ch_2239_3, ch_2239_4, ch_2239_5, ch_2239_6, ch_2239_7])

theorem root_2240 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 2240) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_2240_0, decode 300 d_2240_1, decode 300 d_2240_2, decode 300 d_2240_3, decode 300 d_2240_4, decode 300 d_2240_5, decode 300 d_2240_6, decode 141 d_2240_7] (fun x hx => bits_full_and hx) cov_2240 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_2240_0, ch_2240_1, ch_2240_2, ch_2240_3, ch_2240_4, ch_2240_5, ch_2240_6, ch_2240_7])

theorem root_2241 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 2241) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_2241_0, decode 300 d_2241_1, decode 300 d_2241_2, decode 300 d_2241_3, decode 300 d_2241_4, decode 300 d_2241_5, decode 300 d_2241_6, decode 141 d_2241_7] (fun x hx => bits_full_and hx) cov_2241 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_2241_0, ch_2241_1, ch_2241_2, ch_2241_3, ch_2241_4, ch_2241_5, ch_2241_6, ch_2241_7])

theorem root_2249 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 2249) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_2249_0, decode 300 d_2249_1, decode 300 d_2249_2, decode 300 d_2249_3, decode 300 d_2249_4, decode 300 d_2249_5, decode 300 d_2249_6, decode 141 d_2249_7] (fun x hx => bits_full_and hx) cov_2249 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_2249_0, ch_2249_1, ch_2249_2, ch_2249_3, ch_2249_4, ch_2249_5, ch_2249_6, ch_2249_7])

theorem root_2250 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 2250) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_2250_0, decode 300 d_2250_1, decode 300 d_2250_2, decode 300 d_2250_3, decode 300 d_2250_4, decode 300 d_2250_5, decode 300 d_2250_6, decode 141 d_2250_7] (fun x hx => bits_full_and hx) cov_2250 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_2250_0, ch_2250_1, ch_2250_2, ch_2250_3, ch_2250_4, ch_2250_5, ch_2250_6, ch_2250_7])

theorem root_2259 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 2259) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_2259_0, decode 300 d_2259_1, decode 300 d_2259_2, decode 300 d_2259_3, decode 300 d_2259_4, decode 300 d_2259_5, decode 300 d_2259_6, decode 141 d_2259_7] (fun x hx => bits_full_and hx) cov_2259 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_2259_0, ch_2259_1, ch_2259_2, ch_2259_3, ch_2259_4, ch_2259_5, ch_2259_6, ch_2259_7])

theorem roots_33_ok (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    ∀ k ∈ roots_33, Claim (FULL &&& MT k) 3 := by
  intro k hk
  simp only [roots_33, List.mem_cons, List.mem_nil_iff, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [root_2209 hB hC hCl hCB, root_2210 hB hC hCl hCB, root_2211 hB hC hCl hCB, root_2212 hB hC hCl hCB, root_2216 hB hC hCl hCB, root_2220 hB hC hCl hCB, root_2225 hB hC hCl hCB, root_2226 hB hC hCl hCB, root_2227 hB hC hCl hCB, root_2228 hB hC hCl hCB, root_2233 hB hC hCl hCB, root_2234 hB hC hCl hCB, root_2238 hB hC hCl hCB, root_2239 hB hC hCl hCB, root_2240 hB hC hCl hCB, root_2241 hB hC hCl hCB, root_2249 hB hC hCl hCB, root_2250 hB hC hCl hCB, root_2259 hB hC hCl hCB]

theorem root_2260 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 2260) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_2260_0, decode 300 d_2260_1, decode 300 d_2260_2, decode 300 d_2260_3, decode 300 d_2260_4, decode 300 d_2260_5, decode 300 d_2260_6, decode 141 d_2260_7] (fun x hx => bits_full_and hx) cov_2260 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_2260_0, ch_2260_1, ch_2260_2, ch_2260_3, ch_2260_4, ch_2260_5, ch_2260_6, ch_2260_7])

theorem root_2264 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 2264) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_2264_0, decode 300 d_2264_1, decode 300 d_2264_2, decode 300 d_2264_3, decode 300 d_2264_4, decode 300 d_2264_5, decode 300 d_2264_6, decode 141 d_2264_7] (fun x hx => bits_full_and hx) cov_2264 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_2264_0, ch_2264_1, ch_2264_2, ch_2264_3, ch_2264_4, ch_2264_5, ch_2264_6, ch_2264_7])

theorem root_2265 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 2265) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_2265_0, decode 300 d_2265_1, decode 300 d_2265_2, decode 300 d_2265_3, decode 300 d_2265_4, decode 300 d_2265_5, decode 300 d_2265_6, decode 141 d_2265_7] (fun x hx => bits_full_and hx) cov_2265 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_2265_0, ch_2265_1, ch_2265_2, ch_2265_3, ch_2265_4, ch_2265_5, ch_2265_6, ch_2265_7])

theorem root_2273 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 2273) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_2273_0, decode 300 d_2273_1, decode 300 d_2273_2, decode 300 d_2273_3, decode 300 d_2273_4, decode 300 d_2273_5, decode 19 d_2273_6] (fun x hx => bits_full_and hx) cov_2273 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_2273_0, ch_2273_1, ch_2273_2, ch_2273_3, ch_2273_4, ch_2273_5, ch_2273_6])

theorem root_2274 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 2274) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_2274_0, decode 300 d_2274_1, decode 300 d_2274_2, decode 300 d_2274_3, decode 300 d_2274_4, decode 300 d_2274_5, decode 19 d_2274_6] (fun x hx => bits_full_and hx) cov_2274 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_2274_0, ch_2274_1, ch_2274_2, ch_2274_3, ch_2274_4, ch_2274_5, ch_2274_6])

theorem root_2282 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 2282) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_2282_0, decode 300 d_2282_1, decode 300 d_2282_2, decode 300 d_2282_3, decode 300 d_2282_4, decode 300 d_2282_5, decode 51 d_2282_6] (fun x hx => bits_full_and hx) cov_2282 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_2282_0, ch_2282_1, ch_2282_2, ch_2282_3, ch_2282_4, ch_2282_5, ch_2282_6])

theorem root_2283 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 2283) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_2283_0, decode 300 d_2283_1, decode 300 d_2283_2, decode 300 d_2283_3, decode 300 d_2283_4, decode 300 d_2283_5, decode 59 d_2283_6] (fun x hx => bits_full_and hx) cov_2283 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_2283_0, ch_2283_1, ch_2283_2, ch_2283_3, ch_2283_4, ch_2283_5, ch_2283_6])

theorem root_2286 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 2286) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_2286_0, decode 300 d_2286_1, decode 300 d_2286_2, decode 300 d_2286_3, decode 300 d_2286_4, decode 300 d_2286_5, decode 300 d_2286_6, decode 142 d_2286_7] (fun x hx => bits_full_and hx) cov_2286 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_2286_0, ch_2286_1, ch_2286_2, ch_2286_3, ch_2286_4, ch_2286_5, ch_2286_6, ch_2286_7])

theorem root_2291 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 2291) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_2291_0, decode 300 d_2291_1, decode 300 d_2291_2, decode 300 d_2291_3, decode 300 d_2291_4, decode 300 d_2291_5, decode 300 d_2291_6, decode 141 d_2291_7] (fun x hx => bits_full_and hx) cov_2291 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_2291_0, ch_2291_1, ch_2291_2, ch_2291_3, ch_2291_4, ch_2291_5, ch_2291_6, ch_2291_7])

theorem root_2292 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 2292) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_2292_0, decode 300 d_2292_1, decode 300 d_2292_2, decode 300 d_2292_3, decode 300 d_2292_4, decode 300 d_2292_5, decode 300 d_2292_6, decode 141 d_2292_7] (fun x hx => bits_full_and hx) cov_2292 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_2292_0, ch_2292_1, ch_2292_2, ch_2292_3, ch_2292_4, ch_2292_5, ch_2292_6, ch_2292_7])

theorem root_2295 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 2295) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_2295_0, decode 300 d_2295_1, decode 300 d_2295_2, decode 300 d_2295_3, decode 300 d_2295_4, decode 300 d_2295_5, decode 300 d_2295_6, decode 142 d_2295_7] (fun x hx => bits_full_and hx) cov_2295 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_2295_0, ch_2295_1, ch_2295_2, ch_2295_3, ch_2295_4, ch_2295_5, ch_2295_6, ch_2295_7])

theorem root_2302 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 2302) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_2302_0, decode 300 d_2302_1, decode 300 d_2302_2, decode 300 d_2302_3, decode 300 d_2302_4, decode 300 d_2302_5, decode 300 d_2302_6, decode 141 d_2302_7] (fun x hx => bits_full_and hx) cov_2302 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_2302_0, ch_2302_1, ch_2302_2, ch_2302_3, ch_2302_4, ch_2302_5, ch_2302_6, ch_2302_7])

theorem root_2307 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 2307) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_2307_0, decode 300 d_2307_1, decode 300 d_2307_2, decode 300 d_2307_3, decode 300 d_2307_4, decode 300 d_2307_5, decode 300 d_2307_6, decode 142 d_2307_7] (fun x hx => bits_full_and hx) cov_2307 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_2307_0, ch_2307_1, ch_2307_2, ch_2307_3, ch_2307_4, ch_2307_5, ch_2307_6, ch_2307_7])

theorem root_2310 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 2310) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_2310_0, decode 300 d_2310_1, decode 300 d_2310_2, decode 300 d_2310_3, decode 300 d_2310_4, decode 300 d_2310_5, decode 300 d_2310_6, decode 141 d_2310_7] (fun x hx => bits_full_and hx) cov_2310 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_2310_0, ch_2310_1, ch_2310_2, ch_2310_3, ch_2310_4, ch_2310_5, ch_2310_6, ch_2310_7])

theorem root_2311 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 2311) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_2311_0, decode 300 d_2311_1, decode 300 d_2311_2, decode 300 d_2311_3, decode 300 d_2311_4, decode 300 d_2311_5, decode 300 d_2311_6, decode 141 d_2311_7] (fun x hx => bits_full_and hx) cov_2311 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_2311_0, ch_2311_1, ch_2311_2, ch_2311_3, ch_2311_4, ch_2311_5, ch_2311_6, ch_2311_7])

theorem root_2317 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 2317) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_2317_0, decode 300 d_2317_1, decode 300 d_2317_2, decode 300 d_2317_3, decode 300 d_2317_4, decode 300 d_2317_5, decode 300 d_2317_6, decode 141 d_2317_7] (fun x hx => bits_full_and hx) cov_2317 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_2317_0, ch_2317_1, ch_2317_2, ch_2317_3, ch_2317_4, ch_2317_5, ch_2317_6, ch_2317_7])

theorem root_2326 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 2326) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_2326_0, decode 300 d_2326_1, decode 300 d_2326_2, decode 300 d_2326_3, decode 300 d_2326_4, decode 300 d_2326_5, decode 300 d_2326_6, decode 141 d_2326_7] (fun x hx => bits_full_and hx) cov_2326 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_2326_0, ch_2326_1, ch_2326_2, ch_2326_3, ch_2326_4, ch_2326_5, ch_2326_6, ch_2326_7])

theorem root_2336 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 2336) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_2336_0, decode 300 d_2336_1, decode 300 d_2336_2, decode 300 d_2336_3, decode 300 d_2336_4, decode 300 d_2336_5, decode 300 d_2336_6, decode 142 d_2336_7] (fun x hx => bits_full_and hx) cov_2336 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_2336_0, ch_2336_1, ch_2336_2, ch_2336_3, ch_2336_4, ch_2336_5, ch_2336_6, ch_2336_7])

theorem root_2337 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 2337) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_2337_0, decode 300 d_2337_1, decode 300 d_2337_2, decode 300 d_2337_3, decode 300 d_2337_4, decode 300 d_2337_5, decode 300 d_2337_6, decode 142 d_2337_7] (fun x hx => bits_full_and hx) cov_2337 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_2337_0, ch_2337_1, ch_2337_2, ch_2337_3, ch_2337_4, ch_2337_5, ch_2337_6, ch_2337_7])

theorem roots_34_ok (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    ∀ k ∈ roots_34, Claim (FULL &&& MT k) 3 := by
  intro k hk
  simp only [roots_34, List.mem_cons, List.mem_nil_iff, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [root_2260 hB hC hCl hCB, root_2264 hB hC hCl hCB, root_2265 hB hC hCl hCB, root_2273 hB hC hCl hCB, root_2274 hB hC hCl hCB, root_2282 hB hC hCl hCB, root_2283 hB hC hCl hCB, root_2286 hB hC hCl hCB, root_2291 hB hC hCl hCB, root_2292 hB hC hCl hCB, root_2295 hB hC hCl hCB, root_2302 hB hC hCl hCB, root_2307 hB hC hCl hCB, root_2310 hB hC hCl hCB, root_2311 hB hC hCl hCB, root_2317 hB hC hCl hCB, root_2326 hB hC hCl hCB, root_2336 hB hC hCl hCB, root_2337 hB hC hCl hCB]

theorem root_2339 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 2339) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_2339_0, decode 300 d_2339_1, decode 300 d_2339_2, decode 300 d_2339_3, decode 300 d_2339_4, decode 300 d_2339_5, decode 300 d_2339_6, decode 141 d_2339_7] (fun x hx => bits_full_and hx) cov_2339 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_2339_0, ch_2339_1, ch_2339_2, ch_2339_3, ch_2339_4, ch_2339_5, ch_2339_6, ch_2339_7])

theorem root_2345 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 2345) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_2345_0, decode 300 d_2345_1, decode 300 d_2345_2, decode 300 d_2345_3, decode 300 d_2345_4, decode 300 d_2345_5, decode 250 d_2345_6] (fun x hx => bits_full_and hx) cov_2345 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_2345_0, ch_2345_1, ch_2345_2, ch_2345_3, ch_2345_4, ch_2345_5, ch_2345_6])

theorem root_2346 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 2346) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_2346_0, decode 300 d_2346_1, decode 300 d_2346_2, decode 300 d_2346_3, decode 300 d_2346_4, decode 300 d_2346_5, decode 250 d_2346_6] (fun x hx => bits_full_and hx) cov_2346 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_2346_0, ch_2346_1, ch_2346_2, ch_2346_3, ch_2346_4, ch_2346_5, ch_2346_6])

theorem root_2347 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 2347) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_2347_0, decode 300 d_2347_1, decode 300 d_2347_2, decode 300 d_2347_3, decode 300 d_2347_4, decode 300 d_2347_5, decode 250 d_2347_6] (fun x hx => bits_full_and hx) cov_2347 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_2347_0, ch_2347_1, ch_2347_2, ch_2347_3, ch_2347_4, ch_2347_5, ch_2347_6])

theorem root_2348 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 2348) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_2348_0, decode 300 d_2348_1, decode 300 d_2348_2, decode 300 d_2348_3, decode 300 d_2348_4, decode 273 d_2348_5] (fun x hx => bits_full_and hx) cov_2348 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_2348_0, ch_2348_1, ch_2348_2, ch_2348_3, ch_2348_4, ch_2348_5])

theorem root_2353 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 2353) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_2353_0, decode 300 d_2353_1, decode 300 d_2353_2, decode 300 d_2353_3, decode 300 d_2353_4, decode 300 d_2353_5, decode 250 d_2353_6] (fun x hx => bits_full_and hx) cov_2353 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_2353_0, ch_2353_1, ch_2353_2, ch_2353_3, ch_2353_4, ch_2353_5, ch_2353_6])

theorem root_2354 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 2354) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_2354_0, decode 300 d_2354_1, decode 300 d_2354_2, decode 300 d_2354_3, decode 300 d_2354_4, decode 273 d_2354_5] (fun x hx => bits_full_and hx) cov_2354 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_2354_0, ch_2354_1, ch_2354_2, ch_2354_3, ch_2354_4, ch_2354_5])

theorem root_2356 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 2356) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_2356_0, decode 300 d_2356_1, decode 300 d_2356_2, decode 300 d_2356_3, decode 300 d_2356_4, decode 300 d_2356_5, decode 300 d_2356_6, decode 141 d_2356_7] (fun x hx => bits_full_and hx) cov_2356 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_2356_0, ch_2356_1, ch_2356_2, ch_2356_3, ch_2356_4, ch_2356_5, ch_2356_6, ch_2356_7])

theorem root_2357 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 2357) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_2357_0, decode 300 d_2357_1, decode 300 d_2357_2, decode 300 d_2357_3, decode 300 d_2357_4, decode 300 d_2357_5, decode 300 d_2357_6, decode 141 d_2357_7] (fun x hx => bits_full_and hx) cov_2357 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_2357_0, ch_2357_1, ch_2357_2, ch_2357_3, ch_2357_4, ch_2357_5, ch_2357_6, ch_2357_7])

theorem root_2368 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 2368) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_2368_0, decode 300 d_2368_1, decode 300 d_2368_2, decode 300 d_2368_3, decode 300 d_2368_4, decode 300 d_2368_5, decode 300 d_2368_6, decode 141 d_2368_7] (fun x hx => bits_full_and hx) cov_2368 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_2368_0, ch_2368_1, ch_2368_2, ch_2368_3, ch_2368_4, ch_2368_5, ch_2368_6, ch_2368_7])

theorem root_2386 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 2386) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_2386_0, decode 300 d_2386_1, decode 300 d_2386_2, decode 300 d_2386_3, decode 300 d_2386_4, decode 300 d_2386_5, decode 300 d_2386_6, decode 141 d_2386_7] (fun x hx => bits_full_and hx) cov_2386 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_2386_0, ch_2386_1, ch_2386_2, ch_2386_3, ch_2386_4, ch_2386_5, ch_2386_6, ch_2386_7])

theorem root_2387 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 2387) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_2387_0, decode 300 d_2387_1, decode 300 d_2387_2, decode 300 d_2387_3, decode 300 d_2387_4, decode 300 d_2387_5, decode 300 d_2387_6, decode 141 d_2387_7] (fun x hx => bits_full_and hx) cov_2387 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_2387_0, ch_2387_1, ch_2387_2, ch_2387_3, ch_2387_4, ch_2387_5, ch_2387_6, ch_2387_7])

theorem root_2388 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 2388) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_2388_0, decode 300 d_2388_1, decode 300 d_2388_2, decode 300 d_2388_3, decode 300 d_2388_4, decode 300 d_2388_5, decode 300 d_2388_6, decode 141 d_2388_7] (fun x hx => bits_full_and hx) cov_2388 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_2388_0, ch_2388_1, ch_2388_2, ch_2388_3, ch_2388_4, ch_2388_5, ch_2388_6, ch_2388_7])

theorem root_2399 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 2399) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_2399_0, decode 300 d_2399_1, decode 300 d_2399_2, decode 300 d_2399_3, decode 300 d_2399_4, decode 300 d_2399_5, decode 300 d_2399_6, decode 141 d_2399_7] (fun x hx => bits_full_and hx) cov_2399 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_2399_0, ch_2399_1, ch_2399_2, ch_2399_3, ch_2399_4, ch_2399_5, ch_2399_6, ch_2399_7])

theorem root_2400 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 2400) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_2400_0, decode 300 d_2400_1, decode 300 d_2400_2, decode 300 d_2400_3, decode 300 d_2400_4, decode 300 d_2400_5, decode 300 d_2400_6, decode 141 d_2400_7] (fun x hx => bits_full_and hx) cov_2400 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_2400_0, ch_2400_1, ch_2400_2, ch_2400_3, ch_2400_4, ch_2400_5, ch_2400_6, ch_2400_7])

theorem root_2410 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 2410) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_2410_0, decode 300 d_2410_1, decode 300 d_2410_2, decode 300 d_2410_3, decode 300 d_2410_4, decode 300 d_2410_5, decode 300 d_2410_6, decode 141 d_2410_7] (fun x hx => bits_full_and hx) cov_2410 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_2410_0, ch_2410_1, ch_2410_2, ch_2410_3, ch_2410_4, ch_2410_5, ch_2410_6, ch_2410_7])

theorem root_2413 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 2413) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_2413_0, decode 300 d_2413_1, decode 300 d_2413_2, decode 300 d_2413_3, decode 300 d_2413_4, decode 300 d_2413_5, decode 76 d_2413_6] (fun x hx => bits_full_and hx) cov_2413 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_2413_0, ch_2413_1, ch_2413_2, ch_2413_3, ch_2413_4, ch_2413_5, ch_2413_6])

theorem root_2414 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 2414) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_2414_0, decode 300 d_2414_1, decode 300 d_2414_2, decode 300 d_2414_3, decode 300 d_2414_4, decode 300 d_2414_5, decode 76 d_2414_6] (fun x hx => bits_full_and hx) cov_2414 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_2414_0, ch_2414_1, ch_2414_2, ch_2414_3, ch_2414_4, ch_2414_5, ch_2414_6])

theorem root_2417 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 2417) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_2417_0, decode 300 d_2417_1, decode 300 d_2417_2, decode 300 d_2417_3, decode 300 d_2417_4, decode 300 d_2417_5, decode 300 d_2417_6, decode 141 d_2417_7] (fun x hx => bits_full_and hx) cov_2417 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_2417_0, ch_2417_1, ch_2417_2, ch_2417_3, ch_2417_4, ch_2417_5, ch_2417_6, ch_2417_7])

theorem roots_35_ok (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    ∀ k ∈ roots_35, Claim (FULL &&& MT k) 3 := by
  intro k hk
  simp only [roots_35, List.mem_cons, List.mem_nil_iff, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [root_2339 hB hC hCl hCB, root_2345 hB hC hCl hCB, root_2346 hB hC hCl hCB, root_2347 hB hC hCl hCB, root_2348 hB hC hCl hCB, root_2353 hB hC hCl hCB, root_2354 hB hC hCl hCB, root_2356 hB hC hCl hCB, root_2357 hB hC hCl hCB, root_2368 hB hC hCl hCB, root_2386 hB hC hCl hCB, root_2387 hB hC hCl hCB, root_2388 hB hC hCl hCB, root_2399 hB hC hCl hCB, root_2400 hB hC hCl hCB, root_2410 hB hC hCl hCB, root_2413 hB hC hCl hCB, root_2414 hB hC hCl hCB, root_2417 hB hC hCl hCB]

theorem root_2418 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 2418) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_2418_0, decode 300 d_2418_1, decode 300 d_2418_2, decode 300 d_2418_3, decode 300 d_2418_4, decode 300 d_2418_5, decode 300 d_2418_6, decode 141 d_2418_7] (fun x hx => bits_full_and hx) cov_2418 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_2418_0, ch_2418_1, ch_2418_2, ch_2418_3, ch_2418_4, ch_2418_5, ch_2418_6, ch_2418_7])

theorem root_2425 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 2425) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_2425_0, decode 300 d_2425_1, decode 300 d_2425_2, decode 300 d_2425_3, decode 300 d_2425_4, decode 300 d_2425_5, decode 300 d_2425_6, decode 141 d_2425_7] (fun x hx => bits_full_and hx) cov_2425 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_2425_0, ch_2425_1, ch_2425_2, ch_2425_3, ch_2425_4, ch_2425_5, ch_2425_6, ch_2425_7])

theorem root_2426 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 2426) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_2426_0, decode 300 d_2426_1, decode 300 d_2426_2, decode 300 d_2426_3, decode 300 d_2426_4, decode 300 d_2426_5, decode 300 d_2426_6, decode 141 d_2426_7] (fun x hx => bits_full_and hx) cov_2426 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_2426_0, ch_2426_1, ch_2426_2, ch_2426_3, ch_2426_4, ch_2426_5, ch_2426_6, ch_2426_7])

theorem root_2427 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 2427) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_2427_0, decode 300 d_2427_1, decode 300 d_2427_2, decode 300 d_2427_3, decode 300 d_2427_4, decode 300 d_2427_5, decode 300 d_2427_6, decode 141 d_2427_7] (fun x hx => bits_full_and hx) cov_2427 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_2427_0, ch_2427_1, ch_2427_2, ch_2427_3, ch_2427_4, ch_2427_5, ch_2427_6, ch_2427_7])

theorem root_2428 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 2428) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_2428_0, decode 300 d_2428_1, decode 300 d_2428_2, decode 300 d_2428_3, decode 300 d_2428_4, decode 300 d_2428_5, decode 300 d_2428_6, decode 141 d_2428_7] (fun x hx => bits_full_and hx) cov_2428 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_2428_0, ch_2428_1, ch_2428_2, ch_2428_3, ch_2428_4, ch_2428_5, ch_2428_6, ch_2428_7])

theorem root_2430 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 2430) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_2430_0, decode 300 d_2430_1, decode 300 d_2430_2, decode 300 d_2430_3, decode 300 d_2430_4, decode 300 d_2430_5, decode 3 d_2430_6] (fun x hx => bits_full_and hx) cov_2430 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_2430_0, ch_2430_1, ch_2430_2, ch_2430_3, ch_2430_4, ch_2430_5, ch_2430_6])

theorem root_2431 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 2431) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_2431_0, decode 300 d_2431_1, decode 300 d_2431_2, decode 300 d_2431_3, decode 300 d_2431_4, decode 300 d_2431_5, decode 3 d_2431_6] (fun x hx => bits_full_and hx) cov_2431 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_2431_0, ch_2431_1, ch_2431_2, ch_2431_3, ch_2431_4, ch_2431_5, ch_2431_6])

theorem root_2432 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 2432) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_2432_0, decode 300 d_2432_1, decode 300 d_2432_2, decode 300 d_2432_3, decode 300 d_2432_4, decode 300 d_2432_5, decode 35 d_2432_6] (fun x hx => bits_full_and hx) cov_2432 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_2432_0, ch_2432_1, ch_2432_2, ch_2432_3, ch_2432_4, ch_2432_5, ch_2432_6])

theorem root_2439 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 2439) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_2439_0, decode 300 d_2439_1, decode 300 d_2439_2, decode 300 d_2439_3, decode 300 d_2439_4, decode 300 d_2439_5, decode 13 d_2439_6] (fun x hx => bits_full_and hx) cov_2439 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_2439_0, ch_2439_1, ch_2439_2, ch_2439_3, ch_2439_4, ch_2439_5, ch_2439_6])

theorem root_2440 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 2440) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_2440_0, decode 300 d_2440_1, decode 300 d_2440_2, decode 300 d_2440_3, decode 300 d_2440_4, decode 280 d_2440_5] (fun x hx => bits_full_and hx) cov_2440 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_2440_0, ch_2440_1, ch_2440_2, ch_2440_3, ch_2440_4, ch_2440_5])

theorem root_2441 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 2441) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_2441_0, decode 300 d_2441_1, decode 300 d_2441_2, decode 300 d_2441_3, decode 300 d_2441_4, decode 300 d_2441_5, decode 13 d_2441_6] (fun x hx => bits_full_and hx) cov_2441 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_2441_0, ch_2441_1, ch_2441_2, ch_2441_3, ch_2441_4, ch_2441_5, ch_2441_6])

theorem root_2442 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 2442) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_2442_0, decode 300 d_2442_1, decode 300 d_2442_2, decode 300 d_2442_3, decode 300 d_2442_4, decode 300 d_2442_5, decode 13 d_2442_6] (fun x hx => bits_full_and hx) cov_2442 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_2442_0, ch_2442_1, ch_2442_2, ch_2442_3, ch_2442_4, ch_2442_5, ch_2442_6])

theorem root_2444 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 2444) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_2444_0, decode 300 d_2444_1, decode 300 d_2444_2, decode 300 d_2444_3, decode 300 d_2444_4, decode 280 d_2444_5] (fun x hx => bits_full_and hx) cov_2444 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_2444_0, ch_2444_1, ch_2444_2, ch_2444_3, ch_2444_4, ch_2444_5])

theorem root_2450 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 2450) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_2450_0, decode 300 d_2450_1, decode 300 d_2450_2, decode 300 d_2450_3, decode 300 d_2450_4, decode 300 d_2450_5, decode 36 d_2450_6] (fun x hx => bits_full_and hx) cov_2450 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_2450_0, ch_2450_1, ch_2450_2, ch_2450_3, ch_2450_4, ch_2450_5, ch_2450_6])

theorem root_2451 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 2451) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_2451_0, decode 300 d_2451_1, decode 300 d_2451_2, decode 300 d_2451_3, decode 300 d_2451_4, decode 300 d_2451_5, decode 35 d_2451_6] (fun x hx => bits_full_and hx) cov_2451 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_2451_0, ch_2451_1, ch_2451_2, ch_2451_3, ch_2451_4, ch_2451_5, ch_2451_6])

theorem root_2455 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 2455) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_2455_0, decode 300 d_2455_1, decode 300 d_2455_2, decode 300 d_2455_3, decode 300 d_2455_4, decode 300 d_2455_5, decode 36 d_2455_6] (fun x hx => bits_full_and hx) cov_2455 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_2455_0, ch_2455_1, ch_2455_2, ch_2455_3, ch_2455_4, ch_2455_5, ch_2455_6])

theorem root_2456 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 2456) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_2456_0, decode 300 d_2456_1, decode 300 d_2456_2, decode 300 d_2456_3, decode 300 d_2456_4, decode 292 d_2456_5] (fun x hx => bits_full_and hx) cov_2456 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_2456_0, ch_2456_1, ch_2456_2, ch_2456_3, ch_2456_4, ch_2456_5])

theorem root_2457 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 2457) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_2457_0, decode 300 d_2457_1, decode 300 d_2457_2, decode 300 d_2457_3, decode 300 d_2457_4, decode 242 d_2457_5] (fun x hx => bits_full_and hx) cov_2457 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_2457_0, ch_2457_1, ch_2457_2, ch_2457_3, ch_2457_4, ch_2457_5])

theorem root_2463 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 2463) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_2463_0, decode 300 d_2463_1, decode 300 d_2463_2, decode 300 d_2463_3, decode 300 d_2463_4, decode 300 d_2463_5, decode 135 d_2463_6] (fun x hx => bits_full_and hx) cov_2463 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_2463_0, ch_2463_1, ch_2463_2, ch_2463_3, ch_2463_4, ch_2463_5, ch_2463_6])

theorem root_2464 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 2464) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_2464_0, decode 300 d_2464_1, decode 300 d_2464_2, decode 300 d_2464_3, decode 300 d_2464_4, decode 300 d_2464_5, decode 135 d_2464_6] (fun x hx => bits_full_and hx) cov_2464 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_2464_0, ch_2464_1, ch_2464_2, ch_2464_3, ch_2464_4, ch_2464_5, ch_2464_6])

theorem root_2465 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 2465) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_2465_0, decode 300 d_2465_1, decode 300 d_2465_2, decode 300 d_2465_3, decode 300 d_2465_4, decode 300 d_2465_5, decode 23 d_2465_6] (fun x hx => bits_full_and hx) cov_2465 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_2465_0, ch_2465_1, ch_2465_2, ch_2465_3, ch_2465_4, ch_2465_5, ch_2465_6])

theorem roots_36_ok (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    ∀ k ∈ roots_36, Claim (FULL &&& MT k) 3 := by
  intro k hk
  simp only [roots_36, List.mem_cons, List.mem_nil_iff, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [root_2418 hB hC hCl hCB, root_2425 hB hC hCl hCB, root_2426 hB hC hCl hCB, root_2427 hB hC hCl hCB, root_2428 hB hC hCl hCB, root_2430 hB hC hCl hCB, root_2431 hB hC hCl hCB, root_2432 hB hC hCl hCB, root_2439 hB hC hCl hCB, root_2440 hB hC hCl hCB, root_2441 hB hC hCl hCB, root_2442 hB hC hCl hCB, root_2444 hB hC hCl hCB, root_2450 hB hC hCl hCB, root_2451 hB hC hCl hCB, root_2455 hB hC hCl hCB, root_2456 hB hC hCl hCB, root_2457 hB hC hCl hCB, root_2463 hB hC hCl hCB, root_2464 hB hC hCl hCB, root_2465 hB hC hCl hCB]

theorem root_2470 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 2470) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_2470_0, decode 300 d_2470_1, decode 300 d_2470_2, decode 300 d_2470_3, decode 300 d_2470_4, decode 242 d_2470_5] (fun x hx => bits_full_and hx) cov_2470 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_2470_0, ch_2470_1, ch_2470_2, ch_2470_3, ch_2470_4, ch_2470_5])

theorem root_2477 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 2477) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_2477_0, decode 300 d_2477_1, decode 300 d_2477_2, decode 300 d_2477_3, decode 300 d_2477_4, decode 300 d_2477_5, decode 250 d_2477_6] (fun x hx => bits_full_and hx) cov_2477 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_2477_0, ch_2477_1, ch_2477_2, ch_2477_3, ch_2477_4, ch_2477_5, ch_2477_6])

theorem root_2478 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 2478) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_2478_0, decode 300 d_2478_1, decode 300 d_2478_2, decode 300 d_2478_3, decode 300 d_2478_4, decode 300 d_2478_5, decode 250 d_2478_6] (fun x hx => bits_full_and hx) cov_2478 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_2478_0, ch_2478_1, ch_2478_2, ch_2478_3, ch_2478_4, ch_2478_5, ch_2478_6])

theorem root_2479 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 2479) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_2479_0, decode 300 d_2479_1, decode 300 d_2479_2, decode 300 d_2479_3, decode 300 d_2479_4, decode 300 d_2479_5, decode 39 d_2479_6] (fun x hx => bits_full_and hx) cov_2479 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_2479_0, ch_2479_1, ch_2479_2, ch_2479_3, ch_2479_4, ch_2479_5, ch_2479_6])

theorem root_2480 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 2480) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_2480_0, decode 300 d_2480_1, decode 300 d_2480_2, decode 300 d_2480_3, decode 300 d_2480_4, decode 300 d_2480_5, decode 39 d_2480_6] (fun x hx => bits_full_and hx) cov_2480 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_2480_0, ch_2480_1, ch_2480_2, ch_2480_3, ch_2480_4, ch_2480_5, ch_2480_6])

theorem root_2488 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 2488) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_2488_0, decode 300 d_2488_1, decode 300 d_2488_2, decode 300 d_2488_3, decode 300 d_2488_4, decode 300 d_2488_5, decode 250 d_2488_6] (fun x hx => bits_full_and hx) cov_2488 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_2488_0, ch_2488_1, ch_2488_2, ch_2488_3, ch_2488_4, ch_2488_5, ch_2488_6])

theorem root_2489 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 2489) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_2489_0, decode 300 d_2489_1, decode 300 d_2489_2, decode 300 d_2489_3, decode 300 d_2489_4, decode 300 d_2489_5, decode 250 d_2489_6] (fun x hx => bits_full_and hx) cov_2489 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_2489_0, ch_2489_1, ch_2489_2, ch_2489_3, ch_2489_4, ch_2489_5, ch_2489_6])

theorem root_2490 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 2490) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_2490_0, decode 300 d_2490_1, decode 300 d_2490_2, decode 300 d_2490_3, decode 300 d_2490_4, decode 300 d_2490_5, decode 108 d_2490_6] (fun x hx => bits_full_and hx) cov_2490 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_2490_0, ch_2490_1, ch_2490_2, ch_2490_3, ch_2490_4, ch_2490_5, ch_2490_6])

theorem root_2491 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 2491) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_2491_0, decode 300 d_2491_1, decode 300 d_2491_2, decode 300 d_2491_3, decode 300 d_2491_4, decode 300 d_2491_5, decode 108 d_2491_6] (fun x hx => bits_full_and hx) cov_2491 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_2491_0, ch_2491_1, ch_2491_2, ch_2491_3, ch_2491_4, ch_2491_5, ch_2491_6])

theorem root_2497 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 2497) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_2497_0, decode 300 d_2497_1, decode 300 d_2497_2, decode 300 d_2497_3, decode 300 d_2497_4, decode 300 d_2497_5, decode 250 d_2497_6] (fun x hx => bits_full_and hx) cov_2497 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_2497_0, ch_2497_1, ch_2497_2, ch_2497_3, ch_2497_4, ch_2497_5, ch_2497_6])

theorem root_2498 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 2498) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_2498_0, decode 300 d_2498_1, decode 300 d_2498_2, decode 300 d_2498_3, decode 300 d_2498_4, decode 300 d_2498_5, decode 250 d_2498_6] (fun x hx => bits_full_and hx) cov_2498 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_2498_0, ch_2498_1, ch_2498_2, ch_2498_3, ch_2498_4, ch_2498_5, ch_2498_6])

theorem root_2499 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 2499) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_2499_0, decode 300 d_2499_1, decode 300 d_2499_2, decode 300 d_2499_3, decode 300 d_2499_4, decode 300 d_2499_5, decode 250 d_2499_6] (fun x hx => bits_full_and hx) cov_2499 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_2499_0, ch_2499_1, ch_2499_2, ch_2499_3, ch_2499_4, ch_2499_5, ch_2499_6])

theorem root_2500 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 2500) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_2500_0, decode 300 d_2500_1, decode 300 d_2500_2, decode 300 d_2500_3, decode 300 d_2500_4, decode 300 d_2500_5, decode 108 d_2500_6] (fun x hx => bits_full_and hx) cov_2500 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_2500_0, ch_2500_1, ch_2500_2, ch_2500_3, ch_2500_4, ch_2500_5, ch_2500_6])

theorem root_2507 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 2507) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_2507_0, decode 300 d_2507_1, decode 300 d_2507_2, decode 300 d_2507_3, decode 300 d_2507_4, decode 300 d_2507_5, decode 250 d_2507_6] (fun x hx => bits_full_and hx) cov_2507 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_2507_0, ch_2507_1, ch_2507_2, ch_2507_3, ch_2507_4, ch_2507_5, ch_2507_6])

theorem root_2508 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 2508) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_2508_0, decode 300 d_2508_1, decode 300 d_2508_2, decode 300 d_2508_3, decode 300 d_2508_4, decode 300 d_2508_5, decode 182 d_2508_6] (fun x hx => bits_full_and hx) cov_2508 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_2508_0, ch_2508_1, ch_2508_2, ch_2508_3, ch_2508_4, ch_2508_5, ch_2508_6])

theorem root_2515 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 2515) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_2515_0, decode 300 d_2515_1, decode 300 d_2515_2, decode 300 d_2515_3, decode 300 d_2515_4, decode 300 d_2515_5, decode 300 d_2515_6, decode 141 d_2515_7] (fun x hx => bits_full_and hx) cov_2515 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_2515_0, ch_2515_1, ch_2515_2, ch_2515_3, ch_2515_4, ch_2515_5, ch_2515_6, ch_2515_7])

theorem root_2516 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 2516) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_2516_0, decode 300 d_2516_1, decode 300 d_2516_2, decode 300 d_2516_3, decode 300 d_2516_4, decode 300 d_2516_5, decode 300 d_2516_6, decode 141 d_2516_7] (fun x hx => bits_full_and hx) cov_2516 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_2516_0, ch_2516_1, ch_2516_2, ch_2516_3, ch_2516_4, ch_2516_5, ch_2516_6, ch_2516_7])

theorem root_2522 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 2522) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_2522_0, decode 300 d_2522_1, decode 300 d_2522_2, decode 300 d_2522_3, decode 300 d_2522_4, decode 300 d_2522_5, decode 300 d_2522_6, decode 141 d_2522_7] (fun x hx => bits_full_and hx) cov_2522 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_2522_0, ch_2522_1, ch_2522_2, ch_2522_3, ch_2522_4, ch_2522_5, ch_2522_6, ch_2522_7])

theorem root_2526 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 2526) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_2526_0, decode 300 d_2526_1, decode 300 d_2526_2, decode 300 d_2526_3, decode 300 d_2526_4, decode 300 d_2526_5, decode 300 d_2526_6, decode 158 d_2526_7] (fun x hx => bits_full_and hx) cov_2526 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_2526_0, ch_2526_1, ch_2526_2, ch_2526_3, ch_2526_4, ch_2526_5, ch_2526_6, ch_2526_7])

theorem root_2532 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 2532) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_2532_0, decode 300 d_2532_1, decode 300 d_2532_2, decode 300 d_2532_3, decode 300 d_2532_4, decode 300 d_2532_5, decode 300 d_2532_6, decode 141 d_2532_7] (fun x hx => bits_full_and hx) cov_2532 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_2532_0, ch_2532_1, ch_2532_2, ch_2532_3, ch_2532_4, ch_2532_5, ch_2532_6, ch_2532_7])

theorem roots_37_ok (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    ∀ k ∈ roots_37, Claim (FULL &&& MT k) 3 := by
  intro k hk
  simp only [roots_37, List.mem_cons, List.mem_nil_iff, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [root_2470 hB hC hCl hCB, root_2477 hB hC hCl hCB, root_2478 hB hC hCl hCB, root_2479 hB hC hCl hCB, root_2480 hB hC hCl hCB, root_2488 hB hC hCl hCB, root_2489 hB hC hCl hCB, root_2490 hB hC hCl hCB, root_2491 hB hC hCl hCB, root_2497 hB hC hCl hCB, root_2498 hB hC hCl hCB, root_2499 hB hC hCl hCB, root_2500 hB hC hCl hCB, root_2507 hB hC hCl hCB, root_2508 hB hC hCl hCB, root_2515 hB hC hCl hCB, root_2516 hB hC hCl hCB, root_2522 hB hC hCl hCB, root_2526 hB hC hCl hCB, root_2532 hB hC hCl hCB]

theorem root_2534 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 2534) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_2534_0, decode 300 d_2534_1, decode 300 d_2534_2, decode 300 d_2534_3, decode 300 d_2534_4, decode 300 d_2534_5, decode 300 d_2534_6, decode 158 d_2534_7] (fun x hx => bits_full_and hx) cov_2534 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_2534_0, ch_2534_1, ch_2534_2, ch_2534_3, ch_2534_4, ch_2534_5, ch_2534_6, ch_2534_7])

theorem root_2535 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 2535) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_2535_0, decode 300 d_2535_1, decode 300 d_2535_2, decode 300 d_2535_3, decode 300 d_2535_4, decode 300 d_2535_5, decode 300 d_2535_6, decode 158 d_2535_7] (fun x hx => bits_full_and hx) cov_2535 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_2535_0, ch_2535_1, ch_2535_2, ch_2535_3, ch_2535_4, ch_2535_5, ch_2535_6, ch_2535_7])

theorem root_2545 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 2545) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_2545_0, decode 300 d_2545_1, decode 300 d_2545_2, decode 300 d_2545_3, decode 300 d_2545_4, decode 300 d_2545_5, decode 300 d_2545_6, decode 141 d_2545_7] (fun x hx => bits_full_and hx) cov_2545 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_2545_0, ch_2545_1, ch_2545_2, ch_2545_3, ch_2545_4, ch_2545_5, ch_2545_6, ch_2545_7])

theorem root_2546 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 2546) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_2546_0, decode 300 d_2546_1, decode 300 d_2546_2, decode 300 d_2546_3, decode 300 d_2546_4, decode 300 d_2546_5, decode 300 d_2546_6, decode 141 d_2546_7] (fun x hx => bits_full_and hx) cov_2546 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_2546_0, ch_2546_1, ch_2546_2, ch_2546_3, ch_2546_4, ch_2546_5, ch_2546_6, ch_2546_7])

theorem root_2547 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 2547) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_2547_0, decode 300 d_2547_1, decode 300 d_2547_2, decode 300 d_2547_3, decode 300 d_2547_4, decode 300 d_2547_5, decode 300 d_2547_6, decode 141 d_2547_7] (fun x hx => bits_full_and hx) cov_2547 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_2547_0, ch_2547_1, ch_2547_2, ch_2547_3, ch_2547_4, ch_2547_5, ch_2547_6, ch_2547_7])

theorem root_2548 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 2548) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_2548_0, decode 300 d_2548_1, decode 300 d_2548_2, decode 300 d_2548_3, decode 300 d_2548_4, decode 300 d_2548_5, decode 300 d_2548_6, decode 141 d_2548_7] (fun x hx => bits_full_and hx) cov_2548 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_2548_0, ch_2548_1, ch_2548_2, ch_2548_3, ch_2548_4, ch_2548_5, ch_2548_6, ch_2548_7])

theorem root_2549 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 2549) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_2549_0, decode 300 d_2549_1, decode 300 d_2549_2, decode 300 d_2549_3, decode 300 d_2549_4, decode 300 d_2549_5, decode 300 d_2549_6, decode 141 d_2549_7] (fun x hx => bits_full_and hx) cov_2549 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_2549_0, ch_2549_1, ch_2549_2, ch_2549_3, ch_2549_4, ch_2549_5, ch_2549_6, ch_2549_7])

theorem root_2551 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 2551) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_2551_0, decode 300 d_2551_1, decode 300 d_2551_2, decode 300 d_2551_3, decode 300 d_2551_4, decode 300 d_2551_5, decode 300 d_2551_6, decode 158 d_2551_7] (fun x hx => bits_full_and hx) cov_2551 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_2551_0, ch_2551_1, ch_2551_2, ch_2551_3, ch_2551_4, ch_2551_5, ch_2551_6, ch_2551_7])

theorem root_2552 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 2552) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_2552_0, decode 300 d_2552_1, decode 300 d_2552_2, decode 300 d_2552_3, decode 300 d_2552_4, decode 300 d_2552_5, decode 300 d_2552_6, decode 158 d_2552_7] (fun x hx => bits_full_and hx) cov_2552 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_2552_0, ch_2552_1, ch_2552_2, ch_2552_3, ch_2552_4, ch_2552_5, ch_2552_6, ch_2552_7])

theorem root_2559 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 2559) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_2559_0, decode 300 d_2559_1, decode 300 d_2559_2, decode 300 d_2559_3, decode 300 d_2559_4, decode 300 d_2559_5, decode 300 d_2559_6, decode 142 d_2559_7] (fun x hx => bits_full_and hx) cov_2559 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_2559_0, ch_2559_1, ch_2559_2, ch_2559_3, ch_2559_4, ch_2559_5, ch_2559_6, ch_2559_7])

theorem root_2560 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 2560) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_2560_0, decode 300 d_2560_1, decode 300 d_2560_2, decode 300 d_2560_3, decode 300 d_2560_4, decode 300 d_2560_5, decode 300 d_2560_6, decode 142 d_2560_7] (fun x hx => bits_full_and hx) cov_2560 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_2560_0, ch_2560_1, ch_2560_2, ch_2560_3, ch_2560_4, ch_2560_5, ch_2560_6, ch_2560_7])

theorem root_2561 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 2561) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_2561_0, decode 300 d_2561_1, decode 300 d_2561_2, decode 300 d_2561_3, decode 300 d_2561_4, decode 300 d_2561_5, decode 300 d_2561_6, decode 142 d_2561_7] (fun x hx => bits_full_and hx) cov_2561 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_2561_0, ch_2561_1, ch_2561_2, ch_2561_3, ch_2561_4, ch_2561_5, ch_2561_6, ch_2561_7])

theorem root_2562 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 2562) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_2562_0, decode 300 d_2562_1, decode 300 d_2562_2, decode 300 d_2562_3, decode 300 d_2562_4, decode 300 d_2562_5, decode 300 d_2562_6, decode 141 d_2562_7] (fun x hx => bits_full_and hx) cov_2562 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_2562_0, ch_2562_1, ch_2562_2, ch_2562_3, ch_2562_4, ch_2562_5, ch_2562_6, ch_2562_7])

theorem root_2563 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 2563) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_2563_0, decode 300 d_2563_1, decode 300 d_2563_2, decode 300 d_2563_3, decode 300 d_2563_4, decode 300 d_2563_5, decode 300 d_2563_6, decode 141 d_2563_7] (fun x hx => bits_full_and hx) cov_2563 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_2563_0, ch_2563_1, ch_2563_2, ch_2563_3, ch_2563_4, ch_2563_5, ch_2563_6, ch_2563_7])

theorem root_2570 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 2570) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_2570_0, decode 300 d_2570_1, decode 300 d_2570_2, decode 300 d_2570_3, decode 300 d_2570_4, decode 300 d_2570_5, decode 300 d_2570_6, decode 142 d_2570_7] (fun x hx => bits_full_and hx) cov_2570 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_2570_0, ch_2570_1, ch_2570_2, ch_2570_3, ch_2570_4, ch_2570_5, ch_2570_6, ch_2570_7])

theorem root_2571 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 2571) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_2571_0, decode 300 d_2571_1, decode 300 d_2571_2, decode 300 d_2571_3, decode 300 d_2571_4, decode 300 d_2571_5, decode 300 d_2571_6, decode 141 d_2571_7] (fun x hx => bits_full_and hx) cov_2571 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_2571_0, ch_2571_1, ch_2571_2, ch_2571_3, ch_2571_4, ch_2571_5, ch_2571_6, ch_2571_7])

theorem root_2572 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 2572) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_2572_0, decode 300 d_2572_1, decode 300 d_2572_2, decode 300 d_2572_3, decode 300 d_2572_4, decode 300 d_2572_5, decode 300 d_2572_6, decode 141 d_2572_7] (fun x hx => bits_full_and hx) cov_2572 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_2572_0, ch_2572_1, ch_2572_2, ch_2572_3, ch_2572_4, ch_2572_5, ch_2572_6, ch_2572_7])

theorem root_2573 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 2573) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_2573_0, decode 300 d_2573_1, decode 300 d_2573_2, decode 300 d_2573_3, decode 300 d_2573_4, decode 300 d_2573_5, decode 300 d_2573_6, decode 141 d_2573_7] (fun x hx => bits_full_and hx) cov_2573 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_2573_0, ch_2573_1, ch_2573_2, ch_2573_3, ch_2573_4, ch_2573_5, ch_2573_6, ch_2573_7])

theorem roots_38_ok (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    ∀ k ∈ roots_38, Claim (FULL &&& MT k) 3 := by
  intro k hk
  simp only [roots_38, List.mem_cons, List.mem_nil_iff, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [root_2534 hB hC hCl hCB, root_2535 hB hC hCl hCB, root_2545 hB hC hCl hCB, root_2546 hB hC hCl hCB, root_2547 hB hC hCl hCB, root_2548 hB hC hCl hCB, root_2549 hB hC hCl hCB, root_2551 hB hC hCl hCB, root_2552 hB hC hCl hCB, root_2559 hB hC hCl hCB, root_2560 hB hC hCl hCB, root_2561 hB hC hCl hCB, root_2562 hB hC hCl hCB, root_2563 hB hC hCl hCB, root_2570 hB hC hCl hCB, root_2571 hB hC hCl hCB, root_2572 hB hC hCl hCB, root_2573 hB hC hCl hCB]

theorem root_2583 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 2583) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_2583_0, decode 300 d_2583_1, decode 300 d_2583_2, decode 300 d_2583_3, decode 300 d_2583_4, decode 300 d_2583_5, decode 300 d_2583_6, decode 141 d_2583_7] (fun x hx => bits_full_and hx) cov_2583 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_2583_0, ch_2583_1, ch_2583_2, ch_2583_3, ch_2583_4, ch_2583_5, ch_2583_6, ch_2583_7])

theorem root_2594 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 2594) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_2594_0, decode 300 d_2594_1, decode 300 d_2594_2, decode 300 d_2594_3, decode 300 d_2594_4, decode 300 d_2594_5, decode 300 d_2594_6, decode 141 d_2594_7] (fun x hx => bits_full_and hx) cov_2594 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_2594_0, ch_2594_1, ch_2594_2, ch_2594_3, ch_2594_4, ch_2594_5, ch_2594_6, ch_2594_7])

theorem root_2597 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 2597) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_2597_0, decode 300 d_2597_1, decode 300 d_2597_2, decode 300 d_2597_3, decode 300 d_2597_4, decode 300 d_2597_5, decode 300 d_2597_6, decode 141 d_2597_7] (fun x hx => bits_full_and hx) cov_2597 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_2597_0, ch_2597_1, ch_2597_2, ch_2597_3, ch_2597_4, ch_2597_5, ch_2597_6, ch_2597_7])

theorem root_2602 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 2602) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_2602_0, decode 300 d_2602_1, decode 300 d_2602_2, decode 300 d_2602_3, decode 300 d_2602_4, decode 300 d_2602_5, decode 300 d_2602_6, decode 141 d_2602_7] (fun x hx => bits_full_and hx) cov_2602 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_2602_0, ch_2602_1, ch_2602_2, ch_2602_3, ch_2602_4, ch_2602_5, ch_2602_6, ch_2602_7])

theorem root_2604 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 2604) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_2604_0, decode 300 d_2604_1, decode 300 d_2604_2, decode 300 d_2604_3, decode 300 d_2604_4, decode 300 d_2604_5, decode 300 d_2604_6, decode 141 d_2604_7] (fun x hx => bits_full_and hx) cov_2604 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_2604_0, ch_2604_1, ch_2604_2, ch_2604_3, ch_2604_4, ch_2604_5, ch_2604_6, ch_2604_7])

theorem root_2615 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 2615) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_2615_0, decode 300 d_2615_1, decode 300 d_2615_2, decode 300 d_2615_3, decode 300 d_2615_4, decode 300 d_2615_5, decode 300 d_2615_6, decode 141 d_2615_7] (fun x hx => bits_full_and hx) cov_2615 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_2615_0, ch_2615_1, ch_2615_2, ch_2615_3, ch_2615_4, ch_2615_5, ch_2615_6, ch_2615_7])

theorem root_2616 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 2616) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_2616_0, decode 300 d_2616_1, decode 300 d_2616_2, decode 300 d_2616_3, decode 300 d_2616_4, decode 300 d_2616_5, decode 300 d_2616_6, decode 141 d_2616_7] (fun x hx => bits_full_and hx) cov_2616 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_2616_0, ch_2616_1, ch_2616_2, ch_2616_3, ch_2616_4, ch_2616_5, ch_2616_6, ch_2616_7])

theorem root_2617 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 2617) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_2617_0, decode 300 d_2617_1, decode 300 d_2617_2, decode 300 d_2617_3, decode 300 d_2617_4, decode 300 d_2617_5, decode 300 d_2617_6, decode 141 d_2617_7] (fun x hx => bits_full_and hx) cov_2617 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_2617_0, ch_2617_1, ch_2617_2, ch_2617_3, ch_2617_4, ch_2617_5, ch_2617_6, ch_2617_7])

theorem root_2618 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 2618) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_2618_0, decode 300 d_2618_1, decode 300 d_2618_2, decode 300 d_2618_3, decode 300 d_2618_4, decode 300 d_2618_5, decode 300 d_2618_6, decode 141 d_2618_7] (fun x hx => bits_full_and hx) cov_2618 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_2618_0, ch_2618_1, ch_2618_2, ch_2618_3, ch_2618_4, ch_2618_5, ch_2618_6, ch_2618_7])

theorem root_2637 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 2637) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_2637_0, decode 300 d_2637_1, decode 300 d_2637_2, decode 300 d_2637_3, decode 300 d_2637_4, decode 300 d_2637_5, decode 300 d_2637_6, decode 141 d_2637_7] (fun x hx => bits_full_and hx) cov_2637 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_2637_0, ch_2637_1, ch_2637_2, ch_2637_3, ch_2637_4, ch_2637_5, ch_2637_6, ch_2637_7])

theorem root_2638 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 2638) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_2638_0, decode 300 d_2638_1, decode 300 d_2638_2, decode 300 d_2638_3, decode 300 d_2638_4, decode 300 d_2638_5, decode 300 d_2638_6, decode 142 d_2638_7] (fun x hx => bits_full_and hx) cov_2638 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_2638_0, ch_2638_1, ch_2638_2, ch_2638_3, ch_2638_4, ch_2638_5, ch_2638_6, ch_2638_7])

theorem root_2639 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 2639) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_2639_0, decode 300 d_2639_1, decode 300 d_2639_2, decode 300 d_2639_3, decode 300 d_2639_4, decode 300 d_2639_5, decode 300 d_2639_6, decode 141 d_2639_7] (fun x hx => bits_full_and hx) cov_2639 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_2639_0, ch_2639_1, ch_2639_2, ch_2639_3, ch_2639_4, ch_2639_5, ch_2639_6, ch_2639_7])

theorem root_2645 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 2645) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_2645_0, decode 300 d_2645_1, decode 300 d_2645_2, decode 300 d_2645_3, decode 300 d_2645_4, decode 300 d_2645_5, decode 300 d_2645_6, decode 141 d_2645_7] (fun x hx => bits_full_and hx) cov_2645 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_2645_0, ch_2645_1, ch_2645_2, ch_2645_3, ch_2645_4, ch_2645_5, ch_2645_6, ch_2645_7])

theorem root_2646 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 2646) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_2646_0, decode 300 d_2646_1, decode 300 d_2646_2, decode 300 d_2646_3, decode 300 d_2646_4, decode 300 d_2646_5, decode 300 d_2646_6, decode 141 d_2646_7] (fun x hx => bits_full_and hx) cov_2646 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_2646_0, ch_2646_1, ch_2646_2, ch_2646_3, ch_2646_4, ch_2646_5, ch_2646_6, ch_2646_7])

theorem root_2649 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 2649) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_2649_0, decode 300 d_2649_1, decode 300 d_2649_2, decode 300 d_2649_3, decode 300 d_2649_4, decode 300 d_2649_5, decode 300 d_2649_6, decode 142 d_2649_7] (fun x hx => bits_full_and hx) cov_2649 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_2649_0, ch_2649_1, ch_2649_2, ch_2649_3, ch_2649_4, ch_2649_5, ch_2649_6, ch_2649_7])

theorem root_2650 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 2650) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_2650_0, decode 300 d_2650_1, decode 300 d_2650_2, decode 300 d_2650_3, decode 300 d_2650_4, decode 300 d_2650_5, decode 300 d_2650_6, decode 142 d_2650_7] (fun x hx => bits_full_and hx) cov_2650 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_2650_0, ch_2650_1, ch_2650_2, ch_2650_3, ch_2650_4, ch_2650_5, ch_2650_6, ch_2650_7])

theorem root_2653 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 2653) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_2653_0, decode 300 d_2653_1, decode 300 d_2653_2, decode 300 d_2653_3, decode 300 d_2653_4, decode 300 d_2653_5, decode 300 d_2653_6, decode 141 d_2653_7] (fun x hx => bits_full_and hx) cov_2653 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_2653_0, ch_2653_1, ch_2653_2, ch_2653_3, ch_2653_4, ch_2653_5, ch_2653_6, ch_2653_7])

theorem root_2654 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 2654) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_2654_0, decode 300 d_2654_1, decode 300 d_2654_2, decode 300 d_2654_3, decode 300 d_2654_4, decode 300 d_2654_5, decode 300 d_2654_6, decode 141 d_2654_7] (fun x hx => bits_full_and hx) cov_2654 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_2654_0, ch_2654_1, ch_2654_2, ch_2654_3, ch_2654_4, ch_2654_5, ch_2654_6, ch_2654_7])

theorem roots_39_ok (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    ∀ k ∈ roots_39, Claim (FULL &&& MT k) 3 := by
  intro k hk
  simp only [roots_39, List.mem_cons, List.mem_nil_iff, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [root_2583 hB hC hCl hCB, root_2594 hB hC hCl hCB, root_2597 hB hC hCl hCB, root_2602 hB hC hCl hCB, root_2604 hB hC hCl hCB, root_2615 hB hC hCl hCB, root_2616 hB hC hCl hCB, root_2617 hB hC hCl hCB, root_2618 hB hC hCl hCB, root_2637 hB hC hCl hCB, root_2638 hB hC hCl hCB, root_2639 hB hC hCl hCB, root_2645 hB hC hCl hCB, root_2646 hB hC hCl hCB, root_2649 hB hC hCl hCB, root_2650 hB hC hCl hCB, root_2653 hB hC hCl hCB, root_2654 hB hC hCl hCB]

end LRC.O7U5
