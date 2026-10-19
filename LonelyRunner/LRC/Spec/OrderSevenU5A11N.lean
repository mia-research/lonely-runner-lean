import LonelyRunner.LRC.Spec.OrderSevenU5SoundN
import LonelyRunner.LRC.Spec.OrderSevenU5C110N
import LonelyRunner.LRC.Spec.OrderSevenU5C111N
import LonelyRunner.LRC.Spec.OrderSevenU5C112N
import LonelyRunner.LRC.Spec.OrderSevenU5C113N
import LonelyRunner.LRC.Spec.OrderSevenU5C114N
import LonelyRunner.LRC.Spec.OrderSevenU5C115N
import LonelyRunner.LRC.Spec.OrderSevenU5C116N
import LonelyRunner.LRC.Spec.OrderSevenU5C117N
import LonelyRunner.LRC.Spec.OrderSevenU5C118N
import LonelyRunner.LRC.Spec.OrderSevenU5C119N

set_option maxRecDepth 100000

namespace LRC.O7U5

theorem root_7334 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7334) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7334_0, decode 300 d_7334_1, decode 300 d_7334_2, decode 300 d_7334_3, decode 300 d_7334_4, decode 300 d_7334_5, decode 300 d_7334_6, decode 142 d_7334_7] (fun x hx => bits_full_and hx) cov_7334 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7334_0, ch_7334_1, ch_7334_2, ch_7334_3, ch_7334_4, ch_7334_5, ch_7334_6, ch_7334_7])

theorem root_7335 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7335) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7335_0, decode 300 d_7335_1, decode 300 d_7335_2, decode 300 d_7335_3, decode 300 d_7335_4, decode 300 d_7335_5, decode 300 d_7335_6, decode 141 d_7335_7] (fun x hx => bits_full_and hx) cov_7335 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7335_0, ch_7335_1, ch_7335_2, ch_7335_3, ch_7335_4, ch_7335_5, ch_7335_6, ch_7335_7])

theorem root_7340 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7340) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7340_0, decode 300 d_7340_1, decode 300 d_7340_2, decode 300 d_7340_3, decode 300 d_7340_4, decode 300 d_7340_5, decode 300 d_7340_6, decode 142 d_7340_7] (fun x hx => bits_full_and hx) cov_7340 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7340_0, ch_7340_1, ch_7340_2, ch_7340_3, ch_7340_4, ch_7340_5, ch_7340_6, ch_7340_7])

theorem root_7341 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7341) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7341_0, decode 300 d_7341_1, decode 300 d_7341_2, decode 300 d_7341_3, decode 300 d_7341_4, decode 300 d_7341_5, decode 300 d_7341_6, decode 142 d_7341_7] (fun x hx => bits_full_and hx) cov_7341 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7341_0, ch_7341_1, ch_7341_2, ch_7341_3, ch_7341_4, ch_7341_5, ch_7341_6, ch_7341_7])

theorem root_7342 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7342) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7342_0, decode 300 d_7342_1, decode 300 d_7342_2, decode 300 d_7342_3, decode 300 d_7342_4, decode 300 d_7342_5, decode 300 d_7342_6, decode 141 d_7342_7] (fun x hx => bits_full_and hx) cov_7342 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7342_0, ch_7342_1, ch_7342_2, ch_7342_3, ch_7342_4, ch_7342_5, ch_7342_6, ch_7342_7])

theorem root_7350 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7350) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7350_0, decode 300 d_7350_1, decode 300 d_7350_2, decode 300 d_7350_3, decode 300 d_7350_4, decode 266 d_7350_5] (fun x hx => bits_full_and hx) cov_7350 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7350_0, ch_7350_1, ch_7350_2, ch_7350_3, ch_7350_4, ch_7350_5])

theorem root_7354 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7354) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7354_0, decode 300 d_7354_1, decode 300 d_7354_2, decode 300 d_7354_3, decode 300 d_7354_4, decode 300 d_7354_5, decode 300 d_7354_6, decode 141 d_7354_7] (fun x hx => bits_full_and hx) cov_7354 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7354_0, ch_7354_1, ch_7354_2, ch_7354_3, ch_7354_4, ch_7354_5, ch_7354_6, ch_7354_7])

theorem root_7356 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7356) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7356_0, decode 300 d_7356_1, decode 300 d_7356_2, decode 300 d_7356_3, decode 300 d_7356_4, decode 300 d_7356_5, decode 300 d_7356_6, decode 142 d_7356_7] (fun x hx => bits_full_and hx) cov_7356 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7356_0, ch_7356_1, ch_7356_2, ch_7356_3, ch_7356_4, ch_7356_5, ch_7356_6, ch_7356_7])

theorem root_7357 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7357) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7357_0, decode 300 d_7357_1, decode 300 d_7357_2, decode 300 d_7357_3, decode 300 d_7357_4, decode 300 d_7357_5, decode 300 d_7357_6, decode 142 d_7357_7] (fun x hx => bits_full_and hx) cov_7357 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7357_0, ch_7357_1, ch_7357_2, ch_7357_3, ch_7357_4, ch_7357_5, ch_7357_6, ch_7357_7])

theorem root_7361 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7361) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7361_0, decode 300 d_7361_1, decode 300 d_7361_2, decode 300 d_7361_3, decode 300 d_7361_4, decode 300 d_7361_5, decode 300 d_7361_6, decode 142 d_7361_7] (fun x hx => bits_full_and hx) cov_7361 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7361_0, ch_7361_1, ch_7361_2, ch_7361_3, ch_7361_4, ch_7361_5, ch_7361_6, ch_7361_7])

theorem root_7362 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7362) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7362_0, decode 300 d_7362_1, decode 300 d_7362_2, decode 300 d_7362_3, decode 300 d_7362_4, decode 300 d_7362_5, decode 300 d_7362_6, decode 142 d_7362_7] (fun x hx => bits_full_and hx) cov_7362 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7362_0, ch_7362_1, ch_7362_2, ch_7362_3, ch_7362_4, ch_7362_5, ch_7362_6, ch_7362_7])

theorem root_7369 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7369) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7369_0, decode 300 d_7369_1, decode 300 d_7369_2, decode 300 d_7369_3, decode 300 d_7369_4, decode 300 d_7369_5, decode 300 d_7369_6, decode 141 d_7369_7] (fun x hx => bits_full_and hx) cov_7369 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7369_0, ch_7369_1, ch_7369_2, ch_7369_3, ch_7369_4, ch_7369_5, ch_7369_6, ch_7369_7])

theorem root_7370 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7370) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7370_0, decode 300 d_7370_1, decode 300 d_7370_2, decode 300 d_7370_3, decode 300 d_7370_4, decode 300 d_7370_5, decode 300 d_7370_6, decode 141 d_7370_7] (fun x hx => bits_full_and hx) cov_7370 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7370_0, ch_7370_1, ch_7370_2, ch_7370_3, ch_7370_4, ch_7370_5, ch_7370_6, ch_7370_7])

theorem root_7371 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7371) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7371_0, decode 300 d_7371_1, decode 300 d_7371_2, decode 300 d_7371_3, decode 300 d_7371_4, decode 300 d_7371_5, decode 300 d_7371_6, decode 141 d_7371_7] (fun x hx => bits_full_and hx) cov_7371 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7371_0, ch_7371_1, ch_7371_2, ch_7371_3, ch_7371_4, ch_7371_5, ch_7371_6, ch_7371_7])

theorem root_7380 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7380) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7380_0, decode 300 d_7380_1, decode 300 d_7380_2, decode 300 d_7380_3, decode 300 d_7380_4, decode 300 d_7380_5, decode 300 d_7380_6, decode 141 d_7380_7] (fun x hx => bits_full_and hx) cov_7380 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7380_0, ch_7380_1, ch_7380_2, ch_7380_3, ch_7380_4, ch_7380_5, ch_7380_6, ch_7380_7])

theorem root_7381 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7381) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7381_0, decode 300 d_7381_1, decode 300 d_7381_2, decode 300 d_7381_3, decode 300 d_7381_4, decode 300 d_7381_5, decode 300 d_7381_6, decode 141 d_7381_7] (fun x hx => bits_full_and hx) cov_7381 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7381_0, ch_7381_1, ch_7381_2, ch_7381_3, ch_7381_4, ch_7381_5, ch_7381_6, ch_7381_7])

theorem root_7382 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7382) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7382_0, decode 300 d_7382_1, decode 300 d_7382_2, decode 300 d_7382_3, decode 300 d_7382_4, decode 300 d_7382_5, decode 300 d_7382_6, decode 158 d_7382_7] (fun x hx => bits_full_and hx) cov_7382 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7382_0, ch_7382_1, ch_7382_2, ch_7382_3, ch_7382_4, ch_7382_5, ch_7382_6, ch_7382_7])

theorem root_7383 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7383) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7383_0, decode 300 d_7383_1, decode 300 d_7383_2, decode 300 d_7383_3, decode 300 d_7383_4, decode 300 d_7383_5, decode 300 d_7383_6, decode 141 d_7383_7] (fun x hx => bits_full_and hx) cov_7383 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7383_0, ch_7383_1, ch_7383_2, ch_7383_3, ch_7383_4, ch_7383_5, ch_7383_6, ch_7383_7])

theorem root_7395 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7395) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7395_0, decode 300 d_7395_1, decode 300 d_7395_2, decode 300 d_7395_3, decode 300 d_7395_4, decode 300 d_7395_5, decode 300 d_7395_6, decode 141 d_7395_7] (fun x hx => bits_full_and hx) cov_7395 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7395_0, ch_7395_1, ch_7395_2, ch_7395_3, ch_7395_4, ch_7395_5, ch_7395_6, ch_7395_7])

theorem roots_110_ok (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    ∀ k ∈ roots_110, Claim (FULL &&& MT k) 3 := by
  intro k hk
  simp only [roots_110, List.mem_cons, List.mem_nil_iff, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [root_7334 hB hC hCl hCB, root_7335 hB hC hCl hCB, root_7340 hB hC hCl hCB, root_7341 hB hC hCl hCB, root_7342 hB hC hCl hCB, root_7350 hB hC hCl hCB, root_7354 hB hC hCl hCB, root_7356 hB hC hCl hCB, root_7357 hB hC hCl hCB, root_7361 hB hC hCl hCB, root_7362 hB hC hCl hCB, root_7369 hB hC hCl hCB, root_7370 hB hC hCl hCB, root_7371 hB hC hCl hCB, root_7380 hB hC hCl hCB, root_7381 hB hC hCl hCB, root_7382 hB hC hCl hCB, root_7383 hB hC hCl hCB, root_7395 hB hC hCl hCB]

theorem root_7397 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7397) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7397_0, decode 300 d_7397_1, decode 300 d_7397_2, decode 300 d_7397_3, decode 300 d_7397_4, decode 300 d_7397_5, decode 300 d_7397_6, decode 142 d_7397_7] (fun x hx => bits_full_and hx) cov_7397 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7397_0, ch_7397_1, ch_7397_2, ch_7397_3, ch_7397_4, ch_7397_5, ch_7397_6, ch_7397_7])

theorem root_7398 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7398) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7398_0, decode 300 d_7398_1, decode 300 d_7398_2, decode 300 d_7398_3, decode 300 d_7398_4, decode 300 d_7398_5, decode 300 d_7398_6, decode 142 d_7398_7] (fun x hx => bits_full_and hx) cov_7398 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7398_0, ch_7398_1, ch_7398_2, ch_7398_3, ch_7398_4, ch_7398_5, ch_7398_6, ch_7398_7])

theorem root_7399 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7399) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7399_0, decode 300 d_7399_1, decode 300 d_7399_2, decode 300 d_7399_3, decode 300 d_7399_4, decode 300 d_7399_5, decode 300 d_7399_6, decode 141 d_7399_7] (fun x hx => bits_full_and hx) cov_7399 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7399_0, ch_7399_1, ch_7399_2, ch_7399_3, ch_7399_4, ch_7399_5, ch_7399_6, ch_7399_7])

theorem root_7400 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7400) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7400_0, decode 300 d_7400_1, decode 300 d_7400_2, decode 300 d_7400_3, decode 300 d_7400_4, decode 300 d_7400_5, decode 300 d_7400_6, decode 158 d_7400_7] (fun x hx => bits_full_and hx) cov_7400 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7400_0, ch_7400_1, ch_7400_2, ch_7400_3, ch_7400_4, ch_7400_5, ch_7400_6, ch_7400_7])

theorem root_7401 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7401) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7401_0, decode 300 d_7401_1, decode 300 d_7401_2, decode 300 d_7401_3, decode 300 d_7401_4, decode 300 d_7401_5, decode 300 d_7401_6, decode 141 d_7401_7] (fun x hx => bits_full_and hx) cov_7401 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7401_0, ch_7401_1, ch_7401_2, ch_7401_3, ch_7401_4, ch_7401_5, ch_7401_6, ch_7401_7])

theorem root_7409 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7409) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7409_0, decode 300 d_7409_1, decode 300 d_7409_2, decode 300 d_7409_3, decode 300 d_7409_4, decode 300 d_7409_5, decode 300 d_7409_6, decode 142 d_7409_7] (fun x hx => bits_full_and hx) cov_7409 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7409_0, ch_7409_1, ch_7409_2, ch_7409_3, ch_7409_4, ch_7409_5, ch_7409_6, ch_7409_7])

theorem root_7410 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7410) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7410_0, decode 300 d_7410_1, decode 300 d_7410_2, decode 300 d_7410_3, decode 300 d_7410_4, decode 300 d_7410_5, decode 300 d_7410_6, decode 142 d_7410_7] (fun x hx => bits_full_and hx) cov_7410 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7410_0, ch_7410_1, ch_7410_2, ch_7410_3, ch_7410_4, ch_7410_5, ch_7410_6, ch_7410_7])

theorem root_7411 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7411) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7411_0, decode 300 d_7411_1, decode 300 d_7411_2, decode 300 d_7411_3, decode 300 d_7411_4, decode 300 d_7411_5, decode 300 d_7411_6, decode 141 d_7411_7] (fun x hx => bits_full_and hx) cov_7411 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7411_0, ch_7411_1, ch_7411_2, ch_7411_3, ch_7411_4, ch_7411_5, ch_7411_6, ch_7411_7])

theorem root_7412 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7412) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7412_0, decode 300 d_7412_1, decode 300 d_7412_2, decode 300 d_7412_3, decode 300 d_7412_4, decode 300 d_7412_5, decode 300 d_7412_6, decode 141 d_7412_7] (fun x hx => bits_full_and hx) cov_7412 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7412_0, ch_7412_1, ch_7412_2, ch_7412_3, ch_7412_4, ch_7412_5, ch_7412_6, ch_7412_7])

theorem root_7419 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7419) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7419_0, decode 300 d_7419_1, decode 300 d_7419_2, decode 300 d_7419_3, decode 300 d_7419_4, decode 300 d_7419_5, decode 300 d_7419_6, decode 141 d_7419_7] (fun x hx => bits_full_and hx) cov_7419 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7419_0, ch_7419_1, ch_7419_2, ch_7419_3, ch_7419_4, ch_7419_5, ch_7419_6, ch_7419_7])

theorem root_7420 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7420) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7420_0, decode 300 d_7420_1, decode 300 d_7420_2, decode 300 d_7420_3, decode 300 d_7420_4, decode 300 d_7420_5, decode 300 d_7420_6, decode 142 d_7420_7] (fun x hx => bits_full_and hx) cov_7420 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7420_0, ch_7420_1, ch_7420_2, ch_7420_3, ch_7420_4, ch_7420_5, ch_7420_6, ch_7420_7])

theorem root_7421 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7421) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7421_0, decode 300 d_7421_1, decode 300 d_7421_2, decode 300 d_7421_3, decode 300 d_7421_4, decode 300 d_7421_5, decode 300 d_7421_6, decode 142 d_7421_7] (fun x hx => bits_full_and hx) cov_7421 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7421_0, ch_7421_1, ch_7421_2, ch_7421_3, ch_7421_4, ch_7421_5, ch_7421_6, ch_7421_7])

theorem root_7429 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7429) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7429_0, decode 300 d_7429_1, decode 300 d_7429_2, decode 300 d_7429_3, decode 300 d_7429_4, decode 300 d_7429_5, decode 300 d_7429_6, decode 141 d_7429_7] (fun x hx => bits_full_and hx) cov_7429 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7429_0, ch_7429_1, ch_7429_2, ch_7429_3, ch_7429_4, ch_7429_5, ch_7429_6, ch_7429_7])

theorem root_7430 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7430) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7430_0, decode 300 d_7430_1, decode 300 d_7430_2, decode 300 d_7430_3, decode 300 d_7430_4, decode 300 d_7430_5, decode 300 d_7430_6, decode 141 d_7430_7] (fun x hx => bits_full_and hx) cov_7430 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7430_0, ch_7430_1, ch_7430_2, ch_7430_3, ch_7430_4, ch_7430_5, ch_7430_6, ch_7430_7])

theorem root_7431 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7431) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7431_0, decode 300 d_7431_1, decode 300 d_7431_2, decode 300 d_7431_3, decode 300 d_7431_4, decode 300 d_7431_5, decode 300 d_7431_6, decode 142 d_7431_7] (fun x hx => bits_full_and hx) cov_7431 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7431_0, ch_7431_1, ch_7431_2, ch_7431_3, ch_7431_4, ch_7431_5, ch_7431_6, ch_7431_7])

theorem root_7437 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7437) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7437_0, decode 300 d_7437_1, decode 300 d_7437_2, decode 300 d_7437_3, decode 300 d_7437_4, decode 300 d_7437_5, decode 300 d_7437_6, decode 141 d_7437_7] (fun x hx => bits_full_and hx) cov_7437 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7437_0, ch_7437_1, ch_7437_2, ch_7437_3, ch_7437_4, ch_7437_5, ch_7437_6, ch_7437_7])

theorem root_7447 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7447) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7447_0, decode 300 d_7447_1, decode 300 d_7447_2, decode 300 d_7447_3, decode 300 d_7447_4, decode 300 d_7447_5, decode 300 d_7447_6, decode 141 d_7447_7] (fun x hx => bits_full_and hx) cov_7447 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7447_0, ch_7447_1, ch_7447_2, ch_7447_3, ch_7447_4, ch_7447_5, ch_7447_6, ch_7447_7])

theorem root_7448 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7448) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7448_0, decode 300 d_7448_1, decode 300 d_7448_2, decode 300 d_7448_3, decode 300 d_7448_4, decode 300 d_7448_5, decode 300 d_7448_6, decode 141 d_7448_7] (fun x hx => bits_full_and hx) cov_7448 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7448_0, ch_7448_1, ch_7448_2, ch_7448_3, ch_7448_4, ch_7448_5, ch_7448_6, ch_7448_7])

theorem roots_111_ok (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    ∀ k ∈ roots_111, Claim (FULL &&& MT k) 3 := by
  intro k hk
  simp only [roots_111, List.mem_cons, List.mem_nil_iff, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [root_7397 hB hC hCl hCB, root_7398 hB hC hCl hCB, root_7399 hB hC hCl hCB, root_7400 hB hC hCl hCB, root_7401 hB hC hCl hCB, root_7409 hB hC hCl hCB, root_7410 hB hC hCl hCB, root_7411 hB hC hCl hCB, root_7412 hB hC hCl hCB, root_7419 hB hC hCl hCB, root_7420 hB hC hCl hCB, root_7421 hB hC hCl hCB, root_7429 hB hC hCl hCB, root_7430 hB hC hCl hCB, root_7431 hB hC hCl hCB, root_7437 hB hC hCl hCB, root_7447 hB hC hCl hCB, root_7448 hB hC hCl hCB]

theorem root_7449 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7449) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7449_0, decode 300 d_7449_1, decode 300 d_7449_2, decode 300 d_7449_3, decode 300 d_7449_4, decode 300 d_7449_5, decode 300 d_7449_6, decode 141 d_7449_7] (fun x hx => bits_full_and hx) cov_7449 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7449_0, ch_7449_1, ch_7449_2, ch_7449_3, ch_7449_4, ch_7449_5, ch_7449_6, ch_7449_7])

theorem root_7451 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7451) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7451_0, decode 300 d_7451_1, decode 300 d_7451_2, decode 300 d_7451_3, decode 300 d_7451_4, decode 300 d_7451_5, decode 300 d_7451_6, decode 142 d_7451_7] (fun x hx => bits_full_and hx) cov_7451 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7451_0, ch_7451_1, ch_7451_2, ch_7451_3, ch_7451_4, ch_7451_5, ch_7451_6, ch_7451_7])

theorem root_7452 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7452) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7452_0, decode 300 d_7452_1, decode 300 d_7452_2, decode 300 d_7452_3, decode 300 d_7452_4, decode 300 d_7452_5, decode 300 d_7452_6, decode 142 d_7452_7] (fun x hx => bits_full_and hx) cov_7452 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7452_0, ch_7452_1, ch_7452_2, ch_7452_3, ch_7452_4, ch_7452_5, ch_7452_6, ch_7452_7])

theorem root_7453 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7453) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7453_0, decode 300 d_7453_1, decode 300 d_7453_2, decode 300 d_7453_3, decode 300 d_7453_4, decode 300 d_7453_5, decode 300 d_7453_6, decode 142 d_7453_7] (fun x hx => bits_full_and hx) cov_7453 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7453_0, ch_7453_1, ch_7453_2, ch_7453_3, ch_7453_4, ch_7453_5, ch_7453_6, ch_7453_7])

theorem root_7458 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7458) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7458_0, decode 300 d_7458_1, decode 300 d_7458_2, decode 300 d_7458_3, decode 300 d_7458_4, decode 272 d_7458_5] (fun x hx => bits_full_and hx) cov_7458 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7458_0, ch_7458_1, ch_7458_2, ch_7458_3, ch_7458_4, ch_7458_5])

theorem root_7475 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7475) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7475_0, decode 300 d_7475_1, decode 300 d_7475_2, decode 300 d_7475_3, decode 300 d_7475_4, decode 300 d_7475_5, decode 300 d_7475_6, decode 141 d_7475_7] (fun x hx => bits_full_and hx) cov_7475 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7475_0, ch_7475_1, ch_7475_2, ch_7475_3, ch_7475_4, ch_7475_5, ch_7475_6, ch_7475_7])

theorem root_7476 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7476) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7476_0, decode 300 d_7476_1, decode 300 d_7476_2, decode 300 d_7476_3, decode 300 d_7476_4, decode 300 d_7476_5, decode 300 d_7476_6, decode 141 d_7476_7] (fun x hx => bits_full_and hx) cov_7476 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7476_0, ch_7476_1, ch_7476_2, ch_7476_3, ch_7476_4, ch_7476_5, ch_7476_6, ch_7476_7])

theorem root_7477 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7477) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7477_0, decode 300 d_7477_1, decode 300 d_7477_2, decode 300 d_7477_3, decode 300 d_7477_4, decode 300 d_7477_5, decode 300 d_7477_6, decode 141 d_7477_7] (fun x hx => bits_full_and hx) cov_7477 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7477_0, ch_7477_1, ch_7477_2, ch_7477_3, ch_7477_4, ch_7477_5, ch_7477_6, ch_7477_7])

theorem root_7478 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7478) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7478_0, decode 300 d_7478_1, decode 300 d_7478_2, decode 300 d_7478_3, decode 300 d_7478_4, decode 300 d_7478_5, decode 300 d_7478_6, decode 141 d_7478_7] (fun x hx => bits_full_and hx) cov_7478 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7478_0, ch_7478_1, ch_7478_2, ch_7478_3, ch_7478_4, ch_7478_5, ch_7478_6, ch_7478_7])

theorem root_7479 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7479) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7479_0, decode 300 d_7479_1, decode 300 d_7479_2, decode 300 d_7479_3, decode 300 d_7479_4, decode 300 d_7479_5, decode 300 d_7479_6, decode 141 d_7479_7] (fun x hx => bits_full_and hx) cov_7479 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7479_0, ch_7479_1, ch_7479_2, ch_7479_3, ch_7479_4, ch_7479_5, ch_7479_6, ch_7479_7])

theorem root_7481 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7481) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7481_0, decode 300 d_7481_1, decode 300 d_7481_2, decode 300 d_7481_3, decode 300 d_7481_4, decode 300 d_7481_5, decode 300 d_7481_6, decode 141 d_7481_7] (fun x hx => bits_full_and hx) cov_7481 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7481_0, ch_7481_1, ch_7481_2, ch_7481_3, ch_7481_4, ch_7481_5, ch_7481_6, ch_7481_7])

theorem root_7482 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7482) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7482_0, decode 300 d_7482_1, decode 300 d_7482_2, decode 300 d_7482_3, decode 300 d_7482_4, decode 300 d_7482_5, decode 300 d_7482_6, decode 160 d_7482_7] (fun x hx => bits_full_and hx) cov_7482 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7482_0, ch_7482_1, ch_7482_2, ch_7482_3, ch_7482_4, ch_7482_5, ch_7482_6, ch_7482_7])

theorem root_7483 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7483) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7483_0, decode 300 d_7483_1, decode 300 d_7483_2, decode 300 d_7483_3, decode 300 d_7483_4, decode 300 d_7483_5, decode 300 d_7483_6, decode 160 d_7483_7] (fun x hx => bits_full_and hx) cov_7483 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7483_0, ch_7483_1, ch_7483_2, ch_7483_3, ch_7483_4, ch_7483_5, ch_7483_6, ch_7483_7])

theorem root_7488 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7488) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7488_0, decode 300 d_7488_1, decode 300 d_7488_2, decode 300 d_7488_3, decode 300 d_7488_4, decode 300 d_7488_5, decode 8 d_7488_6] (fun x hx => bits_full_and hx) cov_7488 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7488_0, ch_7488_1, ch_7488_2, ch_7488_3, ch_7488_4, ch_7488_5, ch_7488_6])

theorem root_7492 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7492) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7492_0, decode 300 d_7492_1, decode 300 d_7492_2, decode 300 d_7492_3, decode 300 d_7492_4, decode 266 d_7492_5] (fun x hx => bits_full_and hx) cov_7492 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7492_0, ch_7492_1, ch_7492_2, ch_7492_3, ch_7492_4, ch_7492_5])

theorem root_7493 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7493) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7493_0, decode 300 d_7493_1, decode 300 d_7493_2, decode 300 d_7493_3, decode 300 d_7493_4, decode 266 d_7493_5] (fun x hx => bits_full_and hx) cov_7493 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7493_0, ch_7493_1, ch_7493_2, ch_7493_3, ch_7493_4, ch_7493_5])

theorem root_7502 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7502) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7502_0, decode 300 d_7502_1, decode 300 d_7502_2, decode 300 d_7502_3, decode 300 d_7502_4, decode 300 d_7502_5, decode 300 d_7502_6, decode 141 d_7502_7] (fun x hx => bits_full_and hx) cov_7502 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7502_0, ch_7502_1, ch_7502_2, ch_7502_3, ch_7502_4, ch_7502_5, ch_7502_6, ch_7502_7])

theorem root_7510 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7510) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7510_0, decode 300 d_7510_1, decode 300 d_7510_2, decode 300 d_7510_3, decode 300 d_7510_4, decode 300 d_7510_5, decode 300 d_7510_6, decode 141 d_7510_7] (fun x hx => bits_full_and hx) cov_7510 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7510_0, ch_7510_1, ch_7510_2, ch_7510_3, ch_7510_4, ch_7510_5, ch_7510_6, ch_7510_7])

theorem root_7512 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7512) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7512_0, decode 300 d_7512_1, decode 300 d_7512_2, decode 300 d_7512_3, decode 300 d_7512_4, decode 300 d_7512_5, decode 300 d_7512_6, decode 141 d_7512_7] (fun x hx => bits_full_and hx) cov_7512 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7512_0, ch_7512_1, ch_7512_2, ch_7512_3, ch_7512_4, ch_7512_5, ch_7512_6, ch_7512_7])

theorem roots_112_ok (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    ∀ k ∈ roots_112, Claim (FULL &&& MT k) 3 := by
  intro k hk
  simp only [roots_112, List.mem_cons, List.mem_nil_iff, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [root_7449 hB hC hCl hCB, root_7451 hB hC hCl hCB, root_7452 hB hC hCl hCB, root_7453 hB hC hCl hCB, root_7458 hB hC hCl hCB, root_7475 hB hC hCl hCB, root_7476 hB hC hCl hCB, root_7477 hB hC hCl hCB, root_7478 hB hC hCl hCB, root_7479 hB hC hCl hCB, root_7481 hB hC hCl hCB, root_7482 hB hC hCl hCB, root_7483 hB hC hCl hCB, root_7488 hB hC hCl hCB, root_7492 hB hC hCl hCB, root_7493 hB hC hCl hCB, root_7502 hB hC hCl hCB, root_7510 hB hC hCl hCB, root_7512 hB hC hCl hCB]

theorem root_7513 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7513) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7513_0, decode 300 d_7513_1, decode 300 d_7513_2, decode 300 d_7513_3, decode 300 d_7513_4, decode 300 d_7513_5, decode 300 d_7513_6, decode 141 d_7513_7] (fun x hx => bits_full_and hx) cov_7513 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7513_0, ch_7513_1, ch_7513_2, ch_7513_3, ch_7513_4, ch_7513_5, ch_7513_6, ch_7513_7])

theorem root_7519 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7519) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7519_0, decode 300 d_7519_1, decode 300 d_7519_2, decode 300 d_7519_3, decode 300 d_7519_4, decode 300 d_7519_5, decode 300 d_7519_6, decode 141 d_7519_7] (fun x hx => bits_full_and hx) cov_7519 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7519_0, ch_7519_1, ch_7519_2, ch_7519_3, ch_7519_4, ch_7519_5, ch_7519_6, ch_7519_7])

theorem root_7523 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7523) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7523_0, decode 300 d_7523_1, decode 300 d_7523_2, decode 300 d_7523_3, decode 300 d_7523_4, decode 300 d_7523_5, decode 300 d_7523_6, decode 141 d_7523_7] (fun x hx => bits_full_and hx) cov_7523 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7523_0, ch_7523_1, ch_7523_2, ch_7523_3, ch_7523_4, ch_7523_5, ch_7523_6, ch_7523_7])

theorem root_7529 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7529) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7529_0, decode 300 d_7529_1, decode 300 d_7529_2, decode 300 d_7529_3, decode 300 d_7529_4, decode 300 d_7529_5, decode 300 d_7529_6, decode 141 d_7529_7] (fun x hx => bits_full_and hx) cov_7529 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7529_0, ch_7529_1, ch_7529_2, ch_7529_3, ch_7529_4, ch_7529_5, ch_7529_6, ch_7529_7])

theorem root_7530 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7530) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7530_0, decode 300 d_7530_1, decode 300 d_7530_2, decode 300 d_7530_3, decode 300 d_7530_4, decode 300 d_7530_5, decode 300 d_7530_6, decode 141 d_7530_7] (fun x hx => bits_full_and hx) cov_7530 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7530_0, ch_7530_1, ch_7530_2, ch_7530_3, ch_7530_4, ch_7530_5, ch_7530_6, ch_7530_7])

theorem root_7536 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7536) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7536_0, decode 300 d_7536_1, decode 300 d_7536_2, decode 300 d_7536_3, decode 300 d_7536_4, decode 300 d_7536_5, decode 300 d_7536_6, decode 141 d_7536_7] (fun x hx => bits_full_and hx) cov_7536 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7536_0, ch_7536_1, ch_7536_2, ch_7536_3, ch_7536_4, ch_7536_5, ch_7536_6, ch_7536_7])

theorem root_7537 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7537) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7537_0, decode 300 d_7537_1, decode 300 d_7537_2, decode 300 d_7537_3, decode 300 d_7537_4, decode 300 d_7537_5, decode 300 d_7537_6, decode 141 d_7537_7] (fun x hx => bits_full_and hx) cov_7537 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7537_0, ch_7537_1, ch_7537_2, ch_7537_3, ch_7537_4, ch_7537_5, ch_7537_6, ch_7537_7])

theorem root_7540 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7540) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7540_0, decode 300 d_7540_1, decode 300 d_7540_2, decode 300 d_7540_3, decode 300 d_7540_4, decode 300 d_7540_5, decode 300 d_7540_6, decode 141 d_7540_7] (fun x hx => bits_full_and hx) cov_7540 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7540_0, ch_7540_1, ch_7540_2, ch_7540_3, ch_7540_4, ch_7540_5, ch_7540_6, ch_7540_7])

theorem root_7541 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7541) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7541_0, decode 300 d_7541_1, decode 300 d_7541_2, decode 300 d_7541_3, decode 300 d_7541_4, decode 300 d_7541_5, decode 300 d_7541_6, decode 141 d_7541_7] (fun x hx => bits_full_and hx) cov_7541 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7541_0, ch_7541_1, ch_7541_2, ch_7541_3, ch_7541_4, ch_7541_5, ch_7541_6, ch_7541_7])

theorem root_7547 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7547) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7547_0, decode 300 d_7547_1, decode 300 d_7547_2, decode 300 d_7547_3, decode 300 d_7547_4, decode 300 d_7547_5, decode 300 d_7547_6, decode 141 d_7547_7] (fun x hx => bits_full_and hx) cov_7547 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7547_0, ch_7547_1, ch_7547_2, ch_7547_3, ch_7547_4, ch_7547_5, ch_7547_6, ch_7547_7])

theorem root_7550 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7550) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7550_0, decode 300 d_7550_1, decode 300 d_7550_2, decode 300 d_7550_3, decode 300 d_7550_4, decode 300 d_7550_5, decode 300 d_7550_6, decode 141 d_7550_7] (fun x hx => bits_full_and hx) cov_7550 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7550_0, ch_7550_1, ch_7550_2, ch_7550_3, ch_7550_4, ch_7550_5, ch_7550_6, ch_7550_7])

theorem root_7551 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7551) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7551_0, decode 300 d_7551_1, decode 300 d_7551_2, decode 300 d_7551_3, decode 300 d_7551_4, decode 300 d_7551_5, decode 300 d_7551_6, decode 142 d_7551_7] (fun x hx => bits_full_and hx) cov_7551 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7551_0, ch_7551_1, ch_7551_2, ch_7551_3, ch_7551_4, ch_7551_5, ch_7551_6, ch_7551_7])

theorem root_7552 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7552) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7552_0, decode 300 d_7552_1, decode 300 d_7552_2, decode 300 d_7552_3, decode 300 d_7552_4, decode 300 d_7552_5, decode 300 d_7552_6, decode 142 d_7552_7] (fun x hx => bits_full_and hx) cov_7552 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7552_0, ch_7552_1, ch_7552_2, ch_7552_3, ch_7552_4, ch_7552_5, ch_7552_6, ch_7552_7])

theorem root_7554 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7554) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7554_0, decode 300 d_7554_1, decode 300 d_7554_2, decode 300 d_7554_3, decode 300 d_7554_4, decode 300 d_7554_5, decode 59 d_7554_6] (fun x hx => bits_full_and hx) cov_7554 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7554_0, ch_7554_1, ch_7554_2, ch_7554_3, ch_7554_4, ch_7554_5, ch_7554_6])

theorem root_7555 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7555) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7555_0, decode 300 d_7555_1, decode 300 d_7555_2, decode 300 d_7555_3, decode 300 d_7555_4, decode 300 d_7555_5, decode 59 d_7555_6] (fun x hx => bits_full_and hx) cov_7555 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7555_0, ch_7555_1, ch_7555_2, ch_7555_3, ch_7555_4, ch_7555_5, ch_7555_6])

theorem root_7560 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7560) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7560_0, decode 300 d_7560_1, decode 300 d_7560_2, decode 300 d_7560_3, decode 300 d_7560_4, decode 300 d_7560_5, decode 28 d_7560_6] (fun x hx => bits_full_and hx) cov_7560 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7560_0, ch_7560_1, ch_7560_2, ch_7560_3, ch_7560_4, ch_7560_5, ch_7560_6])

theorem root_7569 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7569) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7569_0, decode 300 d_7569_1, decode 300 d_7569_2, decode 300 d_7569_3, decode 300 d_7569_4, decode 300 d_7569_5, decode 300 d_7569_6, decode 141 d_7569_7] (fun x hx => bits_full_and hx) cov_7569 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7569_0, ch_7569_1, ch_7569_2, ch_7569_3, ch_7569_4, ch_7569_5, ch_7569_6, ch_7569_7])

theorem root_7570 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7570) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7570_0, decode 300 d_7570_1, decode 300 d_7570_2, decode 300 d_7570_3, decode 300 d_7570_4, decode 300 d_7570_5, decode 300 d_7570_6, decode 141 d_7570_7] (fun x hx => bits_full_and hx) cov_7570 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7570_0, ch_7570_1, ch_7570_2, ch_7570_3, ch_7570_4, ch_7570_5, ch_7570_6, ch_7570_7])

theorem root_7576 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7576) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7576_0, decode 300 d_7576_1, decode 300 d_7576_2, decode 300 d_7576_3, decode 300 d_7576_4, decode 300 d_7576_5, decode 300 d_7576_6, decode 141 d_7576_7] (fun x hx => bits_full_and hx) cov_7576 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7576_0, ch_7576_1, ch_7576_2, ch_7576_3, ch_7576_4, ch_7576_5, ch_7576_6, ch_7576_7])

theorem roots_113_ok (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    ∀ k ∈ roots_113, Claim (FULL &&& MT k) 3 := by
  intro k hk
  simp only [roots_113, List.mem_cons, List.mem_nil_iff, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [root_7513 hB hC hCl hCB, root_7519 hB hC hCl hCB, root_7523 hB hC hCl hCB, root_7529 hB hC hCl hCB, root_7530 hB hC hCl hCB, root_7536 hB hC hCl hCB, root_7537 hB hC hCl hCB, root_7540 hB hC hCl hCB, root_7541 hB hC hCl hCB, root_7547 hB hC hCl hCB, root_7550 hB hC hCl hCB, root_7551 hB hC hCl hCB, root_7552 hB hC hCl hCB, root_7554 hB hC hCl hCB, root_7555 hB hC hCl hCB, root_7560 hB hC hCl hCB, root_7569 hB hC hCl hCB, root_7570 hB hC hCl hCB, root_7576 hB hC hCl hCB]

theorem root_7577 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7577) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7577_0, decode 300 d_7577_1, decode 300 d_7577_2, decode 300 d_7577_3, decode 300 d_7577_4, decode 300 d_7577_5, decode 300 d_7577_6, decode 141 d_7577_7] (fun x hx => bits_full_and hx) cov_7577 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7577_0, ch_7577_1, ch_7577_2, ch_7577_3, ch_7577_4, ch_7577_5, ch_7577_6, ch_7577_7])

theorem root_7581 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7581) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7581_0, decode 300 d_7581_1, decode 300 d_7581_2, decode 300 d_7581_3, decode 300 d_7581_4, decode 300 d_7581_5, decode 300 d_7581_6, decode 141 d_7581_7] (fun x hx => bits_full_and hx) cov_7581 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7581_0, ch_7581_1, ch_7581_2, ch_7581_3, ch_7581_4, ch_7581_5, ch_7581_6, ch_7581_7])

theorem root_7582 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7582) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7582_0, decode 300 d_7582_1, decode 300 d_7582_2, decode 300 d_7582_3, decode 300 d_7582_4, decode 300 d_7582_5, decode 300 d_7582_6, decode 141 d_7582_7] (fun x hx => bits_full_and hx) cov_7582 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7582_0, ch_7582_1, ch_7582_2, ch_7582_3, ch_7582_4, ch_7582_5, ch_7582_6, ch_7582_7])

theorem root_7584 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7584) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7584_0, decode 300 d_7584_1, decode 300 d_7584_2, decode 300 d_7584_3, decode 300 d_7584_4, decode 300 d_7584_5, decode 300 d_7584_6, decode 141 d_7584_7] (fun x hx => bits_full_and hx) cov_7584 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7584_0, ch_7584_1, ch_7584_2, ch_7584_3, ch_7584_4, ch_7584_5, ch_7584_6, ch_7584_7])

theorem root_7589 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7589) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7589_0, decode 300 d_7589_1, decode 300 d_7589_2, decode 300 d_7589_3, decode 300 d_7589_4, decode 300 d_7589_5, decode 300 d_7589_6, decode 141 d_7589_7] (fun x hx => bits_full_and hx) cov_7589 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7589_0, ch_7589_1, ch_7589_2, ch_7589_3, ch_7589_4, ch_7589_5, ch_7589_6, ch_7589_7])

theorem root_7590 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7590) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7590_0, decode 300 d_7590_1, decode 300 d_7590_2, decode 300 d_7590_3, decode 300 d_7590_4, decode 300 d_7590_5, decode 300 d_7590_6, decode 141 d_7590_7] (fun x hx => bits_full_and hx) cov_7590 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7590_0, ch_7590_1, ch_7590_2, ch_7590_3, ch_7590_4, ch_7590_5, ch_7590_6, ch_7590_7])

theorem root_7591 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7591) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7591_0, decode 300 d_7591_1, decode 300 d_7591_2, decode 300 d_7591_3, decode 300 d_7591_4, decode 300 d_7591_5, decode 300 d_7591_6, decode 141 d_7591_7] (fun x hx => bits_full_and hx) cov_7591 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7591_0, ch_7591_1, ch_7591_2, ch_7591_3, ch_7591_4, ch_7591_5, ch_7591_6, ch_7591_7])

theorem root_7597 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7597) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7597_0, decode 300 d_7597_1, decode 300 d_7597_2, decode 300 d_7597_3, decode 300 d_7597_4, decode 300 d_7597_5, decode 300 d_7597_6, decode 141 d_7597_7] (fun x hx => bits_full_and hx) cov_7597 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7597_0, ch_7597_1, ch_7597_2, ch_7597_3, ch_7597_4, ch_7597_5, ch_7597_6, ch_7597_7])

theorem root_7598 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7598) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7598_0, decode 300 d_7598_1, decode 300 d_7598_2, decode 300 d_7598_3, decode 300 d_7598_4, decode 300 d_7598_5, decode 300 d_7598_6, decode 141 d_7598_7] (fun x hx => bits_full_and hx) cov_7598 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7598_0, ch_7598_1, ch_7598_2, ch_7598_3, ch_7598_4, ch_7598_5, ch_7598_6, ch_7598_7])

theorem root_7602 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7602) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7602_0, decode 300 d_7602_1, decode 300 d_7602_2, decode 300 d_7602_3, decode 300 d_7602_4, decode 300 d_7602_5, decode 300 d_7602_6, decode 141 d_7602_7] (fun x hx => bits_full_and hx) cov_7602 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7602_0, ch_7602_1, ch_7602_2, ch_7602_3, ch_7602_4, ch_7602_5, ch_7602_6, ch_7602_7])

theorem root_7603 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7603) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7603_0, decode 300 d_7603_1, decode 300 d_7603_2, decode 300 d_7603_3, decode 300 d_7603_4, decode 300 d_7603_5, decode 300 d_7603_6, decode 142 d_7603_7] (fun x hx => bits_full_and hx) cov_7603 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7603_0, ch_7603_1, ch_7603_2, ch_7603_3, ch_7603_4, ch_7603_5, ch_7603_6, ch_7603_7])

theorem root_7604 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7604) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7604_0, decode 300 d_7604_1, decode 300 d_7604_2, decode 300 d_7604_3, decode 300 d_7604_4, decode 300 d_7604_5, decode 300 d_7604_6, decode 142 d_7604_7] (fun x hx => bits_full_and hx) cov_7604 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7604_0, ch_7604_1, ch_7604_2, ch_7604_3, ch_7604_4, ch_7604_5, ch_7604_6, ch_7604_7])

theorem root_7611 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7611) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7611_0, decode 300 d_7611_1, decode 300 d_7611_2, decode 300 d_7611_3, decode 300 d_7611_4, decode 300 d_7611_5, decode 59 d_7611_6] (fun x hx => bits_full_and hx) cov_7611 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7611_0, ch_7611_1, ch_7611_2, ch_7611_3, ch_7611_4, ch_7611_5, ch_7611_6])

theorem root_7617 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7617) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7617_0, decode 300 d_7617_1, decode 300 d_7617_2, decode 300 d_7617_3, decode 300 d_7617_4, decode 300 d_7617_5, decode 28 d_7617_6] (fun x hx => bits_full_and hx) cov_7617 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7617_0, ch_7617_1, ch_7617_2, ch_7617_3, ch_7617_4, ch_7617_5, ch_7617_6])

theorem root_7623 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7623) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7623_0, decode 300 d_7623_1, decode 300 d_7623_2, decode 300 d_7623_3, decode 300 d_7623_4, decode 300 d_7623_5, decode 300 d_7623_6, decode 141 d_7623_7] (fun x hx => bits_full_and hx) cov_7623 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7623_0, ch_7623_1, ch_7623_2, ch_7623_3, ch_7623_4, ch_7623_5, ch_7623_6, ch_7623_7])

theorem root_7624 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7624) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7624_0, decode 300 d_7624_1, decode 300 d_7624_2, decode 300 d_7624_3, decode 300 d_7624_4, decode 300 d_7624_5, decode 300 d_7624_6, decode 141 d_7624_7] (fun x hx => bits_full_and hx) cov_7624 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7624_0, ch_7624_1, ch_7624_2, ch_7624_3, ch_7624_4, ch_7624_5, ch_7624_6, ch_7624_7])

theorem root_7633 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7633) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7633_0, decode 300 d_7633_1, decode 300 d_7633_2, decode 300 d_7633_3, decode 300 d_7633_4, decode 300 d_7633_5, decode 300 d_7633_6, decode 141 d_7633_7] (fun x hx => bits_full_and hx) cov_7633 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7633_0, ch_7633_1, ch_7633_2, ch_7633_3, ch_7633_4, ch_7633_5, ch_7633_6, ch_7633_7])

theorem root_7641 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7641) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7641_0, decode 300 d_7641_1, decode 300 d_7641_2, decode 300 d_7641_3, decode 300 d_7641_4, decode 300 d_7641_5, decode 300 d_7641_6, decode 141 d_7641_7] (fun x hx => bits_full_and hx) cov_7641 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7641_0, ch_7641_1, ch_7641_2, ch_7641_3, ch_7641_4, ch_7641_5, ch_7641_6, ch_7641_7])

theorem root_7644 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7644) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7644_0, decode 300 d_7644_1, decode 300 d_7644_2, decode 300 d_7644_3, decode 300 d_7644_4, decode 300 d_7644_5, decode 300 d_7644_6, decode 141 d_7644_7] (fun x hx => bits_full_and hx) cov_7644 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7644_0, ch_7644_1, ch_7644_2, ch_7644_3, ch_7644_4, ch_7644_5, ch_7644_6, ch_7644_7])

theorem roots_114_ok (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    ∀ k ∈ roots_114, Claim (FULL &&& MT k) 3 := by
  intro k hk
  simp only [roots_114, List.mem_cons, List.mem_nil_iff, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [root_7577 hB hC hCl hCB, root_7581 hB hC hCl hCB, root_7582 hB hC hCl hCB, root_7584 hB hC hCl hCB, root_7589 hB hC hCl hCB, root_7590 hB hC hCl hCB, root_7591 hB hC hCl hCB, root_7597 hB hC hCl hCB, root_7598 hB hC hCl hCB, root_7602 hB hC hCl hCB, root_7603 hB hC hCl hCB, root_7604 hB hC hCl hCB, root_7611 hB hC hCl hCB, root_7617 hB hC hCl hCB, root_7623 hB hC hCl hCB, root_7624 hB hC hCl hCB, root_7633 hB hC hCl hCB, root_7641 hB hC hCl hCB, root_7644 hB hC hCl hCB]

theorem root_7645 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7645) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7645_0, decode 300 d_7645_1, decode 300 d_7645_2, decode 300 d_7645_3, decode 300 d_7645_4, decode 300 d_7645_5, decode 300 d_7645_6, decode 141 d_7645_7] (fun x hx => bits_full_and hx) cov_7645 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7645_0, ch_7645_1, ch_7645_2, ch_7645_3, ch_7645_4, ch_7645_5, ch_7645_6, ch_7645_7])

theorem root_7646 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7646) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7646_0, decode 300 d_7646_1, decode 300 d_7646_2, decode 300 d_7646_3, decode 300 d_7646_4, decode 300 d_7646_5, decode 300 d_7646_6, decode 141 d_7646_7] (fun x hx => bits_full_and hx) cov_7646 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7646_0, ch_7646_1, ch_7646_2, ch_7646_3, ch_7646_4, ch_7646_5, ch_7646_6, ch_7646_7])

theorem root_7650 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7650) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7650_0, decode 300 d_7650_1, decode 300 d_7650_2, decode 300 d_7650_3, decode 300 d_7650_4, decode 300 d_7650_5, decode 300 d_7650_6, decode 141 d_7650_7] (fun x hx => bits_full_and hx) cov_7650 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7650_0, ch_7650_1, ch_7650_2, ch_7650_3, ch_7650_4, ch_7650_5, ch_7650_6, ch_7650_7])

theorem root_7654 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7654) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7654_0, decode 300 d_7654_1, decode 300 d_7654_2, decode 300 d_7654_3, decode 300 d_7654_4, decode 300 d_7654_5, decode 300 d_7654_6, decode 141 d_7654_7] (fun x hx => bits_full_and hx) cov_7654 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7654_0, ch_7654_1, ch_7654_2, ch_7654_3, ch_7654_4, ch_7654_5, ch_7654_6, ch_7654_7])

theorem root_7658 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7658) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7658_0, decode 300 d_7658_1, decode 300 d_7658_2, decode 300 d_7658_3, decode 300 d_7658_4, decode 300 d_7658_5, decode 300 d_7658_6, decode 141 d_7658_7] (fun x hx => bits_full_and hx) cov_7658 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7658_0, ch_7658_1, ch_7658_2, ch_7658_3, ch_7658_4, ch_7658_5, ch_7658_6, ch_7658_7])

theorem root_7659 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7659) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7659_0, decode 300 d_7659_1, decode 300 d_7659_2, decode 300 d_7659_3, decode 300 d_7659_4, decode 300 d_7659_5, decode 300 d_7659_6, decode 141 d_7659_7] (fun x hx => bits_full_and hx) cov_7659 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7659_0, ch_7659_1, ch_7659_2, ch_7659_3, ch_7659_4, ch_7659_5, ch_7659_6, ch_7659_7])

theorem root_7661 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7661) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7661_0, decode 300 d_7661_1, decode 300 d_7661_2, decode 300 d_7661_3, decode 300 d_7661_4, decode 300 d_7661_5, decode 7 d_7661_6] (fun x hx => bits_full_and hx) cov_7661 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7661_0, ch_7661_1, ch_7661_2, ch_7661_3, ch_7661_4, ch_7661_5, ch_7661_6])

theorem root_7667 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7667) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7667_0, decode 300 d_7667_1, decode 300 d_7667_2, decode 300 d_7667_3, decode 300 d_7667_4, decode 283 d_7667_5] (fun x hx => bits_full_and hx) cov_7667 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7667_0, ch_7667_1, ch_7667_2, ch_7667_3, ch_7667_4, ch_7667_5])

theorem root_7671 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7671) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7671_0, decode 300 d_7671_1, decode 300 d_7671_2, decode 300 d_7671_3, decode 300 d_7671_4, decode 300 d_7671_5, decode 300 d_7671_6, decode 141 d_7671_7] (fun x hx => bits_full_and hx) cov_7671 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7671_0, ch_7671_1, ch_7671_2, ch_7671_3, ch_7671_4, ch_7671_5, ch_7671_6, ch_7671_7])

theorem root_7680 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7680) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7680_0, decode 300 d_7680_1, decode 300 d_7680_2, decode 300 d_7680_3, decode 300 d_7680_4, decode 300 d_7680_5, decode 300 d_7680_6, decode 141 d_7680_7] (fun x hx => bits_full_and hx) cov_7680 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7680_0, ch_7680_1, ch_7680_2, ch_7680_3, ch_7680_4, ch_7680_5, ch_7680_6, ch_7680_7])

theorem root_7684 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7684) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7684_0, decode 300 d_7684_1, decode 300 d_7684_2, decode 300 d_7684_3, decode 300 d_7684_4, decode 300 d_7684_5, decode 300 d_7684_6, decode 141 d_7684_7] (fun x hx => bits_full_and hx) cov_7684 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7684_0, ch_7684_1, ch_7684_2, ch_7684_3, ch_7684_4, ch_7684_5, ch_7684_6, ch_7684_7])

theorem root_7689 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7689) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7689_0, decode 300 d_7689_1, decode 300 d_7689_2, decode 300 d_7689_3, decode 300 d_7689_4, decode 300 d_7689_5, decode 300 d_7689_6, decode 141 d_7689_7] (fun x hx => bits_full_and hx) cov_7689 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7689_0, ch_7689_1, ch_7689_2, ch_7689_3, ch_7689_4, ch_7689_5, ch_7689_6, ch_7689_7])

theorem root_7691 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7691) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7691_0, decode 300 d_7691_1, decode 300 d_7691_2, decode 300 d_7691_3, decode 300 d_7691_4, decode 300 d_7691_5, decode 167 d_7691_6] (fun x hx => bits_full_and hx) cov_7691 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7691_0, ch_7691_1, ch_7691_2, ch_7691_3, ch_7691_4, ch_7691_5, ch_7691_6])

theorem root_7692 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7692) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7692_0, decode 300 d_7692_1, decode 300 d_7692_2, decode 300 d_7692_3, decode 300 d_7692_4, decode 300 d_7692_5, decode 91 d_7692_6] (fun x hx => bits_full_and hx) cov_7692 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7692_0, ch_7692_1, ch_7692_2, ch_7692_3, ch_7692_4, ch_7692_5, ch_7692_6])

theorem root_7693 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7693) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7693_0, decode 300 d_7693_1, decode 300 d_7693_2, decode 300 d_7693_3, decode 300 d_7693_4, decode 300 d_7693_5, decode 175 d_7693_6] (fun x hx => bits_full_and hx) cov_7693 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7693_0, ch_7693_1, ch_7693_2, ch_7693_3, ch_7693_4, ch_7693_5, ch_7693_6])

theorem root_7701 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7701) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7701_0, decode 300 d_7701_1, decode 300 d_7701_2, decode 300 d_7701_3, decode 300 d_7701_4, decode 300 d_7701_5, decode 7 d_7701_6] (fun x hx => bits_full_and hx) cov_7701 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7701_0, ch_7701_1, ch_7701_2, ch_7701_3, ch_7701_4, ch_7701_5, ch_7701_6])

theorem root_7708 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7708) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7708_0, decode 300 d_7708_1, decode 300 d_7708_2, decode 300 d_7708_3, decode 300 d_7708_4, decode 300 d_7708_5, decode 7 d_7708_6] (fun x hx => bits_full_and hx) cov_7708 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7708_0, ch_7708_1, ch_7708_2, ch_7708_3, ch_7708_4, ch_7708_5, ch_7708_6])

theorem root_7714 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7714) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7714_0, decode 300 d_7714_1, decode 300 d_7714_2, decode 300 d_7714_3, decode 300 d_7714_4, decode 283 d_7714_5] (fun x hx => bits_full_and hx) cov_7714 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7714_0, ch_7714_1, ch_7714_2, ch_7714_3, ch_7714_4, ch_7714_5])

theorem root_7719 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7719) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7719_0, decode 300 d_7719_1, decode 300 d_7719_2, decode 300 d_7719_3, decode 300 d_7719_4, decode 300 d_7719_5, decode 300 d_7719_6, decode 141 d_7719_7] (fun x hx => bits_full_and hx) cov_7719 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7719_0, ch_7719_1, ch_7719_2, ch_7719_3, ch_7719_4, ch_7719_5, ch_7719_6, ch_7719_7])

theorem root_7736 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7736) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7736_0, decode 300 d_7736_1, decode 300 d_7736_2, decode 300 d_7736_3, decode 300 d_7736_4, decode 300 d_7736_5, decode 300 d_7736_6, decode 141 d_7736_7] (fun x hx => bits_full_and hx) cov_7736 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7736_0, ch_7736_1, ch_7736_2, ch_7736_3, ch_7736_4, ch_7736_5, ch_7736_6, ch_7736_7])

theorem roots_115_ok (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    ∀ k ∈ roots_115, Claim (FULL &&& MT k) 3 := by
  intro k hk
  simp only [roots_115, List.mem_cons, List.mem_nil_iff, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [root_7645 hB hC hCl hCB, root_7646 hB hC hCl hCB, root_7650 hB hC hCl hCB, root_7654 hB hC hCl hCB, root_7658 hB hC hCl hCB, root_7659 hB hC hCl hCB, root_7661 hB hC hCl hCB, root_7667 hB hC hCl hCB, root_7671 hB hC hCl hCB, root_7680 hB hC hCl hCB, root_7684 hB hC hCl hCB, root_7689 hB hC hCl hCB, root_7691 hB hC hCl hCB, root_7692 hB hC hCl hCB, root_7693 hB hC hCl hCB, root_7701 hB hC hCl hCB, root_7708 hB hC hCl hCB, root_7714 hB hC hCl hCB, root_7719 hB hC hCl hCB, root_7736 hB hC hCl hCB]

theorem root_7737 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7737) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7737_0, decode 300 d_7737_1, decode 300 d_7737_2, decode 300 d_7737_3, decode 300 d_7737_4, decode 300 d_7737_5, decode 300 d_7737_6, decode 141 d_7737_7] (fun x hx => bits_full_and hx) cov_7737 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7737_0, ch_7737_1, ch_7737_2, ch_7737_3, ch_7737_4, ch_7737_5, ch_7737_6, ch_7737_7])

theorem root_7738 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7738) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7738_0, decode 300 d_7738_1, decode 300 d_7738_2, decode 300 d_7738_3, decode 300 d_7738_4, decode 300 d_7738_5, decode 300 d_7738_6, decode 141 d_7738_7] (fun x hx => bits_full_and hx) cov_7738 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7738_0, ch_7738_1, ch_7738_2, ch_7738_3, ch_7738_4, ch_7738_5, ch_7738_6, ch_7738_7])

theorem root_7747 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7747) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7747_0, decode 300 d_7747_1, decode 300 d_7747_2, decode 300 d_7747_3, decode 300 d_7747_4, decode 300 d_7747_5, decode 300 d_7747_6, decode 141 d_7747_7] (fun x hx => bits_full_and hx) cov_7747 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7747_0, ch_7747_1, ch_7747_2, ch_7747_3, ch_7747_4, ch_7747_5, ch_7747_6, ch_7747_7])

theorem root_7752 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7752) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7752_0, decode 300 d_7752_1, decode 300 d_7752_2, decode 300 d_7752_3, decode 300 d_7752_4, decode 300 d_7752_5, decode 300 d_7752_6, decode 141 d_7752_7] (fun x hx => bits_full_and hx) cov_7752 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7752_0, ch_7752_1, ch_7752_2, ch_7752_3, ch_7752_4, ch_7752_5, ch_7752_6, ch_7752_7])

theorem root_7758 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7758) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7758_0, decode 300 d_7758_1, decode 300 d_7758_2, decode 300 d_7758_3, decode 300 d_7758_4, decode 300 d_7758_5, decode 300 d_7758_6, decode 158 d_7758_7] (fun x hx => bits_full_and hx) cov_7758 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7758_0, ch_7758_1, ch_7758_2, ch_7758_3, ch_7758_4, ch_7758_5, ch_7758_6, ch_7758_7])

theorem root_7762 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7762) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7762_0, decode 300 d_7762_1, decode 300 d_7762_2, decode 300 d_7762_3, decode 300 d_7762_4, decode 300 d_7762_5, decode 300 d_7762_6, decode 142 d_7762_7] (fun x hx => bits_full_and hx) cov_7762 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7762_0, ch_7762_1, ch_7762_2, ch_7762_3, ch_7762_4, ch_7762_5, ch_7762_6, ch_7762_7])

theorem root_7774 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7774) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7774_0, decode 300 d_7774_1, decode 300 d_7774_2, decode 300 d_7774_3, decode 300 d_7774_4, decode 300 d_7774_5, decode 107 d_7774_6] (fun x hx => bits_full_and hx) cov_7774 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7774_0, ch_7774_1, ch_7774_2, ch_7774_3, ch_7774_4, ch_7774_5, ch_7774_6])

theorem root_7780 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7780) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7780_0, decode 300 d_7780_1, decode 300 d_7780_2, decode 300 d_7780_3, decode 300 d_7780_4, decode 300 d_7780_5, decode 130 d_7780_6] (fun x hx => bits_full_and hx) cov_7780 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7780_0, ch_7780_1, ch_7780_2, ch_7780_3, ch_7780_4, ch_7780_5, ch_7780_6])

theorem root_7781 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7781) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7781_0, decode 300 d_7781_1, decode 300 d_7781_2, decode 300 d_7781_3, decode 300 d_7781_4, decode 300 d_7781_5, decode 108 d_7781_6] (fun x hx => bits_full_and hx) cov_7781 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7781_0, ch_7781_1, ch_7781_2, ch_7781_3, ch_7781_4, ch_7781_5, ch_7781_6])

theorem root_7782 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7782) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7782_0, decode 300 d_7782_1, decode 300 d_7782_2, decode 300 d_7782_3, decode 300 d_7782_4, decode 300 d_7782_5, decode 108 d_7782_6] (fun x hx => bits_full_and hx) cov_7782 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7782_0, ch_7782_1, ch_7782_2, ch_7782_3, ch_7782_4, ch_7782_5, ch_7782_6])

theorem root_7787 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7787) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7787_0, decode 300 d_7787_1, decode 300 d_7787_2, decode 300 d_7787_3, decode 300 d_7787_4, decode 300 d_7787_5, decode 300 d_7787_6, decode 141 d_7787_7] (fun x hx => bits_full_and hx) cov_7787 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7787_0, ch_7787_1, ch_7787_2, ch_7787_3, ch_7787_4, ch_7787_5, ch_7787_6, ch_7787_7])

theorem root_7788 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7788) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7788_0, decode 300 d_7788_1, decode 300 d_7788_2, decode 300 d_7788_3, decode 300 d_7788_4, decode 300 d_7788_5, decode 300 d_7788_6, decode 141 d_7788_7] (fun x hx => bits_full_and hx) cov_7788 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7788_0, ch_7788_1, ch_7788_2, ch_7788_3, ch_7788_4, ch_7788_5, ch_7788_6, ch_7788_7])

theorem root_7791 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7791) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7791_0, decode 300 d_7791_1, decode 300 d_7791_2, decode 300 d_7791_3, decode 300 d_7791_4, decode 300 d_7791_5, decode 300 d_7791_6, decode 141 d_7791_7] (fun x hx => bits_full_and hx) cov_7791 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7791_0, ch_7791_1, ch_7791_2, ch_7791_3, ch_7791_4, ch_7791_5, ch_7791_6, ch_7791_7])

theorem root_7796 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7796) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7796_0, decode 300 d_7796_1, decode 300 d_7796_2, decode 300 d_7796_3, decode 300 d_7796_4, decode 300 d_7796_5, decode 300 d_7796_6, decode 141 d_7796_7] (fun x hx => bits_full_and hx) cov_7796 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7796_0, ch_7796_1, ch_7796_2, ch_7796_3, ch_7796_4, ch_7796_5, ch_7796_6, ch_7796_7])

theorem root_7797 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7797) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7797_0, decode 300 d_7797_1, decode 300 d_7797_2, decode 300 d_7797_3, decode 300 d_7797_4, decode 300 d_7797_5, decode 300 d_7797_6, decode 141 d_7797_7] (fun x hx => bits_full_and hx) cov_7797 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7797_0, ch_7797_1, ch_7797_2, ch_7797_3, ch_7797_4, ch_7797_5, ch_7797_6, ch_7797_7])

theorem root_7798 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7798) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7798_0, decode 300 d_7798_1, decode 300 d_7798_2, decode 300 d_7798_3, decode 300 d_7798_4, decode 300 d_7798_5, decode 300 d_7798_6, decode 141 d_7798_7] (fun x hx => bits_full_and hx) cov_7798 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7798_0, ch_7798_1, ch_7798_2, ch_7798_3, ch_7798_4, ch_7798_5, ch_7798_6, ch_7798_7])

theorem root_7801 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7801) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7801_0, decode 300 d_7801_1, decode 300 d_7801_2, decode 300 d_7801_3, decode 300 d_7801_4, decode 300 d_7801_5, decode 300 d_7801_6, decode 141 d_7801_7] (fun x hx => bits_full_and hx) cov_7801 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7801_0, ch_7801_1, ch_7801_2, ch_7801_3, ch_7801_4, ch_7801_5, ch_7801_6, ch_7801_7])

theorem root_7806 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7806) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7806_0, decode 300 d_7806_1, decode 300 d_7806_2, decode 300 d_7806_3, decode 300 d_7806_4, decode 300 d_7806_5, decode 300 d_7806_6, decode 142 d_7806_7] (fun x hx => bits_full_and hx) cov_7806 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7806_0, ch_7806_1, ch_7806_2, ch_7806_3, ch_7806_4, ch_7806_5, ch_7806_6, ch_7806_7])

theorem root_7807 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7807) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7807_0, decode 300 d_7807_1, decode 300 d_7807_2, decode 300 d_7807_3, decode 300 d_7807_4, decode 300 d_7807_5, decode 300 d_7807_6, decode 142 d_7807_7] (fun x hx => bits_full_and hx) cov_7807 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7807_0, ch_7807_1, ch_7807_2, ch_7807_3, ch_7807_4, ch_7807_5, ch_7807_6, ch_7807_7])

theorem roots_116_ok (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    ∀ k ∈ roots_116, Claim (FULL &&& MT k) 3 := by
  intro k hk
  simp only [roots_116, List.mem_cons, List.mem_nil_iff, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [root_7737 hB hC hCl hCB, root_7738 hB hC hCl hCB, root_7747 hB hC hCl hCB, root_7752 hB hC hCl hCB, root_7758 hB hC hCl hCB, root_7762 hB hC hCl hCB, root_7774 hB hC hCl hCB, root_7780 hB hC hCl hCB, root_7781 hB hC hCl hCB, root_7782 hB hC hCl hCB, root_7787 hB hC hCl hCB, root_7788 hB hC hCl hCB, root_7791 hB hC hCl hCB, root_7796 hB hC hCl hCB, root_7797 hB hC hCl hCB, root_7798 hB hC hCl hCB, root_7801 hB hC hCl hCB, root_7806 hB hC hCl hCB, root_7807 hB hC hCl hCB]

theorem root_7810 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7810) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7810_0, decode 300 d_7810_1, decode 300 d_7810_2, decode 300 d_7810_3, decode 300 d_7810_4, decode 300 d_7810_5, decode 300 d_7810_6, decode 141 d_7810_7] (fun x hx => bits_full_and hx) cov_7810 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7810_0, ch_7810_1, ch_7810_2, ch_7810_3, ch_7810_4, ch_7810_5, ch_7810_6, ch_7810_7])

theorem root_7819 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7819) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7819_0, decode 300 d_7819_1, decode 300 d_7819_2, decode 300 d_7819_3, decode 300 d_7819_4, decode 300 d_7819_5, decode 300 d_7819_6, decode 141 d_7819_7] (fun x hx => bits_full_and hx) cov_7819 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7819_0, ch_7819_1, ch_7819_2, ch_7819_3, ch_7819_4, ch_7819_5, ch_7819_6, ch_7819_7])

theorem root_7823 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7823) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7823_0, decode 300 d_7823_1, decode 300 d_7823_2, decode 300 d_7823_3, decode 300 d_7823_4, decode 300 d_7823_5, decode 70 d_7823_6] (fun x hx => bits_full_and hx) cov_7823 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7823_0, ch_7823_1, ch_7823_2, ch_7823_3, ch_7823_4, ch_7823_5, ch_7823_6])

theorem root_7824 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7824) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7824_0, decode 300 d_7824_1, decode 300 d_7824_2, decode 300 d_7824_3, decode 300 d_7824_4, decode 300 d_7824_5, decode 70 d_7824_6] (fun x hx => bits_full_and hx) cov_7824 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7824_0, ch_7824_1, ch_7824_2, ch_7824_3, ch_7824_4, ch_7824_5, ch_7824_6])

theorem root_7825 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7825) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7825_0, decode 300 d_7825_1, decode 300 d_7825_2, decode 300 d_7825_3, decode 300 d_7825_4, decode 300 d_7825_5, decode 23 d_7825_6] (fun x hx => bits_full_and hx) cov_7825 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7825_0, ch_7825_1, ch_7825_2, ch_7825_3, ch_7825_4, ch_7825_5, ch_7825_6])

theorem root_7830 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7830) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7830_0, decode 300 d_7830_1, decode 300 d_7830_2, decode 300 d_7830_3, decode 300 d_7830_4, decode 300 d_7830_5, decode 300 d_7830_6, decode 141 d_7830_7] (fun x hx => bits_full_and hx) cov_7830 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7830_0, ch_7830_1, ch_7830_2, ch_7830_3, ch_7830_4, ch_7830_5, ch_7830_6, ch_7830_7])

theorem root_7831 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7831) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7831_0, decode 300 d_7831_1, decode 300 d_7831_2, decode 300 d_7831_3, decode 300 d_7831_4, decode 300 d_7831_5, decode 300 d_7831_6, decode 141 d_7831_7] (fun x hx => bits_full_and hx) cov_7831 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7831_0, ch_7831_1, ch_7831_2, ch_7831_3, ch_7831_4, ch_7831_5, ch_7831_6, ch_7831_7])

theorem root_7832 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7832) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7832_0, decode 300 d_7832_1, decode 300 d_7832_2, decode 300 d_7832_3, decode 300 d_7832_4, decode 300 d_7832_5, decode 300 d_7832_6, decode 141 d_7832_7] (fun x hx => bits_full_and hx) cov_7832 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7832_0, ch_7832_1, ch_7832_2, ch_7832_3, ch_7832_4, ch_7832_5, ch_7832_6, ch_7832_7])

theorem root_7833 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7833) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7833_0, decode 300 d_7833_1, decode 300 d_7833_2, decode 300 d_7833_3, decode 300 d_7833_4, decode 300 d_7833_5, decode 300 d_7833_6, decode 141 d_7833_7] (fun x hx => bits_full_and hx) cov_7833 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7833_0, ch_7833_1, ch_7833_2, ch_7833_3, ch_7833_4, ch_7833_5, ch_7833_6, ch_7833_7])

theorem root_7842 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7842) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7842_0, decode 300 d_7842_1, decode 300 d_7842_2, decode 300 d_7842_3, decode 300 d_7842_4, decode 300 d_7842_5, decode 300 d_7842_6, decode 142 d_7842_7] (fun x hx => bits_full_and hx) cov_7842 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7842_0, ch_7842_1, ch_7842_2, ch_7842_3, ch_7842_4, ch_7842_5, ch_7842_6, ch_7842_7])

theorem root_7843 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7843) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7843_0, decode 300 d_7843_1, decode 300 d_7843_2, decode 300 d_7843_3, decode 300 d_7843_4, decode 300 d_7843_5, decode 300 d_7843_6, decode 142 d_7843_7] (fun x hx => bits_full_and hx) cov_7843 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7843_0, ch_7843_1, ch_7843_2, ch_7843_3, ch_7843_4, ch_7843_5, ch_7843_6, ch_7843_7])

theorem root_7847 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7847) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7847_0, decode 300 d_7847_1, decode 300 d_7847_2, decode 300 d_7847_3, decode 300 d_7847_4, decode 300 d_7847_5, decode 36 d_7847_6] (fun x hx => bits_full_and hx) cov_7847 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7847_0, ch_7847_1, ch_7847_2, ch_7847_3, ch_7847_4, ch_7847_5, ch_7847_6])

theorem root_7848 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7848) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7848_0, decode 300 d_7848_1, decode 300 d_7848_2, decode 300 d_7848_3, decode 300 d_7848_4, decode 300 d_7848_5, decode 23 d_7848_6] (fun x hx => bits_full_and hx) cov_7848 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7848_0, ch_7848_1, ch_7848_2, ch_7848_3, ch_7848_4, ch_7848_5, ch_7848_6])

theorem root_7849 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7849) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7849_0, decode 300 d_7849_1, decode 300 d_7849_2, decode 300 d_7849_3, decode 300 d_7849_4, decode 300 d_7849_5, decode 23 d_7849_6] (fun x hx => bits_full_and hx) cov_7849 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7849_0, ch_7849_1, ch_7849_2, ch_7849_3, ch_7849_4, ch_7849_5, ch_7849_6])

theorem root_7855 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7855) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7855_0, decode 300 d_7855_1, decode 300 d_7855_2, decode 300 d_7855_3, decode 300 d_7855_4, decode 300 d_7855_5, decode 300 d_7855_6, decode 142 d_7855_7] (fun x hx => bits_full_and hx) cov_7855 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7855_0, ch_7855_1, ch_7855_2, ch_7855_3, ch_7855_4, ch_7855_5, ch_7855_6, ch_7855_7])

theorem root_7856 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7856) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7856_0, decode 300 d_7856_1, decode 300 d_7856_2, decode 300 d_7856_3, decode 300 d_7856_4, decode 300 d_7856_5, decode 300 d_7856_6, decode 142 d_7856_7] (fun x hx => bits_full_and hx) cov_7856 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7856_0, ch_7856_1, ch_7856_2, ch_7856_3, ch_7856_4, ch_7856_5, ch_7856_6, ch_7856_7])

theorem root_7860 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7860) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7860_0, decode 300 d_7860_1, decode 300 d_7860_2, decode 300 d_7860_3, decode 300 d_7860_4, decode 300 d_7860_5, decode 300 d_7860_6, decode 141 d_7860_7] (fun x hx => bits_full_and hx) cov_7860 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7860_0, ch_7860_1, ch_7860_2, ch_7860_3, ch_7860_4, ch_7860_5, ch_7860_6, ch_7860_7])

theorem root_7861 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7861) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7861_0, decode 300 d_7861_1, decode 300 d_7861_2, decode 300 d_7861_3, decode 300 d_7861_4, decode 300 d_7861_5, decode 300 d_7861_6, decode 141 d_7861_7] (fun x hx => bits_full_and hx) cov_7861 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7861_0, ch_7861_1, ch_7861_2, ch_7861_3, ch_7861_4, ch_7861_5, ch_7861_6, ch_7861_7])

theorem root_7864 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7864) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7864_0, decode 300 d_7864_1, decode 300 d_7864_2, decode 300 d_7864_3, decode 300 d_7864_4, decode 300 d_7864_5, decode 101 d_7864_6] (fun x hx => bits_full_and hx) cov_7864 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7864_0, ch_7864_1, ch_7864_2, ch_7864_3, ch_7864_4, ch_7864_5, ch_7864_6])

theorem root_7865 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7865) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7865_0, decode 300 d_7865_1, decode 300 d_7865_2, decode 300 d_7865_3, decode 300 d_7865_4, decode 300 d_7865_5, decode 36 d_7865_6] (fun x hx => bits_full_and hx) cov_7865 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7865_0, ch_7865_1, ch_7865_2, ch_7865_3, ch_7865_4, ch_7865_5, ch_7865_6])

theorem roots_117_ok (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    ∀ k ∈ roots_117, Claim (FULL &&& MT k) 3 := by
  intro k hk
  simp only [roots_117, List.mem_cons, List.mem_nil_iff, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [root_7810 hB hC hCl hCB, root_7819 hB hC hCl hCB, root_7823 hB hC hCl hCB, root_7824 hB hC hCl hCB, root_7825 hB hC hCl hCB, root_7830 hB hC hCl hCB, root_7831 hB hC hCl hCB, root_7832 hB hC hCl hCB, root_7833 hB hC hCl hCB, root_7842 hB hC hCl hCB, root_7843 hB hC hCl hCB, root_7847 hB hC hCl hCB, root_7848 hB hC hCl hCB, root_7849 hB hC hCl hCB, root_7855 hB hC hCl hCB, root_7856 hB hC hCl hCB, root_7860 hB hC hCl hCB, root_7861 hB hC hCl hCB, root_7864 hB hC hCl hCB, root_7865 hB hC hCl hCB]

theorem root_7866 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7866) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7866_0, decode 300 d_7866_1, decode 300 d_7866_2, decode 300 d_7866_3, decode 300 d_7866_4, decode 300 d_7866_5, decode 23 d_7866_6] (fun x hx => bits_full_and hx) cov_7866 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7866_0, ch_7866_1, ch_7866_2, ch_7866_3, ch_7866_4, ch_7866_5, ch_7866_6])

theorem root_7874 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7874) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7874_0, decode 300 d_7874_1, decode 300 d_7874_2, decode 300 d_7874_3, decode 300 d_7874_4, decode 300 d_7874_5, decode 300 d_7874_6, decode 142 d_7874_7] (fun x hx => bits_full_and hx) cov_7874 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7874_0, ch_7874_1, ch_7874_2, ch_7874_3, ch_7874_4, ch_7874_5, ch_7874_6, ch_7874_7])

theorem root_7875 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7875) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7875_0, decode 300 d_7875_1, decode 300 d_7875_2, decode 300 d_7875_3, decode 300 d_7875_4, decode 300 d_7875_5, decode 300 d_7875_6, decode 142 d_7875_7] (fun x hx => bits_full_and hx) cov_7875 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7875_0, ch_7875_1, ch_7875_2, ch_7875_3, ch_7875_4, ch_7875_5, ch_7875_6, ch_7875_7])

theorem root_7878 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7878) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7878_0, decode 300 d_7878_1, decode 300 d_7878_2, decode 300 d_7878_3, decode 300 d_7878_4, decode 300 d_7878_5, decode 101 d_7878_6] (fun x hx => bits_full_and hx) cov_7878 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7878_0, ch_7878_1, ch_7878_2, ch_7878_3, ch_7878_4, ch_7878_5, ch_7878_6])

theorem root_7879 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7879) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7879_0, decode 300 d_7879_1, decode 300 d_7879_2, decode 300 d_7879_3, decode 300 d_7879_4, decode 300 d_7879_5, decode 66 d_7879_6] (fun x hx => bits_full_and hx) cov_7879 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7879_0, ch_7879_1, ch_7879_2, ch_7879_3, ch_7879_4, ch_7879_5, ch_7879_6])

theorem root_7886 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7886) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7886_0, decode 300 d_7886_1, decode 300 d_7886_2, decode 300 d_7886_3, decode 300 d_7886_4, decode 300 d_7886_5, decode 300 d_7886_6, decode 142 d_7886_7] (fun x hx => bits_full_and hx) cov_7886 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7886_0, ch_7886_1, ch_7886_2, ch_7886_3, ch_7886_4, ch_7886_5, ch_7886_6, ch_7886_7])

theorem root_7890 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7890) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7890_0, decode 300 d_7890_1, decode 300 d_7890_2, decode 300 d_7890_3, decode 300 d_7890_4, decode 300 d_7890_5, decode 300 d_7890_6, decode 141 d_7890_7] (fun x hx => bits_full_and hx) cov_7890 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7890_0, ch_7890_1, ch_7890_2, ch_7890_3, ch_7890_4, ch_7890_5, ch_7890_6, ch_7890_7])

theorem root_7894 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7894) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7894_0, decode 300 d_7894_1, decode 300 d_7894_2, decode 300 d_7894_3, decode 300 d_7894_4, decode 300 d_7894_5, decode 127 d_7894_6] (fun x hx => bits_full_and hx) cov_7894 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7894_0, ch_7894_1, ch_7894_2, ch_7894_3, ch_7894_4, ch_7894_5, ch_7894_6])

theorem root_7895 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7895) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7895_0, decode 300 d_7895_1, decode 300 d_7895_2, decode 300 d_7895_3, decode 300 d_7895_4, decode 300 d_7895_5, decode 127 d_7895_6] (fun x hx => bits_full_and hx) cov_7895 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7895_0, ch_7895_1, ch_7895_2, ch_7895_3, ch_7895_4, ch_7895_5, ch_7895_6])

theorem root_7896 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7896) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7896_0, decode 300 d_7896_1, decode 300 d_7896_2, decode 300 d_7896_3, decode 300 d_7896_4, decode 300 d_7896_5, decode 148 d_7896_6] (fun x hx => bits_full_and hx) cov_7896 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7896_0, ch_7896_1, ch_7896_2, ch_7896_3, ch_7896_4, ch_7896_5, ch_7896_6])

theorem root_7897 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7897) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7897_0, decode 300 d_7897_1, decode 300 d_7897_2, decode 300 d_7897_3, decode 300 d_7897_4, decode 300 d_7897_5, decode 148 d_7897_6] (fun x hx => bits_full_and hx) cov_7897 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7897_0, ch_7897_1, ch_7897_2, ch_7897_3, ch_7897_4, ch_7897_5, ch_7897_6])

theorem root_7904 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7904) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7904_0, decode 300 d_7904_1, decode 300 d_7904_2, decode 300 d_7904_3, decode 300 d_7904_4, decode 300 d_7904_5, decode 87 d_7904_6] (fun x hx => bits_full_and hx) cov_7904 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7904_0, ch_7904_1, ch_7904_2, ch_7904_3, ch_7904_4, ch_7904_5, ch_7904_6])

theorem root_7905 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7905) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7905_0, decode 300 d_7905_1, decode 300 d_7905_2, decode 300 d_7905_3, decode 300 d_7905_4, decode 300 d_7905_5, decode 46 d_7905_6] (fun x hx => bits_full_and hx) cov_7905 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7905_0, ch_7905_1, ch_7905_2, ch_7905_3, ch_7905_4, ch_7905_5, ch_7905_6])

theorem root_7910 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7910) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7910_0, decode 300 d_7910_1, decode 300 d_7910_2, decode 300 d_7910_3, decode 300 d_7910_4, decode 300 d_7910_5, decode 66 d_7910_6] (fun x hx => bits_full_and hx) cov_7910 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7910_0, ch_7910_1, ch_7910_2, ch_7910_3, ch_7910_4, ch_7910_5, ch_7910_6])

theorem root_7918 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7918) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7918_0, decode 300 d_7918_1, decode 300 d_7918_2, decode 300 d_7918_3, decode 300 d_7918_4, decode 300 d_7918_5, decode 300 d_7918_6, decode 142 d_7918_7] (fun x hx => bits_full_and hx) cov_7918 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7918_0, ch_7918_1, ch_7918_2, ch_7918_3, ch_7918_4, ch_7918_5, ch_7918_6, ch_7918_7])

theorem root_7920 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7920) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7920_0, decode 300 d_7920_1, decode 300 d_7920_2, decode 300 d_7920_3, decode 300 d_7920_4, decode 300 d_7920_5, decode 55 d_7920_6] (fun x hx => bits_full_and hx) cov_7920 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7920_0, ch_7920_1, ch_7920_2, ch_7920_3, ch_7920_4, ch_7920_5, ch_7920_6])

theorem root_7921 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7921) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7921_0, decode 300 d_7921_1, decode 300 d_7921_2, decode 300 d_7921_3, decode 300 d_7921_4, decode 300 d_7921_5, decode 55 d_7921_6] (fun x hx => bits_full_and hx) cov_7921 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7921_0, ch_7921_1, ch_7921_2, ch_7921_3, ch_7921_4, ch_7921_5, ch_7921_6])

theorem root_7926 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7926) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7926_0, decode 300 d_7926_1, decode 300 d_7926_2, decode 300 d_7926_3, decode 300 d_7926_4, decode 300 d_7926_5, decode 32 d_7926_6] (fun x hx => bits_full_and hx) cov_7926 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7926_0, ch_7926_1, ch_7926_2, ch_7926_3, ch_7926_4, ch_7926_5, ch_7926_6])

theorem root_7927 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7927) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7927_0, decode 300 d_7927_1, decode 300 d_7927_2, decode 300 d_7927_3, decode 300 d_7927_4, decode 300 d_7927_5, decode 32 d_7927_6] (fun x hx => bits_full_and hx) cov_7927 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7927_0, ch_7927_1, ch_7927_2, ch_7927_3, ch_7927_4, ch_7927_5, ch_7927_6])

theorem root_7928 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7928) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7928_0, decode 300 d_7928_1, decode 300 d_7928_2, decode 300 d_7928_3, decode 300 d_7928_4, decode 300 d_7928_5, decode 72 d_7928_6] (fun x hx => bits_full_and hx) cov_7928 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7928_0, ch_7928_1, ch_7928_2, ch_7928_3, ch_7928_4, ch_7928_5, ch_7928_6])

theorem root_7929 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7929) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7929_0, decode 300 d_7929_1, decode 300 d_7929_2, decode 300 d_7929_3, decode 300 d_7929_4, decode 300 d_7929_5, decode 72 d_7929_6] (fun x hx => bits_full_and hx) cov_7929 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7929_0, ch_7929_1, ch_7929_2, ch_7929_3, ch_7929_4, ch_7929_5, ch_7929_6])

theorem roots_118_ok (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    ∀ k ∈ roots_118, Claim (FULL &&& MT k) 3 := by
  intro k hk
  simp only [roots_118, List.mem_cons, List.mem_nil_iff, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [root_7866 hB hC hCl hCB, root_7874 hB hC hCl hCB, root_7875 hB hC hCl hCB, root_7878 hB hC hCl hCB, root_7879 hB hC hCl hCB, root_7886 hB hC hCl hCB, root_7890 hB hC hCl hCB, root_7894 hB hC hCl hCB, root_7895 hB hC hCl hCB, root_7896 hB hC hCl hCB, root_7897 hB hC hCl hCB, root_7904 hB hC hCl hCB, root_7905 hB hC hCl hCB, root_7910 hB hC hCl hCB, root_7918 hB hC hCl hCB, root_7920 hB hC hCl hCB, root_7921 hB hC hCl hCB, root_7926 hB hC hCl hCB, root_7927 hB hC hCl hCB, root_7928 hB hC hCl hCB, root_7929 hB hC hCl hCB]

theorem root_7934 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7934) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7934_0, decode 300 d_7934_1, decode 300 d_7934_2, decode 300 d_7934_3, decode 300 d_7934_4, decode 300 d_7934_5, decode 27 d_7934_6] (fun x hx => bits_full_and hx) cov_7934 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7934_0, ch_7934_1, ch_7934_2, ch_7934_3, ch_7934_4, ch_7934_5, ch_7934_6])

theorem root_7935 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7935) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7935_0, decode 300 d_7935_1, decode 300 d_7935_2, decode 300 d_7935_3, decode 300 d_7935_4, decode 300 d_7935_5, decode 27 d_7935_6] (fun x hx => bits_full_and hx) cov_7935 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7935_0, ch_7935_1, ch_7935_2, ch_7935_3, ch_7935_4, ch_7935_5, ch_7935_6])

theorem root_7951 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7951) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7951_0, decode 300 d_7951_1, decode 300 d_7951_2, decode 300 d_7951_3, decode 300 d_7951_4, decode 300 d_7951_5, decode 80 d_7951_6] (fun x hx => bits_full_and hx) cov_7951 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7951_0, ch_7951_1, ch_7951_2, ch_7951_3, ch_7951_4, ch_7951_5, ch_7951_6])

theorem root_7957 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7957) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7957_0, decode 300 d_7957_1, decode 300 d_7957_2, decode 300 d_7957_3, decode 300 d_7957_4, decode 300 d_7957_5, decode 80 d_7957_6] (fun x hx => bits_full_and hx) cov_7957 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7957_0, ch_7957_1, ch_7957_2, ch_7957_3, ch_7957_4, ch_7957_5, ch_7957_6])

theorem root_7963 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7963) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7963_0, decode 300 d_7963_1, decode 300 d_7963_2, decode 300 d_7963_3, decode 300 d_7963_4, decode 300 d_7963_5, decode 89 d_7963_6] (fun x hx => bits_full_and hx) cov_7963 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7963_0, ch_7963_1, ch_7963_2, ch_7963_3, ch_7963_4, ch_7963_5, ch_7963_6])

theorem root_7964 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7964) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7964_0, decode 300 d_7964_1, decode 300 d_7964_2, decode 300 d_7964_3, decode 300 d_7964_4, decode 300 d_7964_5, decode 89 d_7964_6] (fun x hx => bits_full_and hx) cov_7964 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7964_0, ch_7964_1, ch_7964_2, ch_7964_3, ch_7964_4, ch_7964_5, ch_7964_6])

theorem root_7972 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7972) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7972_0, decode 300 d_7972_1, decode 300 d_7972_2, decode 300 d_7972_3, decode 300 d_7972_4, decode 300 d_7972_5, decode 105 d_7972_6] (fun x hx => bits_full_and hx) cov_7972 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7972_0, ch_7972_1, ch_7972_2, ch_7972_3, ch_7972_4, ch_7972_5, ch_7972_6])

theorem root_7977 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7977) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7977_0, decode 300 d_7977_1, decode 300 d_7977_2, decode 300 d_7977_3, decode 300 d_7977_4, decode 300 d_7977_5, decode 105 d_7977_6] (fun x hx => bits_full_and hx) cov_7977 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7977_0, ch_7977_1, ch_7977_2, ch_7977_3, ch_7977_4, ch_7977_5, ch_7977_6])

theorem root_7995 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7995) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7995_0, decode 300 d_7995_1, decode 300 d_7995_2, decode 300 d_7995_3, decode 300 d_7995_4, decode 300 d_7995_5, decode 19 d_7995_6] (fun x hx => bits_full_and hx) cov_7995 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7995_0, ch_7995_1, ch_7995_2, ch_7995_3, ch_7995_4, ch_7995_5, ch_7995_6])

theorem root_8007 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 8007) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_8007_0, decode 300 d_8007_1, decode 300 d_8007_2, decode 300 d_8007_3, decode 300 d_8007_4, decode 300 d_8007_5, decode 19 d_8007_6] (fun x hx => bits_full_and hx) cov_8007 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_8007_0, ch_8007_1, ch_8007_2, ch_8007_3, ch_8007_4, ch_8007_5, ch_8007_6])

theorem root_8008 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 8008) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_8008_0, decode 300 d_8008_1, decode 300 d_8008_2, decode 300 d_8008_3, decode 300 d_8008_4, decode 300 d_8008_5, decode 19 d_8008_6] (fun x hx => bits_full_and hx) cov_8008 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_8008_0, ch_8008_1, ch_8008_2, ch_8008_3, ch_8008_4, ch_8008_5, ch_8008_6])

theorem roots_119_ok (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    ∀ k ∈ roots_119, Claim (FULL &&& MT k) 3 := by
  intro k hk
  simp only [roots_119, List.mem_cons, List.mem_nil_iff, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [root_7934 hB hC hCl hCB, root_7935 hB hC hCl hCB, root_7951 hB hC hCl hCB, root_7957 hB hC hCl hCB, root_7963 hB hC hCl hCB, root_7964 hB hC hCl hCB, root_7972 hB hC hCl hCB, root_7977 hB hC hCl hCB, root_7995 hB hC hCl hCB, root_8007 hB hC hCl hCB, root_8008 hB hC hCl hCB]

end LRC.O7U5
