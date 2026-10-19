import LonelyRunner.LRC.Spec.OrderSevenP2BitsN
import LonelyRunner.LRC.Spec.OrderSevenP2C10N
import LonelyRunner.LRC.Spec.OrderSevenP2C11N
import LonelyRunner.LRC.Spec.OrderSevenP2C12N
import LonelyRunner.LRC.Spec.OrderSevenP2C13N
import LonelyRunner.LRC.Spec.OrderSevenP2C14N
import LonelyRunner.LRC.Spec.OrderSevenP2C15N
import LonelyRunner.LRC.Spec.OrderSevenP2C16N
import LonelyRunner.LRC.Spec.OrderSevenP2C17N
import LonelyRunner.LRC.Spec.OrderSevenP2C18N
import LonelyRunner.LRC.Spec.OrderSevenP2C19N

set_option maxRecDepth 100000

namespace LRC.O7P2

theorem qroot_210 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 210) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_210_0, decode 300 e_210_1, decode 300 e_210_2, decode 300 e_210_3, decode 300 e_210_4, decode 300 e_210_5, decode 173 e_210_6] (fun x hx => ab_bits hx) qcov_210 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_210_0, qch_210_1, qch_210_2, qch_210_3, qch_210_4, qch_210_5, qch_210_6])

theorem qroot_211 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 211) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_211_0, decode 300 e_211_1, decode 300 e_211_2, decode 300 e_211_3, decode 300 e_211_4, decode 300 e_211_5, decode 173 e_211_6] (fun x hx => ab_bits hx) qcov_211 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_211_0, qch_211_1, qch_211_2, qch_211_3, qch_211_4, qch_211_5, qch_211_6])

theorem qroot_212 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 212) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_212_0, decode 300 e_212_1, decode 300 e_212_2, decode 300 e_212_3, decode 300 e_212_4, decode 300 e_212_5, decode 173 e_212_6] (fun x hx => ab_bits hx) qcov_212 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_212_0, qch_212_1, qch_212_2, qch_212_3, qch_212_4, qch_212_5, qch_212_6])

theorem qroot_213 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 213) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_213_0, decode 300 e_213_1, decode 300 e_213_2, decode 300 e_213_3, decode 300 e_213_4, decode 300 e_213_5, decode 173 e_213_6] (fun x hx => ab_bits hx) qcov_213 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_213_0, qch_213_1, qch_213_2, qch_213_3, qch_213_4, qch_213_5, qch_213_6])

theorem qroot_214 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 214) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_214_0, decode 300 e_214_1, decode 300 e_214_2, decode 300 e_214_3, decode 300 e_214_4, decode 300 e_214_5, decode 173 e_214_6] (fun x hx => ab_bits hx) qcov_214 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_214_0, qch_214_1, qch_214_2, qch_214_3, qch_214_4, qch_214_5, qch_214_6])

theorem qroot_215 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 215) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_215_0, decode 300 e_215_1, decode 300 e_215_2, decode 300 e_215_3, decode 300 e_215_4, decode 300 e_215_5, decode 173 e_215_6] (fun x hx => ab_bits hx) qcov_215 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_215_0, qch_215_1, qch_215_2, qch_215_3, qch_215_4, qch_215_5, qch_215_6])

theorem qroot_216 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 216) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_216_0, decode 300 e_216_1, decode 300 e_216_2, decode 300 e_216_3, decode 300 e_216_4, decode 300 e_216_5, decode 173 e_216_6] (fun x hx => ab_bits hx) qcov_216 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_216_0, qch_216_1, qch_216_2, qch_216_3, qch_216_4, qch_216_5, qch_216_6])

theorem qroot_217 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 217) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_217_0, decode 300 e_217_1, decode 300 e_217_2, decode 300 e_217_3, decode 300 e_217_4, decode 300 e_217_5, decode 173 e_217_6] (fun x hx => ab_bits hx) qcov_217 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_217_0, qch_217_1, qch_217_2, qch_217_3, qch_217_4, qch_217_5, qch_217_6])

theorem qroot_218 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 218) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_218_0, decode 300 e_218_1, decode 300 e_218_2, decode 300 e_218_3, decode 300 e_218_4, decode 300 e_218_5, decode 173 e_218_6] (fun x hx => ab_bits hx) qcov_218 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_218_0, qch_218_1, qch_218_2, qch_218_3, qch_218_4, qch_218_5, qch_218_6])

theorem qroot_219 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 219) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_219_0, decode 300 e_219_1, decode 300 e_219_2, decode 300 e_219_3, decode 300 e_219_4, decode 300 e_219_5, decode 173 e_219_6] (fun x hx => ab_bits hx) qcov_219 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_219_0, qch_219_1, qch_219_2, qch_219_3, qch_219_4, qch_219_5, qch_219_6])

theorem qroot_220 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 220) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_220_0, decode 300 e_220_1, decode 300 e_220_2, decode 300 e_220_3, decode 300 e_220_4, decode 300 e_220_5, decode 173 e_220_6] (fun x hx => ab_bits hx) qcov_220 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_220_0, qch_220_1, qch_220_2, qch_220_3, qch_220_4, qch_220_5, qch_220_6])

theorem qroot_221 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 221) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_221_0, decode 300 e_221_1, decode 300 e_221_2, decode 300 e_221_3, decode 300 e_221_4, decode 300 e_221_5, decode 173 e_221_6] (fun x hx => ab_bits hx) qcov_221 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_221_0, qch_221_1, qch_221_2, qch_221_3, qch_221_4, qch_221_5, qch_221_6])

theorem qroot_222 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 222) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_222_0, decode 300 e_222_1, decode 300 e_222_2, decode 300 e_222_3, decode 300 e_222_4, decode 300 e_222_5, decode 173 e_222_6] (fun x hx => ab_bits hx) qcov_222 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_222_0, qch_222_1, qch_222_2, qch_222_3, qch_222_4, qch_222_5, qch_222_6])

theorem qroot_223 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 223) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_223_0, decode 300 e_223_1, decode 300 e_223_2, decode 300 e_223_3, decode 300 e_223_4, decode 300 e_223_5, decode 173 e_223_6] (fun x hx => ab_bits hx) qcov_223 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_223_0, qch_223_1, qch_223_2, qch_223_3, qch_223_4, qch_223_5, qch_223_6])

theorem qroot_224 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 224) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_224_0, decode 300 e_224_1, decode 300 e_224_2, decode 300 e_224_3, decode 300 e_224_4, decode 300 e_224_5, decode 173 e_224_6] (fun x hx => ab_bits hx) qcov_224 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_224_0, qch_224_1, qch_224_2, qch_224_3, qch_224_4, qch_224_5, qch_224_6])

theorem qroot_225 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 225) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_225_0, decode 300 e_225_1, decode 300 e_225_2, decode 300 e_225_3, decode 300 e_225_4, decode 300 e_225_5, decode 173 e_225_6] (fun x hx => ab_bits hx) qcov_225 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_225_0, qch_225_1, qch_225_2, qch_225_3, qch_225_4, qch_225_5, qch_225_6])

theorem qroot_226 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 226) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_226_0, decode 300 e_226_1, decode 300 e_226_2, decode 300 e_226_3, decode 300 e_226_4, decode 300 e_226_5, decode 173 e_226_6] (fun x hx => ab_bits hx) qcov_226 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_226_0, qch_226_1, qch_226_2, qch_226_3, qch_226_4, qch_226_5, qch_226_6])

theorem qroot_227 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 227) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_227_0, decode 300 e_227_1, decode 300 e_227_2, decode 300 e_227_3, decode 300 e_227_4, decode 300 e_227_5, decode 173 e_227_6] (fun x hx => ab_bits hx) qcov_227 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_227_0, qch_227_1, qch_227_2, qch_227_3, qch_227_4, qch_227_5, qch_227_6])

theorem qroot_228 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 228) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_228_0, decode 300 e_228_1, decode 300 e_228_2, decode 300 e_228_3, decode 300 e_228_4, decode 300 e_228_5, decode 173 e_228_6] (fun x hx => ab_bits hx) qcov_228 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_228_0, qch_228_1, qch_228_2, qch_228_3, qch_228_4, qch_228_5, qch_228_6])

theorem qroot_229 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 229) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_229_0, decode 300 e_229_1, decode 300 e_229_2, decode 300 e_229_3, decode 300 e_229_4, decode 300 e_229_5, decode 173 e_229_6] (fun x hx => ab_bits hx) qcov_229 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_229_0, qch_229_1, qch_229_2, qch_229_3, qch_229_4, qch_229_5, qch_229_6])

theorem qroot_230 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 230) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_230_0, decode 300 e_230_1, decode 300 e_230_2, decode 300 e_230_3, decode 300 e_230_4, decode 300 e_230_5, decode 173 e_230_6] (fun x hx => ab_bits hx) qcov_230 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_230_0, qch_230_1, qch_230_2, qch_230_3, qch_230_4, qch_230_5, qch_230_6])

theorem qroot_231 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 231) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_231_0, decode 300 e_231_1, decode 300 e_231_2, decode 300 e_231_3, decode 300 e_231_4, decode 300 e_231_5, decode 173 e_231_6] (fun x hx => ab_bits hx) qcov_231 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_231_0, qch_231_1, qch_231_2, qch_231_3, qch_231_4, qch_231_5, qch_231_6])

theorem qroot_232 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 232) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_232_0, decode 300 e_232_1, decode 300 e_232_2, decode 300 e_232_3, decode 300 e_232_4, decode 300 e_232_5, decode 173 e_232_6] (fun x hx => ab_bits hx) qcov_232 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_232_0, qch_232_1, qch_232_2, qch_232_3, qch_232_4, qch_232_5, qch_232_6])

theorem qroot_233 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 233) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_233_0, decode 300 e_233_1, decode 300 e_233_2, decode 300 e_233_3, decode 300 e_233_4, decode 300 e_233_5, decode 173 e_233_6] (fun x hx => ab_bits hx) qcov_233 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_233_0, qch_233_1, qch_233_2, qch_233_3, qch_233_4, qch_233_5, qch_233_6])

theorem qroot_234 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 234) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_234_0, decode 300 e_234_1, decode 300 e_234_2, decode 300 e_234_3, decode 300 e_234_4, decode 300 e_234_5, decode 173 e_234_6] (fun x hx => ab_bits hx) qcov_234 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_234_0, qch_234_1, qch_234_2, qch_234_3, qch_234_4, qch_234_5, qch_234_6])

theorem qroot_235 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 235) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_235_0, decode 300 e_235_1, decode 300 e_235_2, decode 300 e_235_3, decode 300 e_235_4, decode 300 e_235_5, decode 173 e_235_6] (fun x hx => ab_bits hx) qcov_235 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_235_0, qch_235_1, qch_235_2, qch_235_3, qch_235_4, qch_235_5, qch_235_6])

theorem qroot_236 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 236) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_236_0, decode 300 e_236_1, decode 300 e_236_2, decode 300 e_236_3, decode 300 e_236_4, decode 300 e_236_5, decode 173 e_236_6] (fun x hx => ab_bits hx) qcov_236 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_236_0, qch_236_1, qch_236_2, qch_236_3, qch_236_4, qch_236_5, qch_236_6])

theorem qroot_237 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 237) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_237_0, decode 300 e_237_1, decode 300 e_237_2, decode 300 e_237_3, decode 300 e_237_4, decode 300 e_237_5, decode 173 e_237_6] (fun x hx => ab_bits hx) qcov_237 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_237_0, qch_237_1, qch_237_2, qch_237_3, qch_237_4, qch_237_5, qch_237_6])

theorem qroot_238 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 238) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_238_0, decode 300 e_238_1, decode 300 e_238_2, decode 300 e_238_3, decode 300 e_238_4, decode 300 e_238_5, decode 173 e_238_6] (fun x hx => ab_bits hx) qcov_238 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_238_0, qch_238_1, qch_238_2, qch_238_3, qch_238_4, qch_238_5, qch_238_6])

theorem qroot_239 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 239) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_239_0, decode 300 e_239_1, decode 300 e_239_2, decode 300 e_239_3, decode 300 e_239_4, decode 300 e_239_5, decode 173 e_239_6] (fun x hx => ab_bits hx) qcov_239 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_239_0, qch_239_1, qch_239_2, qch_239_3, qch_239_4, qch_239_5, qch_239_6])

theorem qroot_240 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 240) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_240_0, decode 300 e_240_1, decode 300 e_240_2, decode 300 e_240_3, decode 300 e_240_4, decode 300 e_240_5, decode 173 e_240_6] (fun x hx => ab_bits hx) qcov_240 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_240_0, qch_240_1, qch_240_2, qch_240_3, qch_240_4, qch_240_5, qch_240_6])

theorem qroot_241 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 241) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_241_0, decode 300 e_241_1, decode 300 e_241_2, decode 300 e_241_3, decode 300 e_241_4, decode 300 e_241_5, decode 173 e_241_6] (fun x hx => ab_bits hx) qcov_241 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_241_0, qch_241_1, qch_241_2, qch_241_3, qch_241_4, qch_241_5, qch_241_6])

theorem qroot_242 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 242) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_242_0, decode 300 e_242_1, decode 300 e_242_2, decode 300 e_242_3, decode 300 e_242_4, decode 300 e_242_5, decode 173 e_242_6] (fun x hx => ab_bits hx) qcov_242 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_242_0, qch_242_1, qch_242_2, qch_242_3, qch_242_4, qch_242_5, qch_242_6])

theorem qroot_243 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 243) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_243_0, decode 300 e_243_1, decode 300 e_243_2, decode 300 e_243_3, decode 300 e_243_4, decode 300 e_243_5, decode 173 e_243_6] (fun x hx => ab_bits hx) qcov_243 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_243_0, qch_243_1, qch_243_2, qch_243_3, qch_243_4, qch_243_5, qch_243_6])

theorem qroot_244 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 244) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_244_0, decode 300 e_244_1, decode 300 e_244_2, decode 300 e_244_3, decode 300 e_244_4, decode 300 e_244_5, decode 173 e_244_6] (fun x hx => ab_bits hx) qcov_244 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_244_0, qch_244_1, qch_244_2, qch_244_3, qch_244_4, qch_244_5, qch_244_6])

theorem qroot_245 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 245) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_245_0, decode 300 e_245_1, decode 300 e_245_2, decode 300 e_245_3, decode 300 e_245_4, decode 300 e_245_5, decode 173 e_245_6] (fun x hx => ab_bits hx) qcov_245 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_245_0, qch_245_1, qch_245_2, qch_245_3, qch_245_4, qch_245_5, qch_245_6])

theorem qroot_246 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 246) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_246_0, decode 300 e_246_1, decode 300 e_246_2, decode 300 e_246_3, decode 300 e_246_4, decode 300 e_246_5, decode 173 e_246_6] (fun x hx => ab_bits hx) qcov_246 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_246_0, qch_246_1, qch_246_2, qch_246_3, qch_246_4, qch_246_5, qch_246_6])

theorem qroot_247 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 247) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_247_0, decode 300 e_247_1, decode 300 e_247_2, decode 300 e_247_3, decode 300 e_247_4, decode 300 e_247_5, decode 173 e_247_6] (fun x hx => ab_bits hx) qcov_247 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_247_0, qch_247_1, qch_247_2, qch_247_3, qch_247_4, qch_247_5, qch_247_6])

theorem qroot_248 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 248) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_248_0, decode 300 e_248_1, decode 300 e_248_2, decode 300 e_248_3, decode 300 e_248_4, decode 300 e_248_5, decode 173 e_248_6] (fun x hx => ab_bits hx) qcov_248 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_248_0, qch_248_1, qch_248_2, qch_248_3, qch_248_4, qch_248_5, qch_248_6])

theorem qroot_249 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 249) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_249_0, decode 300 e_249_1, decode 300 e_249_2, decode 300 e_249_3, decode 300 e_249_4, decode 300 e_249_5, decode 173 e_249_6] (fun x hx => ab_bits hx) qcov_249 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_249_0, qch_249_1, qch_249_2, qch_249_3, qch_249_4, qch_249_5, qch_249_6])

theorem qroot_250 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 250) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_250_0, decode 300 e_250_1, decode 300 e_250_2, decode 300 e_250_3, decode 300 e_250_4, decode 300 e_250_5, decode 173 e_250_6] (fun x hx => ab_bits hx) qcov_250 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_250_0, qch_250_1, qch_250_2, qch_250_3, qch_250_4, qch_250_5, qch_250_6])

theorem qroot_251 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 251) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_251_0, decode 300 e_251_1, decode 300 e_251_2, decode 300 e_251_3, decode 300 e_251_4, decode 300 e_251_5, decode 173 e_251_6] (fun x hx => ab_bits hx) qcov_251 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_251_0, qch_251_1, qch_251_2, qch_251_3, qch_251_4, qch_251_5, qch_251_6])

theorem qroot_252 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 252) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_252_0, decode 300 e_252_1, decode 300 e_252_2, decode 300 e_252_3, decode 300 e_252_4, decode 300 e_252_5, decode 175 e_252_6] (fun x hx => ab_bits hx) qcov_252 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_252_0, qch_252_1, qch_252_2, qch_252_3, qch_252_4, qch_252_5, qch_252_6])

theorem qroot_253 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 253) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_253_0, decode 300 e_253_1, decode 300 e_253_2, decode 300 e_253_3, decode 300 e_253_4, decode 300 e_253_5, decode 175 e_253_6] (fun x hx => ab_bits hx) qcov_253 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_253_0, qch_253_1, qch_253_2, qch_253_3, qch_253_4, qch_253_5, qch_253_6])

theorem qroot_254 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 254) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_254_0, decode 300 e_254_1, decode 300 e_254_2, decode 300 e_254_3, decode 300 e_254_4, decode 300 e_254_5, decode 175 e_254_6] (fun x hx => ab_bits hx) qcov_254 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_254_0, qch_254_1, qch_254_2, qch_254_3, qch_254_4, qch_254_5, qch_254_6])

theorem qroot_255 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 255) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_255_0, decode 300 e_255_1, decode 300 e_255_2, decode 300 e_255_3, decode 300 e_255_4, decode 300 e_255_5, decode 175 e_255_6] (fun x hx => ab_bits hx) qcov_255 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_255_0, qch_255_1, qch_255_2, qch_255_3, qch_255_4, qch_255_5, qch_255_6])

theorem qroot_256 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 256) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_256_0, decode 300 e_256_1, decode 300 e_256_2, decode 300 e_256_3, decode 300 e_256_4, decode 300 e_256_5, decode 175 e_256_6] (fun x hx => ab_bits hx) qcov_256 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_256_0, qch_256_1, qch_256_2, qch_256_3, qch_256_4, qch_256_5, qch_256_6])

theorem qroot_257 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 257) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_257_0, decode 300 e_257_1, decode 300 e_257_2, decode 300 e_257_3, decode 300 e_257_4, decode 300 e_257_5, decode 175 e_257_6] (fun x hx => ab_bits hx) qcov_257 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_257_0, qch_257_1, qch_257_2, qch_257_3, qch_257_4, qch_257_5, qch_257_6])

theorem qroot_258 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 258) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_258_0, decode 300 e_258_1, decode 300 e_258_2, decode 300 e_258_3, decode 300 e_258_4, decode 300 e_258_5, decode 175 e_258_6] (fun x hx => ab_bits hx) qcov_258 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_258_0, qch_258_1, qch_258_2, qch_258_3, qch_258_4, qch_258_5, qch_258_6])

theorem qroot_259 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 259) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_259_0, decode 300 e_259_1, decode 300 e_259_2, decode 300 e_259_3, decode 300 e_259_4, decode 300 e_259_5, decode 175 e_259_6] (fun x hx => ab_bits hx) qcov_259 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_259_0, qch_259_1, qch_259_2, qch_259_3, qch_259_4, qch_259_5, qch_259_6])

theorem qroot_260 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 260) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_260_0, decode 300 e_260_1, decode 300 e_260_2, decode 300 e_260_3, decode 300 e_260_4, decode 300 e_260_5, decode 175 e_260_6] (fun x hx => ab_bits hx) qcov_260 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_260_0, qch_260_1, qch_260_2, qch_260_3, qch_260_4, qch_260_5, qch_260_6])

theorem qroot_261 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 261) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_261_0, decode 300 e_261_1, decode 300 e_261_2, decode 300 e_261_3, decode 300 e_261_4, decode 300 e_261_5, decode 175 e_261_6] (fun x hx => ab_bits hx) qcov_261 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_261_0, qch_261_1, qch_261_2, qch_261_3, qch_261_4, qch_261_5, qch_261_6])

theorem qroot_262 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 262) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_262_0, decode 300 e_262_1, decode 300 e_262_2, decode 300 e_262_3, decode 300 e_262_4, decode 300 e_262_5, decode 175 e_262_6] (fun x hx => ab_bits hx) qcov_262 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_262_0, qch_262_1, qch_262_2, qch_262_3, qch_262_4, qch_262_5, qch_262_6])

theorem qroot_263 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 263) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_263_0, decode 300 e_263_1, decode 300 e_263_2, decode 300 e_263_3, decode 300 e_263_4, decode 300 e_263_5, decode 175 e_263_6] (fun x hx => ab_bits hx) qcov_263 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_263_0, qch_263_1, qch_263_2, qch_263_3, qch_263_4, qch_263_5, qch_263_6])

theorem qroot_264 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 264) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_264_0, decode 300 e_264_1, decode 300 e_264_2, decode 300 e_264_3, decode 300 e_264_4, decode 300 e_264_5, decode 175 e_264_6] (fun x hx => ab_bits hx) qcov_264 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_264_0, qch_264_1, qch_264_2, qch_264_3, qch_264_4, qch_264_5, qch_264_6])

theorem qroot_265 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 265) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_265_0, decode 300 e_265_1, decode 300 e_265_2, decode 300 e_265_3, decode 300 e_265_4, decode 300 e_265_5, decode 175 e_265_6] (fun x hx => ab_bits hx) qcov_265 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_265_0, qch_265_1, qch_265_2, qch_265_3, qch_265_4, qch_265_5, qch_265_6])

theorem qroot_266 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 266) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_266_0, decode 300 e_266_1, decode 300 e_266_2, decode 300 e_266_3, decode 300 e_266_4, decode 300 e_266_5, decode 175 e_266_6] (fun x hx => ab_bits hx) qcov_266 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_266_0, qch_266_1, qch_266_2, qch_266_3, qch_266_4, qch_266_5, qch_266_6])

theorem qroot_267 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 267) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_267_0, decode 300 e_267_1, decode 300 e_267_2, decode 300 e_267_3, decode 300 e_267_4, decode 300 e_267_5, decode 175 e_267_6] (fun x hx => ab_bits hx) qcov_267 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_267_0, qch_267_1, qch_267_2, qch_267_3, qch_267_4, qch_267_5, qch_267_6])

theorem qroot_268 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 268) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_268_0, decode 300 e_268_1, decode 300 e_268_2, decode 300 e_268_3, decode 300 e_268_4, decode 300 e_268_5, decode 175 e_268_6] (fun x hx => ab_bits hx) qcov_268 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_268_0, qch_268_1, qch_268_2, qch_268_3, qch_268_4, qch_268_5, qch_268_6])

theorem qroot_269 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 269) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_269_0, decode 300 e_269_1, decode 300 e_269_2, decode 300 e_269_3, decode 300 e_269_4, decode 300 e_269_5, decode 175 e_269_6] (fun x hx => ab_bits hx) qcov_269 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_269_0, qch_269_1, qch_269_2, qch_269_3, qch_269_4, qch_269_5, qch_269_6])

theorem qroot_270 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 270) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_270_0, decode 300 e_270_1, decode 300 e_270_2, decode 300 e_270_3, decode 300 e_270_4, decode 300 e_270_5, decode 175 e_270_6] (fun x hx => ab_bits hx) qcov_270 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_270_0, qch_270_1, qch_270_2, qch_270_3, qch_270_4, qch_270_5, qch_270_6])

theorem qroot_271 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 271) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_271_0, decode 300 e_271_1, decode 300 e_271_2, decode 300 e_271_3, decode 300 e_271_4, decode 300 e_271_5, decode 175 e_271_6] (fun x hx => ab_bits hx) qcov_271 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_271_0, qch_271_1, qch_271_2, qch_271_3, qch_271_4, qch_271_5, qch_271_6])

theorem qroot_272 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 272) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_272_0, decode 300 e_272_1, decode 300 e_272_2, decode 300 e_272_3, decode 300 e_272_4, decode 300 e_272_5, decode 175 e_272_6] (fun x hx => ab_bits hx) qcov_272 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_272_0, qch_272_1, qch_272_2, qch_272_3, qch_272_4, qch_272_5, qch_272_6])

theorem qroot_273 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 273) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_273_0, decode 300 e_273_1, decode 300 e_273_2, decode 300 e_273_3, decode 300 e_273_4, decode 300 e_273_5, decode 175 e_273_6] (fun x hx => ab_bits hx) qcov_273 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_273_0, qch_273_1, qch_273_2, qch_273_3, qch_273_4, qch_273_5, qch_273_6])

theorem qroot_274 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 274) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_274_0, decode 300 e_274_1, decode 300 e_274_2, decode 300 e_274_3, decode 300 e_274_4, decode 300 e_274_5, decode 175 e_274_6] (fun x hx => ab_bits hx) qcov_274 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_274_0, qch_274_1, qch_274_2, qch_274_3, qch_274_4, qch_274_5, qch_274_6])

theorem qroot_275 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 275) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_275_0, decode 300 e_275_1, decode 300 e_275_2, decode 300 e_275_3, decode 300 e_275_4, decode 300 e_275_5, decode 175 e_275_6] (fun x hx => ab_bits hx) qcov_275 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_275_0, qch_275_1, qch_275_2, qch_275_3, qch_275_4, qch_275_5, qch_275_6])

theorem qroot_276 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 276) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_276_0, decode 300 e_276_1, decode 300 e_276_2, decode 300 e_276_3, decode 300 e_276_4, decode 300 e_276_5, decode 175 e_276_6] (fun x hx => ab_bits hx) qcov_276 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_276_0, qch_276_1, qch_276_2, qch_276_3, qch_276_4, qch_276_5, qch_276_6])

theorem qroot_277 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 277) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_277_0, decode 300 e_277_1, decode 300 e_277_2, decode 300 e_277_3, decode 300 e_277_4, decode 300 e_277_5, decode 175 e_277_6] (fun x hx => ab_bits hx) qcov_277 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_277_0, qch_277_1, qch_277_2, qch_277_3, qch_277_4, qch_277_5, qch_277_6])

theorem qroot_278 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 278) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_278_0, decode 300 e_278_1, decode 300 e_278_2, decode 300 e_278_3, decode 300 e_278_4, decode 300 e_278_5, decode 175 e_278_6] (fun x hx => ab_bits hx) qcov_278 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_278_0, qch_278_1, qch_278_2, qch_278_3, qch_278_4, qch_278_5, qch_278_6])

theorem qroot_279 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 279) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_279_0, decode 300 e_279_1, decode 300 e_279_2, decode 300 e_279_3, decode 300 e_279_4, decode 300 e_279_5, decode 175 e_279_6] (fun x hx => ab_bits hx) qcov_279 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_279_0, qch_279_1, qch_279_2, qch_279_3, qch_279_4, qch_279_5, qch_279_6])

theorem qroot_280 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 280) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_280_0, decode 300 e_280_1, decode 300 e_280_2, decode 300 e_280_3, decode 300 e_280_4, decode 300 e_280_5, decode 175 e_280_6] (fun x hx => ab_bits hx) qcov_280 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_280_0, qch_280_1, qch_280_2, qch_280_3, qch_280_4, qch_280_5, qch_280_6])

theorem qroot_281 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 281) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_281_0, decode 300 e_281_1, decode 300 e_281_2, decode 300 e_281_3, decode 300 e_281_4, decode 300 e_281_5, decode 175 e_281_6] (fun x hx => ab_bits hx) qcov_281 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_281_0, qch_281_1, qch_281_2, qch_281_3, qch_281_4, qch_281_5, qch_281_6])

theorem qroot_282 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 282) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_282_0, decode 300 e_282_1, decode 300 e_282_2, decode 300 e_282_3, decode 300 e_282_4, decode 300 e_282_5, decode 175 e_282_6] (fun x hx => ab_bits hx) qcov_282 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_282_0, qch_282_1, qch_282_2, qch_282_3, qch_282_4, qch_282_5, qch_282_6])

theorem qroot_283 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 283) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_283_0, decode 300 e_283_1, decode 300 e_283_2, decode 300 e_283_3, decode 300 e_283_4, decode 300 e_283_5, decode 175 e_283_6] (fun x hx => ab_bits hx) qcov_283 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_283_0, qch_283_1, qch_283_2, qch_283_3, qch_283_4, qch_283_5, qch_283_6])

theorem qroot_284 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 284) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_284_0, decode 300 e_284_1, decode 300 e_284_2, decode 300 e_284_3, decode 300 e_284_4, decode 300 e_284_5, decode 175 e_284_6] (fun x hx => ab_bits hx) qcov_284 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_284_0, qch_284_1, qch_284_2, qch_284_3, qch_284_4, qch_284_5, qch_284_6])

theorem qroot_285 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 285) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_285_0, decode 300 e_285_1, decode 300 e_285_2, decode 300 e_285_3, decode 300 e_285_4, decode 300 e_285_5, decode 175 e_285_6] (fun x hx => ab_bits hx) qcov_285 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_285_0, qch_285_1, qch_285_2, qch_285_3, qch_285_4, qch_285_5, qch_285_6])

theorem qroot_286 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 286) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_286_0, decode 300 e_286_1, decode 300 e_286_2, decode 300 e_286_3, decode 300 e_286_4, decode 300 e_286_5, decode 175 e_286_6] (fun x hx => ab_bits hx) qcov_286 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_286_0, qch_286_1, qch_286_2, qch_286_3, qch_286_4, qch_286_5, qch_286_6])

theorem qroot_287 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 287) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_287_0, decode 300 e_287_1, decode 300 e_287_2, decode 300 e_287_3, decode 300 e_287_4, decode 300 e_287_5, decode 175 e_287_6] (fun x hx => ab_bits hx) qcov_287 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_287_0, qch_287_1, qch_287_2, qch_287_3, qch_287_4, qch_287_5, qch_287_6])

theorem qroot_288 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 288) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_288_0, decode 300 e_288_1, decode 300 e_288_2, decode 300 e_288_3, decode 300 e_288_4, decode 300 e_288_5, decode 175 e_288_6] (fun x hx => ab_bits hx) qcov_288 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_288_0, qch_288_1, qch_288_2, qch_288_3, qch_288_4, qch_288_5, qch_288_6])

theorem qroot_289 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 289) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_289_0, decode 300 e_289_1, decode 300 e_289_2, decode 300 e_289_3, decode 300 e_289_4, decode 300 e_289_5, decode 175 e_289_6] (fun x hx => ab_bits hx) qcov_289 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_289_0, qch_289_1, qch_289_2, qch_289_3, qch_289_4, qch_289_5, qch_289_6])

theorem qroot_290 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 290) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_290_0, decode 300 e_290_1, decode 300 e_290_2, decode 300 e_290_3, decode 300 e_290_4, decode 300 e_290_5, decode 175 e_290_6] (fun x hx => ab_bits hx) qcov_290 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_290_0, qch_290_1, qch_290_2, qch_290_3, qch_290_4, qch_290_5, qch_290_6])

theorem qroot_291 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 291) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_291_0, decode 300 e_291_1, decode 300 e_291_2, decode 300 e_291_3, decode 300 e_291_4, decode 300 e_291_5, decode 175 e_291_6] (fun x hx => ab_bits hx) qcov_291 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_291_0, qch_291_1, qch_291_2, qch_291_3, qch_291_4, qch_291_5, qch_291_6])

theorem qroot_292 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 292) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_292_0, decode 300 e_292_1, decode 300 e_292_2, decode 300 e_292_3, decode 300 e_292_4, decode 300 e_292_5, decode 175 e_292_6] (fun x hx => ab_bits hx) qcov_292 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_292_0, qch_292_1, qch_292_2, qch_292_3, qch_292_4, qch_292_5, qch_292_6])

theorem qroot_293 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 293) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_293_0, decode 300 e_293_1, decode 300 e_293_2, decode 300 e_293_3, decode 300 e_293_4, decode 300 e_293_5, decode 175 e_293_6] (fun x hx => ab_bits hx) qcov_293 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_293_0, qch_293_1, qch_293_2, qch_293_3, qch_293_4, qch_293_5, qch_293_6])

theorem qroot_294 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 294) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_294_0, decode 300 e_294_1, decode 300 e_294_2, decode 300 e_294_3, decode 300 e_294_4, decode 300 e_294_5, decode 177 e_294_6] (fun x hx => ab_bits hx) qcov_294 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_294_0, qch_294_1, qch_294_2, qch_294_3, qch_294_4, qch_294_5, qch_294_6])

theorem qroot_295 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 295) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_295_0, decode 300 e_295_1, decode 300 e_295_2, decode 300 e_295_3, decode 300 e_295_4, decode 300 e_295_5, decode 177 e_295_6] (fun x hx => ab_bits hx) qcov_295 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_295_0, qch_295_1, qch_295_2, qch_295_3, qch_295_4, qch_295_5, qch_295_6])

theorem qroot_296 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 296) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_296_0, decode 300 e_296_1, decode 300 e_296_2, decode 300 e_296_3, decode 300 e_296_4, decode 300 e_296_5, decode 177 e_296_6] (fun x hx => ab_bits hx) qcov_296 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_296_0, qch_296_1, qch_296_2, qch_296_3, qch_296_4, qch_296_5, qch_296_6])

theorem qroot_297 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 297) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_297_0, decode 300 e_297_1, decode 300 e_297_2, decode 300 e_297_3, decode 300 e_297_4, decode 300 e_297_5, decode 177 e_297_6] (fun x hx => ab_bits hx) qcov_297 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_297_0, qch_297_1, qch_297_2, qch_297_3, qch_297_4, qch_297_5, qch_297_6])

theorem qroot_298 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 298) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_298_0, decode 300 e_298_1, decode 300 e_298_2, decode 300 e_298_3, decode 300 e_298_4, decode 300 e_298_5, decode 177 e_298_6] (fun x hx => ab_bits hx) qcov_298 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_298_0, qch_298_1, qch_298_2, qch_298_3, qch_298_4, qch_298_5, qch_298_6])

theorem qroot_299 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 299) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_299_0, decode 300 e_299_1, decode 300 e_299_2, decode 300 e_299_3, decode 300 e_299_4, decode 300 e_299_5, decode 177 e_299_6] (fun x hx => ab_bits hx) qcov_299 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_299_0, qch_299_1, qch_299_2, qch_299_3, qch_299_4, qch_299_5, qch_299_6])

theorem qroot_300 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 300) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_300_0, decode 300 e_300_1, decode 300 e_300_2, decode 300 e_300_3, decode 300 e_300_4, decode 300 e_300_5, decode 177 e_300_6] (fun x hx => ab_bits hx) qcov_300 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_300_0, qch_300_1, qch_300_2, qch_300_3, qch_300_4, qch_300_5, qch_300_6])

theorem qroot_301 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 301) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_301_0, decode 300 e_301_1, decode 300 e_301_2, decode 300 e_301_3, decode 300 e_301_4, decode 300 e_301_5, decode 177 e_301_6] (fun x hx => ab_bits hx) qcov_301 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_301_0, qch_301_1, qch_301_2, qch_301_3, qch_301_4, qch_301_5, qch_301_6])

theorem qroot_302 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 302) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_302_0, decode 300 e_302_1, decode 300 e_302_2, decode 300 e_302_3, decode 300 e_302_4, decode 300 e_302_5, decode 177 e_302_6] (fun x hx => ab_bits hx) qcov_302 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_302_0, qch_302_1, qch_302_2, qch_302_3, qch_302_4, qch_302_5, qch_302_6])

theorem qroot_303 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 303) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_303_0, decode 300 e_303_1, decode 300 e_303_2, decode 300 e_303_3, decode 300 e_303_4, decode 300 e_303_5, decode 177 e_303_6] (fun x hx => ab_bits hx) qcov_303 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_303_0, qch_303_1, qch_303_2, qch_303_3, qch_303_4, qch_303_5, qch_303_6])

theorem qroot_304 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 304) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_304_0, decode 300 e_304_1, decode 300 e_304_2, decode 300 e_304_3, decode 300 e_304_4, decode 300 e_304_5, decode 177 e_304_6] (fun x hx => ab_bits hx) qcov_304 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_304_0, qch_304_1, qch_304_2, qch_304_3, qch_304_4, qch_304_5, qch_304_6])

theorem qroot_305 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 305) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_305_0, decode 300 e_305_1, decode 300 e_305_2, decode 300 e_305_3, decode 300 e_305_4, decode 300 e_305_5, decode 177 e_305_6] (fun x hx => ab_bits hx) qcov_305 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_305_0, qch_305_1, qch_305_2, qch_305_3, qch_305_4, qch_305_5, qch_305_6])

theorem qroot_306 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 306) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_306_0, decode 300 e_306_1, decode 300 e_306_2, decode 300 e_306_3, decode 300 e_306_4, decode 300 e_306_5, decode 177 e_306_6] (fun x hx => ab_bits hx) qcov_306 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_306_0, qch_306_1, qch_306_2, qch_306_3, qch_306_4, qch_306_5, qch_306_6])

theorem qroot_307 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 307) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_307_0, decode 300 e_307_1, decode 300 e_307_2, decode 300 e_307_3, decode 300 e_307_4, decode 300 e_307_5, decode 177 e_307_6] (fun x hx => ab_bits hx) qcov_307 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_307_0, qch_307_1, qch_307_2, qch_307_3, qch_307_4, qch_307_5, qch_307_6])

theorem qroot_308 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 308) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_308_0, decode 300 e_308_1, decode 300 e_308_2, decode 300 e_308_3, decode 300 e_308_4, decode 300 e_308_5, decode 177 e_308_6] (fun x hx => ab_bits hx) qcov_308 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_308_0, qch_308_1, qch_308_2, qch_308_3, qch_308_4, qch_308_5, qch_308_6])

theorem qroot_309 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 309) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_309_0, decode 300 e_309_1, decode 300 e_309_2, decode 300 e_309_3, decode 300 e_309_4, decode 300 e_309_5, decode 177 e_309_6] (fun x hx => ab_bits hx) qcov_309 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_309_0, qch_309_1, qch_309_2, qch_309_3, qch_309_4, qch_309_5, qch_309_6])

theorem qroot_310 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 310) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_310_0, decode 300 e_310_1, decode 300 e_310_2, decode 300 e_310_3, decode 300 e_310_4, decode 300 e_310_5, decode 177 e_310_6] (fun x hx => ab_bits hx) qcov_310 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_310_0, qch_310_1, qch_310_2, qch_310_3, qch_310_4, qch_310_5, qch_310_6])

theorem qroot_311 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 311) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_311_0, decode 300 e_311_1, decode 300 e_311_2, decode 300 e_311_3, decode 300 e_311_4, decode 300 e_311_5, decode 177 e_311_6] (fun x hx => ab_bits hx) qcov_311 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_311_0, qch_311_1, qch_311_2, qch_311_3, qch_311_4, qch_311_5, qch_311_6])

theorem qroot_312 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 312) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_312_0, decode 300 e_312_1, decode 300 e_312_2, decode 300 e_312_3, decode 300 e_312_4, decode 300 e_312_5, decode 177 e_312_6] (fun x hx => ab_bits hx) qcov_312 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_312_0, qch_312_1, qch_312_2, qch_312_3, qch_312_4, qch_312_5, qch_312_6])

theorem qroot_313 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 313) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_313_0, decode 300 e_313_1, decode 300 e_313_2, decode 300 e_313_3, decode 300 e_313_4, decode 300 e_313_5, decode 177 e_313_6] (fun x hx => ab_bits hx) qcov_313 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_313_0, qch_313_1, qch_313_2, qch_313_3, qch_313_4, qch_313_5, qch_313_6])

theorem qroot_314 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 314) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_314_0, decode 300 e_314_1, decode 300 e_314_2, decode 300 e_314_3, decode 300 e_314_4, decode 300 e_314_5, decode 177 e_314_6] (fun x hx => ab_bits hx) qcov_314 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_314_0, qch_314_1, qch_314_2, qch_314_3, qch_314_4, qch_314_5, qch_314_6])

theorem qroot_315 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 315) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_315_0, decode 300 e_315_1, decode 300 e_315_2, decode 300 e_315_3, decode 300 e_315_4, decode 300 e_315_5, decode 177 e_315_6] (fun x hx => ab_bits hx) qcov_315 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_315_0, qch_315_1, qch_315_2, qch_315_3, qch_315_4, qch_315_5, qch_315_6])

theorem qroot_316 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 316) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_316_0, decode 300 e_316_1, decode 300 e_316_2, decode 300 e_316_3, decode 300 e_316_4, decode 300 e_316_5, decode 177 e_316_6] (fun x hx => ab_bits hx) qcov_316 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_316_0, qch_316_1, qch_316_2, qch_316_3, qch_316_4, qch_316_5, qch_316_6])

theorem qroot_317 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 317) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_317_0, decode 300 e_317_1, decode 300 e_317_2, decode 300 e_317_3, decode 300 e_317_4, decode 300 e_317_5, decode 177 e_317_6] (fun x hx => ab_bits hx) qcov_317 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_317_0, qch_317_1, qch_317_2, qch_317_3, qch_317_4, qch_317_5, qch_317_6])

theorem qroot_318 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 318) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_318_0, decode 300 e_318_1, decode 300 e_318_2, decode 300 e_318_3, decode 300 e_318_4, decode 300 e_318_5, decode 177 e_318_6] (fun x hx => ab_bits hx) qcov_318 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_318_0, qch_318_1, qch_318_2, qch_318_3, qch_318_4, qch_318_5, qch_318_6])

theorem qroot_319 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 319) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_319_0, decode 300 e_319_1, decode 300 e_319_2, decode 300 e_319_3, decode 300 e_319_4, decode 300 e_319_5, decode 177 e_319_6] (fun x hx => ab_bits hx) qcov_319 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_319_0, qch_319_1, qch_319_2, qch_319_3, qch_319_4, qch_319_5, qch_319_6])

theorem qroot_320 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 320) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_320_0, decode 300 e_320_1, decode 300 e_320_2, decode 300 e_320_3, decode 300 e_320_4, decode 300 e_320_5, decode 177 e_320_6] (fun x hx => ab_bits hx) qcov_320 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_320_0, qch_320_1, qch_320_2, qch_320_3, qch_320_4, qch_320_5, qch_320_6])

theorem qroot_321 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 321) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_321_0, decode 300 e_321_1, decode 300 e_321_2, decode 300 e_321_3, decode 300 e_321_4, decode 300 e_321_5, decode 177 e_321_6] (fun x hx => ab_bits hx) qcov_321 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_321_0, qch_321_1, qch_321_2, qch_321_3, qch_321_4, qch_321_5, qch_321_6])

theorem qroot_322 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 322) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_322_0, decode 300 e_322_1, decode 300 e_322_2, decode 300 e_322_3, decode 300 e_322_4, decode 300 e_322_5, decode 177 e_322_6] (fun x hx => ab_bits hx) qcov_322 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_322_0, qch_322_1, qch_322_2, qch_322_3, qch_322_4, qch_322_5, qch_322_6])

theorem qroot_323 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 323) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_323_0, decode 300 e_323_1, decode 300 e_323_2, decode 300 e_323_3, decode 300 e_323_4, decode 300 e_323_5, decode 177 e_323_6] (fun x hx => ab_bits hx) qcov_323 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_323_0, qch_323_1, qch_323_2, qch_323_3, qch_323_4, qch_323_5, qch_323_6])

theorem qroot_324 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 324) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_324_0, decode 300 e_324_1, decode 300 e_324_2, decode 300 e_324_3, decode 300 e_324_4, decode 300 e_324_5, decode 177 e_324_6] (fun x hx => ab_bits hx) qcov_324 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_324_0, qch_324_1, qch_324_2, qch_324_3, qch_324_4, qch_324_5, qch_324_6])

theorem qroot_325 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 325) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_325_0, decode 300 e_325_1, decode 300 e_325_2, decode 300 e_325_3, decode 300 e_325_4, decode 300 e_325_5, decode 177 e_325_6] (fun x hx => ab_bits hx) qcov_325 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_325_0, qch_325_1, qch_325_2, qch_325_3, qch_325_4, qch_325_5, qch_325_6])

theorem qroot_326 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 326) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_326_0, decode 300 e_326_1, decode 300 e_326_2, decode 300 e_326_3, decode 300 e_326_4, decode 300 e_326_5, decode 177 e_326_6] (fun x hx => ab_bits hx) qcov_326 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_326_0, qch_326_1, qch_326_2, qch_326_3, qch_326_4, qch_326_5, qch_326_6])

theorem qroot_327 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 327) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_327_0, decode 300 e_327_1, decode 300 e_327_2, decode 300 e_327_3, decode 300 e_327_4, decode 300 e_327_5, decode 177 e_327_6] (fun x hx => ab_bits hx) qcov_327 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_327_0, qch_327_1, qch_327_2, qch_327_3, qch_327_4, qch_327_5, qch_327_6])

theorem qroot_328 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 328) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_328_0, decode 300 e_328_1, decode 300 e_328_2, decode 300 e_328_3, decode 300 e_328_4, decode 300 e_328_5, decode 177 e_328_6] (fun x hx => ab_bits hx) qcov_328 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_328_0, qch_328_1, qch_328_2, qch_328_3, qch_328_4, qch_328_5, qch_328_6])

theorem qroot_329 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 329) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_329_0, decode 300 e_329_1, decode 300 e_329_2, decode 300 e_329_3, decode 300 e_329_4, decode 300 e_329_5, decode 177 e_329_6] (fun x hx => ab_bits hx) qcov_329 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_329_0, qch_329_1, qch_329_2, qch_329_3, qch_329_4, qch_329_5, qch_329_6])

theorem qroot_330 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 330) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_330_0, decode 300 e_330_1, decode 300 e_330_2, decode 300 e_330_3, decode 300 e_330_4, decode 300 e_330_5, decode 177 e_330_6] (fun x hx => ab_bits hx) qcov_330 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_330_0, qch_330_1, qch_330_2, qch_330_3, qch_330_4, qch_330_5, qch_330_6])

theorem qroot_331 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 331) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_331_0, decode 300 e_331_1, decode 300 e_331_2, decode 300 e_331_3, decode 300 e_331_4, decode 300 e_331_5, decode 177 e_331_6] (fun x hx => ab_bits hx) qcov_331 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_331_0, qch_331_1, qch_331_2, qch_331_3, qch_331_4, qch_331_5, qch_331_6])

theorem qroot_332 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 332) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_332_0, decode 300 e_332_1, decode 300 e_332_2, decode 300 e_332_3, decode 300 e_332_4, decode 300 e_332_5, decode 177 e_332_6] (fun x hx => ab_bits hx) qcov_332 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_332_0, qch_332_1, qch_332_2, qch_332_3, qch_332_4, qch_332_5, qch_332_6])

theorem qroot_333 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 333) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_333_0, decode 300 e_333_1, decode 300 e_333_2, decode 300 e_333_3, decode 300 e_333_4, decode 300 e_333_5, decode 177 e_333_6] (fun x hx => ab_bits hx) qcov_333 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_333_0, qch_333_1, qch_333_2, qch_333_3, qch_333_4, qch_333_5, qch_333_6])

theorem qroot_334 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 334) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_334_0, decode 300 e_334_1, decode 300 e_334_2, decode 300 e_334_3, decode 300 e_334_4, decode 300 e_334_5, decode 177 e_334_6] (fun x hx => ab_bits hx) qcov_334 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_334_0, qch_334_1, qch_334_2, qch_334_3, qch_334_4, qch_334_5, qch_334_6])

theorem qroot_335 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 335) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_335_0, decode 300 e_335_1, decode 300 e_335_2, decode 300 e_335_3, decode 300 e_335_4, decode 300 e_335_5, decode 177 e_335_6] (fun x hx => ab_bits hx) qcov_335 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_335_0, qch_335_1, qch_335_2, qch_335_3, qch_335_4, qch_335_5, qch_335_6])

theorem qroot_336 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 336) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_336_0, decode 300 e_336_1, decode 300 e_336_2, decode 300 e_336_3, decode 300 e_336_4, decode 300 e_336_5, decode 174 e_336_6] (fun x hx => ab_bits hx) qcov_336 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_336_0, qch_336_1, qch_336_2, qch_336_3, qch_336_4, qch_336_5, qch_336_6])

theorem qroot_337 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 337) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_337_0, decode 300 e_337_1, decode 300 e_337_2, decode 300 e_337_3, decode 300 e_337_4, decode 300 e_337_5, decode 174 e_337_6] (fun x hx => ab_bits hx) qcov_337 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_337_0, qch_337_1, qch_337_2, qch_337_3, qch_337_4, qch_337_5, qch_337_6])

theorem qroot_338 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 338) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_338_0, decode 300 e_338_1, decode 300 e_338_2, decode 300 e_338_3, decode 300 e_338_4, decode 300 e_338_5, decode 174 e_338_6] (fun x hx => ab_bits hx) qcov_338 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_338_0, qch_338_1, qch_338_2, qch_338_3, qch_338_4, qch_338_5, qch_338_6])

theorem qroot_339 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 339) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_339_0, decode 300 e_339_1, decode 300 e_339_2, decode 300 e_339_3, decode 300 e_339_4, decode 300 e_339_5, decode 174 e_339_6] (fun x hx => ab_bits hx) qcov_339 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_339_0, qch_339_1, qch_339_2, qch_339_3, qch_339_4, qch_339_5, qch_339_6])

theorem qroot_340 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 340) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_340_0, decode 300 e_340_1, decode 300 e_340_2, decode 300 e_340_3, decode 300 e_340_4, decode 300 e_340_5, decode 174 e_340_6] (fun x hx => ab_bits hx) qcov_340 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_340_0, qch_340_1, qch_340_2, qch_340_3, qch_340_4, qch_340_5, qch_340_6])

theorem qroot_341 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 341) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_341_0, decode 300 e_341_1, decode 300 e_341_2, decode 300 e_341_3, decode 300 e_341_4, decode 300 e_341_5, decode 174 e_341_6] (fun x hx => ab_bits hx) qcov_341 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_341_0, qch_341_1, qch_341_2, qch_341_3, qch_341_4, qch_341_5, qch_341_6])

theorem qroot_342 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 342) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_342_0, decode 300 e_342_1, decode 300 e_342_2, decode 300 e_342_3, decode 300 e_342_4, decode 300 e_342_5, decode 174 e_342_6] (fun x hx => ab_bits hx) qcov_342 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_342_0, qch_342_1, qch_342_2, qch_342_3, qch_342_4, qch_342_5, qch_342_6])

theorem qroot_343 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 343) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_343_0, decode 300 e_343_1, decode 300 e_343_2, decode 300 e_343_3, decode 300 e_343_4, decode 300 e_343_5, decode 174 e_343_6] (fun x hx => ab_bits hx) qcov_343 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_343_0, qch_343_1, qch_343_2, qch_343_3, qch_343_4, qch_343_5, qch_343_6])

theorem qroot_344 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 344) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_344_0, decode 300 e_344_1, decode 300 e_344_2, decode 300 e_344_3, decode 300 e_344_4, decode 300 e_344_5, decode 174 e_344_6] (fun x hx => ab_bits hx) qcov_344 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_344_0, qch_344_1, qch_344_2, qch_344_3, qch_344_4, qch_344_5, qch_344_6])

theorem qroot_345 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 345) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_345_0, decode 300 e_345_1, decode 300 e_345_2, decode 300 e_345_3, decode 300 e_345_4, decode 300 e_345_5, decode 174 e_345_6] (fun x hx => ab_bits hx) qcov_345 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_345_0, qch_345_1, qch_345_2, qch_345_3, qch_345_4, qch_345_5, qch_345_6])

theorem qroot_346 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 346) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_346_0, decode 300 e_346_1, decode 300 e_346_2, decode 300 e_346_3, decode 300 e_346_4, decode 300 e_346_5, decode 174 e_346_6] (fun x hx => ab_bits hx) qcov_346 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_346_0, qch_346_1, qch_346_2, qch_346_3, qch_346_4, qch_346_5, qch_346_6])

theorem qroot_347 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 347) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_347_0, decode 300 e_347_1, decode 300 e_347_2, decode 300 e_347_3, decode 300 e_347_4, decode 300 e_347_5, decode 174 e_347_6] (fun x hx => ab_bits hx) qcov_347 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_347_0, qch_347_1, qch_347_2, qch_347_3, qch_347_4, qch_347_5, qch_347_6])

theorem qroot_348 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 348) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_348_0, decode 300 e_348_1, decode 300 e_348_2, decode 300 e_348_3, decode 300 e_348_4, decode 300 e_348_5, decode 174 e_348_6] (fun x hx => ab_bits hx) qcov_348 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_348_0, qch_348_1, qch_348_2, qch_348_3, qch_348_4, qch_348_5, qch_348_6])

theorem qroot_349 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 349) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_349_0, decode 300 e_349_1, decode 300 e_349_2, decode 300 e_349_3, decode 300 e_349_4, decode 300 e_349_5, decode 174 e_349_6] (fun x hx => ab_bits hx) qcov_349 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_349_0, qch_349_1, qch_349_2, qch_349_3, qch_349_4, qch_349_5, qch_349_6])

theorem qroot_350 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 350) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_350_0, decode 300 e_350_1, decode 300 e_350_2, decode 300 e_350_3, decode 300 e_350_4, decode 300 e_350_5, decode 174 e_350_6] (fun x hx => ab_bits hx) qcov_350 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_350_0, qch_350_1, qch_350_2, qch_350_3, qch_350_4, qch_350_5, qch_350_6])

theorem qroot_351 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 351) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_351_0, decode 300 e_351_1, decode 300 e_351_2, decode 300 e_351_3, decode 300 e_351_4, decode 300 e_351_5, decode 174 e_351_6] (fun x hx => ab_bits hx) qcov_351 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_351_0, qch_351_1, qch_351_2, qch_351_3, qch_351_4, qch_351_5, qch_351_6])

theorem qroot_352 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 352) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_352_0, decode 300 e_352_1, decode 300 e_352_2, decode 300 e_352_3, decode 300 e_352_4, decode 300 e_352_5, decode 174 e_352_6] (fun x hx => ab_bits hx) qcov_352 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_352_0, qch_352_1, qch_352_2, qch_352_3, qch_352_4, qch_352_5, qch_352_6])

theorem qroot_353 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 353) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_353_0, decode 300 e_353_1, decode 300 e_353_2, decode 300 e_353_3, decode 300 e_353_4, decode 300 e_353_5, decode 174 e_353_6] (fun x hx => ab_bits hx) qcov_353 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_353_0, qch_353_1, qch_353_2, qch_353_3, qch_353_4, qch_353_5, qch_353_6])

theorem qroot_354 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 354) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_354_0, decode 300 e_354_1, decode 300 e_354_2, decode 300 e_354_3, decode 300 e_354_4, decode 300 e_354_5, decode 174 e_354_6] (fun x hx => ab_bits hx) qcov_354 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_354_0, qch_354_1, qch_354_2, qch_354_3, qch_354_4, qch_354_5, qch_354_6])

theorem qroot_355 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 355) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_355_0, decode 300 e_355_1, decode 300 e_355_2, decode 300 e_355_3, decode 300 e_355_4, decode 300 e_355_5, decode 174 e_355_6] (fun x hx => ab_bits hx) qcov_355 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_355_0, qch_355_1, qch_355_2, qch_355_3, qch_355_4, qch_355_5, qch_355_6])

theorem qroot_356 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 356) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_356_0, decode 300 e_356_1, decode 300 e_356_2, decode 300 e_356_3, decode 300 e_356_4, decode 300 e_356_5, decode 174 e_356_6] (fun x hx => ab_bits hx) qcov_356 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_356_0, qch_356_1, qch_356_2, qch_356_3, qch_356_4, qch_356_5, qch_356_6])

theorem qroot_357 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 357) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_357_0, decode 300 e_357_1, decode 300 e_357_2, decode 300 e_357_3, decode 300 e_357_4, decode 300 e_357_5, decode 174 e_357_6] (fun x hx => ab_bits hx) qcov_357 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_357_0, qch_357_1, qch_357_2, qch_357_3, qch_357_4, qch_357_5, qch_357_6])

theorem qroot_358 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 358) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_358_0, decode 300 e_358_1, decode 300 e_358_2, decode 300 e_358_3, decode 300 e_358_4, decode 300 e_358_5, decode 174 e_358_6] (fun x hx => ab_bits hx) qcov_358 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_358_0, qch_358_1, qch_358_2, qch_358_3, qch_358_4, qch_358_5, qch_358_6])

theorem qroot_359 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 359) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_359_0, decode 300 e_359_1, decode 300 e_359_2, decode 300 e_359_3, decode 300 e_359_4, decode 300 e_359_5, decode 174 e_359_6] (fun x hx => ab_bits hx) qcov_359 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_359_0, qch_359_1, qch_359_2, qch_359_3, qch_359_4, qch_359_5, qch_359_6])

theorem qroot_360 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 360) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_360_0, decode 300 e_360_1, decode 300 e_360_2, decode 300 e_360_3, decode 300 e_360_4, decode 300 e_360_5, decode 174 e_360_6] (fun x hx => ab_bits hx) qcov_360 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_360_0, qch_360_1, qch_360_2, qch_360_3, qch_360_4, qch_360_5, qch_360_6])

theorem qroot_361 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 361) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_361_0, decode 300 e_361_1, decode 300 e_361_2, decode 300 e_361_3, decode 300 e_361_4, decode 300 e_361_5, decode 174 e_361_6] (fun x hx => ab_bits hx) qcov_361 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_361_0, qch_361_1, qch_361_2, qch_361_3, qch_361_4, qch_361_5, qch_361_6])

theorem qroot_362 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 362) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_362_0, decode 300 e_362_1, decode 300 e_362_2, decode 300 e_362_3, decode 300 e_362_4, decode 300 e_362_5, decode 174 e_362_6] (fun x hx => ab_bits hx) qcov_362 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_362_0, qch_362_1, qch_362_2, qch_362_3, qch_362_4, qch_362_5, qch_362_6])

theorem qroot_363 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 363) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_363_0, decode 300 e_363_1, decode 300 e_363_2, decode 300 e_363_3, decode 300 e_363_4, decode 300 e_363_5, decode 174 e_363_6] (fun x hx => ab_bits hx) qcov_363 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_363_0, qch_363_1, qch_363_2, qch_363_3, qch_363_4, qch_363_5, qch_363_6])

theorem qroot_364 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 364) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_364_0, decode 300 e_364_1, decode 300 e_364_2, decode 300 e_364_3, decode 300 e_364_4, decode 300 e_364_5, decode 174 e_364_6] (fun x hx => ab_bits hx) qcov_364 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_364_0, qch_364_1, qch_364_2, qch_364_3, qch_364_4, qch_364_5, qch_364_6])

theorem qroot_365 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 365) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_365_0, decode 300 e_365_1, decode 300 e_365_2, decode 300 e_365_3, decode 300 e_365_4, decode 300 e_365_5, decode 174 e_365_6] (fun x hx => ab_bits hx) qcov_365 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_365_0, qch_365_1, qch_365_2, qch_365_3, qch_365_4, qch_365_5, qch_365_6])

theorem qroot_366 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 366) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_366_0, decode 300 e_366_1, decode 300 e_366_2, decode 300 e_366_3, decode 300 e_366_4, decode 300 e_366_5, decode 174 e_366_6] (fun x hx => ab_bits hx) qcov_366 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_366_0, qch_366_1, qch_366_2, qch_366_3, qch_366_4, qch_366_5, qch_366_6])

theorem qroot_367 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 367) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_367_0, decode 300 e_367_1, decode 300 e_367_2, decode 300 e_367_3, decode 300 e_367_4, decode 300 e_367_5, decode 174 e_367_6] (fun x hx => ab_bits hx) qcov_367 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_367_0, qch_367_1, qch_367_2, qch_367_3, qch_367_4, qch_367_5, qch_367_6])

theorem qroot_368 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 368) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_368_0, decode 300 e_368_1, decode 300 e_368_2, decode 300 e_368_3, decode 300 e_368_4, decode 300 e_368_5, decode 174 e_368_6] (fun x hx => ab_bits hx) qcov_368 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_368_0, qch_368_1, qch_368_2, qch_368_3, qch_368_4, qch_368_5, qch_368_6])

theorem qroot_369 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 369) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_369_0, decode 300 e_369_1, decode 300 e_369_2, decode 300 e_369_3, decode 300 e_369_4, decode 300 e_369_5, decode 174 e_369_6] (fun x hx => ab_bits hx) qcov_369 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_369_0, qch_369_1, qch_369_2, qch_369_3, qch_369_4, qch_369_5, qch_369_6])

theorem qroot_370 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 370) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_370_0, decode 300 e_370_1, decode 300 e_370_2, decode 300 e_370_3, decode 300 e_370_4, decode 300 e_370_5, decode 174 e_370_6] (fun x hx => ab_bits hx) qcov_370 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_370_0, qch_370_1, qch_370_2, qch_370_3, qch_370_4, qch_370_5, qch_370_6])

theorem qroot_371 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 371) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_371_0, decode 300 e_371_1, decode 300 e_371_2, decode 300 e_371_3, decode 300 e_371_4, decode 300 e_371_5, decode 174 e_371_6] (fun x hx => ab_bits hx) qcov_371 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_371_0, qch_371_1, qch_371_2, qch_371_3, qch_371_4, qch_371_5, qch_371_6])

theorem qroot_372 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 372) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_372_0, decode 300 e_372_1, decode 300 e_372_2, decode 300 e_372_3, decode 300 e_372_4, decode 300 e_372_5, decode 174 e_372_6] (fun x hx => ab_bits hx) qcov_372 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_372_0, qch_372_1, qch_372_2, qch_372_3, qch_372_4, qch_372_5, qch_372_6])

theorem qroot_373 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 373) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_373_0, decode 300 e_373_1, decode 300 e_373_2, decode 300 e_373_3, decode 300 e_373_4, decode 300 e_373_5, decode 174 e_373_6] (fun x hx => ab_bits hx) qcov_373 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_373_0, qch_373_1, qch_373_2, qch_373_3, qch_373_4, qch_373_5, qch_373_6])

theorem qroot_374 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 374) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_374_0, decode 300 e_374_1, decode 300 e_374_2, decode 300 e_374_3, decode 300 e_374_4, decode 300 e_374_5, decode 174 e_374_6] (fun x hx => ab_bits hx) qcov_374 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_374_0, qch_374_1, qch_374_2, qch_374_3, qch_374_4, qch_374_5, qch_374_6])

theorem qroot_375 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 375) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_375_0, decode 300 e_375_1, decode 300 e_375_2, decode 300 e_375_3, decode 300 e_375_4, decode 300 e_375_5, decode 174 e_375_6] (fun x hx => ab_bits hx) qcov_375 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_375_0, qch_375_1, qch_375_2, qch_375_3, qch_375_4, qch_375_5, qch_375_6])

theorem qroot_376 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 376) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_376_0, decode 300 e_376_1, decode 300 e_376_2, decode 300 e_376_3, decode 300 e_376_4, decode 300 e_376_5, decode 174 e_376_6] (fun x hx => ab_bits hx) qcov_376 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_376_0, qch_376_1, qch_376_2, qch_376_3, qch_376_4, qch_376_5, qch_376_6])

theorem qroot_377 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 377) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_377_0, decode 300 e_377_1, decode 300 e_377_2, decode 300 e_377_3, decode 300 e_377_4, decode 300 e_377_5, decode 174 e_377_6] (fun x hx => ab_bits hx) qcov_377 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_377_0, qch_377_1, qch_377_2, qch_377_3, qch_377_4, qch_377_5, qch_377_6])

theorem qroot_378 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 378) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_378_0, decode 300 e_378_1, decode 300 e_378_2, decode 300 e_378_3, decode 300 e_378_4, decode 300 e_378_5, decode 171 e_378_6] (fun x hx => ab_bits hx) qcov_378 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_378_0, qch_378_1, qch_378_2, qch_378_3, qch_378_4, qch_378_5, qch_378_6])

theorem qroot_379 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 379) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_379_0, decode 300 e_379_1, decode 300 e_379_2, decode 300 e_379_3, decode 300 e_379_4, decode 300 e_379_5, decode 171 e_379_6] (fun x hx => ab_bits hx) qcov_379 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_379_0, qch_379_1, qch_379_2, qch_379_3, qch_379_4, qch_379_5, qch_379_6])

theorem qroot_380 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 380) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_380_0, decode 300 e_380_1, decode 300 e_380_2, decode 300 e_380_3, decode 300 e_380_4, decode 300 e_380_5, decode 171 e_380_6] (fun x hx => ab_bits hx) qcov_380 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_380_0, qch_380_1, qch_380_2, qch_380_3, qch_380_4, qch_380_5, qch_380_6])

theorem qroot_381 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 381) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_381_0, decode 300 e_381_1, decode 300 e_381_2, decode 300 e_381_3, decode 300 e_381_4, decode 300 e_381_5, decode 171 e_381_6] (fun x hx => ab_bits hx) qcov_381 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_381_0, qch_381_1, qch_381_2, qch_381_3, qch_381_4, qch_381_5, qch_381_6])

theorem qroot_382 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 382) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_382_0, decode 300 e_382_1, decode 300 e_382_2, decode 300 e_382_3, decode 300 e_382_4, decode 300 e_382_5, decode 171 e_382_6] (fun x hx => ab_bits hx) qcov_382 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_382_0, qch_382_1, qch_382_2, qch_382_3, qch_382_4, qch_382_5, qch_382_6])

theorem qroot_383 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 383) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_383_0, decode 300 e_383_1, decode 300 e_383_2, decode 300 e_383_3, decode 300 e_383_4, decode 300 e_383_5, decode 171 e_383_6] (fun x hx => ab_bits hx) qcov_383 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_383_0, qch_383_1, qch_383_2, qch_383_3, qch_383_4, qch_383_5, qch_383_6])

theorem qroot_384 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 384) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_384_0, decode 300 e_384_1, decode 300 e_384_2, decode 300 e_384_3, decode 300 e_384_4, decode 300 e_384_5, decode 171 e_384_6] (fun x hx => ab_bits hx) qcov_384 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_384_0, qch_384_1, qch_384_2, qch_384_3, qch_384_4, qch_384_5, qch_384_6])

theorem qroot_385 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 385) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_385_0, decode 300 e_385_1, decode 300 e_385_2, decode 300 e_385_3, decode 300 e_385_4, decode 300 e_385_5, decode 171 e_385_6] (fun x hx => ab_bits hx) qcov_385 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_385_0, qch_385_1, qch_385_2, qch_385_3, qch_385_4, qch_385_5, qch_385_6])

theorem qroot_386 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 386) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_386_0, decode 300 e_386_1, decode 300 e_386_2, decode 300 e_386_3, decode 300 e_386_4, decode 300 e_386_5, decode 171 e_386_6] (fun x hx => ab_bits hx) qcov_386 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_386_0, qch_386_1, qch_386_2, qch_386_3, qch_386_4, qch_386_5, qch_386_6])

theorem qroot_387 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 387) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_387_0, decode 300 e_387_1, decode 300 e_387_2, decode 300 e_387_3, decode 300 e_387_4, decode 300 e_387_5, decode 171 e_387_6] (fun x hx => ab_bits hx) qcov_387 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_387_0, qch_387_1, qch_387_2, qch_387_3, qch_387_4, qch_387_5, qch_387_6])

theorem qroot_388 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 388) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_388_0, decode 300 e_388_1, decode 300 e_388_2, decode 300 e_388_3, decode 300 e_388_4, decode 300 e_388_5, decode 171 e_388_6] (fun x hx => ab_bits hx) qcov_388 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_388_0, qch_388_1, qch_388_2, qch_388_3, qch_388_4, qch_388_5, qch_388_6])

theorem qroot_389 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 389) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_389_0, decode 300 e_389_1, decode 300 e_389_2, decode 300 e_389_3, decode 300 e_389_4, decode 300 e_389_5, decode 171 e_389_6] (fun x hx => ab_bits hx) qcov_389 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_389_0, qch_389_1, qch_389_2, qch_389_3, qch_389_4, qch_389_5, qch_389_6])

theorem qroot_390 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 390) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_390_0, decode 300 e_390_1, decode 300 e_390_2, decode 300 e_390_3, decode 300 e_390_4, decode 300 e_390_5, decode 171 e_390_6] (fun x hx => ab_bits hx) qcov_390 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_390_0, qch_390_1, qch_390_2, qch_390_3, qch_390_4, qch_390_5, qch_390_6])

theorem qroot_391 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 391) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_391_0, decode 300 e_391_1, decode 300 e_391_2, decode 300 e_391_3, decode 300 e_391_4, decode 300 e_391_5, decode 171 e_391_6] (fun x hx => ab_bits hx) qcov_391 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_391_0, qch_391_1, qch_391_2, qch_391_3, qch_391_4, qch_391_5, qch_391_6])

theorem qroot_392 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 392) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_392_0, decode 300 e_392_1, decode 300 e_392_2, decode 300 e_392_3, decode 300 e_392_4, decode 300 e_392_5, decode 171 e_392_6] (fun x hx => ab_bits hx) qcov_392 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_392_0, qch_392_1, qch_392_2, qch_392_3, qch_392_4, qch_392_5, qch_392_6])

theorem qroot_393 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 393) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_393_0, decode 300 e_393_1, decode 300 e_393_2, decode 300 e_393_3, decode 300 e_393_4, decode 300 e_393_5, decode 171 e_393_6] (fun x hx => ab_bits hx) qcov_393 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_393_0, qch_393_1, qch_393_2, qch_393_3, qch_393_4, qch_393_5, qch_393_6])

theorem qroot_394 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 394) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_394_0, decode 300 e_394_1, decode 300 e_394_2, decode 300 e_394_3, decode 300 e_394_4, decode 300 e_394_5, decode 171 e_394_6] (fun x hx => ab_bits hx) qcov_394 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_394_0, qch_394_1, qch_394_2, qch_394_3, qch_394_4, qch_394_5, qch_394_6])

theorem qroot_395 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 395) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_395_0, decode 300 e_395_1, decode 300 e_395_2, decode 300 e_395_3, decode 300 e_395_4, decode 300 e_395_5, decode 171 e_395_6] (fun x hx => ab_bits hx) qcov_395 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_395_0, qch_395_1, qch_395_2, qch_395_3, qch_395_4, qch_395_5, qch_395_6])

theorem qroot_396 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 396) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_396_0, decode 300 e_396_1, decode 300 e_396_2, decode 300 e_396_3, decode 300 e_396_4, decode 300 e_396_5, decode 171 e_396_6] (fun x hx => ab_bits hx) qcov_396 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_396_0, qch_396_1, qch_396_2, qch_396_3, qch_396_4, qch_396_5, qch_396_6])

theorem qroot_397 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 397) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_397_0, decode 300 e_397_1, decode 300 e_397_2, decode 300 e_397_3, decode 300 e_397_4, decode 300 e_397_5, decode 171 e_397_6] (fun x hx => ab_bits hx) qcov_397 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_397_0, qch_397_1, qch_397_2, qch_397_3, qch_397_4, qch_397_5, qch_397_6])

theorem qroot_398 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 398) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_398_0, decode 300 e_398_1, decode 300 e_398_2, decode 300 e_398_3, decode 300 e_398_4, decode 300 e_398_5, decode 171 e_398_6] (fun x hx => ab_bits hx) qcov_398 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_398_0, qch_398_1, qch_398_2, qch_398_3, qch_398_4, qch_398_5, qch_398_6])

theorem qroot_399 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 399) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_399_0, decode 300 e_399_1, decode 300 e_399_2, decode 300 e_399_3, decode 300 e_399_4, decode 300 e_399_5, decode 171 e_399_6] (fun x hx => ab_bits hx) qcov_399 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_399_0, qch_399_1, qch_399_2, qch_399_3, qch_399_4, qch_399_5, qch_399_6])

theorem qroot_400 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 400) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_400_0, decode 300 e_400_1, decode 300 e_400_2, decode 300 e_400_3, decode 300 e_400_4, decode 300 e_400_5, decode 171 e_400_6] (fun x hx => ab_bits hx) qcov_400 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_400_0, qch_400_1, qch_400_2, qch_400_3, qch_400_4, qch_400_5, qch_400_6])

theorem qroot_401 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 401) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_401_0, decode 300 e_401_1, decode 300 e_401_2, decode 300 e_401_3, decode 300 e_401_4, decode 300 e_401_5, decode 171 e_401_6] (fun x hx => ab_bits hx) qcov_401 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_401_0, qch_401_1, qch_401_2, qch_401_3, qch_401_4, qch_401_5, qch_401_6])

theorem qroot_402 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 402) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_402_0, decode 300 e_402_1, decode 300 e_402_2, decode 300 e_402_3, decode 300 e_402_4, decode 300 e_402_5, decode 171 e_402_6] (fun x hx => ab_bits hx) qcov_402 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_402_0, qch_402_1, qch_402_2, qch_402_3, qch_402_4, qch_402_5, qch_402_6])

theorem qroot_403 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 403) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_403_0, decode 300 e_403_1, decode 300 e_403_2, decode 300 e_403_3, decode 300 e_403_4, decode 300 e_403_5, decode 171 e_403_6] (fun x hx => ab_bits hx) qcov_403 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_403_0, qch_403_1, qch_403_2, qch_403_3, qch_403_4, qch_403_5, qch_403_6])

theorem qroot_404 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 404) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_404_0, decode 300 e_404_1, decode 300 e_404_2, decode 300 e_404_3, decode 300 e_404_4, decode 300 e_404_5, decode 171 e_404_6] (fun x hx => ab_bits hx) qcov_404 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_404_0, qch_404_1, qch_404_2, qch_404_3, qch_404_4, qch_404_5, qch_404_6])

theorem qroot_405 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 405) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_405_0, decode 300 e_405_1, decode 300 e_405_2, decode 300 e_405_3, decode 300 e_405_4, decode 300 e_405_5, decode 171 e_405_6] (fun x hx => ab_bits hx) qcov_405 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_405_0, qch_405_1, qch_405_2, qch_405_3, qch_405_4, qch_405_5, qch_405_6])

theorem qroot_406 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 406) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_406_0, decode 300 e_406_1, decode 300 e_406_2, decode 300 e_406_3, decode 300 e_406_4, decode 300 e_406_5, decode 171 e_406_6] (fun x hx => ab_bits hx) qcov_406 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_406_0, qch_406_1, qch_406_2, qch_406_3, qch_406_4, qch_406_5, qch_406_6])

theorem qroot_407 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 407) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_407_0, decode 300 e_407_1, decode 300 e_407_2, decode 300 e_407_3, decode 300 e_407_4, decode 300 e_407_5, decode 171 e_407_6] (fun x hx => ab_bits hx) qcov_407 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_407_0, qch_407_1, qch_407_2, qch_407_3, qch_407_4, qch_407_5, qch_407_6])

theorem qroot_408 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 408) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_408_0, decode 300 e_408_1, decode 300 e_408_2, decode 300 e_408_3, decode 300 e_408_4, decode 300 e_408_5, decode 171 e_408_6] (fun x hx => ab_bits hx) qcov_408 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_408_0, qch_408_1, qch_408_2, qch_408_3, qch_408_4, qch_408_5, qch_408_6])

theorem qroot_409 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 409) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_409_0, decode 300 e_409_1, decode 300 e_409_2, decode 300 e_409_3, decode 300 e_409_4, decode 300 e_409_5, decode 171 e_409_6] (fun x hx => ab_bits hx) qcov_409 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_409_0, qch_409_1, qch_409_2, qch_409_3, qch_409_4, qch_409_5, qch_409_6])

theorem qroot_410 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 410) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_410_0, decode 300 e_410_1, decode 300 e_410_2, decode 300 e_410_3, decode 300 e_410_4, decode 300 e_410_5, decode 171 e_410_6] (fun x hx => ab_bits hx) qcov_410 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_410_0, qch_410_1, qch_410_2, qch_410_3, qch_410_4, qch_410_5, qch_410_6])

theorem qroot_411 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 411) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_411_0, decode 300 e_411_1, decode 300 e_411_2, decode 300 e_411_3, decode 300 e_411_4, decode 300 e_411_5, decode 171 e_411_6] (fun x hx => ab_bits hx) qcov_411 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_411_0, qch_411_1, qch_411_2, qch_411_3, qch_411_4, qch_411_5, qch_411_6])

theorem qroot_412 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 412) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_412_0, decode 300 e_412_1, decode 300 e_412_2, decode 300 e_412_3, decode 300 e_412_4, decode 300 e_412_5, decode 171 e_412_6] (fun x hx => ab_bits hx) qcov_412 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_412_0, qch_412_1, qch_412_2, qch_412_3, qch_412_4, qch_412_5, qch_412_6])

theorem qroot_413 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 413) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_413_0, decode 300 e_413_1, decode 300 e_413_2, decode 300 e_413_3, decode 300 e_413_4, decode 300 e_413_5, decode 171 e_413_6] (fun x hx => ab_bits hx) qcov_413 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_413_0, qch_413_1, qch_413_2, qch_413_3, qch_413_4, qch_413_5, qch_413_6])

theorem qroot_414 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 414) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_414_0, decode 300 e_414_1, decode 300 e_414_2, decode 300 e_414_3, decode 300 e_414_4, decode 300 e_414_5, decode 171 e_414_6] (fun x hx => ab_bits hx) qcov_414 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_414_0, qch_414_1, qch_414_2, qch_414_3, qch_414_4, qch_414_5, qch_414_6])

theorem qroot_415 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 415) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_415_0, decode 300 e_415_1, decode 300 e_415_2, decode 300 e_415_3, decode 300 e_415_4, decode 300 e_415_5, decode 171 e_415_6] (fun x hx => ab_bits hx) qcov_415 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_415_0, qch_415_1, qch_415_2, qch_415_3, qch_415_4, qch_415_5, qch_415_6])

theorem qroot_416 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 416) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_416_0, decode 300 e_416_1, decode 300 e_416_2, decode 300 e_416_3, decode 300 e_416_4, decode 300 e_416_5, decode 171 e_416_6] (fun x hx => ab_bits hx) qcov_416 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_416_0, qch_416_1, qch_416_2, qch_416_3, qch_416_4, qch_416_5, qch_416_6])

theorem qroot_417 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 417) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_417_0, decode 300 e_417_1, decode 300 e_417_2, decode 300 e_417_3, decode 300 e_417_4, decode 300 e_417_5, decode 171 e_417_6] (fun x hx => ab_bits hx) qcov_417 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_417_0, qch_417_1, qch_417_2, qch_417_3, qch_417_4, qch_417_5, qch_417_6])

theorem qroot_418 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 418) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_418_0, decode 300 e_418_1, decode 300 e_418_2, decode 300 e_418_3, decode 300 e_418_4, decode 300 e_418_5, decode 171 e_418_6] (fun x hx => ab_bits hx) qcov_418 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_418_0, qch_418_1, qch_418_2, qch_418_3, qch_418_4, qch_418_5, qch_418_6])

theorem qroot_419 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 419) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_419_0, decode 300 e_419_1, decode 300 e_419_2, decode 300 e_419_3, decode 300 e_419_4, decode 300 e_419_5, decode 171 e_419_6] (fun x hx => ab_bits hx) qcov_419 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_419_0, qch_419_1, qch_419_2, qch_419_3, qch_419_4, qch_419_5, qch_419_6])

end LRC.O7P2
