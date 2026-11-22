import Fresh.M4CertSound

/-!
# M4FixResBank_v1: the CONSTRUCTED C3 mini-bank (m4res_* + m4resData_* records)

Written by `experiments/n8/m4fix_bank_v1.py` (new file; nothing existing is edited).
The 53 boxes below are C3-killed residual boxes (merged U-closure key aA,
`Fresh.UClosureKill`): they HAVE an M4-fired DFS certificate -- the two checkpoint
artifacts `j2_admit_cert2_checkpoint.jsonl` and `m4comp_cert_ckpt_v1.jsonl` agree
field-for-field on leaves/nodes/maxdepth/nstart over all 10,211 of them -- but NO
banked `Fresh.MechDataBatch.m4res_<box>` record (E923's named gap).  This file
supplies the record side: the shape fields from the constructed record
(`m4fix_res_v1.jsonl`, built from the j2 checkpoint) and the leaf-kind / frontier /
lzones fields from the instrumented re-run (`m4comp_cert_ckpt_v1.jsonl`) -- in the
constructed record those are placeholders (the j2 checkpoint does not record them),
and this is exactly the fill m4fix_res_v1.py documents.  Per box the pipeline's
live cross-check is `experiments/n8/m4fix_recon_v1.py` ([T n/n]: the reconstructed
DFS tree against ckpt1 + ckpt2 + this record, all 16 fields), and the kernel
re-checks every arithmetic condition of `M4ResData` here.  A python-side pre-flight
audit of all 10,211 records (0 violations) is in the m4fix run log.
-/

namespace Fresh.MechDataBatch

/-- `m4res_1_1_1_10_12_14_15`: the CONSTRUCTED residual-certificate record of the C3-killed box
(t = [1, 1, 10, 12, 14, 15], merged U-closure key aA): shape fields from `m4fix_res_v1.jsonl`
(built from `j2_admit_cert2_checkpoint.jsonl`), leaf-kind / frontier / lzones
fields from the instrumented re-run `m4comp_cert_ckpt_v1.jsonl`.  Reconstructed
live and [T]-verified per box by `m4fix_recon_v1.py`; validity kernel-checked
below. -/
-- STANDING: DATA
def m4res_1_1_1_10_12_14_15 : M4Res :=
  ⟨[1, 1, 1, 10, 12, 14, 15], 1, 1, 1, 1, 1, 0, 0, [(7, 17)],
    some (13 / 3 : ℚ), some (13 / 3 : ℚ), some (13 / 3 : ℚ), some 1, some 1, none, none⟩

theorem m4resData_1_1_1_10_12_14_15 : M4ResData m4res_1_1_1_10_12_14_15 := by
  simp [M4ResData, m4res_1_1_1_10_12_14_15, InLeafEnvB] <;> norm_num

#print axioms m4resData_1_1_1_10_12_14_15

/-- `m4res_1_1_1_11_12_13_15`: the CONSTRUCTED residual-certificate record of the C3-killed box
(t = [1, 1, 11, 12, 13, 15], merged U-closure key aA): shape fields from `m4fix_res_v1.jsonl`
(built from `j2_admit_cert2_checkpoint.jsonl`), leaf-kind / frontier / lzones
fields from the instrumented re-run `m4comp_cert_ckpt_v1.jsonl`.  Reconstructed
live and [T]-verified per box by `m4fix_recon_v1.py`; validity kernel-checked
below. -/
-- STANDING: DATA
def m4res_1_1_1_11_12_13_15 : M4Res :=
  ⟨[1, 1, 1, 11, 12, 13, 15], 1, 1, 1, 1, 1, 0, 0, [(7, 17)],
    some (5 / 3 : ℚ), some (5 / 3 : ℚ), some (5 / 3 : ℚ), some 1, some 1, none, none⟩

theorem m4resData_1_1_1_11_12_13_15 : M4ResData m4res_1_1_1_11_12_13_15 := by
  simp [M4ResData, m4res_1_1_1_11_12_13_15, InLeafEnvB] <;> norm_num

#print axioms m4resData_1_1_1_11_12_13_15

/-- `m4res_1_1_1_1_4_6_15`: the CONSTRUCTED residual-certificate record of the C3-killed box
(t = [1, 1, 1, 4, 6, 15], merged U-closure key aA): shape fields from `m4fix_res_v1.jsonl`
(built from `j2_admit_cert2_checkpoint.jsonl`), leaf-kind / frontier / lzones
fields from the instrumented re-run `m4comp_cert_ckpt_v1.jsonl`.  Reconstructed
live and [T]-verified per box by `m4fix_recon_v1.py`; validity kernel-checked
below. -/
-- STANDING: DATA
def m4res_1_1_1_1_4_6_15 : M4Res :=
  ⟨[1, 1, 1, 1, 4, 6, 15], 1, 1, 1, 1, 1, 0, 0, [(7, 17)],
    some (49 / 15 : ℚ), some (49 / 15 : ℚ), some (49 / 15 : ℚ), some 1, some 1, none, none⟩

theorem m4resData_1_1_1_1_4_6_15 : M4ResData m4res_1_1_1_1_4_6_15 := by
  simp [M4ResData, m4res_1_1_1_1_4_6_15, InLeafEnvB] <;> norm_num

#print axioms m4resData_1_1_1_1_4_6_15

/-- `m4res_1_1_1_1_5_7_12`: the CONSTRUCTED residual-certificate record of the C3-killed box
(t = [1, 1, 1, 5, 7, 12], merged U-closure key aA): shape fields from `m4fix_res_v1.jsonl`
(built from `j2_admit_cert2_checkpoint.jsonl`), leaf-kind / frontier / lzones
fields from the instrumented re-run `m4comp_cert_ckpt_v1.jsonl`.  Reconstructed
live and [T]-verified per box by `m4fix_recon_v1.py`; validity kernel-checked
below. -/
-- STANDING: DATA
def m4res_1_1_1_1_5_7_12 : M4Res :=
  ⟨[1, 1, 1, 1, 5, 7, 12], 1, 1, 1, 1, 1, 0, 0, [(6, 9)],
    some (17 / 7 : ℚ), some (17 / 7 : ℚ), some (17 / 7 : ℚ), some 1, some 1, none, none⟩

theorem m4resData_1_1_1_1_5_7_12 : M4ResData m4res_1_1_1_1_5_7_12 := by
  simp [M4ResData, m4res_1_1_1_1_5_7_12, InLeafEnvB] <;> norm_num

#print axioms m4resData_1_1_1_1_5_7_12

/-- `m4res_1_1_1_2_4_6_8`: the CONSTRUCTED residual-certificate record of the C3-killed box
(t = [1, 1, 2, 4, 6, 8], merged U-closure key aA): shape fields from `m4fix_res_v1.jsonl`
(built from `j2_admit_cert2_checkpoint.jsonl`), leaf-kind / frontier / lzones
fields from the instrumented re-run `m4comp_cert_ckpt_v1.jsonl`.  Reconstructed
live and [T]-verified per box by `m4fix_recon_v1.py`; validity kernel-checked
below. -/
-- STANDING: DATA
def m4res_1_1_1_2_4_6_8 : M4Res :=
  ⟨[1, 1, 1, 2, 4, 6, 8], 1, 2, 2, 1, 0, 1, 0, [(6, 9)],
    none, none, none, none, none, some 2, some 2⟩

theorem m4resData_1_1_1_2_4_6_8 : M4ResData m4res_1_1_1_2_4_6_8 := by
  simp [M4ResData, m4res_1_1_1_2_4_6_8, InLeafEnvB] <;> norm_num

#print axioms m4resData_1_1_1_2_4_6_8

/-- `m4res_1_1_1_2_5_7_12`: the CONSTRUCTED residual-certificate record of the C3-killed box
(t = [1, 1, 2, 5, 7, 12], merged U-closure key aA): shape fields from `m4fix_res_v1.jsonl`
(built from `j2_admit_cert2_checkpoint.jsonl`), leaf-kind / frontier / lzones
fields from the instrumented re-run `m4comp_cert_ckpt_v1.jsonl`.  Reconstructed
live and [T]-verified per box by `m4fix_recon_v1.py`; validity kernel-checked
below. -/
-- STANDING: DATA
def m4res_1_1_1_2_5_7_12 : M4Res :=
  ⟨[1, 1, 1, 2, 5, 7, 12], 1, 1, 1, 1, 1, 0, 0, [(6, 9)],
    some (17 / 7 : ℚ), some (17 / 7 : ℚ), some (17 / 7 : ℚ), some 1, some 1, none, none⟩

theorem m4resData_1_1_1_2_5_7_12 : M4ResData m4res_1_1_1_2_5_7_12 := by
  simp [M4ResData, m4res_1_1_1_2_5_7_12, InLeafEnvB] <;> norm_num

#print axioms m4resData_1_1_1_2_5_7_12

/-- `m4res_1_1_1_3_4_7_11`: the CONSTRUCTED residual-certificate record of the C3-killed box
(t = [1, 1, 3, 4, 7, 11], merged U-closure key aA): shape fields from `m4fix_res_v1.jsonl`
(built from `j2_admit_cert2_checkpoint.jsonl`), leaf-kind / frontier / lzones
fields from the instrumented re-run `m4comp_cert_ckpt_v1.jsonl`.  Reconstructed
live and [T]-verified per box by `m4fix_recon_v1.py`; validity kernel-checked
below. -/
-- STANDING: DATA
def m4res_1_1_1_3_4_7_11 : M4Res :=
  ⟨[1, 1, 1, 3, 4, 7, 11], 1, 1, 1, 1, 1, 0, 0, [(6, 9)],
    some (9 / 7 : ℚ), some (9 / 7 : ℚ), some (9 / 7 : ℚ), some 1, some 1, none, none⟩

theorem m4resData_1_1_1_3_4_7_11 : M4ResData m4res_1_1_1_3_4_7_11 := by
  simp [M4ResData, m4res_1_1_1_3_4_7_11, InLeafEnvB] <;> norm_num

#print axioms m4resData_1_1_1_3_4_7_11

/-- `m4res_1_1_1_4_11_13_15`: the CONSTRUCTED residual-certificate record of the C3-killed box
(t = [1, 1, 4, 11, 13, 15], merged U-closure key aA): shape fields from `m4fix_res_v1.jsonl`
(built from `j2_admit_cert2_checkpoint.jsonl`), leaf-kind / frontier / lzones
fields from the instrumented re-run `m4comp_cert_ckpt_v1.jsonl`.  Reconstructed
live and [T]-verified per box by `m4fix_recon_v1.py`; validity kernel-checked
below. -/
-- STANDING: DATA
def m4res_1_1_1_4_11_13_15 : M4Res :=
  ⟨[1, 1, 1, 4, 11, 13, 15], 1, 1, 1, 1, 1, 0, 0, [(7, 17)],
    some (82 / 25 : ℚ), some (82 / 25 : ℚ), some (82 / 25 : ℚ), some 1, some 1, none, none⟩

theorem m4resData_1_1_1_4_11_13_15 : M4ResData m4res_1_1_1_4_11_13_15 := by
  simp [M4ResData, m4res_1_1_1_4_11_13_15, InLeafEnvB] <;> norm_num

#print axioms m4resData_1_1_1_4_11_13_15

/-- `m4res_1_1_1_4_4_6_15`: the CONSTRUCTED residual-certificate record of the C3-killed box
(t = [1, 1, 4, 4, 6, 15], merged U-closure key aA): shape fields from `m4fix_res_v1.jsonl`
(built from `j2_admit_cert2_checkpoint.jsonl`), leaf-kind / frontier / lzones
fields from the instrumented re-run `m4comp_cert_ckpt_v1.jsonl`.  Reconstructed
live and [T]-verified per box by `m4fix_recon_v1.py`; validity kernel-checked
below. -/
-- STANDING: DATA
def m4res_1_1_1_4_4_6_15 : M4Res :=
  ⟨[1, 1, 1, 4, 4, 6, 15], 1, 1, 1, 1, 1, 0, 0, [(7, 17)],
    some (49 / 15 : ℚ), some (49 / 15 : ℚ), some (49 / 15 : ℚ), some 1, some 1, none, none⟩

theorem m4resData_1_1_1_4_4_6_15 : M4ResData m4res_1_1_1_4_4_6_15 := by
  simp [M4ResData, m4res_1_1_1_4_4_6_15, InLeafEnvB] <;> norm_num

#print axioms m4resData_1_1_1_4_4_6_15

/-- `m4res_1_1_1_4_6_11_15`: the CONSTRUCTED residual-certificate record of the C3-killed box
(t = [1, 1, 4, 6, 11, 15], merged U-closure key aA): shape fields from `m4fix_res_v1.jsonl`
(built from `j2_admit_cert2_checkpoint.jsonl`), leaf-kind / frontier / lzones
fields from the instrumented re-run `m4comp_cert_ckpt_v1.jsonl`.  Reconstructed
live and [T]-verified per box by `m4fix_recon_v1.py`; validity kernel-checked
below. -/
-- STANDING: DATA
def m4res_1_1_1_4_6_11_15 : M4Res :=
  ⟨[1, 1, 1, 4, 6, 11, 15], 1, 1, 1, 1, 1, 0, 0, [(7, 17)],
    some (49 / 15 : ℚ), some (49 / 15 : ℚ), some (49 / 15 : ℚ), some 1, some 1, none, none⟩

theorem m4resData_1_1_1_4_6_11_15 : M4ResData m4res_1_1_1_4_6_11_15 := by
  simp [M4ResData, m4res_1_1_1_4_6_11_15, InLeafEnvB] <;> norm_num

#print axioms m4resData_1_1_1_4_6_11_15

/-- `m4res_1_1_1_4_6_13_15`: the CONSTRUCTED residual-certificate record of the C3-killed box
(t = [1, 1, 4, 6, 13, 15], merged U-closure key aA): shape fields from `m4fix_res_v1.jsonl`
(built from `j2_admit_cert2_checkpoint.jsonl`), leaf-kind / frontier / lzones
fields from the instrumented re-run `m4comp_cert_ckpt_v1.jsonl`.  Reconstructed
live and [T]-verified per box by `m4fix_recon_v1.py`; validity kernel-checked
below. -/
-- STANDING: DATA
def m4res_1_1_1_4_6_13_15 : M4Res :=
  ⟨[1, 1, 1, 4, 6, 13, 15], 1, 1, 1, 1, 1, 0, 0, [(7, 17)],
    some (82 / 25 : ℚ), some (82 / 25 : ℚ), some (82 / 25 : ℚ), some 1, some 1, none, none⟩

theorem m4resData_1_1_1_4_6_13_15 : M4ResData m4res_1_1_1_4_6_13_15 := by
  simp [M4ResData, m4res_1_1_1_4_6_13_15, InLeafEnvB] <;> norm_num

#print axioms m4resData_1_1_1_4_6_13_15

/-- `m4res_1_1_1_4_6_6_15`: the CONSTRUCTED residual-certificate record of the C3-killed box
(t = [1, 1, 4, 6, 6, 15], merged U-closure key aA): shape fields from `m4fix_res_v1.jsonl`
(built from `j2_admit_cert2_checkpoint.jsonl`), leaf-kind / frontier / lzones
fields from the instrumented re-run `m4comp_cert_ckpt_v1.jsonl`.  Reconstructed
live and [T]-verified per box by `m4fix_recon_v1.py`; validity kernel-checked
below. -/
-- STANDING: DATA
def m4res_1_1_1_4_6_6_15 : M4Res :=
  ⟨[1, 1, 1, 4, 6, 6, 15], 1, 1, 1, 1, 1, 0, 0, [(7, 17)],
    some (49 / 15 : ℚ), some (49 / 15 : ℚ), some (49 / 15 : ℚ), some 1, some 1, none, none⟩

theorem m4resData_1_1_1_4_6_6_15 : M4ResData m4res_1_1_1_4_6_6_15 := by
  simp [M4ResData, m4res_1_1_1_4_6_6_15, InLeafEnvB] <;> norm_num

#print axioms m4resData_1_1_1_4_6_6_15

/-- `m4res_1_1_1_5_5_7_12`: the CONSTRUCTED residual-certificate record of the C3-killed box
(t = [1, 1, 5, 5, 7, 12], merged U-closure key aA): shape fields from `m4fix_res_v1.jsonl`
(built from `j2_admit_cert2_checkpoint.jsonl`), leaf-kind / frontier / lzones
fields from the instrumented re-run `m4comp_cert_ckpt_v1.jsonl`.  Reconstructed
live and [T]-verified per box by `m4fix_recon_v1.py`; validity kernel-checked
below. -/
-- STANDING: DATA
def m4res_1_1_1_5_5_7_12 : M4Res :=
  ⟨[1, 1, 1, 5, 5, 7, 12], 1, 1, 1, 1, 1, 0, 0, [(6, 9)],
    some (17 / 7 : ℚ), some (17 / 7 : ℚ), some (17 / 7 : ℚ), some 1, some 1, none, none⟩

theorem m4resData_1_1_1_5_5_7_12 : M4ResData m4res_1_1_1_5_5_7_12 := by
  simp [M4ResData, m4res_1_1_1_5_5_7_12, InLeafEnvB] <;> norm_num

#print axioms m4resData_1_1_1_5_5_7_12

/-- `m4res_1_1_1_5_7_11_12`: the CONSTRUCTED residual-certificate record of the C3-killed box
(t = [1, 1, 5, 7, 11, 12], merged U-closure key aA): shape fields from `m4fix_res_v1.jsonl`
(built from `j2_admit_cert2_checkpoint.jsonl`), leaf-kind / frontier / lzones
fields from the instrumented re-run `m4comp_cert_ckpt_v1.jsonl`.  Reconstructed
live and [T]-verified per box by `m4fix_recon_v1.py`; validity kernel-checked
below. -/
-- STANDING: DATA
def m4res_1_1_1_5_7_11_12 : M4Res :=
  ⟨[1, 1, 1, 5, 7, 11, 12], 1, 1, 1, 1, 1, 0, 0, [(5, 9)],
    some (17 / 7 : ℚ), some (17 / 7 : ℚ), some (17 / 7 : ℚ), some 1, some 1, none, none⟩

theorem m4resData_1_1_1_5_7_11_12 : M4ResData m4res_1_1_1_5_7_11_12 := by
  simp [M4ResData, m4res_1_1_1_5_7_11_12, InLeafEnvB] <;> norm_num

#print axioms m4resData_1_1_1_5_7_11_12

/-- `m4res_1_1_1_5_7_12_12`: the CONSTRUCTED residual-certificate record of the C3-killed box
(t = [1, 1, 5, 7, 12, 12], merged U-closure key aA): shape fields from `m4fix_res_v1.jsonl`
(built from `j2_admit_cert2_checkpoint.jsonl`), leaf-kind / frontier / lzones
fields from the instrumented re-run `m4comp_cert_ckpt_v1.jsonl`.  Reconstructed
live and [T]-verified per box by `m4fix_recon_v1.py`; validity kernel-checked
below. -/
-- STANDING: DATA
def m4res_1_1_1_5_7_12_12 : M4Res :=
  ⟨[1, 1, 1, 5, 7, 12, 12], 1, 1, 1, 1, 1, 0, 0, [(5, 9)],
    some (17 / 7 : ℚ), some (17 / 7 : ℚ), some (17 / 7 : ℚ), some 1, some 1, none, none⟩

theorem m4resData_1_1_1_5_7_12_12 : M4ResData m4res_1_1_1_5_7_12_12 := by
  simp [M4ResData, m4res_1_1_1_5_7_12_12, InLeafEnvB] <;> norm_num

#print axioms m4resData_1_1_1_5_7_12_12

/-- `m4res_1_1_1_5_7_12_13`: the CONSTRUCTED residual-certificate record of the C3-killed box
(t = [1, 1, 5, 7, 12, 13], merged U-closure key aA): shape fields from `m4fix_res_v1.jsonl`
(built from `j2_admit_cert2_checkpoint.jsonl`), leaf-kind / frontier / lzones
fields from the instrumented re-run `m4comp_cert_ckpt_v1.jsonl`.  Reconstructed
live and [T]-verified per box by `m4fix_recon_v1.py`; validity kernel-checked
below. -/
-- STANDING: DATA
def m4res_1_1_1_5_7_12_13 : M4Res :=
  ⟨[1, 1, 1, 5, 7, 12, 13], 4, 12, 7, 1, 1, 3, 0, [(4, 9), (5, 17), (7, 25)],
    some (99 / 35 : ℚ), some (99 / 35 : ℚ), some (99 / 35 : ℚ), some 4, some 4, some 2, some 7⟩

theorem m4resData_1_1_1_5_7_12_13 : M4ResData m4res_1_1_1_5_7_12_13 := by
  simp [M4ResData, m4res_1_1_1_5_7_12_13, InLeafEnvB] <;> norm_num

#print axioms m4resData_1_1_1_5_7_12_13

/-- `m4res_1_1_1_5_7_12_14`: the CONSTRUCTED residual-certificate record of the C3-killed box
(t = [1, 1, 5, 7, 12, 14], merged U-closure key aA): shape fields from `m4fix_res_v1.jsonl`
(built from `j2_admit_cert2_checkpoint.jsonl`), leaf-kind / frontier / lzones
fields from the instrumented re-run `m4comp_cert_ckpt_v1.jsonl`.  Reconstructed
live and [T]-verified per box by `m4fix_recon_v1.py`; validity kernel-checked
below. -/
-- STANDING: DATA
def m4res_1_1_1_5_7_12_14 : M4Res :=
  ⟨[1, 1, 1, 5, 7, 12, 14], 1, 1, 1, 1, 1, 0, 0, [(5, 9)],
    some (22 / 9 : ℚ), some (22 / 9 : ℚ), some (22 / 9 : ℚ), some 1, some 1, none, none⟩

theorem m4resData_1_1_1_5_7_12_14 : M4ResData m4res_1_1_1_5_7_12_14 := by
  simp [M4ResData, m4res_1_1_1_5_7_12_14, InLeafEnvB] <;> norm_num

#print axioms m4resData_1_1_1_5_7_12_14

/-- `m4res_1_1_1_5_9_12_14`: the CONSTRUCTED residual-certificate record of the C3-killed box
(t = [1, 1, 5, 9, 12, 14], merged U-closure key aA): shape fields from `m4fix_res_v1.jsonl`
(built from `j2_admit_cert2_checkpoint.jsonl`), leaf-kind / frontier / lzones
fields from the instrumented re-run `m4comp_cert_ckpt_v1.jsonl`.  Reconstructed
live and [T]-verified per box by `m4fix_recon_v1.py`; validity kernel-checked
below. -/
-- STANDING: DATA
def m4res_1_1_1_5_9_12_14 : M4Res :=
  ⟨[1, 1, 1, 5, 9, 12, 14], 1, 1, 1, 1, 1, 0, 0, [(5, 9)],
    some (22 / 9 : ℚ), some (22 / 9 : ℚ), some (22 / 9 : ℚ), some 1, some 1, none, none⟩

theorem m4resData_1_1_1_5_9_12_14 : M4ResData m4res_1_1_1_5_9_12_14 := by
  simp [M4ResData, m4res_1_1_1_5_9_12_14, InLeafEnvB] <;> norm_num

#print axioms m4resData_1_1_1_5_9_12_14

/-- `m4res_1_1_1_7_10_12_14`: the CONSTRUCTED residual-certificate record of the C3-killed box
(t = [1, 1, 7, 10, 12, 14], merged U-closure key aA): shape fields from `m4fix_res_v1.jsonl`
(built from `j2_admit_cert2_checkpoint.jsonl`), leaf-kind / frontier / lzones
fields from the instrumented re-run `m4comp_cert_ckpt_v1.jsonl`.  Reconstructed
live and [T]-verified per box by `m4fix_recon_v1.py`; validity kernel-checked
below. -/
-- STANDING: DATA
def m4res_1_1_1_7_10_12_14 : M4Res :=
  ⟨[1, 1, 1, 7, 10, 12, 14], 1, 1, 1, 1, 1, 0, 0, [(4, 9)],
    some (98 / 27 : ℚ), some (98 / 27 : ℚ), some (98 / 27 : ℚ), some 1, some 1, none, none⟩

theorem m4resData_1_1_1_7_10_12_14 : M4ResData m4res_1_1_1_7_10_12_14 := by
  simp [M4ResData, m4res_1_1_1_7_10_12_14, InLeafEnvB] <;> norm_num

#print axioms m4resData_1_1_1_7_10_12_14

/-- `m4res_1_1_1_7_11_12_14`: the CONSTRUCTED residual-certificate record of the C3-killed box
(t = [1, 1, 7, 11, 12, 14], merged U-closure key aA): shape fields from `m4fix_res_v1.jsonl`
(built from `j2_admit_cert2_checkpoint.jsonl`), leaf-kind / frontier / lzones
fields from the instrumented re-run `m4comp_cert_ckpt_v1.jsonl`.  Reconstructed
live and [T]-verified per box by `m4fix_recon_v1.py`; validity kernel-checked
below. -/
-- STANDING: DATA
def m4res_1_1_1_7_11_12_14 : M4Res :=
  ⟨[1, 1, 1, 7, 11, 12, 14], 1, 1, 1, 1, 1, 0, 0, [(4, 9)],
    some (22 / 9 : ℚ), some (22 / 9 : ℚ), some (22 / 9 : ℚ), some 1, some 1, none, none⟩

theorem m4resData_1_1_1_7_11_12_14 : M4ResData m4res_1_1_1_7_11_12_14 := by
  simp [M4ResData, m4res_1_1_1_7_11_12_14, InLeafEnvB] <;> norm_num

#print axioms m4resData_1_1_1_7_11_12_14

/-- `m4res_1_1_1_9_10_12_14`: the CONSTRUCTED residual-certificate record of the C3-killed box
(t = [1, 1, 9, 10, 12, 14], merged U-closure key aA): shape fields from `m4fix_res_v1.jsonl`
(built from `j2_admit_cert2_checkpoint.jsonl`), leaf-kind / frontier / lzones
fields from the instrumented re-run `m4comp_cert_ckpt_v1.jsonl`.  Reconstructed
live and [T]-verified per box by `m4fix_recon_v1.py`; validity kernel-checked
below. -/
-- STANDING: DATA
def m4res_1_1_1_9_10_12_14 : M4Res :=
  ⟨[1, 1, 1, 9, 10, 12, 14], 1, 1, 1, 1, 1, 0, 0, [(4, 9)],
    some (82 / 19 : ℚ), some (82 / 19 : ℚ), some (82 / 19 : ℚ), some 1, some 1, none, none⟩

theorem m4resData_1_1_1_9_10_12_14 : M4ResData m4res_1_1_1_9_10_12_14 := by
  simp [M4ResData, m4res_1_1_1_9_10_12_14, InLeafEnvB] <;> norm_num

#print axioms m4resData_1_1_1_9_10_12_14

/-- `m4res_1_1_1_9_11_12_14`: the CONSTRUCTED residual-certificate record of the C3-killed box
(t = [1, 1, 9, 11, 12, 14], merged U-closure key aA): shape fields from `m4fix_res_v1.jsonl`
(built from `j2_admit_cert2_checkpoint.jsonl`), leaf-kind / frontier / lzones
fields from the instrumented re-run `m4comp_cert_ckpt_v1.jsonl`.  Reconstructed
live and [T]-verified per box by `m4fix_recon_v1.py`; validity kernel-checked
below. -/
-- STANDING: DATA
def m4res_1_1_1_9_11_12_14 : M4Res :=
  ⟨[1, 1, 1, 9, 11, 12, 14], 1, 1, 1, 1, 1, 0, 0, [(4, 9)],
    some (22 / 9 : ℚ), some (22 / 9 : ℚ), some (22 / 9 : ℚ), some 1, some 1, none, none⟩

theorem m4resData_1_1_1_9_11_12_14 : M4ResData m4res_1_1_1_9_11_12_14 := by
  simp [M4ResData, m4res_1_1_1_9_11_12_14, InLeafEnvB] <;> norm_num

#print axioms m4resData_1_1_1_9_11_12_14

/-- `m4res_1_1_2_11_12_13_15`: the CONSTRUCTED residual-certificate record of the C3-killed box
(t = [1, 2, 11, 12, 13, 15], merged U-closure key aA): shape fields from `m4fix_res_v1.jsonl`
(built from `j2_admit_cert2_checkpoint.jsonl`), leaf-kind / frontier / lzones
fields from the instrumented re-run `m4comp_cert_ckpt_v1.jsonl`.  Reconstructed
live and [T]-verified per box by `m4fix_recon_v1.py`; validity kernel-checked
below. -/
-- STANDING: DATA
def m4res_1_1_2_11_12_13_15 : M4Res :=
  ⟨[1, 1, 2, 11, 12, 13, 15], 1, 1, 1, 1, 1, 0, 0, [(7, 17)],
    some (5 / 3 : ℚ), some (5 / 3 : ℚ), some (5 / 3 : ℚ), some 1, some 1, none, none⟩

theorem m4resData_1_1_2_11_12_13_15 : M4ResData m4res_1_1_2_11_12_13_15 := by
  simp [M4ResData, m4res_1_1_2_11_12_13_15, InLeafEnvB] <;> norm_num

#print axioms m4resData_1_1_2_11_12_13_15

/-- `m4res_1_1_2_2_5_7_12`: the CONSTRUCTED residual-certificate record of the C3-killed box
(t = [1, 2, 2, 5, 7, 12], merged U-closure key aA): shape fields from `m4fix_res_v1.jsonl`
(built from `j2_admit_cert2_checkpoint.jsonl`), leaf-kind / frontier / lzones
fields from the instrumented re-run `m4comp_cert_ckpt_v1.jsonl`.  Reconstructed
live and [T]-verified per box by `m4fix_recon_v1.py`; validity kernel-checked
below. -/
-- STANDING: DATA
def m4res_1_1_2_2_5_7_12 : M4Res :=
  ⟨[1, 1, 2, 2, 5, 7, 12], 1, 1, 1, 1, 1, 0, 0, [(6, 9)],
    some (17 / 7 : ℚ), some (17 / 7 : ℚ), some (17 / 7 : ℚ), some 1, some 1, none, none⟩

theorem m4resData_1_1_2_2_5_7_12 : M4ResData m4res_1_1_2_2_5_7_12 := by
  simp [M4ResData, m4res_1_1_2_2_5_7_12, InLeafEnvB] <;> norm_num

#print axioms m4resData_1_1_2_2_5_7_12

/-- `m4res_1_1_2_3_4_7_11`: the CONSTRUCTED residual-certificate record of the C3-killed box
(t = [1, 2, 3, 4, 7, 11], merged U-closure key aA): shape fields from `m4fix_res_v1.jsonl`
(built from `j2_admit_cert2_checkpoint.jsonl`), leaf-kind / frontier / lzones
fields from the instrumented re-run `m4comp_cert_ckpt_v1.jsonl`.  Reconstructed
live and [T]-verified per box by `m4fix_recon_v1.py`; validity kernel-checked
below. -/
-- STANDING: DATA
def m4res_1_1_2_3_4_7_11 : M4Res :=
  ⟨[1, 1, 2, 3, 4, 7, 11], 1, 1, 1, 1, 1, 0, 0, [(6, 9)],
    some (9 / 7 : ℚ), some (9 / 7 : ℚ), some (9 / 7 : ℚ), some 1, some 1, none, none⟩

theorem m4resData_1_1_2_3_4_7_11 : M4ResData m4res_1_1_2_3_4_7_11 := by
  simp [M4ResData, m4res_1_1_2_3_4_7_11, InLeafEnvB] <;> norm_num

#print axioms m4resData_1_1_2_3_4_7_11

/-- `m4res_1_1_2_5_5_7_12`: the CONSTRUCTED residual-certificate record of the C3-killed box
(t = [1, 2, 5, 5, 7, 12], merged U-closure key aA): shape fields from `m4fix_res_v1.jsonl`
(built from `j2_admit_cert2_checkpoint.jsonl`), leaf-kind / frontier / lzones
fields from the instrumented re-run `m4comp_cert_ckpt_v1.jsonl`.  Reconstructed
live and [T]-verified per box by `m4fix_recon_v1.py`; validity kernel-checked
below. -/
-- STANDING: DATA
def m4res_1_1_2_5_5_7_12 : M4Res :=
  ⟨[1, 1, 2, 5, 5, 7, 12], 1, 1, 1, 1, 1, 0, 0, [(6, 9)],
    some (17 / 7 : ℚ), some (17 / 7 : ℚ), some (17 / 7 : ℚ), some 1, some 1, none, none⟩

theorem m4resData_1_1_2_5_5_7_12 : M4ResData m4res_1_1_2_5_5_7_12 := by
  simp [M4ResData, m4res_1_1_2_5_5_7_12, InLeafEnvB] <;> norm_num

#print axioms m4resData_1_1_2_5_5_7_12

/-- `m4res_1_1_2_5_7_11_12`: the CONSTRUCTED residual-certificate record of the C3-killed box
(t = [1, 2, 5, 7, 11, 12], merged U-closure key aA): shape fields from `m4fix_res_v1.jsonl`
(built from `j2_admit_cert2_checkpoint.jsonl`), leaf-kind / frontier / lzones
fields from the instrumented re-run `m4comp_cert_ckpt_v1.jsonl`.  Reconstructed
live and [T]-verified per box by `m4fix_recon_v1.py`; validity kernel-checked
below. -/
-- STANDING: DATA
def m4res_1_1_2_5_7_11_12 : M4Res :=
  ⟨[1, 1, 2, 5, 7, 11, 12], 1, 1, 1, 1, 1, 0, 0, [(5, 9)],
    some (17 / 7 : ℚ), some (17 / 7 : ℚ), some (17 / 7 : ℚ), some 1, some 1, none, none⟩

theorem m4resData_1_1_2_5_7_11_12 : M4ResData m4res_1_1_2_5_7_11_12 := by
  simp [M4ResData, m4res_1_1_2_5_7_11_12, InLeafEnvB] <;> norm_num

#print axioms m4resData_1_1_2_5_7_11_12

/-- `m4res_1_1_2_5_7_12_12`: the CONSTRUCTED residual-certificate record of the C3-killed box
(t = [1, 2, 5, 7, 12, 12], merged U-closure key aA): shape fields from `m4fix_res_v1.jsonl`
(built from `j2_admit_cert2_checkpoint.jsonl`), leaf-kind / frontier / lzones
fields from the instrumented re-run `m4comp_cert_ckpt_v1.jsonl`.  Reconstructed
live and [T]-verified per box by `m4fix_recon_v1.py`; validity kernel-checked
below. -/
-- STANDING: DATA
def m4res_1_1_2_5_7_12_12 : M4Res :=
  ⟨[1, 1, 2, 5, 7, 12, 12], 1, 1, 1, 1, 1, 0, 0, [(5, 9)],
    some (17 / 7 : ℚ), some (17 / 7 : ℚ), some (17 / 7 : ℚ), some 1, some 1, none, none⟩

theorem m4resData_1_1_2_5_7_12_12 : M4ResData m4res_1_1_2_5_7_12_12 := by
  simp [M4ResData, m4res_1_1_2_5_7_12_12, InLeafEnvB] <;> norm_num

#print axioms m4resData_1_1_2_5_7_12_12

/-- `m4res_1_1_2_5_7_12_14`: the CONSTRUCTED residual-certificate record of the C3-killed box
(t = [1, 2, 5, 7, 12, 14], merged U-closure key aA): shape fields from `m4fix_res_v1.jsonl`
(built from `j2_admit_cert2_checkpoint.jsonl`), leaf-kind / frontier / lzones
fields from the instrumented re-run `m4comp_cert_ckpt_v1.jsonl`.  Reconstructed
live and [T]-verified per box by `m4fix_recon_v1.py`; validity kernel-checked
below. -/
-- STANDING: DATA
def m4res_1_1_2_5_7_12_14 : M4Res :=
  ⟨[1, 1, 2, 5, 7, 12, 14], 1, 1, 1, 1, 1, 0, 0, [(5, 9)],
    some (22 / 9 : ℚ), some (22 / 9 : ℚ), some (22 / 9 : ℚ), some 1, some 1, none, none⟩

theorem m4resData_1_1_2_5_7_12_14 : M4ResData m4res_1_1_2_5_7_12_14 := by
  simp [M4ResData, m4res_1_1_2_5_7_12_14, InLeafEnvB] <;> norm_num

#print axioms m4resData_1_1_2_5_7_12_14

/-- `m4res_1_1_2_5_9_12_14`: the CONSTRUCTED residual-certificate record of the C3-killed box
(t = [1, 2, 5, 9, 12, 14], merged U-closure key aA): shape fields from `m4fix_res_v1.jsonl`
(built from `j2_admit_cert2_checkpoint.jsonl`), leaf-kind / frontier / lzones
fields from the instrumented re-run `m4comp_cert_ckpt_v1.jsonl`.  Reconstructed
live and [T]-verified per box by `m4fix_recon_v1.py`; validity kernel-checked
below. -/
-- STANDING: DATA
def m4res_1_1_2_5_9_12_14 : M4Res :=
  ⟨[1, 1, 2, 5, 9, 12, 14], 1, 1, 1, 1, 1, 0, 0, [(5, 9)],
    some (22 / 9 : ℚ), some (22 / 9 : ℚ), some (22 / 9 : ℚ), some 1, some 1, none, none⟩

theorem m4resData_1_1_2_5_9_12_14 : M4ResData m4res_1_1_2_5_9_12_14 := by
  simp [M4ResData, m4res_1_1_2_5_9_12_14, InLeafEnvB] <;> norm_num

#print axioms m4resData_1_1_2_5_9_12_14

/-- `m4res_1_1_2_7_11_12_14`: the CONSTRUCTED residual-certificate record of the C3-killed box
(t = [1, 2, 7, 11, 12, 14], merged U-closure key aA): shape fields from `m4fix_res_v1.jsonl`
(built from `j2_admit_cert2_checkpoint.jsonl`), leaf-kind / frontier / lzones
fields from the instrumented re-run `m4comp_cert_ckpt_v1.jsonl`.  Reconstructed
live and [T]-verified per box by `m4fix_recon_v1.py`; validity kernel-checked
below. -/
-- STANDING: DATA
def m4res_1_1_2_7_11_12_14 : M4Res :=
  ⟨[1, 1, 2, 7, 11, 12, 14], 1, 1, 1, 1, 1, 0, 0, [(4, 9)],
    some (22 / 9 : ℚ), some (22 / 9 : ℚ), some (22 / 9 : ℚ), some 1, some 1, none, none⟩

theorem m4resData_1_1_2_7_11_12_14 : M4ResData m4res_1_1_2_7_11_12_14 := by
  simp [M4ResData, m4res_1_1_2_7_11_12_14, InLeafEnvB] <;> norm_num

#print axioms m4resData_1_1_2_7_11_12_14

/-- `m4res_1_1_2_9_11_12_14`: the CONSTRUCTED residual-certificate record of the C3-killed box
(t = [1, 2, 9, 11, 12, 14], merged U-closure key aA): shape fields from `m4fix_res_v1.jsonl`
(built from `j2_admit_cert2_checkpoint.jsonl`), leaf-kind / frontier / lzones
fields from the instrumented re-run `m4comp_cert_ckpt_v1.jsonl`.  Reconstructed
live and [T]-verified per box by `m4fix_recon_v1.py`; validity kernel-checked
below. -/
-- STANDING: DATA
def m4res_1_1_2_9_11_12_14 : M4Res :=
  ⟨[1, 1, 2, 9, 11, 12, 14], 1, 1, 1, 1, 1, 0, 0, [(4, 9)],
    some (22 / 9 : ℚ), some (22 / 9 : ℚ), some (22 / 9 : ℚ), some 1, some 1, none, none⟩

theorem m4resData_1_1_2_9_11_12_14 : M4ResData m4res_1_1_2_9_11_12_14 := by
  simp [M4ResData, m4res_1_1_2_9_11_12_14, InLeafEnvB] <;> norm_num

#print axioms m4resData_1_1_2_9_11_12_14

/-- `m4res_1_1_3_11_12_13_15`: the CONSTRUCTED residual-certificate record of the C3-killed box
(t = [1, 3, 11, 12, 13, 15], merged U-closure key aA): shape fields from `m4fix_res_v1.jsonl`
(built from `j2_admit_cert2_checkpoint.jsonl`), leaf-kind / frontier / lzones
fields from the instrumented re-run `m4comp_cert_ckpt_v1.jsonl`.  Reconstructed
live and [T]-verified per box by `m4fix_recon_v1.py`; validity kernel-checked
below. -/
-- STANDING: DATA
def m4res_1_1_3_11_12_13_15 : M4Res :=
  ⟨[1, 1, 3, 11, 12, 13, 15], 1, 1, 1, 1, 1, 0, 0, [(7, 17)],
    some (5 / 3 : ℚ), some (5 / 3 : ℚ), some (5 / 3 : ℚ), some 1, some 1, none, none⟩

theorem m4resData_1_1_3_11_12_13_15 : M4ResData m4res_1_1_3_11_12_13_15 := by
  simp [M4ResData, m4res_1_1_3_11_12_13_15, InLeafEnvB] <;> norm_num

#print axioms m4resData_1_1_3_11_12_13_15

/-- `m4res_1_1_3_3_4_7_11`: the CONSTRUCTED residual-certificate record of the C3-killed box
(t = [1, 3, 3, 4, 7, 11], merged U-closure key aA): shape fields from `m4fix_res_v1.jsonl`
(built from `j2_admit_cert2_checkpoint.jsonl`), leaf-kind / frontier / lzones
fields from the instrumented re-run `m4comp_cert_ckpt_v1.jsonl`.  Reconstructed
live and [T]-verified per box by `m4fix_recon_v1.py`; validity kernel-checked
below. -/
-- STANDING: DATA
def m4res_1_1_3_3_4_7_11 : M4Res :=
  ⟨[1, 1, 3, 3, 4, 7, 11], 1, 1, 1, 1, 1, 0, 0, [(6, 9)],
    some (9 / 7 : ℚ), some (9 / 7 : ℚ), some (9 / 7 : ℚ), some 1, some 1, none, none⟩

theorem m4resData_1_1_3_3_4_7_11 : M4ResData m4res_1_1_3_3_4_7_11 := by
  simp [M4ResData, m4res_1_1_3_3_4_7_11, InLeafEnvB] <;> norm_num

#print axioms m4resData_1_1_3_3_4_7_11

/-- `m4res_1_1_3_4_4_7_11`: the CONSTRUCTED residual-certificate record of the C3-killed box
(t = [1, 3, 4, 4, 7, 11], merged U-closure key aA): shape fields from `m4fix_res_v1.jsonl`
(built from `j2_admit_cert2_checkpoint.jsonl`), leaf-kind / frontier / lzones
fields from the instrumented re-run `m4comp_cert_ckpt_v1.jsonl`.  Reconstructed
live and [T]-verified per box by `m4fix_recon_v1.py`; validity kernel-checked
below. -/
-- STANDING: DATA
def m4res_1_1_3_4_4_7_11 : M4Res :=
  ⟨[1, 1, 3, 4, 4, 7, 11], 1, 1, 1, 1, 1, 0, 0, [(6, 9)],
    some (9 / 7 : ℚ), some (9 / 7 : ℚ), some (9 / 7 : ℚ), some 1, some 1, none, none⟩

theorem m4resData_1_1_3_4_4_7_11 : M4ResData m4res_1_1_3_4_4_7_11 := by
  simp [M4ResData, m4res_1_1_3_4_4_7_11, InLeafEnvB] <;> norm_num

#print axioms m4resData_1_1_3_4_4_7_11

/-- `m4res_1_1_3_4_7_10_11`: the CONSTRUCTED residual-certificate record of the C3-killed box
(t = [1, 3, 4, 7, 10, 11], merged U-closure key aA): shape fields from `m4fix_res_v1.jsonl`
(built from `j2_admit_cert2_checkpoint.jsonl`), leaf-kind / frontier / lzones
fields from the instrumented re-run `m4comp_cert_ckpt_v1.jsonl`.  Reconstructed
live and [T]-verified per box by `m4fix_recon_v1.py`; validity kernel-checked
below. -/
-- STANDING: DATA
def m4res_1_1_3_4_7_10_11 : M4Res :=
  ⟨[1, 1, 3, 4, 7, 10, 11], 1, 1, 1, 1, 1, 0, 0, [(5, 9)],
    some (9 / 7 : ℚ), some (9 / 7 : ℚ), some (9 / 7 : ℚ), some 1, some 1, none, none⟩

theorem m4resData_1_1_3_4_7_10_11 : M4ResData m4res_1_1_3_4_7_10_11 := by
  simp [M4ResData, m4res_1_1_3_4_7_10_11, InLeafEnvB] <;> norm_num

#print axioms m4resData_1_1_3_4_7_10_11

/-- `m4res_1_1_3_4_7_11_11`: the CONSTRUCTED residual-certificate record of the C3-killed box
(t = [1, 3, 4, 7, 11, 11], merged U-closure key aA): shape fields from `m4fix_res_v1.jsonl`
(built from `j2_admit_cert2_checkpoint.jsonl`), leaf-kind / frontier / lzones
fields from the instrumented re-run `m4comp_cert_ckpt_v1.jsonl`.  Reconstructed
live and [T]-verified per box by `m4fix_recon_v1.py`; validity kernel-checked
below. -/
-- STANDING: DATA
def m4res_1_1_3_4_7_11_11 : M4Res :=
  ⟨[1, 1, 3, 4, 7, 11, 11], 1, 1, 1, 1, 1, 0, 0, [(5, 9)],
    some (9 / 7 : ℚ), some (9 / 7 : ℚ), some (9 / 7 : ℚ), some 1, some 1, none, none⟩

theorem m4resData_1_1_3_4_7_11_11 : M4ResData m4res_1_1_3_4_7_11_11 := by
  simp [M4ResData, m4res_1_1_3_4_7_11_11, InLeafEnvB] <;> norm_num

#print axioms m4resData_1_1_3_4_7_11_11

/-- `m4res_1_1_3_4_7_11_14`: the CONSTRUCTED residual-certificate record of the C3-killed box
(t = [1, 3, 4, 7, 11, 14], merged U-closure key aA): shape fields from `m4fix_res_v1.jsonl`
(built from `j2_admit_cert2_checkpoint.jsonl`), leaf-kind / frontier / lzones
fields from the instrumented re-run `m4comp_cert_ckpt_v1.jsonl`.  Reconstructed
live and [T]-verified per box by `m4fix_recon_v1.py`; validity kernel-checked
below. -/
-- STANDING: DATA
def m4res_1_1_3_4_7_11_14 : M4Res :=
  ⟨[1, 1, 3, 4, 7, 11, 14], 1, 1, 1, 1, 1, 0, 0, [(5, 9)],
    some (9 / 7 : ℚ), some (9 / 7 : ℚ), some (9 / 7 : ℚ), some 1, some 1, none, none⟩

theorem m4resData_1_1_3_4_7_11_14 : M4ResData m4res_1_1_3_4_7_11_14 := by
  simp [M4ResData, m4res_1_1_3_4_7_11_14, InLeafEnvB] <;> norm_num

#print axioms m4resData_1_1_3_4_7_11_14

/-- `m4res_1_1_3_6_12_13_15`: the CONSTRUCTED residual-certificate record of the C3-killed box
(t = [1, 3, 6, 12, 13, 15], merged U-closure key aA): shape fields from `m4fix_res_v1.jsonl`
(built from `j2_admit_cert2_checkpoint.jsonl`), leaf-kind / frontier / lzones
fields from the instrumented re-run `m4comp_cert_ckpt_v1.jsonl`.  Reconstructed
live and [T]-verified per box by `m4fix_recon_v1.py`; validity kernel-checked
below. -/
-- STANDING: DATA
def m4res_1_1_3_6_12_13_15 : M4Res :=
  ⟨[1, 1, 3, 6, 12, 13, 15], 1, 1, 1, 1, 1, 0, 0, [(7, 17)],
    some (5 / 3 : ℚ), some (5 / 3 : ℚ), some (5 / 3 : ℚ), some 1, some 1, none, none⟩

theorem m4resData_1_1_3_6_12_13_15 : M4ResData m4res_1_1_3_6_12_13_15 := by
  simp [M4ResData, m4res_1_1_3_6_12_13_15, InLeafEnvB] <;> norm_num

#print axioms m4resData_1_1_3_6_12_13_15

/-- `m4res_1_1_3_7_10_12_14`: the CONSTRUCTED residual-certificate record of the C3-killed box
(t = [1, 3, 7, 10, 12, 14], merged U-closure key aA): shape fields from `m4fix_res_v1.jsonl`
(built from `j2_admit_cert2_checkpoint.jsonl`), leaf-kind / frontier / lzones
fields from the instrumented re-run `m4comp_cert_ckpt_v1.jsonl`.  Reconstructed
live and [T]-verified per box by `m4fix_recon_v1.py`; validity kernel-checked
below. -/
-- STANDING: DATA
def m4res_1_1_3_7_10_12_14 : M4Res :=
  ⟨[1, 1, 3, 7, 10, 12, 14], 1, 1, 1, 1, 1, 0, 0, [(4, 9)],
    some (98 / 27 : ℚ), some (98 / 27 : ℚ), some (98 / 27 : ℚ), some 1, some 1, none, none⟩

theorem m4resData_1_1_3_7_10_12_14 : M4ResData m4res_1_1_3_7_10_12_14 := by
  simp [M4ResData, m4res_1_1_3_7_10_12_14, InLeafEnvB] <;> norm_num

#print axioms m4resData_1_1_3_7_10_12_14

/-- `m4res_1_1_4_11_11_13_15`: the CONSTRUCTED residual-certificate record of the C3-killed box
(t = [1, 4, 11, 11, 13, 15], merged U-closure key aA): shape fields from `m4fix_res_v1.jsonl`
(built from `j2_admit_cert2_checkpoint.jsonl`), leaf-kind / frontier / lzones
fields from the instrumented re-run `m4comp_cert_ckpt_v1.jsonl`.  Reconstructed
live and [T]-verified per box by `m4fix_recon_v1.py`; validity kernel-checked
below. -/
-- STANDING: DATA
def m4res_1_1_4_11_11_13_15 : M4Res :=
  ⟨[1, 1, 4, 11, 11, 13, 15], 1, 1, 1, 1, 1, 0, 0, [(7, 17)],
    some (82 / 25 : ℚ), some (82 / 25 : ℚ), some (82 / 25 : ℚ), some 1, some 1, none, none⟩

theorem m4resData_1_1_4_11_11_13_15 : M4ResData m4res_1_1_4_11_11_13_15 := by
  simp [M4ResData, m4res_1_1_4_11_11_13_15, InLeafEnvB] <;> norm_num

#print axioms m4resData_1_1_4_11_11_13_15

/-- `m4res_1_1_4_4_11_13_15`: the CONSTRUCTED residual-certificate record of the C3-killed box
(t = [1, 4, 4, 11, 13, 15], merged U-closure key aA): shape fields from `m4fix_res_v1.jsonl`
(built from `j2_admit_cert2_checkpoint.jsonl`), leaf-kind / frontier / lzones
fields from the instrumented re-run `m4comp_cert_ckpt_v1.jsonl`.  Reconstructed
live and [T]-verified per box by `m4fix_recon_v1.py`; validity kernel-checked
below. -/
-- STANDING: DATA
def m4res_1_1_4_4_11_13_15 : M4Res :=
  ⟨[1, 1, 4, 4, 11, 13, 15], 1, 1, 1, 1, 1, 0, 0, [(7, 17)],
    some (82 / 25 : ℚ), some (82 / 25 : ℚ), some (82 / 25 : ℚ), some 1, some 1, none, none⟩

theorem m4resData_1_1_4_4_11_13_15 : M4ResData m4res_1_1_4_4_11_13_15 := by
  simp [M4ResData, m4res_1_1_4_4_11_13_15, InLeafEnvB] <;> norm_num

#print axioms m4resData_1_1_4_4_11_13_15

/-- `m4res_1_1_4_4_4_6_15`: the CONSTRUCTED residual-certificate record of the C3-killed box
(t = [1, 4, 4, 4, 6, 15], merged U-closure key aA): shape fields from `m4fix_res_v1.jsonl`
(built from `j2_admit_cert2_checkpoint.jsonl`), leaf-kind / frontier / lzones
fields from the instrumented re-run `m4comp_cert_ckpt_v1.jsonl`.  Reconstructed
live and [T]-verified per box by `m4fix_recon_v1.py`; validity kernel-checked
below. -/
-- STANDING: DATA
def m4res_1_1_4_4_4_6_15 : M4Res :=
  ⟨[1, 1, 4, 4, 4, 6, 15], 1, 1, 1, 1, 1, 0, 0, [(7, 17)],
    some (49 / 15 : ℚ), some (49 / 15 : ℚ), some (49 / 15 : ℚ), some 1, some 1, none, none⟩

theorem m4resData_1_1_4_4_4_6_15 : M4ResData m4res_1_1_4_4_4_6_15 := by
  simp [M4ResData, m4res_1_1_4_4_4_6_15, InLeafEnvB] <;> norm_num

#print axioms m4resData_1_1_4_4_4_6_15

/-- `m4res_1_1_4_4_6_11_15`: the CONSTRUCTED residual-certificate record of the C3-killed box
(t = [1, 4, 4, 6, 11, 15], merged U-closure key aA): shape fields from `m4fix_res_v1.jsonl`
(built from `j2_admit_cert2_checkpoint.jsonl`), leaf-kind / frontier / lzones
fields from the instrumented re-run `m4comp_cert_ckpt_v1.jsonl`.  Reconstructed
live and [T]-verified per box by `m4fix_recon_v1.py`; validity kernel-checked
below. -/
-- STANDING: DATA
def m4res_1_1_4_4_6_11_15 : M4Res :=
  ⟨[1, 1, 4, 4, 6, 11, 15], 1, 1, 1, 1, 1, 0, 0, [(7, 17)],
    some (49 / 15 : ℚ), some (49 / 15 : ℚ), some (49 / 15 : ℚ), some 1, some 1, none, none⟩

theorem m4resData_1_1_4_4_6_11_15 : M4ResData m4res_1_1_4_4_6_11_15 := by
  simp [M4ResData, m4res_1_1_4_4_6_11_15, InLeafEnvB] <;> norm_num

#print axioms m4resData_1_1_4_4_6_11_15

/-- `m4res_1_1_4_4_6_13_15`: the CONSTRUCTED residual-certificate record of the C3-killed box
(t = [1, 4, 4, 6, 13, 15], merged U-closure key aA): shape fields from `m4fix_res_v1.jsonl`
(built from `j2_admit_cert2_checkpoint.jsonl`), leaf-kind / frontier / lzones
fields from the instrumented re-run `m4comp_cert_ckpt_v1.jsonl`.  Reconstructed
live and [T]-verified per box by `m4fix_recon_v1.py`; validity kernel-checked
below. -/
-- STANDING: DATA
def m4res_1_1_4_4_6_13_15 : M4Res :=
  ⟨[1, 1, 4, 4, 6, 13, 15], 1, 1, 1, 1, 1, 0, 0, [(7, 17)],
    some (82 / 25 : ℚ), some (82 / 25 : ℚ), some (82 / 25 : ℚ), some 1, some 1, none, none⟩

theorem m4resData_1_1_4_4_6_13_15 : M4ResData m4res_1_1_4_4_6_13_15 := by
  simp [M4ResData, m4res_1_1_4_4_6_13_15, InLeafEnvB] <;> norm_num

#print axioms m4resData_1_1_4_4_6_13_15

/-- `m4res_1_1_4_4_6_6_15`: the CONSTRUCTED residual-certificate record of the C3-killed box
(t = [1, 4, 4, 6, 6, 15], merged U-closure key aA): shape fields from `m4fix_res_v1.jsonl`
(built from `j2_admit_cert2_checkpoint.jsonl`), leaf-kind / frontier / lzones
fields from the instrumented re-run `m4comp_cert_ckpt_v1.jsonl`.  Reconstructed
live and [T]-verified per box by `m4fix_recon_v1.py`; validity kernel-checked
below. -/
-- STANDING: DATA
def m4res_1_1_4_4_6_6_15 : M4Res :=
  ⟨[1, 1, 4, 4, 6, 6, 15], 1, 1, 1, 1, 1, 0, 0, [(7, 17)],
    some (49 / 15 : ℚ), some (49 / 15 : ℚ), some (49 / 15 : ℚ), some 1, some 1, none, none⟩

theorem m4resData_1_1_4_4_6_6_15 : M4ResData m4res_1_1_4_4_6_6_15 := by
  simp [M4ResData, m4res_1_1_4_4_6_6_15, InLeafEnvB] <;> norm_num

#print axioms m4resData_1_1_4_4_6_6_15

/-- `m4res_1_1_4_5_6_8_12`: the CONSTRUCTED residual-certificate record of the C3-killed box
(t = [1, 4, 5, 6, 8, 12], merged U-closure key aA): shape fields from `m4fix_res_v1.jsonl`
(built from `j2_admit_cert2_checkpoint.jsonl`), leaf-kind / frontier / lzones
fields from the instrumented re-run `m4comp_cert_ckpt_v1.jsonl`.  Reconstructed
live and [T]-verified per box by `m4fix_recon_v1.py`; validity kernel-checked
below. -/
-- STANDING: DATA
def m4res_1_1_4_5_6_8_12 : M4Res :=
  ⟨[1, 1, 4, 5, 6, 8, 12], 16, 40, 10, 1, 10, 6, 0, [(4, 17), (5, 17), (6, 17), (6, 25), (7, 25), (7, 33)],
    some (50 / 23 : ℚ), some (34 / 15 : ℚ), some (16830 / 3703 : ℚ), some 5, some 9, some 6, some 10⟩

theorem m4resData_1_1_4_5_6_8_12 : M4ResData m4res_1_1_4_5_6_8_12 := by
  simp [M4ResData, m4res_1_1_4_5_6_8_12, InLeafEnvB] <;> norm_num

#print axioms m4resData_1_1_4_5_6_8_12

/-- `m4res_1_1_4_6_11_11_15`: the CONSTRUCTED residual-certificate record of the C3-killed box
(t = [1, 4, 6, 11, 11, 15], merged U-closure key aA): shape fields from `m4fix_res_v1.jsonl`
(built from `j2_admit_cert2_checkpoint.jsonl`), leaf-kind / frontier / lzones
fields from the instrumented re-run `m4comp_cert_ckpt_v1.jsonl`.  Reconstructed
live and [T]-verified per box by `m4fix_recon_v1.py`; validity kernel-checked
below. -/
-- STANDING: DATA
def m4res_1_1_4_6_11_11_15 : M4Res :=
  ⟨[1, 1, 4, 6, 11, 11, 15], 1, 1, 1, 1, 1, 0, 0, [(7, 17)],
    some (49 / 15 : ℚ), some (49 / 15 : ℚ), some (49 / 15 : ℚ), some 1, some 1, none, none⟩

theorem m4resData_1_1_4_6_11_11_15 : M4ResData m4res_1_1_4_6_11_11_15 := by
  simp [M4ResData, m4res_1_1_4_6_11_11_15, InLeafEnvB] <;> norm_num

#print axioms m4resData_1_1_4_6_11_11_15

/-- `m4res_1_1_4_6_11_13_15`: the CONSTRUCTED residual-certificate record of the C3-killed box
(t = [1, 4, 6, 11, 13, 15], merged U-closure key aA): shape fields from `m4fix_res_v1.jsonl`
(built from `j2_admit_cert2_checkpoint.jsonl`), leaf-kind / frontier / lzones
fields from the instrumented re-run `m4comp_cert_ckpt_v1.jsonl`.  Reconstructed
live and [T]-verified per box by `m4fix_recon_v1.py`; validity kernel-checked
below. -/
-- STANDING: DATA
def m4res_1_1_4_6_11_13_15 : M4Res :=
  ⟨[1, 1, 4, 6, 11, 13, 15], 1, 1, 1, 1, 1, 0, 0, [(7, 17)],
    some (82 / 25 : ℚ), some (82 / 25 : ℚ), some (82 / 25 : ℚ), some 1, some 1, none, none⟩

theorem m4resData_1_1_4_6_11_13_15 : M4ResData m4res_1_1_4_6_11_13_15 := by
  simp [M4ResData, m4res_1_1_4_6_11_13_15, InLeafEnvB] <;> norm_num

#print axioms m4resData_1_1_4_6_11_13_15

/-- `m4res_1_1_4_6_13_13_15`: the CONSTRUCTED residual-certificate record of the C3-killed box
(t = [1, 4, 6, 13, 13, 15], merged U-closure key aA): shape fields from `m4fix_res_v1.jsonl`
(built from `j2_admit_cert2_checkpoint.jsonl`), leaf-kind / frontier / lzones
fields from the instrumented re-run `m4comp_cert_ckpt_v1.jsonl`.  Reconstructed
live and [T]-verified per box by `m4fix_recon_v1.py`; validity kernel-checked
below. -/
-- STANDING: DATA
def m4res_1_1_4_6_13_13_15 : M4Res :=
  ⟨[1, 1, 4, 6, 13, 13, 15], 1, 1, 1, 1, 1, 0, 0, [(7, 17)],
    some (82 / 25 : ℚ), some (82 / 25 : ℚ), some (82 / 25 : ℚ), some 1, some 1, none, none⟩

theorem m4resData_1_1_4_6_13_13_15 : M4ResData m4res_1_1_4_6_13_13_15 := by
  simp [M4ResData, m4res_1_1_4_6_13_13_15, InLeafEnvB] <;> norm_num

#print axioms m4resData_1_1_4_6_13_13_15

/-- `m4res_1_1_4_6_6_11_15`: the CONSTRUCTED residual-certificate record of the C3-killed box
(t = [1, 4, 6, 6, 11, 15], merged U-closure key aA): shape fields from `m4fix_res_v1.jsonl`
(built from `j2_admit_cert2_checkpoint.jsonl`), leaf-kind / frontier / lzones
fields from the instrumented re-run `m4comp_cert_ckpt_v1.jsonl`.  Reconstructed
live and [T]-verified per box by `m4fix_recon_v1.py`; validity kernel-checked
below. -/
-- STANDING: DATA
def m4res_1_1_4_6_6_11_15 : M4Res :=
  ⟨[1, 1, 4, 6, 6, 11, 15], 1, 1, 1, 1, 1, 0, 0, [(7, 17)],
    some (49 / 15 : ℚ), some (49 / 15 : ℚ), some (49 / 15 : ℚ), some 1, some 1, none, none⟩

theorem m4resData_1_1_4_6_6_11_15 : M4ResData m4res_1_1_4_6_6_11_15 := by
  simp [M4ResData, m4res_1_1_4_6_6_11_15, InLeafEnvB] <;> norm_num

#print axioms m4resData_1_1_4_6_6_11_15

/-- `m4res_1_1_4_6_6_13_15`: the CONSTRUCTED residual-certificate record of the C3-killed box
(t = [1, 4, 6, 6, 13, 15], merged U-closure key aA): shape fields from `m4fix_res_v1.jsonl`
(built from `j2_admit_cert2_checkpoint.jsonl`), leaf-kind / frontier / lzones
fields from the instrumented re-run `m4comp_cert_ckpt_v1.jsonl`.  Reconstructed
live and [T]-verified per box by `m4fix_recon_v1.py`; validity kernel-checked
below. -/
-- STANDING: DATA
def m4res_1_1_4_6_6_13_15 : M4Res :=
  ⟨[1, 1, 4, 6, 6, 13, 15], 1, 1, 1, 1, 1, 0, 0, [(7, 17)],
    some (82 / 25 : ℚ), some (82 / 25 : ℚ), some (82 / 25 : ℚ), some 1, some 1, none, none⟩

theorem m4resData_1_1_4_6_6_13_15 : M4ResData m4res_1_1_4_6_6_13_15 := by
  simp [M4ResData, m4res_1_1_4_6_6_13_15, InLeafEnvB] <;> norm_num

#print axioms m4resData_1_1_4_6_6_13_15

/-- `m4res_1_1_4_6_6_6_15`: the CONSTRUCTED residual-certificate record of the C3-killed box
(t = [1, 4, 6, 6, 6, 15], merged U-closure key aA): shape fields from `m4fix_res_v1.jsonl`
(built from `j2_admit_cert2_checkpoint.jsonl`), leaf-kind / frontier / lzones
fields from the instrumented re-run `m4comp_cert_ckpt_v1.jsonl`.  Reconstructed
live and [T]-verified per box by `m4fix_recon_v1.py`; validity kernel-checked
below. -/
-- STANDING: DATA
def m4res_1_1_4_6_6_6_15 : M4Res :=
  ⟨[1, 1, 4, 6, 6, 6, 15], 1, 1, 1, 1, 1, 0, 0, [(7, 17)],
    some (49 / 15 : ℚ), some (49 / 15 : ℚ), some (49 / 15 : ℚ), some 1, some 1, none, none⟩

theorem m4resData_1_1_4_6_6_6_15 : M4ResData m4res_1_1_4_6_6_6_15 := by
  simp [M4ResData, m4res_1_1_4_6_6_6_15, InLeafEnvB] <;> norm_num

#print axioms m4resData_1_1_4_6_6_6_15

end Fresh.MechDataBatch

