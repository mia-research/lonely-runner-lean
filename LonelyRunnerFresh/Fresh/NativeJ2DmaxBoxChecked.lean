import Fresh.NativeJ2RatioEnvelopeChecked

namespace Fresh.NativeJ2DmaxBoxChecked

open NativeRationalGuardPaths NativeJ2RatioEnvelopeChecked

def dmaxBox : List Guard := [
  ⟨0, 5, 7 / 1, true⟩,
  ⟨0, 6, 10000 / 649, false⟩,
  ⟨1, 6, 10000 / 1837, false⟩,
  ⟨2, 6, 10000 / 2489, false⟩,
  ⟨3, 6, 625 / 197, false⟩,
  ⟨4, 6, 10000 / 4037, false⟩,
  ⟨5, 6, 10000 / 4543, false⟩,
  ⟨6, 0, 661 / 10000, false⟩,
  ⟨6, 1, 919 / 5000, false⟩,
  ⟨6, 2, 249 / 1000, false⟩,
  ⟨6, 3, 319 / 1000, false⟩,
  ⟨6, 4, 2019 / 5000, false⟩,
  ⟨6, 5, 284 / 625, false⟩
]

def box1_0 : List (Guard × List Guard) :=
  (part1_0.map Prod.fst).zip [
  [],
  [],
  [],
  [⟨0, 5, 7 / 1, true⟩, ⟨5, 6, 10000 / 4543, false⟩, ⟨6, 1, 919 / 5000, false⟩],
  [⟨0, 5, 7 / 1, true⟩, ⟨5, 6, 10000 / 4543, false⟩, ⟨6, 1, 919 / 5000, false⟩],
  [⟨0, 5, 7 / 1, true⟩, ⟨5, 6, 10000 / 4543, false⟩, ⟨6, 1, 919 / 5000, false⟩],
  [⟨0, 5, 7 / 1, true⟩, ⟨5, 6, 10000 / 4543, false⟩, ⟨6, 1, 919 / 5000, false⟩],
  [⟨0, 5, 7 / 1, true⟩, ⟨5, 6, 10000 / 4543, false⟩, ⟨6, 2, 249 / 1000, false⟩],
  [⟨0, 5, 7 / 1, true⟩, ⟨5, 6, 10000 / 4543, false⟩, ⟨6, 2, 249 / 1000, false⟩],
  [⟨0, 5, 7 / 1, true⟩, ⟨5, 6, 10000 / 4543, false⟩, ⟨6, 2, 249 / 1000, false⟩],
  [⟨0, 5, 7 / 1, true⟩, ⟨5, 6, 10000 / 4543, false⟩, ⟨6, 2, 249 / 1000, false⟩],
  [⟨0, 5, 7 / 1, true⟩, ⟨5, 6, 10000 / 4543, false⟩, ⟨6, 2, 249 / 1000, false⟩],
  [⟨0, 5, 7 / 1, true⟩, ⟨5, 3, 33 / 47, true⟩],
  [⟨0, 5, 7 / 1, true⟩, ⟨5, 3, 33 / 47, true⟩],
  [⟨0, 5, 7 / 1, true⟩, ⟨5, 3, 33 / 47, true⟩],
  [⟨0, 5, 7 / 1, true⟩, ⟨5, 3, 33 / 47, true⟩],
  [⟨0, 5, 7 / 1, true⟩, ⟨5, 3, 33 / 47, true⟩],
  [⟨0, 5, 7 / 1, true⟩, ⟨5, 3, 33 / 47, true⟩],
  [⟨0, 5, 7 / 1, true⟩, ⟨5, 6, 10000 / 4543, false⟩, ⟨6, 4, 2019 / 5000, false⟩],
  [⟨0, 5, 7 / 1, true⟩, ⟨5, 6, 10000 / 4543, false⟩, ⟨6, 4, 2019 / 5000, false⟩],
  [⟨0, 5, 7 / 1, true⟩, ⟨5, 6, 10000 / 4543, false⟩, ⟨6, 4, 2019 / 5000, false⟩],
  [⟨0, 5, 7 / 1, true⟩, ⟨5, 6, 10000 / 4543, false⟩, ⟨6, 4, 2019 / 5000, false⟩],
  [⟨0, 5, 7 / 1, true⟩, ⟨5, 6, 10000 / 4543, false⟩, ⟨6, 4, 2019 / 5000, false⟩],
  [⟨0, 5, 7 / 1, true⟩, ⟨5, 6, 10000 / 4543, false⟩, ⟨6, 4, 2019 / 5000, false⟩]
]

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem box1_0_checked : box1_0.all (fun row =>
    verify (dmaxBox ++ selectors1) row.1 row.2) = true := by decide +kernel
set_option maxRecDepth 12000 in
private theorem box1_0_targets : box1_0.map Prod.fst = part1_0.map Prod.fst := by decide +kernel

def box1_1 : List (Guard × List Guard) :=
  (part1_1.map Prod.fst).zip [
  [⟨0, 5, 7 / 1, true⟩, ⟨5, 6, 10000 / 4543, false⟩, ⟨6, 4, 2019 / 5000, false⟩],
  [⟨0, 5, 7 / 1, true⟩],
  [⟨0, 5, 7 / 1, true⟩],
  [⟨0, 5, 7 / 1, true⟩],
  [⟨0, 5, 7 / 1, true⟩],
  [⟨0, 5, 7 / 1, true⟩],
  [⟨0, 5, 7 / 1, true⟩],
  [⟨0, 5, 7 / 1, true⟩],
  [⟨0, 5, 7 / 1, true⟩, ⟨5, 6, 10000 / 4543, false⟩],
  [⟨0, 5, 7 / 1, true⟩, ⟨5, 6, 10000 / 4543, false⟩],
  [⟨0, 5, 7 / 1, true⟩, ⟨5, 6, 10000 / 4543, false⟩],
  [⟨0, 5, 7 / 1, true⟩, ⟨5, 6, 10000 / 4543, false⟩],
  [⟨0, 5, 7 / 1, true⟩, ⟨5, 6, 10000 / 4543, false⟩],
  [⟨1, 6, 10000 / 1837, false⟩, ⟨6, 4, 2019 / 5000, false⟩, ⟨4, 0, 9 / 55, true⟩],
  [⟨1, 6, 10000 / 1837, false⟩, ⟨6, 4, 2019 / 5000, false⟩, ⟨4, 0, 9 / 55, true⟩],
  [⟨1, 6, 10000 / 1837, false⟩, ⟨6, 4, 2019 / 5000, false⟩, ⟨4, 0, 9 / 55, true⟩],
  [⟨1, 6, 10000 / 1837, false⟩, ⟨6, 4, 2019 / 5000, false⟩, ⟨4, 0, 9 / 55, true⟩],
  [⟨1, 6, 10000 / 1837, false⟩, ⟨6, 4, 2019 / 5000, false⟩, ⟨4, 0, 9 / 55, true⟩],
  [],
  [],
  [],
  [⟨1, 6, 10000 / 1837, false⟩, ⟨6, 2, 249 / 1000, false⟩],
  [⟨1, 6, 10000 / 1837, false⟩, ⟨6, 2, 249 / 1000, false⟩],
  [⟨1, 6, 10000 / 1837, false⟩, ⟨6, 2, 249 / 1000, false⟩]
]

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem box1_1_checked : box1_1.all (fun row =>
    verify (dmaxBox ++ selectors1) row.1 row.2) = true := by decide +kernel
set_option maxRecDepth 12000 in
private theorem box1_1_targets : box1_1.map Prod.fst = part1_1.map Prod.fst := by decide +kernel

def box1_2 : List (Guard × List Guard) :=
  (part1_2.map Prod.fst).zip [
  [⟨1, 6, 10000 / 1837, false⟩, ⟨6, 2, 249 / 1000, false⟩],
  [⟨1, 6, 10000 / 1837, false⟩, ⟨6, 2, 249 / 1000, false⟩],
  [⟨1, 6, 10000 / 1837, false⟩, ⟨6, 3, 319 / 1000, false⟩],
  [⟨1, 6, 10000 / 1837, false⟩, ⟨6, 3, 319 / 1000, false⟩],
  [⟨1, 6, 10000 / 1837, false⟩, ⟨6, 3, 319 / 1000, false⟩],
  [⟨1, 6, 10000 / 1837, false⟩, ⟨6, 3, 319 / 1000, false⟩],
  [⟨1, 6, 10000 / 1837, false⟩, ⟨6, 3, 319 / 1000, false⟩],
  [⟨1, 6, 10000 / 1837, false⟩, ⟨6, 3, 319 / 1000, false⟩],
  [⟨1, 6, 10000 / 1837, false⟩, ⟨6, 4, 2019 / 5000, false⟩],
  [⟨1, 6, 10000 / 1837, false⟩, ⟨6, 4, 2019 / 5000, false⟩],
  [⟨1, 6, 10000 / 1837, false⟩, ⟨6, 4, 2019 / 5000, false⟩],
  [⟨1, 6, 10000 / 1837, false⟩, ⟨6, 4, 2019 / 5000, false⟩],
  [⟨1, 6, 10000 / 1837, false⟩, ⟨6, 4, 2019 / 5000, false⟩],
  [⟨1, 6, 10000 / 1837, false⟩, ⟨6, 4, 2019 / 5000, false⟩],
  [⟨1, 6, 10000 / 1837, false⟩, ⟨6, 4, 2019 / 5000, false⟩],
  [⟨1, 6, 10000 / 1837, false⟩, ⟨6, 5, 284 / 625, false⟩],
  [⟨1, 6, 10000 / 1837, false⟩, ⟨6, 5, 284 / 625, false⟩],
  [⟨1, 6, 10000 / 1837, false⟩, ⟨6, 5, 284 / 625, false⟩],
  [⟨1, 6, 10000 / 1837, false⟩, ⟨6, 5, 284 / 625, false⟩],
  [⟨1, 6, 10000 / 1837, false⟩, ⟨6, 5, 284 / 625, false⟩],
  [⟨1, 6, 10000 / 1837, false⟩, ⟨6, 5, 284 / 625, false⟩],
  [⟨1, 6, 10000 / 1837, false⟩, ⟨6, 5, 284 / 625, false⟩],
  [⟨1, 6, 10000 / 1837, false⟩, ⟨6, 5, 284 / 625, false⟩],
  [⟨1, 6, 10000 / 1837, false⟩]
]

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem box1_2_checked : box1_2.all (fun row =>
    verify (dmaxBox ++ selectors1) row.1 row.2) = true := by decide +kernel
set_option maxRecDepth 12000 in
private theorem box1_2_targets : box1_2.map Prod.fst = part1_2.map Prod.fst := by decide +kernel

def box1_3 : List (Guard × List Guard) :=
  (part1_3.map Prod.fst).zip [
  [⟨1, 6, 10000 / 1837, false⟩],
  [⟨1, 6, 10000 / 1837, false⟩],
  [⟨1, 6, 10000 / 1837, false⟩],
  [⟨1, 6, 10000 / 1837, false⟩],
  [⟨2, 6, 10000 / 2489, false⟩, ⟨6, 4, 2019 / 5000, false⟩, ⟨4, 0, 9 / 55, true⟩],
  [⟨2, 6, 10000 / 2489, false⟩, ⟨6, 4, 2019 / 5000, false⟩, ⟨4, 0, 9 / 55, true⟩],
  [⟨2, 6, 10000 / 2489, false⟩, ⟨6, 4, 2019 / 5000, false⟩, ⟨4, 0, 9 / 55, true⟩],
  [⟨2, 6, 10000 / 2489, false⟩, ⟨6, 4, 2019 / 5000, false⟩, ⟨4, 0, 9 / 55, true⟩],
  [⟨2, 6, 10000 / 2489, false⟩, ⟨6, 4, 2019 / 5000, false⟩, ⟨4, 0, 9 / 55, true⟩],
  [⟨2, 6, 10000 / 2489, false⟩, ⟨6, 1, 919 / 5000, false⟩],
  [⟨2, 6, 10000 / 2489, false⟩, ⟨6, 1, 919 / 5000, false⟩],
  [⟨2, 6, 10000 / 2489, false⟩, ⟨6, 1, 919 / 5000, false⟩],
  [⟨2, 6, 10000 / 2489, false⟩, ⟨6, 1, 919 / 5000, false⟩],
  [⟨2, 6, 10000 / 2489, false⟩, ⟨6, 1, 919 / 5000, false⟩],
  [⟨2, 6, 10000 / 2489, false⟩, ⟨6, 1, 919 / 5000, false⟩],
  [],
  [],
  [],
  [],
  [⟨2, 6, 10000 / 2489, false⟩, ⟨6, 3, 319 / 1000, false⟩],
  [⟨2, 6, 10000 / 2489, false⟩, ⟨6, 3, 319 / 1000, false⟩],
  [⟨2, 6, 10000 / 2489, false⟩, ⟨6, 3, 319 / 1000, false⟩],
  [⟨2, 6, 10000 / 2489, false⟩, ⟨6, 3, 319 / 1000, false⟩],
  [⟨2, 6, 10000 / 2489, false⟩, ⟨6, 3, 319 / 1000, false⟩]
]

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem box1_3_checked : box1_3.all (fun row =>
    verify (dmaxBox ++ selectors1) row.1 row.2) = true := by decide +kernel
set_option maxRecDepth 12000 in
private theorem box1_3_targets : box1_3.map Prod.fst = part1_3.map Prod.fst := by decide +kernel

def box1_4 : List (Guard × List Guard) :=
  (part1_4.map Prod.fst).zip [
  [⟨2, 6, 10000 / 2489, false⟩, ⟨6, 3, 319 / 1000, false⟩],
  [⟨2, 6, 10000 / 2489, false⟩, ⟨6, 3, 319 / 1000, false⟩],
  [⟨2, 6, 10000 / 2489, false⟩, ⟨6, 4, 2019 / 5000, false⟩],
  [⟨2, 6, 10000 / 2489, false⟩, ⟨6, 4, 2019 / 5000, false⟩],
  [⟨2, 6, 10000 / 2489, false⟩, ⟨6, 4, 2019 / 5000, false⟩],
  [⟨2, 6, 10000 / 2489, false⟩, ⟨6, 4, 2019 / 5000, false⟩],
  [⟨2, 6, 10000 / 2489, false⟩, ⟨6, 4, 2019 / 5000, false⟩],
  [⟨2, 6, 10000 / 2489, false⟩, ⟨6, 4, 2019 / 5000, false⟩],
  [⟨2, 6, 10000 / 2489, false⟩, ⟨6, 4, 2019 / 5000, false⟩],
  [⟨2, 6, 10000 / 2489, false⟩, ⟨6, 4, 2019 / 5000, false⟩],
  [⟨2, 6, 10000 / 2489, false⟩, ⟨6, 5, 284 / 625, false⟩],
  [⟨2, 6, 10000 / 2489, false⟩, ⟨6, 5, 284 / 625, false⟩],
  [⟨2, 6, 10000 / 2489, false⟩, ⟨6, 5, 284 / 625, false⟩],
  [⟨2, 6, 10000 / 2489, false⟩, ⟨6, 5, 284 / 625, false⟩],
  [⟨2, 6, 10000 / 2489, false⟩, ⟨6, 5, 284 / 625, false⟩],
  [⟨2, 6, 10000 / 2489, false⟩, ⟨6, 5, 284 / 625, false⟩],
  [⟨2, 6, 10000 / 2489, false⟩, ⟨6, 5, 284 / 625, false⟩],
  [⟨2, 6, 10000 / 2489, false⟩, ⟨6, 5, 284 / 625, false⟩],
  [⟨2, 6, 10000 / 2489, false⟩, ⟨6, 5, 284 / 625, false⟩],
  [⟨2, 6, 10000 / 2489, false⟩],
  [⟨2, 6, 10000 / 2489, false⟩],
  [⟨2, 6, 10000 / 2489, false⟩],
  [⟨2, 6, 10000 / 2489, false⟩],
  [⟨2, 6, 10000 / 2489, false⟩]
]

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem box1_4_checked : box1_4.all (fun row =>
    verify (dmaxBox ++ selectors1) row.1 row.2) = true := by decide +kernel
set_option maxRecDepth 12000 in
private theorem box1_4_targets : box1_4.map Prod.fst = part1_4.map Prod.fst := by decide +kernel

def box1_5 : List (Guard × List Guard) :=
  (part1_5.map Prod.fst).zip [
  [⟨2, 6, 10000 / 2489, false⟩],
  [⟨3, 5, 33 / 23, true⟩, ⟨5, 6, 10000 / 4543, false⟩, ⟨6, 4, 2019 / 5000, false⟩, ⟨4, 0, 9 / 55, true⟩],
  [⟨3, 5, 33 / 23, true⟩, ⟨5, 6, 10000 / 4543, false⟩, ⟨6, 4, 2019 / 5000, false⟩, ⟨4, 0, 9 / 55, true⟩],
  [⟨3, 5, 33 / 23, true⟩, ⟨5, 6, 10000 / 4543, false⟩, ⟨6, 4, 2019 / 5000, false⟩, ⟨4, 0, 9 / 55, true⟩],
  [⟨3, 5, 33 / 23, true⟩, ⟨5, 6, 10000 / 4543, false⟩, ⟨6, 4, 2019 / 5000, false⟩, ⟨4, 0, 9 / 55, true⟩],
  [⟨3, 5, 33 / 23, true⟩, ⟨5, 6, 10000 / 4543, false⟩, ⟨6, 4, 2019 / 5000, false⟩, ⟨4, 0, 9 / 55, true⟩],
  [⟨3, 5, 33 / 23, true⟩, ⟨5, 6, 10000 / 4543, false⟩, ⟨6, 4, 2019 / 5000, false⟩, ⟨4, 0, 9 / 55, true⟩],
  [⟨3, 5, 33 / 23, true⟩, ⟨5, 6, 10000 / 4543, false⟩, ⟨6, 1, 919 / 5000, false⟩],
  [⟨3, 5, 33 / 23, true⟩, ⟨5, 6, 10000 / 4543, false⟩, ⟨6, 1, 919 / 5000, false⟩],
  [⟨3, 5, 33 / 23, true⟩, ⟨5, 6, 10000 / 4543, false⟩, ⟨6, 1, 919 / 5000, false⟩],
  [⟨3, 5, 33 / 23, true⟩, ⟨5, 6, 10000 / 4543, false⟩, ⟨6, 1, 919 / 5000, false⟩],
  [⟨3, 5, 33 / 23, true⟩, ⟨5, 6, 10000 / 4543, false⟩, ⟨6, 1, 919 / 5000, false⟩],
  [⟨3, 5, 33 / 23, true⟩, ⟨5, 6, 10000 / 4543, false⟩, ⟨6, 1, 919 / 5000, false⟩],
  [⟨3, 5, 33 / 23, true⟩, ⟨5, 6, 10000 / 4543, false⟩, ⟨6, 2, 249 / 1000, false⟩],
  [⟨3, 5, 33 / 23, true⟩, ⟨5, 6, 10000 / 4543, false⟩, ⟨6, 2, 249 / 1000, false⟩],
  [⟨3, 5, 33 / 23, true⟩, ⟨5, 6, 10000 / 4543, false⟩, ⟨6, 2, 249 / 1000, false⟩],
  [⟨3, 5, 33 / 23, true⟩, ⟨5, 6, 10000 / 4543, false⟩, ⟨6, 2, 249 / 1000, false⟩],
  [⟨3, 5, 33 / 23, true⟩, ⟨5, 6, 10000 / 4543, false⟩, ⟨6, 2, 249 / 1000, false⟩],
  [⟨3, 5, 33 / 23, true⟩, ⟨5, 6, 10000 / 4543, false⟩, ⟨6, 2, 249 / 1000, false⟩],
  [],
  [],
  [],
  [],
  []
]

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem box1_5_checked : box1_5.all (fun row =>
    verify (dmaxBox ++ selectors1) row.1 row.2) = true := by decide +kernel
set_option maxRecDepth 12000 in
private theorem box1_5_targets : box1_5.map Prod.fst = part1_5.map Prod.fst := by decide +kernel

def box1_6 : List (Guard × List Guard) :=
  (part1_6.map Prod.fst).zip [
  [⟨3, 5, 33 / 23, true⟩, ⟨5, 6, 10000 / 4543, false⟩, ⟨6, 4, 2019 / 5000, false⟩],
  [⟨3, 5, 33 / 23, true⟩, ⟨5, 6, 10000 / 4543, false⟩, ⟨6, 4, 2019 / 5000, false⟩],
  [⟨3, 5, 33 / 23, true⟩, ⟨5, 6, 10000 / 4543, false⟩, ⟨6, 4, 2019 / 5000, false⟩],
  [⟨3, 5, 33 / 23, true⟩, ⟨5, 6, 10000 / 4543, false⟩, ⟨6, 4, 2019 / 5000, false⟩],
  [⟨3, 5, 33 / 23, true⟩, ⟨5, 6, 10000 / 4543, false⟩, ⟨6, 4, 2019 / 5000, false⟩],
  [⟨3, 5, 33 / 23, true⟩, ⟨5, 6, 10000 / 4543, false⟩, ⟨6, 4, 2019 / 5000, false⟩],
  [⟨3, 5, 33 / 23, true⟩, ⟨5, 6, 10000 / 4543, false⟩, ⟨6, 4, 2019 / 5000, false⟩],
  [⟨3, 5, 33 / 23, true⟩, ⟨5, 6, 10000 / 4543, false⟩, ⟨6, 4, 2019 / 5000, false⟩],
  [⟨3, 5, 33 / 23, true⟩, ⟨5, 6, 10000 / 4543, false⟩, ⟨6, 4, 2019 / 5000, false⟩],
  [⟨3, 5, 33 / 23, true⟩],
  [⟨3, 5, 33 / 23, true⟩],
  [⟨3, 5, 33 / 23, true⟩],
  [⟨3, 5, 33 / 23, true⟩],
  [⟨3, 5, 33 / 23, true⟩],
  [⟨3, 5, 33 / 23, true⟩],
  [⟨3, 5, 33 / 23, true⟩],
  [⟨3, 5, 33 / 23, true⟩],
  [⟨3, 5, 33 / 23, true⟩],
  [⟨3, 5, 33 / 23, true⟩],
  [⟨3, 5, 33 / 23, true⟩, ⟨5, 6, 10000 / 4543, false⟩],
  [⟨3, 5, 33 / 23, true⟩, ⟨5, 6, 10000 / 4543, false⟩],
  [⟨3, 5, 33 / 23, true⟩, ⟨5, 6, 10000 / 4543, false⟩],
  [⟨3, 5, 33 / 23, true⟩, ⟨5, 6, 10000 / 4543, false⟩],
  [⟨3, 5, 33 / 23, true⟩, ⟨5, 6, 10000 / 4543, false⟩]
]

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem box1_6_checked : box1_6.all (fun row =>
    verify (dmaxBox ++ selectors1) row.1 row.2) = true := by decide +kernel
set_option maxRecDepth 12000 in
private theorem box1_6_targets : box1_6.map Prod.fst = part1_6.map Prod.fst := by decide +kernel

def box1_7 : List (Guard × List Guard) :=
  (part1_7.map Prod.fst).zip [
  [⟨3, 5, 33 / 23, true⟩, ⟨5, 6, 10000 / 4543, false⟩],
  [⟨3, 5, 33 / 23, true⟩, ⟨5, 6, 10000 / 4543, false⟩],
  [⟨4, 0, 9 / 55, true⟩],
  [⟨4, 0, 9 / 55, true⟩],
  [⟨4, 0, 9 / 55, true⟩],
  [⟨4, 0, 9 / 55, true⟩],
  [⟨4, 0, 9 / 55, true⟩],
  [⟨4, 0, 9 / 55, true⟩],
  [⟨4, 0, 9 / 55, true⟩],
  [⟨4, 6, 10000 / 4037, false⟩, ⟨6, 1, 919 / 5000, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩, ⟨6, 1, 919 / 5000, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩, ⟨6, 1, 919 / 5000, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩, ⟨6, 1, 919 / 5000, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩, ⟨6, 1, 919 / 5000, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩, ⟨6, 1, 919 / 5000, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩, ⟨6, 1, 919 / 5000, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩, ⟨6, 2, 249 / 1000, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩, ⟨6, 2, 249 / 1000, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩, ⟨6, 2, 249 / 1000, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩, ⟨6, 2, 249 / 1000, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩, ⟨6, 2, 249 / 1000, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩, ⟨6, 2, 249 / 1000, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩, ⟨6, 2, 249 / 1000, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩, ⟨6, 2, 249 / 1000, false⟩]
]

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem box1_7_checked : box1_7.all (fun row =>
    verify (dmaxBox ++ selectors1) row.1 row.2) = true := by decide +kernel
set_option maxRecDepth 12000 in
private theorem box1_7_targets : box1_7.map Prod.fst = part1_7.map Prod.fst := by decide +kernel

def box1_8 : List (Guard × List Guard) :=
  (part1_8.map Prod.fst).zip [
  [⟨4, 6, 10000 / 4037, false⟩, ⟨6, 3, 319 / 1000, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩, ⟨6, 3, 319 / 1000, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩, ⟨6, 3, 319 / 1000, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩, ⟨6, 3, 319 / 1000, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩, ⟨6, 3, 319 / 1000, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩, ⟨6, 3, 319 / 1000, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩, ⟨6, 3, 319 / 1000, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩, ⟨6, 3, 319 / 1000, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩, ⟨6, 3, 319 / 1000, false⟩],
  [],
  [],
  [],
  [],
  [],
  [],
  [⟨4, 6, 10000 / 4037, false⟩, ⟨6, 5, 284 / 625, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩, ⟨6, 5, 284 / 625, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩, ⟨6, 5, 284 / 625, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩, ⟨6, 5, 284 / 625, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩, ⟨6, 5, 284 / 625, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩, ⟨6, 5, 284 / 625, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩, ⟨6, 5, 284 / 625, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩, ⟨6, 5, 284 / 625, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩, ⟨6, 5, 284 / 625, false⟩]
]

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem box1_8_checked : box1_8.all (fun row =>
    verify (dmaxBox ++ selectors1) row.1 row.2) = true := by decide +kernel
set_option maxRecDepth 12000 in
private theorem box1_8_targets : box1_8.map Prod.fst = part1_8.map Prod.fst := by decide +kernel

def box1_9 : List (Guard × List Guard) :=
  (part1_9.map Prod.fst).zip [
  [⟨4, 6, 10000 / 4037, false⟩, ⟨6, 5, 284 / 625, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩, ⟨6, 5, 284 / 625, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩],
  [⟨5, 6, 10000 / 4543, false⟩, ⟨6, 4, 2019 / 5000, false⟩, ⟨4, 0, 9 / 55, true⟩],
  [⟨5, 6, 10000 / 4543, false⟩, ⟨6, 4, 2019 / 5000, false⟩, ⟨4, 0, 9 / 55, true⟩],
  [⟨5, 6, 10000 / 4543, false⟩, ⟨6, 4, 2019 / 5000, false⟩, ⟨4, 0, 9 / 55, true⟩],
  [⟨5, 6, 10000 / 4543, false⟩, ⟨6, 4, 2019 / 5000, false⟩, ⟨4, 0, 9 / 55, true⟩],
  [⟨5, 6, 10000 / 4543, false⟩, ⟨6, 4, 2019 / 5000, false⟩, ⟨4, 0, 9 / 55, true⟩],
  [⟨5, 6, 10000 / 4543, false⟩, ⟨6, 4, 2019 / 5000, false⟩, ⟨4, 0, 9 / 55, true⟩],
  [⟨5, 6, 10000 / 4543, false⟩, ⟨6, 4, 2019 / 5000, false⟩, ⟨4, 0, 9 / 55, true⟩],
  [⟨5, 6, 10000 / 4543, false⟩, ⟨6, 4, 2019 / 5000, false⟩, ⟨4, 0, 9 / 55, true⟩],
  [⟨5, 6, 10000 / 4543, false⟩, ⟨6, 1, 919 / 5000, false⟩],
  [⟨5, 6, 10000 / 4543, false⟩, ⟨6, 1, 919 / 5000, false⟩],
  [⟨5, 6, 10000 / 4543, false⟩, ⟨6, 1, 919 / 5000, false⟩],
  [⟨5, 6, 10000 / 4543, false⟩, ⟨6, 1, 919 / 5000, false⟩],
  [⟨5, 6, 10000 / 4543, false⟩, ⟨6, 1, 919 / 5000, false⟩],
  [⟨5, 6, 10000 / 4543, false⟩, ⟨6, 1, 919 / 5000, false⟩]
]

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem box1_9_checked : box1_9.all (fun row =>
    verify (dmaxBox ++ selectors1) row.1 row.2) = true := by decide +kernel
set_option maxRecDepth 12000 in
private theorem box1_9_targets : box1_9.map Prod.fst = part1_9.map Prod.fst := by decide +kernel

def box1_10 : List (Guard × List Guard) :=
  (part1_10.map Prod.fst).zip [
  [⟨5, 6, 10000 / 4543, false⟩, ⟨6, 1, 919 / 5000, false⟩],
  [⟨5, 6, 10000 / 4543, false⟩, ⟨6, 1, 919 / 5000, false⟩],
  [⟨5, 6, 10000 / 4543, false⟩, ⟨6, 2, 249 / 1000, false⟩],
  [⟨5, 6, 10000 / 4543, false⟩, ⟨6, 2, 249 / 1000, false⟩],
  [⟨5, 6, 10000 / 4543, false⟩, ⟨6, 2, 249 / 1000, false⟩],
  [⟨5, 6, 10000 / 4543, false⟩, ⟨6, 2, 249 / 1000, false⟩],
  [⟨5, 6, 10000 / 4543, false⟩, ⟨6, 2, 249 / 1000, false⟩],
  [⟨5, 6, 10000 / 4543, false⟩, ⟨6, 2, 249 / 1000, false⟩],
  [⟨5, 6, 10000 / 4543, false⟩, ⟨6, 2, 249 / 1000, false⟩],
  [⟨5, 6, 10000 / 4543, false⟩, ⟨6, 2, 249 / 1000, false⟩],
  [⟨5, 3, 33 / 47, true⟩],
  [⟨5, 3, 33 / 47, true⟩],
  [⟨5, 3, 33 / 47, true⟩],
  [⟨5, 3, 33 / 47, true⟩],
  [⟨5, 3, 33 / 47, true⟩],
  [⟨5, 3, 33 / 47, true⟩],
  [⟨5, 3, 33 / 47, true⟩],
  [⟨5, 3, 33 / 47, true⟩],
  [⟨5, 3, 33 / 47, true⟩],
  [⟨5, 3, 33 / 47, true⟩],
  [⟨5, 6, 10000 / 4543, false⟩, ⟨6, 4, 2019 / 5000, false⟩],
  [⟨5, 6, 10000 / 4543, false⟩, ⟨6, 4, 2019 / 5000, false⟩],
  [⟨5, 6, 10000 / 4543, false⟩, ⟨6, 4, 2019 / 5000, false⟩],
  [⟨5, 6, 10000 / 4543, false⟩, ⟨6, 4, 2019 / 5000, false⟩]
]

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem box1_10_checked : box1_10.all (fun row =>
    verify (dmaxBox ++ selectors1) row.1 row.2) = true := by decide +kernel
set_option maxRecDepth 12000 in
private theorem box1_10_targets : box1_10.map Prod.fst = part1_10.map Prod.fst := by decide +kernel

def box1_11 : List (Guard × List Guard) :=
  (part1_11.map Prod.fst).zip [
  [⟨5, 6, 10000 / 4543, false⟩, ⟨6, 4, 2019 / 5000, false⟩],
  [⟨5, 6, 10000 / 4543, false⟩, ⟨6, 4, 2019 / 5000, false⟩],
  [⟨5, 6, 10000 / 4543, false⟩, ⟨6, 4, 2019 / 5000, false⟩],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [⟨5, 6, 10000 / 4543, false⟩],
  [⟨5, 6, 10000 / 4543, false⟩],
  [⟨5, 6, 10000 / 4543, false⟩],
  [⟨5, 6, 10000 / 4543, false⟩],
  [⟨5, 6, 10000 / 4543, false⟩],
  [⟨5, 6, 10000 / 4543, false⟩],
  [⟨5, 6, 10000 / 4543, false⟩],
  [⟨5, 6, 10000 / 4543, false⟩],
  [⟨5, 6, 10000 / 4543, false⟩],
  [⟨6, 4, 2019 / 5000, false⟩, ⟨4, 0, 9 / 55, true⟩],
  [⟨6, 4, 2019 / 5000, false⟩, ⟨4, 0, 9 / 55, true⟩],
  [⟨6, 4, 2019 / 5000, false⟩, ⟨4, 0, 9 / 55, true⟩],
  [⟨6, 4, 2019 / 5000, false⟩, ⟨4, 0, 9 / 55, true⟩],
  [⟨6, 4, 2019 / 5000, false⟩, ⟨4, 0, 9 / 55, true⟩]
]

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem box1_11_checked : box1_11.all (fun row =>
    verify (dmaxBox ++ selectors1) row.1 row.2) = true := by decide +kernel
set_option maxRecDepth 12000 in
private theorem box1_11_targets : box1_11.map Prod.fst = part1_11.map Prod.fst := by decide +kernel

def box1_12 : List (Guard × List Guard) :=
  (part1_12.map Prod.fst).zip [
  [⟨6, 1, 919 / 5000, false⟩],
  [⟨6, 1, 919 / 5000, false⟩],
  [⟨6, 1, 919 / 5000, false⟩],
  [⟨6, 1, 919 / 5000, false⟩],
  [⟨6, 1, 919 / 5000, false⟩],
  [⟨6, 2, 249 / 1000, false⟩],
  [⟨6, 2, 249 / 1000, false⟩],
  [⟨6, 2, 249 / 1000, false⟩],
  [⟨6, 2, 249 / 1000, false⟩],
  [⟨6, 2, 249 / 1000, false⟩],
  [⟨6, 2, 249 / 1000, false⟩],
  [⟨6, 3, 319 / 1000, false⟩],
  [⟨6, 3, 319 / 1000, false⟩],
  [⟨6, 3, 319 / 1000, false⟩],
  [⟨6, 3, 319 / 1000, false⟩],
  [⟨6, 3, 319 / 1000, false⟩],
  [⟨6, 3, 319 / 1000, false⟩],
  [⟨6, 3, 319 / 1000, false⟩],
  [⟨6, 3, 319 / 1000, false⟩],
  [⟨6, 3, 319 / 1000, false⟩],
  [⟨6, 4, 2019 / 5000, false⟩],
  [⟨6, 4, 2019 / 5000, false⟩],
  [⟨6, 4, 2019 / 5000, false⟩],
  [⟨6, 4, 2019 / 5000, false⟩]
]

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem box1_12_checked : box1_12.all (fun row =>
    verify (dmaxBox ++ selectors1) row.1 row.2) = true := by decide +kernel
set_option maxRecDepth 12000 in
private theorem box1_12_targets : box1_12.map Prod.fst = part1_12.map Prod.fst := by decide +kernel

def box1_13 : List (Guard × List Guard) :=
  (part1_13.map Prod.fst).zip [
  [⟨6, 4, 2019 / 5000, false⟩],
  [⟨6, 4, 2019 / 5000, false⟩],
  [⟨6, 4, 2019 / 5000, false⟩],
  [⟨6, 4, 2019 / 5000, false⟩],
  [⟨6, 4, 2019 / 5000, false⟩],
  [⟨6, 4, 2019 / 5000, false⟩],
  [⟨6, 5, 284 / 625, false⟩],
  [⟨6, 5, 284 / 625, false⟩],
  [⟨6, 5, 284 / 625, false⟩],
  [⟨6, 5, 284 / 625, false⟩],
  [⟨6, 5, 284 / 625, false⟩],
  [⟨6, 5, 284 / 625, false⟩],
  [⟨6, 5, 284 / 625, false⟩],
  [⟨6, 5, 284 / 625, false⟩],
  [⟨6, 5, 284 / 625, false⟩],
  [⟨6, 5, 284 / 625, false⟩],
  [],
  [],
  [],
  []
]

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem box1_13_checked : box1_13.all (fun row =>
    verify (dmaxBox ++ selectors1) row.1 row.2) = true := by decide +kernel
set_option maxRecDepth 12000 in
private theorem box1_13_targets : box1_13.map Prod.fst = part1_13.map Prod.fst := by decide +kernel

def boxRoute1 := box1_0 ++ box1_1 ++ box1_2 ++ box1_3 ++ box1_4 ++ box1_5 ++ box1_6 ++ box1_7 ++ box1_8 ++ box1_9 ++ box1_10 ++ box1_11 ++ box1_12 ++ box1_13

theorem guards1 (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (he : ∀ g ∈ dmaxBox ++ selectors1, g.valid r) :
    ∀ g ∈ route1.map Prod.fst, g.valid r := by
  have hc : boxRoute1.all (fun row =>
      verify (dmaxBox ++ selectors1) row.1 row.2) = true := by
    simp only [boxRoute1, List.all_append, box1_0_checked, box1_1_checked, box1_2_checked, box1_3_checked, box1_4_checked, box1_5_checked, box1_6_checked, box1_7_checked, box1_8_checked, box1_9_checked, box1_10_checked, box1_11_checked, box1_12_checked, box1_13_checked, Bool.true_and]
  have ht : boxRoute1.map Prod.fst = route1.map Prod.fst := by
    simp only [boxRoute1, route1, List.map_append, box1_0_targets, box1_1_targets, box1_2_targets, box1_3_targets, box1_4_targets, box1_5_targets, box1_6_targets, box1_7_targets, box1_8_targets, box1_9_targets, box1_10_targets, box1_11_targets, box1_12_targets, box1_13_targets]
  intro g hg
  rw [← ht] at hg
  obtain ⟨row, hr, rfl⟩ := List.mem_map.mp hg
  exact verify_all_sound r hp he hc row hr

#print axioms guards1

def box2_0 : List (Guard × List Guard) :=
  (part2_0.map Prod.fst).zip [
  [],
  [],
  [],
  [⟨0, 4, 55 / 9, false⟩, ⟨4, 6, 10000 / 4037, false⟩, ⟨6, 1, 919 / 5000, false⟩],
  [⟨0, 4, 55 / 9, false⟩, ⟨4, 6, 10000 / 4037, false⟩, ⟨6, 1, 919 / 5000, false⟩],
  [⟨0, 4, 55 / 9, false⟩, ⟨4, 6, 10000 / 4037, false⟩, ⟨6, 1, 919 / 5000, false⟩],
  [⟨0, 4, 55 / 9, false⟩, ⟨4, 6, 10000 / 4037, false⟩, ⟨6, 1, 919 / 5000, false⟩],
  [⟨0, 4, 55 / 9, false⟩, ⟨4, 6, 10000 / 4037, false⟩, ⟨6, 2, 249 / 1000, false⟩],
  [⟨0, 4, 55 / 9, false⟩, ⟨4, 6, 10000 / 4037, false⟩, ⟨6, 2, 249 / 1000, false⟩],
  [⟨0, 4, 55 / 9, false⟩, ⟨4, 6, 10000 / 4037, false⟩, ⟨6, 2, 249 / 1000, false⟩],
  [⟨0, 4, 55 / 9, false⟩, ⟨4, 6, 10000 / 4037, false⟩, ⟨6, 2, 249 / 1000, false⟩],
  [⟨0, 4, 55 / 9, false⟩, ⟨4, 6, 10000 / 4037, false⟩, ⟨6, 2, 249 / 1000, false⟩],
  [⟨0, 4, 55 / 9, false⟩, ⟨4, 6, 10000 / 4037, false⟩, ⟨6, 3, 319 / 1000, false⟩],
  [⟨0, 4, 55 / 9, false⟩, ⟨4, 6, 10000 / 4037, false⟩, ⟨6, 3, 319 / 1000, false⟩],
  [⟨0, 4, 55 / 9, false⟩, ⟨4, 6, 10000 / 4037, false⟩, ⟨6, 3, 319 / 1000, false⟩],
  [⟨0, 4, 55 / 9, false⟩, ⟨4, 6, 10000 / 4037, false⟩, ⟨6, 3, 319 / 1000, false⟩],
  [⟨0, 4, 55 / 9, false⟩, ⟨4, 6, 10000 / 4037, false⟩, ⟨6, 3, 319 / 1000, false⟩],
  [⟨0, 4, 55 / 9, false⟩, ⟨4, 6, 10000 / 4037, false⟩, ⟨6, 3, 319 / 1000, false⟩],
  [⟨0, 4, 55 / 9, false⟩],
  [⟨0, 4, 55 / 9, false⟩],
  [⟨0, 4, 55 / 9, false⟩],
  [⟨0, 4, 55 / 9, false⟩],
  [⟨0, 4, 55 / 9, false⟩],
  [⟨0, 4, 55 / 9, false⟩]
]

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem box2_0_checked : box2_0.all (fun row =>
    verify (dmaxBox ++ selectors2) row.1 row.2) = true := by decide +kernel
set_option maxRecDepth 12000 in
private theorem box2_0_targets : box2_0.map Prod.fst = part2_0.map Prod.fst := by decide +kernel

def box2_1 : List (Guard × List Guard) :=
  (part2_1.map Prod.fst).zip [
  [⟨0, 4, 55 / 9, false⟩],
  [⟨0, 4, 55 / 9, false⟩, ⟨4, 6, 10000 / 4037, false⟩, ⟨6, 5, 284 / 625, false⟩],
  [⟨0, 4, 55 / 9, false⟩, ⟨4, 6, 10000 / 4037, false⟩, ⟨6, 5, 284 / 625, false⟩],
  [⟨0, 4, 55 / 9, false⟩, ⟨4, 6, 10000 / 4037, false⟩, ⟨6, 5, 284 / 625, false⟩],
  [⟨0, 4, 55 / 9, false⟩, ⟨4, 6, 10000 / 4037, false⟩, ⟨6, 5, 284 / 625, false⟩],
  [⟨0, 4, 55 / 9, false⟩, ⟨4, 6, 10000 / 4037, false⟩, ⟨6, 5, 284 / 625, false⟩],
  [⟨0, 4, 55 / 9, false⟩, ⟨4, 6, 10000 / 4037, false⟩, ⟨6, 5, 284 / 625, false⟩],
  [⟨0, 4, 55 / 9, false⟩, ⟨4, 6, 10000 / 4037, false⟩, ⟨6, 5, 284 / 625, false⟩],
  [⟨0, 4, 55 / 9, false⟩, ⟨4, 6, 10000 / 4037, false⟩],
  [⟨0, 4, 55 / 9, false⟩, ⟨4, 6, 10000 / 4037, false⟩],
  [⟨0, 4, 55 / 9, false⟩, ⟨4, 6, 10000 / 4037, false⟩],
  [⟨0, 4, 55 / 9, false⟩, ⟨4, 6, 10000 / 4037, false⟩],
  [⟨0, 4, 55 / 9, false⟩, ⟨4, 6, 10000 / 4037, false⟩],
  [⟨0, 4, 55 / 9, false⟩, ⟨4, 6, 10000 / 4037, false⟩],
  [⟨1, 6, 10000 / 1837, false⟩, ⟨6, 0, 661 / 10000, false⟩],
  [⟨1, 6, 10000 / 1837, false⟩, ⟨6, 0, 661 / 10000, false⟩],
  [⟨1, 6, 10000 / 1837, false⟩, ⟨6, 0, 661 / 10000, false⟩],
  [⟨1, 6, 10000 / 1837, false⟩, ⟨6, 0, 661 / 10000, false⟩],
  [⟨1, 6, 10000 / 1837, false⟩, ⟨6, 0, 661 / 10000, false⟩],
  [],
  [],
  [],
  [⟨1, 6, 10000 / 1837, false⟩, ⟨6, 2, 249 / 1000, false⟩],
  [⟨1, 6, 10000 / 1837, false⟩, ⟨6, 2, 249 / 1000, false⟩]
]

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem box2_1_checked : box2_1.all (fun row =>
    verify (dmaxBox ++ selectors2) row.1 row.2) = true := by decide +kernel
set_option maxRecDepth 12000 in
private theorem box2_1_targets : box2_1.map Prod.fst = part2_1.map Prod.fst := by decide +kernel

def box2_2 : List (Guard × List Guard) :=
  (part2_2.map Prod.fst).zip [
  [⟨1, 6, 10000 / 1837, false⟩, ⟨6, 2, 249 / 1000, false⟩],
  [⟨1, 6, 10000 / 1837, false⟩, ⟨6, 2, 249 / 1000, false⟩],
  [⟨1, 6, 10000 / 1837, false⟩, ⟨6, 2, 249 / 1000, false⟩],
  [⟨1, 6, 10000 / 1837, false⟩, ⟨6, 3, 319 / 1000, false⟩],
  [⟨1, 6, 10000 / 1837, false⟩, ⟨6, 3, 319 / 1000, false⟩],
  [⟨1, 6, 10000 / 1837, false⟩, ⟨6, 3, 319 / 1000, false⟩],
  [⟨1, 6, 10000 / 1837, false⟩, ⟨6, 3, 319 / 1000, false⟩],
  [⟨1, 6, 10000 / 1837, false⟩, ⟨6, 3, 319 / 1000, false⟩],
  [⟨1, 6, 10000 / 1837, false⟩, ⟨6, 3, 319 / 1000, false⟩],
  [⟨1, 6, 10000 / 1837, false⟩, ⟨6, 4, 2019 / 5000, false⟩],
  [⟨1, 6, 10000 / 1837, false⟩, ⟨6, 4, 2019 / 5000, false⟩],
  [⟨1, 6, 10000 / 1837, false⟩, ⟨6, 4, 2019 / 5000, false⟩],
  [⟨1, 6, 10000 / 1837, false⟩, ⟨6, 4, 2019 / 5000, false⟩],
  [⟨1, 6, 10000 / 1837, false⟩, ⟨6, 4, 2019 / 5000, false⟩],
  [⟨1, 6, 10000 / 1837, false⟩, ⟨6, 4, 2019 / 5000, false⟩],
  [⟨1, 6, 10000 / 1837, false⟩, ⟨6, 4, 2019 / 5000, false⟩],
  [⟨1, 6, 10000 / 1837, false⟩, ⟨6, 5, 284 / 625, false⟩],
  [⟨1, 6, 10000 / 1837, false⟩, ⟨6, 5, 284 / 625, false⟩],
  [⟨1, 6, 10000 / 1837, false⟩, ⟨6, 5, 284 / 625, false⟩],
  [⟨1, 6, 10000 / 1837, false⟩, ⟨6, 5, 284 / 625, false⟩],
  [⟨1, 6, 10000 / 1837, false⟩, ⟨6, 5, 284 / 625, false⟩],
  [⟨1, 6, 10000 / 1837, false⟩, ⟨6, 5, 284 / 625, false⟩],
  [⟨1, 6, 10000 / 1837, false⟩, ⟨6, 5, 284 / 625, false⟩],
  [⟨1, 6, 10000 / 1837, false⟩, ⟨6, 5, 284 / 625, false⟩]
]

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem box2_2_checked : box2_2.all (fun row =>
    verify (dmaxBox ++ selectors2) row.1 row.2) = true := by decide +kernel
set_option maxRecDepth 12000 in
private theorem box2_2_targets : box2_2.map Prod.fst = part2_2.map Prod.fst := by decide +kernel

def box2_3 : List (Guard × List Guard) :=
  (part2_3.map Prod.fst).zip [
  [⟨1, 6, 10000 / 1837, false⟩],
  [⟨1, 6, 10000 / 1837, false⟩],
  [⟨1, 6, 10000 / 1837, false⟩],
  [⟨1, 6, 10000 / 1837, false⟩],
  [⟨1, 6, 10000 / 1837, false⟩],
  [⟨1, 6, 10000 / 1837, false⟩],
  [⟨2, 6, 10000 / 2489, false⟩, ⟨6, 0, 661 / 10000, false⟩],
  [⟨2, 6, 10000 / 2489, false⟩, ⟨6, 0, 661 / 10000, false⟩],
  [⟨2, 6, 10000 / 2489, false⟩, ⟨6, 0, 661 / 10000, false⟩],
  [⟨2, 6, 10000 / 2489, false⟩, ⟨6, 0, 661 / 10000, false⟩],
  [⟨2, 6, 10000 / 2489, false⟩, ⟨6, 0, 661 / 10000, false⟩],
  [⟨2, 6, 10000 / 2489, false⟩, ⟨6, 1, 919 / 5000, false⟩],
  [⟨2, 6, 10000 / 2489, false⟩, ⟨6, 1, 919 / 5000, false⟩],
  [⟨2, 6, 10000 / 2489, false⟩, ⟨6, 1, 919 / 5000, false⟩],
  [⟨2, 6, 10000 / 2489, false⟩, ⟨6, 1, 919 / 5000, false⟩],
  [⟨2, 6, 10000 / 2489, false⟩, ⟨6, 1, 919 / 5000, false⟩],
  [⟨2, 6, 10000 / 2489, false⟩, ⟨6, 1, 919 / 5000, false⟩],
  [],
  [],
  [],
  [],
  [⟨2, 6, 10000 / 2489, false⟩, ⟨6, 3, 319 / 1000, false⟩],
  [⟨2, 6, 10000 / 2489, false⟩, ⟨6, 3, 319 / 1000, false⟩],
  [⟨2, 6, 10000 / 2489, false⟩, ⟨6, 3, 319 / 1000, false⟩]
]

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem box2_3_checked : box2_3.all (fun row =>
    verify (dmaxBox ++ selectors2) row.1 row.2) = true := by decide +kernel
set_option maxRecDepth 12000 in
private theorem box2_3_targets : box2_3.map Prod.fst = part2_3.map Prod.fst := by decide +kernel

def box2_4 : List (Guard × List Guard) :=
  (part2_4.map Prod.fst).zip [
  [⟨2, 6, 10000 / 2489, false⟩, ⟨6, 3, 319 / 1000, false⟩],
  [⟨2, 6, 10000 / 2489, false⟩, ⟨6, 3, 319 / 1000, false⟩],
  [⟨2, 6, 10000 / 2489, false⟩, ⟨6, 3, 319 / 1000, false⟩],
  [⟨2, 6, 10000 / 2489, false⟩, ⟨6, 3, 319 / 1000, false⟩],
  [⟨2, 6, 10000 / 2489, false⟩, ⟨6, 4, 2019 / 5000, false⟩],
  [⟨2, 6, 10000 / 2489, false⟩, ⟨6, 4, 2019 / 5000, false⟩],
  [⟨2, 6, 10000 / 2489, false⟩, ⟨6, 4, 2019 / 5000, false⟩],
  [⟨2, 6, 10000 / 2489, false⟩, ⟨6, 4, 2019 / 5000, false⟩],
  [⟨2, 6, 10000 / 2489, false⟩, ⟨6, 4, 2019 / 5000, false⟩],
  [⟨2, 6, 10000 / 2489, false⟩, ⟨6, 4, 2019 / 5000, false⟩],
  [⟨2, 6, 10000 / 2489, false⟩, ⟨6, 4, 2019 / 5000, false⟩],
  [⟨2, 6, 10000 / 2489, false⟩, ⟨6, 4, 2019 / 5000, false⟩],
  [⟨2, 6, 10000 / 2489, false⟩, ⟨6, 5, 284 / 625, false⟩],
  [⟨2, 6, 10000 / 2489, false⟩, ⟨6, 5, 284 / 625, false⟩],
  [⟨2, 6, 10000 / 2489, false⟩, ⟨6, 5, 284 / 625, false⟩],
  [⟨2, 6, 10000 / 2489, false⟩, ⟨6, 5, 284 / 625, false⟩],
  [⟨2, 6, 10000 / 2489, false⟩, ⟨6, 5, 284 / 625, false⟩],
  [⟨2, 6, 10000 / 2489, false⟩, ⟨6, 5, 284 / 625, false⟩],
  [⟨2, 6, 10000 / 2489, false⟩, ⟨6, 5, 284 / 625, false⟩],
  [⟨2, 6, 10000 / 2489, false⟩, ⟨6, 5, 284 / 625, false⟩],
  [⟨2, 6, 10000 / 2489, false⟩, ⟨6, 5, 284 / 625, false⟩],
  [⟨2, 6, 10000 / 2489, false⟩],
  [⟨2, 6, 10000 / 2489, false⟩],
  [⟨2, 6, 10000 / 2489, false⟩]
]

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem box2_4_checked : box2_4.all (fun row =>
    verify (dmaxBox ++ selectors2) row.1 row.2) = true := by decide +kernel
set_option maxRecDepth 12000 in
private theorem box2_4_targets : box2_4.map Prod.fst = part2_4.map Prod.fst := by decide +kernel

def box2_5 : List (Guard × List Guard) :=
  (part2_5.map Prod.fst).zip [
  [⟨2, 6, 10000 / 2489, false⟩],
  [⟨2, 6, 10000 / 2489, false⟩],
  [⟨2, 6, 10000 / 2489, false⟩],
  [⟨2, 6, 10000 / 2489, false⟩],
  [⟨3, 5, 33 / 23, true⟩, ⟨5, 6, 10000 / 4543, false⟩, ⟨6, 0, 661 / 10000, false⟩],
  [⟨3, 5, 33 / 23, true⟩, ⟨5, 6, 10000 / 4543, false⟩, ⟨6, 0, 661 / 10000, false⟩],
  [⟨3, 5, 33 / 23, true⟩, ⟨5, 6, 10000 / 4543, false⟩, ⟨6, 0, 661 / 10000, false⟩],
  [⟨3, 5, 33 / 23, true⟩, ⟨5, 6, 10000 / 4543, false⟩, ⟨6, 0, 661 / 10000, false⟩],
  [⟨3, 5, 33 / 23, true⟩, ⟨5, 6, 10000 / 4543, false⟩, ⟨6, 0, 661 / 10000, false⟩],
  [⟨3, 5, 33 / 23, true⟩, ⟨5, 6, 10000 / 4543, false⟩, ⟨6, 0, 661 / 10000, false⟩],
  [⟨3, 5, 33 / 23, true⟩, ⟨5, 6, 10000 / 4543, false⟩, ⟨6, 1, 919 / 5000, false⟩],
  [⟨3, 5, 33 / 23, true⟩, ⟨5, 6, 10000 / 4543, false⟩, ⟨6, 1, 919 / 5000, false⟩],
  [⟨3, 5, 33 / 23, true⟩, ⟨5, 6, 10000 / 4543, false⟩, ⟨6, 1, 919 / 5000, false⟩],
  [⟨3, 5, 33 / 23, true⟩, ⟨5, 6, 10000 / 4543, false⟩, ⟨6, 1, 919 / 5000, false⟩],
  [⟨3, 5, 33 / 23, true⟩, ⟨5, 6, 10000 / 4543, false⟩, ⟨6, 1, 919 / 5000, false⟩],
  [⟨3, 5, 33 / 23, true⟩, ⟨5, 6, 10000 / 4543, false⟩, ⟨6, 1, 919 / 5000, false⟩],
  [⟨3, 5, 33 / 23, true⟩, ⟨5, 6, 10000 / 4543, false⟩, ⟨6, 2, 249 / 1000, false⟩],
  [⟨3, 5, 33 / 23, true⟩, ⟨5, 6, 10000 / 4543, false⟩, ⟨6, 2, 249 / 1000, false⟩],
  [⟨3, 5, 33 / 23, true⟩, ⟨5, 6, 10000 / 4543, false⟩, ⟨6, 2, 249 / 1000, false⟩],
  [⟨3, 5, 33 / 23, true⟩, ⟨5, 6, 10000 / 4543, false⟩, ⟨6, 2, 249 / 1000, false⟩],
  [⟨3, 5, 33 / 23, true⟩, ⟨5, 6, 10000 / 4543, false⟩, ⟨6, 2, 249 / 1000, false⟩],
  [⟨3, 5, 33 / 23, true⟩, ⟨5, 6, 10000 / 4543, false⟩, ⟨6, 2, 249 / 1000, false⟩],
  [],
  []
]

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem box2_5_checked : box2_5.all (fun row =>
    verify (dmaxBox ++ selectors2) row.1 row.2) = true := by decide +kernel
set_option maxRecDepth 12000 in
private theorem box2_5_targets : box2_5.map Prod.fst = part2_5.map Prod.fst := by decide +kernel

def box2_6 : List (Guard × List Guard) :=
  (part2_6.map Prod.fst).zip [
  [],
  [],
  [],
  [⟨3, 5, 33 / 23, true⟩, ⟨5, 6, 10000 / 4543, false⟩, ⟨6, 4, 2019 / 5000, false⟩],
  [⟨3, 5, 33 / 23, true⟩, ⟨5, 6, 10000 / 4543, false⟩, ⟨6, 4, 2019 / 5000, false⟩],
  [⟨3, 5, 33 / 23, true⟩, ⟨5, 6, 10000 / 4543, false⟩, ⟨6, 4, 2019 / 5000, false⟩],
  [⟨3, 5, 33 / 23, true⟩, ⟨5, 6, 10000 / 4543, false⟩, ⟨6, 4, 2019 / 5000, false⟩],
  [⟨3, 5, 33 / 23, true⟩, ⟨5, 6, 10000 / 4543, false⟩, ⟨6, 4, 2019 / 5000, false⟩],
  [⟨3, 5, 33 / 23, true⟩, ⟨5, 6, 10000 / 4543, false⟩, ⟨6, 4, 2019 / 5000, false⟩],
  [⟨3, 5, 33 / 23, true⟩, ⟨5, 6, 10000 / 4543, false⟩, ⟨6, 4, 2019 / 5000, false⟩],
  [⟨3, 5, 33 / 23, true⟩, ⟨5, 6, 10000 / 4543, false⟩, ⟨6, 4, 2019 / 5000, false⟩],
  [⟨3, 5, 33 / 23, true⟩, ⟨5, 6, 10000 / 4543, false⟩, ⟨6, 4, 2019 / 5000, false⟩],
  [⟨3, 5, 33 / 23, true⟩],
  [⟨3, 5, 33 / 23, true⟩],
  [⟨3, 5, 33 / 23, true⟩],
  [⟨3, 5, 33 / 23, true⟩],
  [⟨3, 5, 33 / 23, true⟩],
  [⟨3, 5, 33 / 23, true⟩],
  [⟨3, 5, 33 / 23, true⟩],
  [⟨3, 5, 33 / 23, true⟩],
  [⟨3, 5, 33 / 23, true⟩],
  [⟨3, 5, 33 / 23, true⟩],
  [⟨3, 5, 33 / 23, true⟩, ⟨5, 6, 10000 / 4543, false⟩],
  [⟨3, 5, 33 / 23, true⟩, ⟨5, 6, 10000 / 4543, false⟩]
]

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem box2_6_checked : box2_6.all (fun row =>
    verify (dmaxBox ++ selectors2) row.1 row.2) = true := by decide +kernel
set_option maxRecDepth 12000 in
private theorem box2_6_targets : box2_6.map Prod.fst = part2_6.map Prod.fst := by decide +kernel

def box2_7 : List (Guard × List Guard) :=
  (part2_7.map Prod.fst).zip [
  [⟨3, 5, 33 / 23, true⟩, ⟨5, 6, 10000 / 4543, false⟩],
  [⟨3, 5, 33 / 23, true⟩, ⟨5, 6, 10000 / 4543, false⟩],
  [⟨3, 5, 33 / 23, true⟩, ⟨5, 6, 10000 / 4543, false⟩],
  [⟨3, 5, 33 / 23, true⟩, ⟨5, 6, 10000 / 4543, false⟩],
  [⟨3, 5, 33 / 23, true⟩, ⟨5, 6, 10000 / 4543, false⟩],
  [⟨3, 5, 33 / 23, true⟩, ⟨5, 6, 10000 / 4543, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩, ⟨6, 0, 661 / 10000, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩, ⟨6, 0, 661 / 10000, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩, ⟨6, 0, 661 / 10000, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩, ⟨6, 0, 661 / 10000, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩, ⟨6, 0, 661 / 10000, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩, ⟨6, 0, 661 / 10000, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩, ⟨6, 0, 661 / 10000, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩, ⟨6, 1, 919 / 5000, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩, ⟨6, 1, 919 / 5000, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩, ⟨6, 1, 919 / 5000, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩, ⟨6, 1, 919 / 5000, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩, ⟨6, 1, 919 / 5000, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩, ⟨6, 1, 919 / 5000, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩, ⟨6, 1, 919 / 5000, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩, ⟨6, 2, 249 / 1000, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩, ⟨6, 2, 249 / 1000, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩, ⟨6, 2, 249 / 1000, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩, ⟨6, 2, 249 / 1000, false⟩]
]

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem box2_7_checked : box2_7.all (fun row =>
    verify (dmaxBox ++ selectors2) row.1 row.2) = true := by decide +kernel
set_option maxRecDepth 12000 in
private theorem box2_7_targets : box2_7.map Prod.fst = part2_7.map Prod.fst := by decide +kernel

def box2_8 : List (Guard × List Guard) :=
  (part2_8.map Prod.fst).zip [
  [⟨4, 6, 10000 / 4037, false⟩, ⟨6, 2, 249 / 1000, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩, ⟨6, 2, 249 / 1000, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩, ⟨6, 2, 249 / 1000, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩, ⟨6, 2, 249 / 1000, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩, ⟨6, 3, 319 / 1000, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩, ⟨6, 3, 319 / 1000, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩, ⟨6, 3, 319 / 1000, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩, ⟨6, 3, 319 / 1000, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩, ⟨6, 3, 319 / 1000, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩, ⟨6, 3, 319 / 1000, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩, ⟨6, 3, 319 / 1000, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩, ⟨6, 3, 319 / 1000, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩, ⟨6, 3, 319 / 1000, false⟩],
  [],
  [],
  [],
  [],
  [],
  [],
  [⟨4, 6, 10000 / 4037, false⟩, ⟨6, 5, 284 / 625, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩, ⟨6, 5, 284 / 625, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩, ⟨6, 5, 284 / 625, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩, ⟨6, 5, 284 / 625, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩, ⟨6, 5, 284 / 625, false⟩]
]

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem box2_8_checked : box2_8.all (fun row =>
    verify (dmaxBox ++ selectors2) row.1 row.2) = true := by decide +kernel
set_option maxRecDepth 12000 in
private theorem box2_8_targets : box2_8.map Prod.fst = part2_8.map Prod.fst := by decide +kernel

def box2_9 : List (Guard × List Guard) :=
  (part2_9.map Prod.fst).zip [
  [⟨4, 6, 10000 / 4037, false⟩, ⟨6, 5, 284 / 625, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩, ⟨6, 5, 284 / 625, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩, ⟨6, 5, 284 / 625, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩, ⟨6, 5, 284 / 625, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩, ⟨6, 5, 284 / 625, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩, ⟨6, 5, 284 / 625, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩],
  [⟨5, 6, 10000 / 4543, false⟩, ⟨6, 0, 661 / 10000, false⟩],
  [⟨5, 6, 10000 / 4543, false⟩, ⟨6, 0, 661 / 10000, false⟩],
  [⟨5, 6, 10000 / 4543, false⟩, ⟨6, 0, 661 / 10000, false⟩],
  [⟨5, 6, 10000 / 4543, false⟩, ⟨6, 0, 661 / 10000, false⟩],
  [⟨5, 6, 10000 / 4543, false⟩, ⟨6, 0, 661 / 10000, false⟩],
  [⟨5, 6, 10000 / 4543, false⟩, ⟨6, 0, 661 / 10000, false⟩],
  [⟨5, 6, 10000 / 4543, false⟩, ⟨6, 0, 661 / 10000, false⟩],
  [⟨5, 6, 10000 / 4543, false⟩, ⟨6, 0, 661 / 10000, false⟩],
  [⟨5, 6, 10000 / 4543, false⟩, ⟨6, 1, 919 / 5000, false⟩]
]

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem box2_9_checked : box2_9.all (fun row =>
    verify (dmaxBox ++ selectors2) row.1 row.2) = true := by decide +kernel
set_option maxRecDepth 12000 in
private theorem box2_9_targets : box2_9.map Prod.fst = part2_9.map Prod.fst := by decide +kernel

def box2_10 : List (Guard × List Guard) :=
  (part2_10.map Prod.fst).zip [
  [⟨5, 6, 10000 / 4543, false⟩, ⟨6, 1, 919 / 5000, false⟩],
  [⟨5, 6, 10000 / 4543, false⟩, ⟨6, 1, 919 / 5000, false⟩],
  [⟨5, 6, 10000 / 4543, false⟩, ⟨6, 1, 919 / 5000, false⟩],
  [⟨5, 6, 10000 / 4543, false⟩, ⟨6, 1, 919 / 5000, false⟩],
  [⟨5, 6, 10000 / 4543, false⟩, ⟨6, 1, 919 / 5000, false⟩],
  [⟨5, 6, 10000 / 4543, false⟩, ⟨6, 1, 919 / 5000, false⟩],
  [⟨5, 6, 10000 / 4543, false⟩, ⟨6, 1, 919 / 5000, false⟩],
  [⟨5, 6, 10000 / 4543, false⟩, ⟨6, 2, 249 / 1000, false⟩],
  [⟨5, 6, 10000 / 4543, false⟩, ⟨6, 2, 249 / 1000, false⟩],
  [⟨5, 6, 10000 / 4543, false⟩, ⟨6, 2, 249 / 1000, false⟩],
  [⟨5, 6, 10000 / 4543, false⟩, ⟨6, 2, 249 / 1000, false⟩],
  [⟨5, 6, 10000 / 4543, false⟩, ⟨6, 2, 249 / 1000, false⟩],
  [⟨5, 6, 10000 / 4543, false⟩, ⟨6, 2, 249 / 1000, false⟩],
  [⟨5, 6, 10000 / 4543, false⟩, ⟨6, 2, 249 / 1000, false⟩],
  [⟨5, 6, 10000 / 4543, false⟩, ⟨6, 2, 249 / 1000, false⟩],
  [⟨5, 3, 33 / 47, true⟩],
  [⟨5, 3, 33 / 47, true⟩],
  [⟨5, 3, 33 / 47, true⟩],
  [⟨5, 3, 33 / 47, true⟩],
  [⟨5, 3, 33 / 47, true⟩],
  [⟨5, 3, 33 / 47, true⟩],
  [⟨5, 3, 33 / 47, true⟩],
  [⟨5, 3, 33 / 47, true⟩],
  [⟨5, 3, 33 / 47, true⟩]
]

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem box2_10_checked : box2_10.all (fun row =>
    verify (dmaxBox ++ selectors2) row.1 row.2) = true := by decide +kernel
set_option maxRecDepth 12000 in
private theorem box2_10_targets : box2_10.map Prod.fst = part2_10.map Prod.fst := by decide +kernel

def box2_11 : List (Guard × List Guard) :=
  (part2_11.map Prod.fst).zip [
  [⟨5, 3, 33 / 47, true⟩],
  [⟨5, 6, 10000 / 4543, false⟩, ⟨6, 4, 2019 / 5000, false⟩],
  [⟨5, 6, 10000 / 4543, false⟩, ⟨6, 4, 2019 / 5000, false⟩],
  [⟨5, 6, 10000 / 4543, false⟩, ⟨6, 4, 2019 / 5000, false⟩],
  [⟨5, 6, 10000 / 4543, false⟩, ⟨6, 4, 2019 / 5000, false⟩],
  [⟨5, 6, 10000 / 4543, false⟩, ⟨6, 4, 2019 / 5000, false⟩],
  [⟨5, 6, 10000 / 4543, false⟩, ⟨6, 4, 2019 / 5000, false⟩],
  [⟨5, 6, 10000 / 4543, false⟩, ⟨6, 4, 2019 / 5000, false⟩],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [⟨5, 6, 10000 / 4543, false⟩],
  [⟨5, 6, 10000 / 4543, false⟩],
  [⟨5, 6, 10000 / 4543, false⟩],
  [⟨5, 6, 10000 / 4543, false⟩],
  [⟨5, 6, 10000 / 4543, false⟩],
  [⟨5, 6, 10000 / 4543, false⟩],
  [⟨5, 6, 10000 / 4543, false⟩],
  [⟨5, 6, 10000 / 4543, false⟩],
  [⟨5, 6, 10000 / 4543, false⟩]
]

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem box2_11_checked : box2_11.all (fun row =>
    verify (dmaxBox ++ selectors2) row.1 row.2) = true := by decide +kernel
set_option maxRecDepth 12000 in
private theorem box2_11_targets : box2_11.map Prod.fst = part2_11.map Prod.fst := by decide +kernel

def box2_12 : List (Guard × List Guard) :=
  (part2_12.map Prod.fst).zip [
  [⟨5, 6, 10000 / 4543, false⟩],
  [⟨6, 0, 661 / 10000, false⟩],
  [⟨6, 0, 661 / 10000, false⟩],
  [⟨6, 0, 661 / 10000, false⟩],
  [⟨6, 0, 661 / 10000, false⟩],
  [⟨6, 0, 661 / 10000, false⟩],
  [⟨6, 1, 919 / 5000, false⟩],
  [⟨6, 1, 919 / 5000, false⟩],
  [⟨6, 1, 919 / 5000, false⟩],
  [⟨6, 1, 919 / 5000, false⟩],
  [⟨6, 1, 919 / 5000, false⟩],
  [⟨6, 1, 919 / 5000, false⟩],
  [⟨6, 2, 249 / 1000, false⟩],
  [⟨6, 2, 249 / 1000, false⟩],
  [⟨6, 2, 249 / 1000, false⟩],
  [⟨6, 2, 249 / 1000, false⟩],
  [⟨6, 2, 249 / 1000, false⟩],
  [⟨6, 2, 249 / 1000, false⟩],
  [⟨6, 2, 249 / 1000, false⟩],
  [⟨6, 3, 319 / 1000, false⟩],
  [⟨6, 3, 319 / 1000, false⟩],
  [⟨6, 3, 319 / 1000, false⟩],
  [⟨6, 3, 319 / 1000, false⟩],
  [⟨6, 3, 319 / 1000, false⟩]
]

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem box2_12_checked : box2_12.all (fun row =>
    verify (dmaxBox ++ selectors2) row.1 row.2) = true := by decide +kernel
set_option maxRecDepth 12000 in
private theorem box2_12_targets : box2_12.map Prod.fst = part2_12.map Prod.fst := by decide +kernel

def box2_13 : List (Guard × List Guard) :=
  (part2_13.map Prod.fst).zip [
  [⟨6, 3, 319 / 1000, false⟩],
  [⟨6, 3, 319 / 1000, false⟩],
  [⟨6, 3, 319 / 1000, false⟩],
  [⟨6, 3, 319 / 1000, false⟩],
  [⟨6, 3, 319 / 1000, false⟩],
  [⟨6, 4, 2019 / 5000, false⟩],
  [⟨6, 4, 2019 / 5000, false⟩],
  [⟨6, 4, 2019 / 5000, false⟩],
  [⟨6, 4, 2019 / 5000, false⟩],
  [⟨6, 4, 2019 / 5000, false⟩],
  [⟨6, 4, 2019 / 5000, false⟩],
  [⟨6, 4, 2019 / 5000, false⟩],
  [⟨6, 4, 2019 / 5000, false⟩],
  [⟨6, 4, 2019 / 5000, false⟩],
  [⟨6, 4, 2019 / 5000, false⟩],
  [⟨6, 5, 284 / 625, false⟩],
  [⟨6, 5, 284 / 625, false⟩],
  [⟨6, 5, 284 / 625, false⟩],
  [⟨6, 5, 284 / 625, false⟩],
  [⟨6, 5, 284 / 625, false⟩],
  [⟨6, 5, 284 / 625, false⟩],
  [⟨6, 5, 284 / 625, false⟩],
  [⟨6, 5, 284 / 625, false⟩],
  [⟨6, 5, 284 / 625, false⟩]
]

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem box2_13_checked : box2_13.all (fun row =>
    verify (dmaxBox ++ selectors2) row.1 row.2) = true := by decide +kernel
set_option maxRecDepth 12000 in
private theorem box2_13_targets : box2_13.map Prod.fst = part2_13.map Prod.fst := by decide +kernel

def box2_14 : List (Guard × List Guard) :=
  (part2_14.map Prod.fst).zip [
  [⟨6, 5, 284 / 625, false⟩],
  [⟨6, 5, 284 / 625, false⟩],
  [],
  [],
  [],
  [],
  []
]

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem box2_14_checked : box2_14.all (fun row =>
    verify (dmaxBox ++ selectors2) row.1 row.2) = true := by decide +kernel
set_option maxRecDepth 12000 in
private theorem box2_14_targets : box2_14.map Prod.fst = part2_14.map Prod.fst := by decide +kernel

def boxRoute2 := box2_0 ++ box2_1 ++ box2_2 ++ box2_3 ++ box2_4 ++ box2_5 ++ box2_6 ++ box2_7 ++ box2_8 ++ box2_9 ++ box2_10 ++ box2_11 ++ box2_12 ++ box2_13 ++ box2_14

theorem guards2 (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (he : ∀ g ∈ dmaxBox ++ selectors2, g.valid r) :
    ∀ g ∈ route2.map Prod.fst, g.valid r := by
  have hc : boxRoute2.all (fun row =>
      verify (dmaxBox ++ selectors2) row.1 row.2) = true := by
    simp only [boxRoute2, List.all_append, box2_0_checked, box2_1_checked, box2_2_checked, box2_3_checked, box2_4_checked, box2_5_checked, box2_6_checked, box2_7_checked, box2_8_checked, box2_9_checked, box2_10_checked, box2_11_checked, box2_12_checked, box2_13_checked, box2_14_checked, Bool.true_and]
  have ht : boxRoute2.map Prod.fst = route2.map Prod.fst := by
    simp only [boxRoute2, route2, List.map_append, box2_0_targets, box2_1_targets, box2_2_targets, box2_3_targets, box2_4_targets, box2_5_targets, box2_6_targets, box2_7_targets, box2_8_targets, box2_9_targets, box2_10_targets, box2_11_targets, box2_12_targets, box2_13_targets, box2_14_targets]
  intro g hg
  rw [← ht] at hg
  obtain ⟨row, hr, rfl⟩ := List.mem_map.mp hg
  exact verify_all_sound r hp he hc row hr

#print axioms guards2

def box3_0 : List (Guard × List Guard) :=
  (part3_0.map Prod.fst).zip [
  [],
  [],
  [],
  [⟨0, 5, 7 / 1, true⟩, ⟨5, 6, 10000 / 4543, false⟩, ⟨6, 1, 919 / 5000, false⟩],
  [⟨0, 5, 7 / 1, true⟩, ⟨5, 6, 10000 / 4543, false⟩, ⟨6, 1, 919 / 5000, false⟩],
  [⟨0, 5, 7 / 1, true⟩, ⟨5, 6, 10000 / 4543, false⟩, ⟨6, 1, 919 / 5000, false⟩],
  [⟨0, 5, 7 / 1, true⟩, ⟨5, 6, 10000 / 4543, false⟩, ⟨6, 1, 919 / 5000, false⟩],
  [⟨0, 5, 7 / 1, true⟩, ⟨5, 6, 10000 / 4543, false⟩, ⟨6, 2, 249 / 1000, false⟩],
  [⟨0, 5, 7 / 1, true⟩, ⟨5, 6, 10000 / 4543, false⟩, ⟨6, 2, 249 / 1000, false⟩],
  [⟨0, 5, 7 / 1, true⟩, ⟨5, 6, 10000 / 4543, false⟩, ⟨6, 2, 249 / 1000, false⟩],
  [⟨0, 5, 7 / 1, true⟩, ⟨5, 6, 10000 / 4543, false⟩, ⟨6, 2, 249 / 1000, false⟩],
  [⟨0, 5, 7 / 1, true⟩, ⟨5, 6, 10000 / 4543, false⟩, ⟨6, 2, 249 / 1000, false⟩],
  [⟨0, 5, 7 / 1, true⟩, ⟨5, 6, 10000 / 4543, false⟩, ⟨6, 3, 319 / 1000, false⟩],
  [⟨0, 5, 7 / 1, true⟩, ⟨5, 6, 10000 / 4543, false⟩, ⟨6, 3, 319 / 1000, false⟩],
  [⟨0, 5, 7 / 1, true⟩, ⟨5, 6, 10000 / 4543, false⟩, ⟨6, 3, 319 / 1000, false⟩],
  [⟨0, 5, 7 / 1, true⟩, ⟨5, 6, 10000 / 4543, false⟩, ⟨6, 3, 319 / 1000, false⟩],
  [⟨0, 5, 7 / 1, true⟩, ⟨5, 6, 10000 / 4543, false⟩, ⟨6, 3, 319 / 1000, false⟩],
  [⟨0, 5, 7 / 1, true⟩, ⟨5, 6, 10000 / 4543, false⟩, ⟨6, 3, 319 / 1000, false⟩],
  [⟨0, 5, 7 / 1, true⟩, ⟨5, 6, 10000 / 4543, false⟩, ⟨6, 4, 2019 / 5000, false⟩],
  [⟨0, 5, 7 / 1, true⟩, ⟨5, 6, 10000 / 4543, false⟩, ⟨6, 4, 2019 / 5000, false⟩],
  [⟨0, 5, 7 / 1, true⟩, ⟨5, 6, 10000 / 4543, false⟩, ⟨6, 4, 2019 / 5000, false⟩],
  [⟨0, 5, 7 / 1, true⟩, ⟨5, 6, 10000 / 4543, false⟩, ⟨6, 4, 2019 / 5000, false⟩],
  [⟨0, 5, 7 / 1, true⟩, ⟨5, 6, 10000 / 4543, false⟩, ⟨6, 4, 2019 / 5000, false⟩],
  [⟨0, 5, 7 / 1, true⟩, ⟨5, 6, 10000 / 4543, false⟩, ⟨6, 4, 2019 / 5000, false⟩]
]

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem box3_0_checked : box3_0.all (fun row =>
    verify (dmaxBox ++ selectors3) row.1 row.2) = true := by decide +kernel
set_option maxRecDepth 12000 in
private theorem box3_0_targets : box3_0.map Prod.fst = part3_0.map Prod.fst := by decide +kernel

def box3_1 : List (Guard × List Guard) :=
  (part3_1.map Prod.fst).zip [
  [⟨0, 5, 7 / 1, true⟩, ⟨5, 6, 10000 / 4543, false⟩, ⟨6, 4, 2019 / 5000, false⟩],
  [⟨0, 5, 7 / 1, true⟩],
  [⟨0, 5, 7 / 1, true⟩],
  [⟨0, 5, 7 / 1, true⟩],
  [⟨0, 5, 7 / 1, true⟩],
  [⟨0, 5, 7 / 1, true⟩],
  [⟨0, 5, 7 / 1, true⟩],
  [⟨0, 5, 7 / 1, true⟩],
  [⟨0, 5, 7 / 1, true⟩, ⟨5, 6, 10000 / 4543, false⟩],
  [⟨0, 5, 7 / 1, true⟩, ⟨5, 6, 10000 / 4543, false⟩],
  [⟨0, 5, 7 / 1, true⟩, ⟨5, 6, 10000 / 4543, false⟩],
  [⟨0, 5, 7 / 1, true⟩, ⟨5, 6, 10000 / 4543, false⟩],
  [⟨0, 5, 7 / 1, true⟩, ⟨5, 6, 10000 / 4543, false⟩],
  [⟨0, 5, 7 / 1, true⟩, ⟨5, 6, 10000 / 4543, false⟩],
  [⟨1, 6, 10000 / 1837, false⟩, ⟨6, 4, 2019 / 5000, false⟩, ⟨4, 0, 9 / 55, true⟩],
  [⟨1, 6, 10000 / 1837, false⟩, ⟨6, 4, 2019 / 5000, false⟩, ⟨4, 0, 9 / 55, true⟩],
  [⟨1, 6, 10000 / 1837, false⟩, ⟨6, 4, 2019 / 5000, false⟩, ⟨4, 0, 9 / 55, true⟩],
  [⟨1, 6, 10000 / 1837, false⟩, ⟨6, 4, 2019 / 5000, false⟩, ⟨4, 0, 9 / 55, true⟩],
  [⟨1, 6, 10000 / 1837, false⟩, ⟨6, 4, 2019 / 5000, false⟩, ⟨4, 0, 9 / 55, true⟩],
  [],
  [],
  [],
  [⟨1, 6, 10000 / 1837, false⟩, ⟨6, 2, 249 / 1000, false⟩],
  [⟨1, 6, 10000 / 1837, false⟩, ⟨6, 2, 249 / 1000, false⟩]
]

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem box3_1_checked : box3_1.all (fun row =>
    verify (dmaxBox ++ selectors3) row.1 row.2) = true := by decide +kernel
set_option maxRecDepth 12000 in
private theorem box3_1_targets : box3_1.map Prod.fst = part3_1.map Prod.fst := by decide +kernel

def box3_2 : List (Guard × List Guard) :=
  (part3_2.map Prod.fst).zip [
  [⟨1, 6, 10000 / 1837, false⟩, ⟨6, 2, 249 / 1000, false⟩],
  [⟨1, 6, 10000 / 1837, false⟩, ⟨6, 2, 249 / 1000, false⟩],
  [⟨1, 6, 10000 / 1837, false⟩, ⟨6, 2, 249 / 1000, false⟩],
  [⟨1, 6, 10000 / 1837, false⟩, ⟨6, 3, 319 / 1000, false⟩],
  [⟨1, 6, 10000 / 1837, false⟩, ⟨6, 3, 319 / 1000, false⟩],
  [⟨1, 6, 10000 / 1837, false⟩, ⟨6, 3, 319 / 1000, false⟩],
  [⟨1, 6, 10000 / 1837, false⟩, ⟨6, 3, 319 / 1000, false⟩],
  [⟨1, 6, 10000 / 1837, false⟩, ⟨6, 3, 319 / 1000, false⟩],
  [⟨1, 6, 10000 / 1837, false⟩, ⟨6, 3, 319 / 1000, false⟩],
  [⟨1, 6, 10000 / 1837, false⟩, ⟨6, 4, 2019 / 5000, false⟩],
  [⟨1, 6, 10000 / 1837, false⟩, ⟨6, 4, 2019 / 5000, false⟩],
  [⟨1, 6, 10000 / 1837, false⟩, ⟨6, 4, 2019 / 5000, false⟩],
  [⟨1, 6, 10000 / 1837, false⟩, ⟨6, 4, 2019 / 5000, false⟩],
  [⟨1, 6, 10000 / 1837, false⟩, ⟨6, 4, 2019 / 5000, false⟩],
  [⟨1, 6, 10000 / 1837, false⟩, ⟨6, 4, 2019 / 5000, false⟩],
  [⟨1, 6, 10000 / 1837, false⟩, ⟨6, 4, 2019 / 5000, false⟩],
  [⟨1, 6, 10000 / 1837, false⟩, ⟨6, 3, 319 / 1000, false⟩, ⟨3, 5, 47 / 33, false⟩],
  [⟨1, 6, 10000 / 1837, false⟩, ⟨6, 3, 319 / 1000, false⟩, ⟨3, 5, 47 / 33, false⟩],
  [⟨1, 6, 10000 / 1837, false⟩, ⟨6, 3, 319 / 1000, false⟩, ⟨3, 5, 47 / 33, false⟩],
  [⟨1, 6, 10000 / 1837, false⟩, ⟨6, 3, 319 / 1000, false⟩, ⟨3, 5, 47 / 33, false⟩],
  [⟨1, 6, 10000 / 1837, false⟩, ⟨6, 3, 319 / 1000, false⟩, ⟨3, 5, 47 / 33, false⟩],
  [⟨1, 6, 10000 / 1837, false⟩, ⟨6, 3, 319 / 1000, false⟩, ⟨3, 5, 47 / 33, false⟩],
  [⟨1, 6, 10000 / 1837, false⟩, ⟨6, 3, 319 / 1000, false⟩, ⟨3, 5, 47 / 33, false⟩],
  [⟨1, 6, 10000 / 1837, false⟩, ⟨6, 3, 319 / 1000, false⟩, ⟨3, 5, 47 / 33, false⟩]
]

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem box3_2_checked : box3_2.all (fun row =>
    verify (dmaxBox ++ selectors3) row.1 row.2) = true := by decide +kernel
set_option maxRecDepth 12000 in
private theorem box3_2_targets : box3_2.map Prod.fst = part3_2.map Prod.fst := by decide +kernel

def box3_3 : List (Guard × List Guard) :=
  (part3_3.map Prod.fst).zip [
  [⟨1, 6, 10000 / 1837, false⟩],
  [⟨1, 6, 10000 / 1837, false⟩],
  [⟨1, 6, 10000 / 1837, false⟩],
  [⟨1, 6, 10000 / 1837, false⟩],
  [⟨1, 6, 10000 / 1837, false⟩],
  [⟨1, 6, 10000 / 1837, false⟩],
  [⟨2, 6, 10000 / 2489, false⟩, ⟨6, 4, 2019 / 5000, false⟩, ⟨4, 0, 9 / 55, true⟩],
  [⟨2, 6, 10000 / 2489, false⟩, ⟨6, 4, 2019 / 5000, false⟩, ⟨4, 0, 9 / 55, true⟩],
  [⟨2, 6, 10000 / 2489, false⟩, ⟨6, 4, 2019 / 5000, false⟩, ⟨4, 0, 9 / 55, true⟩],
  [⟨2, 6, 10000 / 2489, false⟩, ⟨6, 4, 2019 / 5000, false⟩, ⟨4, 0, 9 / 55, true⟩],
  [⟨2, 6, 10000 / 2489, false⟩, ⟨6, 4, 2019 / 5000, false⟩, ⟨4, 0, 9 / 55, true⟩],
  [⟨2, 6, 10000 / 2489, false⟩, ⟨6, 1, 919 / 5000, false⟩],
  [⟨2, 6, 10000 / 2489, false⟩, ⟨6, 1, 919 / 5000, false⟩],
  [⟨2, 6, 10000 / 2489, false⟩, ⟨6, 1, 919 / 5000, false⟩],
  [⟨2, 6, 10000 / 2489, false⟩, ⟨6, 1, 919 / 5000, false⟩],
  [⟨2, 6, 10000 / 2489, false⟩, ⟨6, 1, 919 / 5000, false⟩],
  [⟨2, 6, 10000 / 2489, false⟩, ⟨6, 1, 919 / 5000, false⟩],
  [],
  [],
  [],
  [],
  [⟨2, 6, 10000 / 2489, false⟩, ⟨6, 3, 319 / 1000, false⟩],
  [⟨2, 6, 10000 / 2489, false⟩, ⟨6, 3, 319 / 1000, false⟩],
  [⟨2, 6, 10000 / 2489, false⟩, ⟨6, 3, 319 / 1000, false⟩]
]

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem box3_3_checked : box3_3.all (fun row =>
    verify (dmaxBox ++ selectors3) row.1 row.2) = true := by decide +kernel
set_option maxRecDepth 12000 in
private theorem box3_3_targets : box3_3.map Prod.fst = part3_3.map Prod.fst := by decide +kernel

def box3_4 : List (Guard × List Guard) :=
  (part3_4.map Prod.fst).zip [
  [⟨2, 6, 10000 / 2489, false⟩, ⟨6, 3, 319 / 1000, false⟩],
  [⟨2, 6, 10000 / 2489, false⟩, ⟨6, 3, 319 / 1000, false⟩],
  [⟨2, 6, 10000 / 2489, false⟩, ⟨6, 3, 319 / 1000, false⟩],
  [⟨2, 6, 10000 / 2489, false⟩, ⟨6, 3, 319 / 1000, false⟩],
  [⟨2, 6, 10000 / 2489, false⟩, ⟨6, 4, 2019 / 5000, false⟩],
  [⟨2, 6, 10000 / 2489, false⟩, ⟨6, 4, 2019 / 5000, false⟩],
  [⟨2, 6, 10000 / 2489, false⟩, ⟨6, 4, 2019 / 5000, false⟩],
  [⟨2, 6, 10000 / 2489, false⟩, ⟨6, 4, 2019 / 5000, false⟩],
  [⟨2, 6, 10000 / 2489, false⟩, ⟨6, 4, 2019 / 5000, false⟩],
  [⟨2, 6, 10000 / 2489, false⟩, ⟨6, 4, 2019 / 5000, false⟩],
  [⟨2, 6, 10000 / 2489, false⟩, ⟨6, 4, 2019 / 5000, false⟩],
  [⟨2, 6, 10000 / 2489, false⟩, ⟨6, 4, 2019 / 5000, false⟩],
  [⟨2, 6, 10000 / 2489, false⟩, ⟨6, 3, 319 / 1000, false⟩, ⟨3, 5, 47 / 33, false⟩],
  [⟨2, 6, 10000 / 2489, false⟩, ⟨6, 3, 319 / 1000, false⟩, ⟨3, 5, 47 / 33, false⟩],
  [⟨2, 6, 10000 / 2489, false⟩, ⟨6, 3, 319 / 1000, false⟩, ⟨3, 5, 47 / 33, false⟩],
  [⟨2, 6, 10000 / 2489, false⟩, ⟨6, 3, 319 / 1000, false⟩, ⟨3, 5, 47 / 33, false⟩],
  [⟨2, 6, 10000 / 2489, false⟩, ⟨6, 3, 319 / 1000, false⟩, ⟨3, 5, 47 / 33, false⟩],
  [⟨2, 6, 10000 / 2489, false⟩, ⟨6, 3, 319 / 1000, false⟩, ⟨3, 5, 47 / 33, false⟩],
  [⟨2, 6, 10000 / 2489, false⟩, ⟨6, 3, 319 / 1000, false⟩, ⟨3, 5, 47 / 33, false⟩],
  [⟨2, 6, 10000 / 2489, false⟩, ⟨6, 3, 319 / 1000, false⟩, ⟨3, 5, 47 / 33, false⟩],
  [⟨2, 6, 10000 / 2489, false⟩, ⟨6, 3, 319 / 1000, false⟩, ⟨3, 5, 47 / 33, false⟩],
  [⟨2, 6, 10000 / 2489, false⟩],
  [⟨2, 6, 10000 / 2489, false⟩],
  [⟨2, 6, 10000 / 2489, false⟩]
]

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem box3_4_checked : box3_4.all (fun row =>
    verify (dmaxBox ++ selectors3) row.1 row.2) = true := by decide +kernel
set_option maxRecDepth 12000 in
private theorem box3_4_targets : box3_4.map Prod.fst = part3_4.map Prod.fst := by decide +kernel

def box3_5 : List (Guard × List Guard) :=
  (part3_5.map Prod.fst).zip [
  [⟨2, 6, 10000 / 2489, false⟩],
  [⟨2, 6, 10000 / 2489, false⟩],
  [⟨2, 6, 10000 / 2489, false⟩],
  [⟨2, 6, 10000 / 2489, false⟩],
  [⟨3, 5, 47 / 33, false⟩, ⟨5, 6, 10000 / 4543, false⟩, ⟨6, 4, 2019 / 5000, false⟩, ⟨4, 0, 9 / 55, true⟩],
  [⟨3, 5, 47 / 33, false⟩, ⟨5, 6, 10000 / 4543, false⟩, ⟨6, 4, 2019 / 5000, false⟩, ⟨4, 0, 9 / 55, true⟩],
  [⟨3, 5, 47 / 33, false⟩, ⟨5, 6, 10000 / 4543, false⟩, ⟨6, 4, 2019 / 5000, false⟩, ⟨4, 0, 9 / 55, true⟩],
  [⟨3, 5, 47 / 33, false⟩, ⟨5, 6, 10000 / 4543, false⟩, ⟨6, 4, 2019 / 5000, false⟩, ⟨4, 0, 9 / 55, true⟩],
  [⟨3, 5, 47 / 33, false⟩, ⟨5, 6, 10000 / 4543, false⟩, ⟨6, 4, 2019 / 5000, false⟩, ⟨4, 0, 9 / 55, true⟩],
  [⟨3, 5, 47 / 33, false⟩, ⟨5, 6, 10000 / 4543, false⟩, ⟨6, 4, 2019 / 5000, false⟩, ⟨4, 0, 9 / 55, true⟩],
  [⟨3, 5, 47 / 33, false⟩, ⟨5, 6, 10000 / 4543, false⟩, ⟨6, 1, 919 / 5000, false⟩],
  [⟨3, 5, 47 / 33, false⟩, ⟨5, 6, 10000 / 4543, false⟩, ⟨6, 1, 919 / 5000, false⟩],
  [⟨3, 5, 47 / 33, false⟩, ⟨5, 6, 10000 / 4543, false⟩, ⟨6, 1, 919 / 5000, false⟩],
  [⟨3, 5, 47 / 33, false⟩, ⟨5, 6, 10000 / 4543, false⟩, ⟨6, 1, 919 / 5000, false⟩],
  [⟨3, 5, 47 / 33, false⟩, ⟨5, 6, 10000 / 4543, false⟩, ⟨6, 1, 919 / 5000, false⟩],
  [⟨3, 5, 47 / 33, false⟩, ⟨5, 6, 10000 / 4543, false⟩, ⟨6, 1, 919 / 5000, false⟩],
  [⟨3, 5, 47 / 33, false⟩, ⟨5, 6, 10000 / 4543, false⟩, ⟨6, 2, 249 / 1000, false⟩],
  [⟨3, 5, 47 / 33, false⟩, ⟨5, 6, 10000 / 4543, false⟩, ⟨6, 2, 249 / 1000, false⟩],
  [⟨3, 5, 47 / 33, false⟩, ⟨5, 6, 10000 / 4543, false⟩, ⟨6, 2, 249 / 1000, false⟩],
  [⟨3, 5, 47 / 33, false⟩, ⟨5, 6, 10000 / 4543, false⟩, ⟨6, 2, 249 / 1000, false⟩],
  [⟨3, 5, 47 / 33, false⟩, ⟨5, 6, 10000 / 4543, false⟩, ⟨6, 2, 249 / 1000, false⟩],
  [⟨3, 5, 47 / 33, false⟩, ⟨5, 6, 10000 / 4543, false⟩, ⟨6, 2, 249 / 1000, false⟩],
  [],
  []
]

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem box3_5_checked : box3_5.all (fun row =>
    verify (dmaxBox ++ selectors3) row.1 row.2) = true := by decide +kernel
set_option maxRecDepth 12000 in
private theorem box3_5_targets : box3_5.map Prod.fst = part3_5.map Prod.fst := by decide +kernel

def box3_6 : List (Guard × List Guard) :=
  (part3_6.map Prod.fst).zip [
  [],
  [],
  [],
  [⟨3, 5, 47 / 33, false⟩, ⟨5, 6, 10000 / 4543, false⟩, ⟨6, 4, 2019 / 5000, false⟩],
  [⟨3, 5, 47 / 33, false⟩, ⟨5, 6, 10000 / 4543, false⟩, ⟨6, 4, 2019 / 5000, false⟩],
  [⟨3, 5, 47 / 33, false⟩, ⟨5, 6, 10000 / 4543, false⟩, ⟨6, 4, 2019 / 5000, false⟩],
  [⟨3, 5, 47 / 33, false⟩, ⟨5, 6, 10000 / 4543, false⟩, ⟨6, 4, 2019 / 5000, false⟩],
  [⟨3, 5, 47 / 33, false⟩, ⟨5, 6, 10000 / 4543, false⟩, ⟨6, 4, 2019 / 5000, false⟩],
  [⟨3, 5, 47 / 33, false⟩, ⟨5, 6, 10000 / 4543, false⟩, ⟨6, 4, 2019 / 5000, false⟩],
  [⟨3, 5, 47 / 33, false⟩, ⟨5, 6, 10000 / 4543, false⟩, ⟨6, 4, 2019 / 5000, false⟩],
  [⟨3, 5, 47 / 33, false⟩, ⟨5, 6, 10000 / 4543, false⟩, ⟨6, 4, 2019 / 5000, false⟩],
  [⟨3, 5, 47 / 33, false⟩, ⟨5, 6, 10000 / 4543, false⟩, ⟨6, 4, 2019 / 5000, false⟩],
  [⟨3, 5, 47 / 33, false⟩],
  [⟨3, 5, 47 / 33, false⟩],
  [⟨3, 5, 47 / 33, false⟩],
  [⟨3, 5, 47 / 33, false⟩],
  [⟨3, 5, 47 / 33, false⟩],
  [⟨3, 5, 47 / 33, false⟩],
  [⟨3, 5, 47 / 33, false⟩],
  [⟨3, 5, 47 / 33, false⟩],
  [⟨3, 5, 47 / 33, false⟩],
  [⟨3, 5, 47 / 33, false⟩],
  [⟨3, 5, 47 / 33, false⟩, ⟨5, 6, 10000 / 4543, false⟩],
  [⟨3, 5, 47 / 33, false⟩, ⟨5, 6, 10000 / 4543, false⟩]
]

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem box3_6_checked : box3_6.all (fun row =>
    verify (dmaxBox ++ selectors3) row.1 row.2) = true := by decide +kernel
set_option maxRecDepth 12000 in
private theorem box3_6_targets : box3_6.map Prod.fst = part3_6.map Prod.fst := by decide +kernel

def box3_7 : List (Guard × List Guard) :=
  (part3_7.map Prod.fst).zip [
  [⟨3, 5, 47 / 33, false⟩, ⟨5, 6, 10000 / 4543, false⟩],
  [⟨3, 5, 47 / 33, false⟩, ⟨5, 6, 10000 / 4543, false⟩],
  [⟨3, 5, 47 / 33, false⟩, ⟨5, 6, 10000 / 4543, false⟩],
  [⟨3, 5, 47 / 33, false⟩, ⟨5, 6, 10000 / 4543, false⟩],
  [⟨3, 5, 47 / 33, false⟩, ⟨5, 6, 10000 / 4543, false⟩],
  [⟨3, 5, 47 / 33, false⟩, ⟨5, 6, 10000 / 4543, false⟩],
  [⟨4, 0, 9 / 55, true⟩],
  [⟨4, 0, 9 / 55, true⟩],
  [⟨4, 0, 9 / 55, true⟩],
  [⟨4, 0, 9 / 55, true⟩],
  [⟨4, 0, 9 / 55, true⟩],
  [⟨4, 0, 9 / 55, true⟩],
  [⟨4, 0, 9 / 55, true⟩],
  [⟨4, 6, 10000 / 4037, false⟩, ⟨6, 1, 919 / 5000, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩, ⟨6, 1, 919 / 5000, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩, ⟨6, 1, 919 / 5000, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩, ⟨6, 1, 919 / 5000, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩, ⟨6, 1, 919 / 5000, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩, ⟨6, 1, 919 / 5000, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩, ⟨6, 1, 919 / 5000, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩, ⟨6, 2, 249 / 1000, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩, ⟨6, 2, 249 / 1000, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩, ⟨6, 2, 249 / 1000, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩, ⟨6, 2, 249 / 1000, false⟩]
]

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem box3_7_checked : box3_7.all (fun row =>
    verify (dmaxBox ++ selectors3) row.1 row.2) = true := by decide +kernel
set_option maxRecDepth 12000 in
private theorem box3_7_targets : box3_7.map Prod.fst = part3_7.map Prod.fst := by decide +kernel

def box3_8 : List (Guard × List Guard) :=
  (part3_8.map Prod.fst).zip [
  [⟨4, 6, 10000 / 4037, false⟩, ⟨6, 2, 249 / 1000, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩, ⟨6, 2, 249 / 1000, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩, ⟨6, 2, 249 / 1000, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩, ⟨6, 2, 249 / 1000, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩, ⟨6, 3, 319 / 1000, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩, ⟨6, 3, 319 / 1000, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩, ⟨6, 3, 319 / 1000, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩, ⟨6, 3, 319 / 1000, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩, ⟨6, 3, 319 / 1000, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩, ⟨6, 3, 319 / 1000, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩, ⟨6, 3, 319 / 1000, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩, ⟨6, 3, 319 / 1000, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩, ⟨6, 3, 319 / 1000, false⟩],
  [],
  [],
  [],
  [],
  [],
  [],
  [⟨4, 6, 10000 / 4037, false⟩, ⟨6, 3, 319 / 1000, false⟩, ⟨3, 5, 47 / 33, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩, ⟨6, 3, 319 / 1000, false⟩, ⟨3, 5, 47 / 33, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩, ⟨6, 3, 319 / 1000, false⟩, ⟨3, 5, 47 / 33, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩, ⟨6, 3, 319 / 1000, false⟩, ⟨3, 5, 47 / 33, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩, ⟨6, 3, 319 / 1000, false⟩, ⟨3, 5, 47 / 33, false⟩]
]

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem box3_8_checked : box3_8.all (fun row =>
    verify (dmaxBox ++ selectors3) row.1 row.2) = true := by decide +kernel
set_option maxRecDepth 12000 in
private theorem box3_8_targets : box3_8.map Prod.fst = part3_8.map Prod.fst := by decide +kernel

def box3_9 : List (Guard × List Guard) :=
  (part3_9.map Prod.fst).zip [
  [⟨4, 6, 10000 / 4037, false⟩, ⟨6, 3, 319 / 1000, false⟩, ⟨3, 5, 47 / 33, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩, ⟨6, 3, 319 / 1000, false⟩, ⟨3, 5, 47 / 33, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩, ⟨6, 3, 319 / 1000, false⟩, ⟨3, 5, 47 / 33, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩, ⟨6, 3, 319 / 1000, false⟩, ⟨3, 5, 47 / 33, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩, ⟨6, 3, 319 / 1000, false⟩, ⟨3, 5, 47 / 33, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩, ⟨6, 3, 319 / 1000, false⟩, ⟨3, 5, 47 / 33, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩],
  [⟨5, 6, 10000 / 4543, false⟩, ⟨6, 4, 2019 / 5000, false⟩, ⟨4, 0, 9 / 55, true⟩],
  [⟨5, 6, 10000 / 4543, false⟩, ⟨6, 4, 2019 / 5000, false⟩, ⟨4, 0, 9 / 55, true⟩],
  [⟨5, 6, 10000 / 4543, false⟩, ⟨6, 4, 2019 / 5000, false⟩, ⟨4, 0, 9 / 55, true⟩],
  [⟨5, 6, 10000 / 4543, false⟩, ⟨6, 4, 2019 / 5000, false⟩, ⟨4, 0, 9 / 55, true⟩],
  [⟨5, 6, 10000 / 4543, false⟩, ⟨6, 4, 2019 / 5000, false⟩, ⟨4, 0, 9 / 55, true⟩],
  [⟨5, 6, 10000 / 4543, false⟩, ⟨6, 4, 2019 / 5000, false⟩, ⟨4, 0, 9 / 55, true⟩],
  [⟨5, 6, 10000 / 4543, false⟩, ⟨6, 4, 2019 / 5000, false⟩, ⟨4, 0, 9 / 55, true⟩],
  [⟨5, 6, 10000 / 4543, false⟩, ⟨6, 4, 2019 / 5000, false⟩, ⟨4, 0, 9 / 55, true⟩],
  [⟨5, 6, 10000 / 4543, false⟩, ⟨6, 1, 919 / 5000, false⟩]
]

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem box3_9_checked : box3_9.all (fun row =>
    verify (dmaxBox ++ selectors3) row.1 row.2) = true := by decide +kernel
set_option maxRecDepth 12000 in
private theorem box3_9_targets : box3_9.map Prod.fst = part3_9.map Prod.fst := by decide +kernel

def box3_10 : List (Guard × List Guard) :=
  (part3_10.map Prod.fst).zip [
  [⟨5, 6, 10000 / 4543, false⟩, ⟨6, 1, 919 / 5000, false⟩],
  [⟨5, 6, 10000 / 4543, false⟩, ⟨6, 1, 919 / 5000, false⟩],
  [⟨5, 6, 10000 / 4543, false⟩, ⟨6, 1, 919 / 5000, false⟩],
  [⟨5, 6, 10000 / 4543, false⟩, ⟨6, 1, 919 / 5000, false⟩],
  [⟨5, 6, 10000 / 4543, false⟩, ⟨6, 1, 919 / 5000, false⟩],
  [⟨5, 6, 10000 / 4543, false⟩, ⟨6, 1, 919 / 5000, false⟩],
  [⟨5, 6, 10000 / 4543, false⟩, ⟨6, 1, 919 / 5000, false⟩],
  [⟨5, 6, 10000 / 4543, false⟩, ⟨6, 2, 249 / 1000, false⟩],
  [⟨5, 6, 10000 / 4543, false⟩, ⟨6, 2, 249 / 1000, false⟩],
  [⟨5, 6, 10000 / 4543, false⟩, ⟨6, 2, 249 / 1000, false⟩],
  [⟨5, 6, 10000 / 4543, false⟩, ⟨6, 2, 249 / 1000, false⟩],
  [⟨5, 6, 10000 / 4543, false⟩, ⟨6, 2, 249 / 1000, false⟩],
  [⟨5, 6, 10000 / 4543, false⟩, ⟨6, 2, 249 / 1000, false⟩],
  [⟨5, 6, 10000 / 4543, false⟩, ⟨6, 2, 249 / 1000, false⟩],
  [⟨5, 6, 10000 / 4543, false⟩, ⟨6, 2, 249 / 1000, false⟩],
  [⟨5, 6, 10000 / 4543, false⟩, ⟨6, 3, 319 / 1000, false⟩],
  [⟨5, 6, 10000 / 4543, false⟩, ⟨6, 3, 319 / 1000, false⟩],
  [⟨5, 6, 10000 / 4543, false⟩, ⟨6, 3, 319 / 1000, false⟩],
  [⟨5, 6, 10000 / 4543, false⟩, ⟨6, 3, 319 / 1000, false⟩],
  [⟨5, 6, 10000 / 4543, false⟩, ⟨6, 3, 319 / 1000, false⟩],
  [⟨5, 6, 10000 / 4543, false⟩, ⟨6, 3, 319 / 1000, false⟩],
  [⟨5, 6, 10000 / 4543, false⟩, ⟨6, 3, 319 / 1000, false⟩],
  [⟨5, 6, 10000 / 4543, false⟩, ⟨6, 3, 319 / 1000, false⟩],
  [⟨5, 6, 10000 / 4543, false⟩, ⟨6, 3, 319 / 1000, false⟩]
]

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem box3_10_checked : box3_10.all (fun row =>
    verify (dmaxBox ++ selectors3) row.1 row.2) = true := by decide +kernel
set_option maxRecDepth 12000 in
private theorem box3_10_targets : box3_10.map Prod.fst = part3_10.map Prod.fst := by decide +kernel

def box3_11 : List (Guard × List Guard) :=
  (part3_11.map Prod.fst).zip [
  [⟨5, 6, 10000 / 4543, false⟩, ⟨6, 3, 319 / 1000, false⟩],
  [⟨5, 6, 10000 / 4543, false⟩, ⟨6, 4, 2019 / 5000, false⟩],
  [⟨5, 6, 10000 / 4543, false⟩, ⟨6, 4, 2019 / 5000, false⟩],
  [⟨5, 6, 10000 / 4543, false⟩, ⟨6, 4, 2019 / 5000, false⟩],
  [⟨5, 6, 10000 / 4543, false⟩, ⟨6, 4, 2019 / 5000, false⟩],
  [⟨5, 6, 10000 / 4543, false⟩, ⟨6, 4, 2019 / 5000, false⟩],
  [⟨5, 6, 10000 / 4543, false⟩, ⟨6, 4, 2019 / 5000, false⟩],
  [⟨5, 6, 10000 / 4543, false⟩, ⟨6, 4, 2019 / 5000, false⟩],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [⟨5, 6, 10000 / 4543, false⟩],
  [⟨5, 6, 10000 / 4543, false⟩],
  [⟨5, 6, 10000 / 4543, false⟩],
  [⟨5, 6, 10000 / 4543, false⟩],
  [⟨5, 6, 10000 / 4543, false⟩],
  [⟨5, 6, 10000 / 4543, false⟩],
  [⟨5, 6, 10000 / 4543, false⟩],
  [⟨5, 6, 10000 / 4543, false⟩],
  [⟨5, 6, 10000 / 4543, false⟩]
]

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem box3_11_checked : box3_11.all (fun row =>
    verify (dmaxBox ++ selectors3) row.1 row.2) = true := by decide +kernel
set_option maxRecDepth 12000 in
private theorem box3_11_targets : box3_11.map Prod.fst = part3_11.map Prod.fst := by decide +kernel

def box3_12 : List (Guard × List Guard) :=
  (part3_12.map Prod.fst).zip [
  [⟨5, 6, 10000 / 4543, false⟩],
  [⟨6, 4, 2019 / 5000, false⟩, ⟨4, 0, 9 / 55, true⟩],
  [⟨6, 4, 2019 / 5000, false⟩, ⟨4, 0, 9 / 55, true⟩],
  [⟨6, 4, 2019 / 5000, false⟩, ⟨4, 0, 9 / 55, true⟩],
  [⟨6, 4, 2019 / 5000, false⟩, ⟨4, 0, 9 / 55, true⟩],
  [⟨6, 4, 2019 / 5000, false⟩, ⟨4, 0, 9 / 55, true⟩],
  [⟨6, 4, 2019 / 5000, false⟩, ⟨4, 0, 9 / 55, true⟩],
  [⟨6, 1, 919 / 5000, false⟩],
  [⟨6, 1, 919 / 5000, false⟩],
  [⟨6, 1, 919 / 5000, false⟩],
  [⟨6, 1, 919 / 5000, false⟩],
  [⟨6, 1, 919 / 5000, false⟩],
  [⟨6, 1, 919 / 5000, false⟩],
  [⟨6, 2, 249 / 1000, false⟩],
  [⟨6, 2, 249 / 1000, false⟩],
  [⟨6, 2, 249 / 1000, false⟩],
  [⟨6, 2, 249 / 1000, false⟩],
  [⟨6, 2, 249 / 1000, false⟩],
  [⟨6, 2, 249 / 1000, false⟩],
  [⟨6, 2, 249 / 1000, false⟩],
  [⟨6, 3, 319 / 1000, false⟩],
  [⟨6, 3, 319 / 1000, false⟩],
  [⟨6, 3, 319 / 1000, false⟩],
  [⟨6, 3, 319 / 1000, false⟩]
]

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem box3_12_checked : box3_12.all (fun row =>
    verify (dmaxBox ++ selectors3) row.1 row.2) = true := by decide +kernel
set_option maxRecDepth 12000 in
private theorem box3_12_targets : box3_12.map Prod.fst = part3_12.map Prod.fst := by decide +kernel

def box3_13 : List (Guard × List Guard) :=
  (part3_13.map Prod.fst).zip [
  [⟨6, 3, 319 / 1000, false⟩],
  [⟨6, 3, 319 / 1000, false⟩],
  [⟨6, 3, 319 / 1000, false⟩],
  [⟨6, 3, 319 / 1000, false⟩],
  [⟨6, 3, 319 / 1000, false⟩],
  [⟨6, 3, 319 / 1000, false⟩],
  [⟨6, 4, 2019 / 5000, false⟩],
  [⟨6, 4, 2019 / 5000, false⟩],
  [⟨6, 4, 2019 / 5000, false⟩],
  [⟨6, 4, 2019 / 5000, false⟩],
  [⟨6, 4, 2019 / 5000, false⟩],
  [⟨6, 4, 2019 / 5000, false⟩],
  [⟨6, 4, 2019 / 5000, false⟩],
  [⟨6, 4, 2019 / 5000, false⟩],
  [⟨6, 4, 2019 / 5000, false⟩],
  [⟨6, 4, 2019 / 5000, false⟩],
  [⟨6, 4, 2019 / 5000, false⟩],
  [⟨6, 3, 319 / 1000, false⟩, ⟨3, 5, 47 / 33, false⟩],
  [⟨6, 3, 319 / 1000, false⟩, ⟨3, 5, 47 / 33, false⟩],
  [⟨6, 3, 319 / 1000, false⟩, ⟨3, 5, 47 / 33, false⟩],
  [⟨6, 3, 319 / 1000, false⟩, ⟨3, 5, 47 / 33, false⟩],
  [⟨6, 3, 319 / 1000, false⟩, ⟨3, 5, 47 / 33, false⟩],
  [⟨6, 3, 319 / 1000, false⟩, ⟨3, 5, 47 / 33, false⟩],
  [⟨6, 3, 319 / 1000, false⟩, ⟨3, 5, 47 / 33, false⟩]
]

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem box3_13_checked : box3_13.all (fun row =>
    verify (dmaxBox ++ selectors3) row.1 row.2) = true := by decide +kernel
set_option maxRecDepth 12000 in
private theorem box3_13_targets : box3_13.map Prod.fst = part3_13.map Prod.fst := by decide +kernel

def box3_14 : List (Guard × List Guard) :=
  (part3_14.map Prod.fst).zip [
  [⟨6, 3, 319 / 1000, false⟩, ⟨3, 5, 47 / 33, false⟩],
  [⟨6, 3, 319 / 1000, false⟩, ⟨3, 5, 47 / 33, false⟩],
  [⟨6, 3, 319 / 1000, false⟩, ⟨3, 5, 47 / 33, false⟩],
  [],
  [],
  [],
  [],
  []
]

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem box3_14_checked : box3_14.all (fun row =>
    verify (dmaxBox ++ selectors3) row.1 row.2) = true := by decide +kernel
set_option maxRecDepth 12000 in
private theorem box3_14_targets : box3_14.map Prod.fst = part3_14.map Prod.fst := by decide +kernel

def boxRoute3 := box3_0 ++ box3_1 ++ box3_2 ++ box3_3 ++ box3_4 ++ box3_5 ++ box3_6 ++ box3_7 ++ box3_8 ++ box3_9 ++ box3_10 ++ box3_11 ++ box3_12 ++ box3_13 ++ box3_14

theorem guards3 (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (he : ∀ g ∈ dmaxBox ++ selectors3, g.valid r) :
    ∀ g ∈ route3.map Prod.fst, g.valid r := by
  have hc : boxRoute3.all (fun row =>
      verify (dmaxBox ++ selectors3) row.1 row.2) = true := by
    simp only [boxRoute3, List.all_append, box3_0_checked, box3_1_checked, box3_2_checked, box3_3_checked, box3_4_checked, box3_5_checked, box3_6_checked, box3_7_checked, box3_8_checked, box3_9_checked, box3_10_checked, box3_11_checked, box3_12_checked, box3_13_checked, box3_14_checked, Bool.true_and]
  have ht : boxRoute3.map Prod.fst = route3.map Prod.fst := by
    simp only [boxRoute3, route3, List.map_append, box3_0_targets, box3_1_targets, box3_2_targets, box3_3_targets, box3_4_targets, box3_5_targets, box3_6_targets, box3_7_targets, box3_8_targets, box3_9_targets, box3_10_targets, box3_11_targets, box3_12_targets, box3_13_targets, box3_14_targets]
  intro g hg
  rw [← ht] at hg
  obtain ⟨row, hr, rfl⟩ := List.mem_map.mp hg
  exact verify_all_sound r hp he hc row hr

#print axioms guards3

def box4_0 : List (Guard × List Guard) :=
  (part4_0.map Prod.fst).zip [
  [],
  [],
  [],
  [⟨0, 4, 55 / 9, false⟩, ⟨4, 6, 10000 / 4037, false⟩, ⟨6, 1, 919 / 5000, false⟩],
  [⟨0, 4, 55 / 9, false⟩, ⟨4, 6, 10000 / 4037, false⟩, ⟨6, 1, 919 / 5000, false⟩],
  [⟨0, 4, 55 / 9, false⟩, ⟨4, 6, 10000 / 4037, false⟩, ⟨6, 1, 919 / 5000, false⟩],
  [⟨0, 4, 55 / 9, false⟩, ⟨4, 6, 10000 / 4037, false⟩, ⟨6, 1, 919 / 5000, false⟩],
  [⟨0, 4, 55 / 9, false⟩, ⟨4, 6, 10000 / 4037, false⟩, ⟨6, 2, 249 / 1000, false⟩],
  [⟨0, 4, 55 / 9, false⟩, ⟨4, 6, 10000 / 4037, false⟩, ⟨6, 2, 249 / 1000, false⟩],
  [⟨0, 4, 55 / 9, false⟩, ⟨4, 6, 10000 / 4037, false⟩, ⟨6, 2, 249 / 1000, false⟩],
  [⟨0, 4, 55 / 9, false⟩, ⟨4, 6, 10000 / 4037, false⟩, ⟨6, 2, 249 / 1000, false⟩],
  [⟨0, 4, 55 / 9, false⟩, ⟨4, 6, 10000 / 4037, false⟩, ⟨6, 2, 249 / 1000, false⟩],
  [⟨0, 4, 55 / 9, false⟩, ⟨4, 6, 10000 / 4037, false⟩, ⟨6, 3, 319 / 1000, false⟩],
  [⟨0, 4, 55 / 9, false⟩, ⟨4, 6, 10000 / 4037, false⟩, ⟨6, 3, 319 / 1000, false⟩],
  [⟨0, 4, 55 / 9, false⟩, ⟨4, 6, 10000 / 4037, false⟩, ⟨6, 3, 319 / 1000, false⟩],
  [⟨0, 4, 55 / 9, false⟩, ⟨4, 6, 10000 / 4037, false⟩, ⟨6, 3, 319 / 1000, false⟩],
  [⟨0, 4, 55 / 9, false⟩, ⟨4, 6, 10000 / 4037, false⟩, ⟨6, 3, 319 / 1000, false⟩],
  [⟨0, 4, 55 / 9, false⟩, ⟨4, 6, 10000 / 4037, false⟩, ⟨6, 3, 319 / 1000, false⟩],
  [⟨0, 4, 55 / 9, false⟩],
  [⟨0, 4, 55 / 9, false⟩],
  [⟨0, 4, 55 / 9, false⟩],
  [⟨0, 4, 55 / 9, false⟩],
  [⟨0, 4, 55 / 9, false⟩],
  [⟨0, 4, 55 / 9, false⟩]
]

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem box4_0_checked : box4_0.all (fun row =>
    verify (dmaxBox ++ selectors4) row.1 row.2) = true := by decide +kernel
set_option maxRecDepth 12000 in
private theorem box4_0_targets : box4_0.map Prod.fst = part4_0.map Prod.fst := by decide +kernel

def box4_1 : List (Guard × List Guard) :=
  (part4_1.map Prod.fst).zip [
  [⟨0, 4, 55 / 9, false⟩],
  [⟨0, 4, 55 / 9, false⟩, ⟨4, 6, 10000 / 4037, false⟩, ⟨6, 3, 319 / 1000, false⟩, ⟨3, 5, 47 / 33, false⟩],
  [⟨0, 4, 55 / 9, false⟩, ⟨4, 6, 10000 / 4037, false⟩, ⟨6, 3, 319 / 1000, false⟩, ⟨3, 5, 47 / 33, false⟩],
  [⟨0, 4, 55 / 9, false⟩, ⟨4, 6, 10000 / 4037, false⟩, ⟨6, 3, 319 / 1000, false⟩, ⟨3, 5, 47 / 33, false⟩],
  [⟨0, 4, 55 / 9, false⟩, ⟨4, 6, 10000 / 4037, false⟩, ⟨6, 3, 319 / 1000, false⟩, ⟨3, 5, 47 / 33, false⟩],
  [⟨0, 4, 55 / 9, false⟩, ⟨4, 6, 10000 / 4037, false⟩, ⟨6, 3, 319 / 1000, false⟩, ⟨3, 5, 47 / 33, false⟩],
  [⟨0, 4, 55 / 9, false⟩, ⟨4, 6, 10000 / 4037, false⟩, ⟨6, 3, 319 / 1000, false⟩, ⟨3, 5, 47 / 33, false⟩],
  [⟨0, 4, 55 / 9, false⟩, ⟨4, 6, 10000 / 4037, false⟩, ⟨6, 3, 319 / 1000, false⟩, ⟨3, 5, 47 / 33, false⟩],
  [⟨0, 4, 55 / 9, false⟩, ⟨4, 6, 10000 / 4037, false⟩],
  [⟨0, 4, 55 / 9, false⟩, ⟨4, 6, 10000 / 4037, false⟩],
  [⟨0, 4, 55 / 9, false⟩, ⟨4, 6, 10000 / 4037, false⟩],
  [⟨0, 4, 55 / 9, false⟩, ⟨4, 6, 10000 / 4037, false⟩],
  [⟨0, 4, 55 / 9, false⟩, ⟨4, 6, 10000 / 4037, false⟩],
  [⟨0, 4, 55 / 9, false⟩, ⟨4, 6, 10000 / 4037, false⟩],
  [⟨0, 4, 55 / 9, false⟩, ⟨4, 6, 10000 / 4037, false⟩],
  [⟨1, 6, 10000 / 1837, false⟩, ⟨6, 0, 661 / 10000, false⟩],
  [⟨1, 6, 10000 / 1837, false⟩, ⟨6, 0, 661 / 10000, false⟩],
  [⟨1, 6, 10000 / 1837, false⟩, ⟨6, 0, 661 / 10000, false⟩],
  [⟨1, 6, 10000 / 1837, false⟩, ⟨6, 0, 661 / 10000, false⟩],
  [⟨1, 6, 10000 / 1837, false⟩, ⟨6, 0, 661 / 10000, false⟩],
  [],
  [],
  [],
  [⟨1, 6, 10000 / 1837, false⟩, ⟨6, 2, 249 / 1000, false⟩]
]

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem box4_1_checked : box4_1.all (fun row =>
    verify (dmaxBox ++ selectors4) row.1 row.2) = true := by decide +kernel
set_option maxRecDepth 12000 in
private theorem box4_1_targets : box4_1.map Prod.fst = part4_1.map Prod.fst := by decide +kernel

def box4_2 : List (Guard × List Guard) :=
  (part4_2.map Prod.fst).zip [
  [⟨1, 6, 10000 / 1837, false⟩, ⟨6, 2, 249 / 1000, false⟩],
  [⟨1, 6, 10000 / 1837, false⟩, ⟨6, 2, 249 / 1000, false⟩],
  [⟨1, 6, 10000 / 1837, false⟩, ⟨6, 2, 249 / 1000, false⟩],
  [⟨1, 6, 10000 / 1837, false⟩, ⟨6, 2, 249 / 1000, false⟩],
  [⟨1, 6, 10000 / 1837, false⟩, ⟨6, 3, 319 / 1000, false⟩],
  [⟨1, 6, 10000 / 1837, false⟩, ⟨6, 3, 319 / 1000, false⟩],
  [⟨1, 6, 10000 / 1837, false⟩, ⟨6, 3, 319 / 1000, false⟩],
  [⟨1, 6, 10000 / 1837, false⟩, ⟨6, 3, 319 / 1000, false⟩],
  [⟨1, 6, 10000 / 1837, false⟩, ⟨6, 3, 319 / 1000, false⟩],
  [⟨1, 6, 10000 / 1837, false⟩, ⟨6, 3, 319 / 1000, false⟩],
  [⟨1, 6, 10000 / 1837, false⟩, ⟨6, 4, 2019 / 5000, false⟩],
  [⟨1, 6, 10000 / 1837, false⟩, ⟨6, 4, 2019 / 5000, false⟩],
  [⟨1, 6, 10000 / 1837, false⟩, ⟨6, 4, 2019 / 5000, false⟩],
  [⟨1, 6, 10000 / 1837, false⟩, ⟨6, 4, 2019 / 5000, false⟩],
  [⟨1, 6, 10000 / 1837, false⟩, ⟨6, 4, 2019 / 5000, false⟩],
  [⟨1, 6, 10000 / 1837, false⟩, ⟨6, 4, 2019 / 5000, false⟩],
  [⟨1, 6, 10000 / 1837, false⟩, ⟨6, 4, 2019 / 5000, false⟩],
  [⟨1, 6, 10000 / 1837, false⟩, ⟨6, 3, 319 / 1000, false⟩, ⟨3, 5, 47 / 33, false⟩],
  [⟨1, 6, 10000 / 1837, false⟩, ⟨6, 3, 319 / 1000, false⟩, ⟨3, 5, 47 / 33, false⟩],
  [⟨1, 6, 10000 / 1837, false⟩, ⟨6, 3, 319 / 1000, false⟩, ⟨3, 5, 47 / 33, false⟩],
  [⟨1, 6, 10000 / 1837, false⟩, ⟨6, 3, 319 / 1000, false⟩, ⟨3, 5, 47 / 33, false⟩],
  [⟨1, 6, 10000 / 1837, false⟩, ⟨6, 3, 319 / 1000, false⟩, ⟨3, 5, 47 / 33, false⟩],
  [⟨1, 6, 10000 / 1837, false⟩, ⟨6, 3, 319 / 1000, false⟩, ⟨3, 5, 47 / 33, false⟩],
  [⟨1, 6, 10000 / 1837, false⟩, ⟨6, 3, 319 / 1000, false⟩, ⟨3, 5, 47 / 33, false⟩]
]

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem box4_2_checked : box4_2.all (fun row =>
    verify (dmaxBox ++ selectors4) row.1 row.2) = true := by decide +kernel
set_option maxRecDepth 12000 in
private theorem box4_2_targets : box4_2.map Prod.fst = part4_2.map Prod.fst := by decide +kernel

def box4_3 : List (Guard × List Guard) :=
  (part4_3.map Prod.fst).zip [
  [⟨1, 6, 10000 / 1837, false⟩, ⟨6, 3, 319 / 1000, false⟩, ⟨3, 5, 47 / 33, false⟩],
  [⟨1, 6, 10000 / 1837, false⟩],
  [⟨1, 6, 10000 / 1837, false⟩],
  [⟨1, 6, 10000 / 1837, false⟩],
  [⟨1, 6, 10000 / 1837, false⟩],
  [⟨1, 6, 10000 / 1837, false⟩],
  [⟨1, 6, 10000 / 1837, false⟩],
  [⟨1, 6, 10000 / 1837, false⟩],
  [⟨2, 6, 10000 / 2489, false⟩, ⟨6, 0, 661 / 10000, false⟩],
  [⟨2, 6, 10000 / 2489, false⟩, ⟨6, 0, 661 / 10000, false⟩],
  [⟨2, 6, 10000 / 2489, false⟩, ⟨6, 0, 661 / 10000, false⟩],
  [⟨2, 6, 10000 / 2489, false⟩, ⟨6, 0, 661 / 10000, false⟩],
  [⟨2, 6, 10000 / 2489, false⟩, ⟨6, 0, 661 / 10000, false⟩],
  [⟨2, 6, 10000 / 2489, false⟩, ⟨6, 1, 919 / 5000, false⟩],
  [⟨2, 6, 10000 / 2489, false⟩, ⟨6, 1, 919 / 5000, false⟩],
  [⟨2, 6, 10000 / 2489, false⟩, ⟨6, 1, 919 / 5000, false⟩],
  [⟨2, 6, 10000 / 2489, false⟩, ⟨6, 1, 919 / 5000, false⟩],
  [⟨2, 6, 10000 / 2489, false⟩, ⟨6, 1, 919 / 5000, false⟩],
  [⟨2, 6, 10000 / 2489, false⟩, ⟨6, 1, 919 / 5000, false⟩],
  [],
  [],
  [],
  [],
  [⟨2, 6, 10000 / 2489, false⟩, ⟨6, 3, 319 / 1000, false⟩]
]

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem box4_3_checked : box4_3.all (fun row =>
    verify (dmaxBox ++ selectors4) row.1 row.2) = true := by decide +kernel
set_option maxRecDepth 12000 in
private theorem box4_3_targets : box4_3.map Prod.fst = part4_3.map Prod.fst := by decide +kernel

def box4_4 : List (Guard × List Guard) :=
  (part4_4.map Prod.fst).zip [
  [⟨2, 6, 10000 / 2489, false⟩, ⟨6, 3, 319 / 1000, false⟩],
  [⟨2, 6, 10000 / 2489, false⟩, ⟨6, 3, 319 / 1000, false⟩],
  [⟨2, 6, 10000 / 2489, false⟩, ⟨6, 3, 319 / 1000, false⟩],
  [⟨2, 6, 10000 / 2489, false⟩, ⟨6, 3, 319 / 1000, false⟩],
  [⟨2, 6, 10000 / 2489, false⟩, ⟨6, 3, 319 / 1000, false⟩],
  [⟨2, 6, 10000 / 2489, false⟩, ⟨6, 3, 319 / 1000, false⟩],
  [⟨2, 6, 10000 / 2489, false⟩, ⟨6, 4, 2019 / 5000, false⟩],
  [⟨2, 6, 10000 / 2489, false⟩, ⟨6, 4, 2019 / 5000, false⟩],
  [⟨2, 6, 10000 / 2489, false⟩, ⟨6, 4, 2019 / 5000, false⟩],
  [⟨2, 6, 10000 / 2489, false⟩, ⟨6, 4, 2019 / 5000, false⟩],
  [⟨2, 6, 10000 / 2489, false⟩, ⟨6, 4, 2019 / 5000, false⟩],
  [⟨2, 6, 10000 / 2489, false⟩, ⟨6, 4, 2019 / 5000, false⟩],
  [⟨2, 6, 10000 / 2489, false⟩, ⟨6, 4, 2019 / 5000, false⟩],
  [⟨2, 6, 10000 / 2489, false⟩, ⟨6, 4, 2019 / 5000, false⟩],
  [⟨2, 6, 10000 / 2489, false⟩, ⟨6, 3, 319 / 1000, false⟩, ⟨3, 5, 47 / 33, false⟩],
  [⟨2, 6, 10000 / 2489, false⟩, ⟨6, 3, 319 / 1000, false⟩, ⟨3, 5, 47 / 33, false⟩],
  [⟨2, 6, 10000 / 2489, false⟩, ⟨6, 3, 319 / 1000, false⟩, ⟨3, 5, 47 / 33, false⟩],
  [⟨2, 6, 10000 / 2489, false⟩, ⟨6, 3, 319 / 1000, false⟩, ⟨3, 5, 47 / 33, false⟩],
  [⟨2, 6, 10000 / 2489, false⟩, ⟨6, 3, 319 / 1000, false⟩, ⟨3, 5, 47 / 33, false⟩],
  [⟨2, 6, 10000 / 2489, false⟩, ⟨6, 3, 319 / 1000, false⟩, ⟨3, 5, 47 / 33, false⟩],
  [⟨2, 6, 10000 / 2489, false⟩, ⟨6, 3, 319 / 1000, false⟩, ⟨3, 5, 47 / 33, false⟩],
  [⟨2, 6, 10000 / 2489, false⟩, ⟨6, 3, 319 / 1000, false⟩, ⟨3, 5, 47 / 33, false⟩],
  [⟨2, 6, 10000 / 2489, false⟩, ⟨6, 3, 319 / 1000, false⟩, ⟨3, 5, 47 / 33, false⟩],
  [⟨2, 6, 10000 / 2489, false⟩]
]

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem box4_4_checked : box4_4.all (fun row =>
    verify (dmaxBox ++ selectors4) row.1 row.2) = true := by decide +kernel
set_option maxRecDepth 12000 in
private theorem box4_4_targets : box4_4.map Prod.fst = part4_4.map Prod.fst := by decide +kernel

def box4_5 : List (Guard × List Guard) :=
  (part4_5.map Prod.fst).zip [
  [⟨2, 6, 10000 / 2489, false⟩],
  [⟨2, 6, 10000 / 2489, false⟩],
  [⟨2, 6, 10000 / 2489, false⟩],
  [⟨2, 6, 10000 / 2489, false⟩],
  [⟨2, 6, 10000 / 2489, false⟩],
  [⟨2, 6, 10000 / 2489, false⟩],
  [⟨2, 6, 10000 / 2489, false⟩],
  [⟨3, 5, 47 / 33, false⟩, ⟨5, 6, 10000 / 4543, false⟩, ⟨6, 0, 661 / 10000, false⟩],
  [⟨3, 5, 47 / 33, false⟩, ⟨5, 6, 10000 / 4543, false⟩, ⟨6, 0, 661 / 10000, false⟩],
  [⟨3, 5, 47 / 33, false⟩, ⟨5, 6, 10000 / 4543, false⟩, ⟨6, 0, 661 / 10000, false⟩],
  [⟨3, 5, 47 / 33, false⟩, ⟨5, 6, 10000 / 4543, false⟩, ⟨6, 0, 661 / 10000, false⟩],
  [⟨3, 5, 47 / 33, false⟩, ⟨5, 6, 10000 / 4543, false⟩, ⟨6, 0, 661 / 10000, false⟩],
  [⟨3, 5, 47 / 33, false⟩, ⟨5, 6, 10000 / 4543, false⟩, ⟨6, 0, 661 / 10000, false⟩],
  [⟨3, 5, 47 / 33, false⟩, ⟨5, 6, 10000 / 4543, false⟩, ⟨6, 1, 919 / 5000, false⟩],
  [⟨3, 5, 47 / 33, false⟩, ⟨5, 6, 10000 / 4543, false⟩, ⟨6, 1, 919 / 5000, false⟩],
  [⟨3, 5, 47 / 33, false⟩, ⟨5, 6, 10000 / 4543, false⟩, ⟨6, 1, 919 / 5000, false⟩],
  [⟨3, 5, 47 / 33, false⟩, ⟨5, 6, 10000 / 4543, false⟩, ⟨6, 1, 919 / 5000, false⟩],
  [⟨3, 5, 47 / 33, false⟩, ⟨5, 6, 10000 / 4543, false⟩, ⟨6, 1, 919 / 5000, false⟩],
  [⟨3, 5, 47 / 33, false⟩, ⟨5, 6, 10000 / 4543, false⟩, ⟨6, 1, 919 / 5000, false⟩],
  [⟨3, 5, 47 / 33, false⟩, ⟨5, 6, 10000 / 4543, false⟩, ⟨6, 2, 249 / 1000, false⟩],
  [⟨3, 5, 47 / 33, false⟩, ⟨5, 6, 10000 / 4543, false⟩, ⟨6, 2, 249 / 1000, false⟩],
  [⟨3, 5, 47 / 33, false⟩, ⟨5, 6, 10000 / 4543, false⟩, ⟨6, 2, 249 / 1000, false⟩],
  [⟨3, 5, 47 / 33, false⟩, ⟨5, 6, 10000 / 4543, false⟩, ⟨6, 2, 249 / 1000, false⟩],
  [⟨3, 5, 47 / 33, false⟩, ⟨5, 6, 10000 / 4543, false⟩, ⟨6, 2, 249 / 1000, false⟩]
]

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem box4_5_checked : box4_5.all (fun row =>
    verify (dmaxBox ++ selectors4) row.1 row.2) = true := by decide +kernel
set_option maxRecDepth 12000 in
private theorem box4_5_targets : box4_5.map Prod.fst = part4_5.map Prod.fst := by decide +kernel

def box4_6 : List (Guard × List Guard) :=
  (part4_6.map Prod.fst).zip [
  [⟨3, 5, 47 / 33, false⟩, ⟨5, 6, 10000 / 4543, false⟩, ⟨6, 2, 249 / 1000, false⟩],
  [],
  [],
  [],
  [],
  [],
  [⟨3, 5, 47 / 33, false⟩, ⟨5, 6, 10000 / 4543, false⟩, ⟨6, 4, 2019 / 5000, false⟩],
  [⟨3, 5, 47 / 33, false⟩, ⟨5, 6, 10000 / 4543, false⟩, ⟨6, 4, 2019 / 5000, false⟩],
  [⟨3, 5, 47 / 33, false⟩, ⟨5, 6, 10000 / 4543, false⟩, ⟨6, 4, 2019 / 5000, false⟩],
  [⟨3, 5, 47 / 33, false⟩, ⟨5, 6, 10000 / 4543, false⟩, ⟨6, 4, 2019 / 5000, false⟩],
  [⟨3, 5, 47 / 33, false⟩, ⟨5, 6, 10000 / 4543, false⟩, ⟨6, 4, 2019 / 5000, false⟩],
  [⟨3, 5, 47 / 33, false⟩, ⟨5, 6, 10000 / 4543, false⟩, ⟨6, 4, 2019 / 5000, false⟩],
  [⟨3, 5, 47 / 33, false⟩, ⟨5, 6, 10000 / 4543, false⟩, ⟨6, 4, 2019 / 5000, false⟩],
  [⟨3, 5, 47 / 33, false⟩, ⟨5, 6, 10000 / 4543, false⟩, ⟨6, 4, 2019 / 5000, false⟩],
  [⟨3, 5, 47 / 33, false⟩, ⟨5, 6, 10000 / 4543, false⟩, ⟨6, 4, 2019 / 5000, false⟩],
  [⟨3, 5, 47 / 33, false⟩],
  [⟨3, 5, 47 / 33, false⟩],
  [⟨3, 5, 47 / 33, false⟩],
  [⟨3, 5, 47 / 33, false⟩],
  [⟨3, 5, 47 / 33, false⟩],
  [⟨3, 5, 47 / 33, false⟩],
  [⟨3, 5, 47 / 33, false⟩],
  [⟨3, 5, 47 / 33, false⟩],
  [⟨3, 5, 47 / 33, false⟩]
]

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem box4_6_checked : box4_6.all (fun row =>
    verify (dmaxBox ++ selectors4) row.1 row.2) = true := by decide +kernel
set_option maxRecDepth 12000 in
private theorem box4_6_targets : box4_6.map Prod.fst = part4_6.map Prod.fst := by decide +kernel

def box4_7 : List (Guard × List Guard) :=
  (part4_7.map Prod.fst).zip [
  [⟨3, 5, 47 / 33, false⟩],
  [⟨3, 5, 47 / 33, false⟩, ⟨5, 6, 10000 / 4543, false⟩],
  [⟨3, 5, 47 / 33, false⟩, ⟨5, 6, 10000 / 4543, false⟩],
  [⟨3, 5, 47 / 33, false⟩, ⟨5, 6, 10000 / 4543, false⟩],
  [⟨3, 5, 47 / 33, false⟩, ⟨5, 6, 10000 / 4543, false⟩],
  [⟨3, 5, 47 / 33, false⟩, ⟨5, 6, 10000 / 4543, false⟩],
  [⟨3, 5, 47 / 33, false⟩, ⟨5, 6, 10000 / 4543, false⟩],
  [⟨3, 5, 47 / 33, false⟩, ⟨5, 6, 10000 / 4543, false⟩],
  [⟨3, 5, 47 / 33, false⟩, ⟨5, 6, 10000 / 4543, false⟩],
  [⟨3, 5, 47 / 33, false⟩, ⟨5, 6, 10000 / 4543, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩, ⟨6, 0, 661 / 10000, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩, ⟨6, 0, 661 / 10000, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩, ⟨6, 0, 661 / 10000, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩, ⟨6, 0, 661 / 10000, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩, ⟨6, 0, 661 / 10000, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩, ⟨6, 0, 661 / 10000, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩, ⟨6, 0, 661 / 10000, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩, ⟨6, 1, 919 / 5000, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩, ⟨6, 1, 919 / 5000, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩, ⟨6, 1, 919 / 5000, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩, ⟨6, 1, 919 / 5000, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩, ⟨6, 1, 919 / 5000, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩, ⟨6, 1, 919 / 5000, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩, ⟨6, 1, 919 / 5000, false⟩]
]

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem box4_7_checked : box4_7.all (fun row =>
    verify (dmaxBox ++ selectors4) row.1 row.2) = true := by decide +kernel
set_option maxRecDepth 12000 in
private theorem box4_7_targets : box4_7.map Prod.fst = part4_7.map Prod.fst := by decide +kernel

def box4_8 : List (Guard × List Guard) :=
  (part4_8.map Prod.fst).zip [
  [⟨4, 6, 10000 / 4037, false⟩, ⟨6, 2, 249 / 1000, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩, ⟨6, 2, 249 / 1000, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩, ⟨6, 2, 249 / 1000, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩, ⟨6, 2, 249 / 1000, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩, ⟨6, 2, 249 / 1000, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩, ⟨6, 2, 249 / 1000, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩, ⟨6, 2, 249 / 1000, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩, ⟨6, 2, 249 / 1000, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩, ⟨6, 3, 319 / 1000, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩, ⟨6, 3, 319 / 1000, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩, ⟨6, 3, 319 / 1000, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩, ⟨6, 3, 319 / 1000, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩, ⟨6, 3, 319 / 1000, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩, ⟨6, 3, 319 / 1000, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩, ⟨6, 3, 319 / 1000, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩, ⟨6, 3, 319 / 1000, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩, ⟨6, 3, 319 / 1000, false⟩],
  [],
  [],
  [],
  [],
  [],
  [],
  [⟨4, 6, 10000 / 4037, false⟩, ⟨6, 3, 319 / 1000, false⟩, ⟨3, 5, 47 / 33, false⟩]
]

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem box4_8_checked : box4_8.all (fun row =>
    verify (dmaxBox ++ selectors4) row.1 row.2) = true := by decide +kernel
set_option maxRecDepth 12000 in
private theorem box4_8_targets : box4_8.map Prod.fst = part4_8.map Prod.fst := by decide +kernel

def box4_9 : List (Guard × List Guard) :=
  (part4_9.map Prod.fst).zip [
  [⟨4, 6, 10000 / 4037, false⟩, ⟨6, 3, 319 / 1000, false⟩, ⟨3, 5, 47 / 33, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩, ⟨6, 3, 319 / 1000, false⟩, ⟨3, 5, 47 / 33, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩, ⟨6, 3, 319 / 1000, false⟩, ⟨3, 5, 47 / 33, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩, ⟨6, 3, 319 / 1000, false⟩, ⟨3, 5, 47 / 33, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩, ⟨6, 3, 319 / 1000, false⟩, ⟨3, 5, 47 / 33, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩, ⟨6, 3, 319 / 1000, false⟩, ⟨3, 5, 47 / 33, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩, ⟨6, 3, 319 / 1000, false⟩, ⟨3, 5, 47 / 33, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩, ⟨6, 3, 319 / 1000, false⟩, ⟨3, 5, 47 / 33, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩, ⟨6, 3, 319 / 1000, false⟩, ⟨3, 5, 47 / 33, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩, ⟨6, 3, 319 / 1000, false⟩, ⟨3, 5, 47 / 33, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩],
  [⟨5, 6, 10000 / 4543, false⟩, ⟨6, 0, 661 / 10000, false⟩],
  [⟨5, 6, 10000 / 4543, false⟩, ⟨6, 0, 661 / 10000, false⟩],
  [⟨5, 6, 10000 / 4543, false⟩, ⟨6, 0, 661 / 10000, false⟩],
  [⟨5, 6, 10000 / 4543, false⟩, ⟨6, 0, 661 / 10000, false⟩]
]

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem box4_9_checked : box4_9.all (fun row =>
    verify (dmaxBox ++ selectors4) row.1 row.2) = true := by decide +kernel
set_option maxRecDepth 12000 in
private theorem box4_9_targets : box4_9.map Prod.fst = part4_9.map Prod.fst := by decide +kernel

def box4_10 : List (Guard × List Guard) :=
  (part4_10.map Prod.fst).zip [
  [⟨5, 6, 10000 / 4543, false⟩, ⟨6, 0, 661 / 10000, false⟩],
  [⟨5, 6, 10000 / 4543, false⟩, ⟨6, 0, 661 / 10000, false⟩],
  [⟨5, 6, 10000 / 4543, false⟩, ⟨6, 0, 661 / 10000, false⟩],
  [⟨5, 6, 10000 / 4543, false⟩, ⟨6, 0, 661 / 10000, false⟩],
  [⟨5, 6, 10000 / 4543, false⟩, ⟨6, 1, 919 / 5000, false⟩],
  [⟨5, 6, 10000 / 4543, false⟩, ⟨6, 1, 919 / 5000, false⟩],
  [⟨5, 6, 10000 / 4543, false⟩, ⟨6, 1, 919 / 5000, false⟩],
  [⟨5, 6, 10000 / 4543, false⟩, ⟨6, 1, 919 / 5000, false⟩],
  [⟨5, 6, 10000 / 4543, false⟩, ⟨6, 1, 919 / 5000, false⟩],
  [⟨5, 6, 10000 / 4543, false⟩, ⟨6, 1, 919 / 5000, false⟩],
  [⟨5, 6, 10000 / 4543, false⟩, ⟨6, 1, 919 / 5000, false⟩],
  [⟨5, 6, 10000 / 4543, false⟩, ⟨6, 1, 919 / 5000, false⟩],
  [⟨5, 6, 10000 / 4543, false⟩, ⟨6, 2, 249 / 1000, false⟩],
  [⟨5, 6, 10000 / 4543, false⟩, ⟨6, 2, 249 / 1000, false⟩],
  [⟨5, 6, 10000 / 4543, false⟩, ⟨6, 2, 249 / 1000, false⟩],
  [⟨5, 6, 10000 / 4543, false⟩, ⟨6, 2, 249 / 1000, false⟩],
  [⟨5, 6, 10000 / 4543, false⟩, ⟨6, 2, 249 / 1000, false⟩],
  [⟨5, 6, 10000 / 4543, false⟩, ⟨6, 2, 249 / 1000, false⟩],
  [⟨5, 6, 10000 / 4543, false⟩, ⟨6, 2, 249 / 1000, false⟩],
  [⟨5, 6, 10000 / 4543, false⟩, ⟨6, 2, 249 / 1000, false⟩],
  [⟨5, 6, 10000 / 4543, false⟩, ⟨6, 3, 319 / 1000, false⟩],
  [⟨5, 6, 10000 / 4543, false⟩, ⟨6, 3, 319 / 1000, false⟩],
  [⟨5, 6, 10000 / 4543, false⟩, ⟨6, 3, 319 / 1000, false⟩],
  [⟨5, 6, 10000 / 4543, false⟩, ⟨6, 3, 319 / 1000, false⟩]
]

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem box4_10_checked : box4_10.all (fun row =>
    verify (dmaxBox ++ selectors4) row.1 row.2) = true := by decide +kernel
set_option maxRecDepth 12000 in
private theorem box4_10_targets : box4_10.map Prod.fst = part4_10.map Prod.fst := by decide +kernel

def box4_11 : List (Guard × List Guard) :=
  (part4_11.map Prod.fst).zip [
  [⟨5, 6, 10000 / 4543, false⟩, ⟨6, 3, 319 / 1000, false⟩],
  [⟨5, 6, 10000 / 4543, false⟩, ⟨6, 3, 319 / 1000, false⟩],
  [⟨5, 6, 10000 / 4543, false⟩, ⟨6, 3, 319 / 1000, false⟩],
  [⟨5, 6, 10000 / 4543, false⟩, ⟨6, 3, 319 / 1000, false⟩],
  [⟨5, 6, 10000 / 4543, false⟩, ⟨6, 3, 319 / 1000, false⟩],
  [⟨5, 6, 10000 / 4543, false⟩, ⟨6, 3, 319 / 1000, false⟩],
  [⟨5, 6, 10000 / 4543, false⟩, ⟨6, 4, 2019 / 5000, false⟩],
  [⟨5, 6, 10000 / 4543, false⟩, ⟨6, 4, 2019 / 5000, false⟩],
  [⟨5, 6, 10000 / 4543, false⟩, ⟨6, 4, 2019 / 5000, false⟩],
  [⟨5, 6, 10000 / 4543, false⟩, ⟨6, 4, 2019 / 5000, false⟩],
  [⟨5, 6, 10000 / 4543, false⟩, ⟨6, 4, 2019 / 5000, false⟩],
  [⟨5, 6, 10000 / 4543, false⟩, ⟨6, 4, 2019 / 5000, false⟩],
  [⟨5, 6, 10000 / 4543, false⟩, ⟨6, 4, 2019 / 5000, false⟩],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [⟨5, 6, 10000 / 4543, false⟩],
  [⟨5, 6, 10000 / 4543, false⟩],
  [⟨5, 6, 10000 / 4543, false⟩],
  [⟨5, 6, 10000 / 4543, false⟩]
]

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem box4_11_checked : box4_11.all (fun row =>
    verify (dmaxBox ++ selectors4) row.1 row.2) = true := by decide +kernel
set_option maxRecDepth 12000 in
private theorem box4_11_targets : box4_11.map Prod.fst = part4_11.map Prod.fst := by decide +kernel

def box4_12 : List (Guard × List Guard) :=
  (part4_12.map Prod.fst).zip [
  [⟨5, 6, 10000 / 4543, false⟩],
  [⟨5, 6, 10000 / 4543, false⟩],
  [⟨5, 6, 10000 / 4543, false⟩],
  [⟨5, 6, 10000 / 4543, false⟩],
  [⟨5, 6, 10000 / 4543, false⟩],
  [⟨5, 6, 10000 / 4543, false⟩],
  [⟨5, 6, 10000 / 4543, false⟩],
  [⟨6, 0, 661 / 10000, false⟩],
  [⟨6, 0, 661 / 10000, false⟩],
  [⟨6, 0, 661 / 10000, false⟩],
  [⟨6, 0, 661 / 10000, false⟩],
  [⟨6, 0, 661 / 10000, false⟩],
  [⟨6, 0, 661 / 10000, false⟩],
  [⟨6, 1, 919 / 5000, false⟩],
  [⟨6, 1, 919 / 5000, false⟩],
  [⟨6, 1, 919 / 5000, false⟩],
  [⟨6, 1, 919 / 5000, false⟩],
  [⟨6, 1, 919 / 5000, false⟩],
  [⟨6, 1, 919 / 5000, false⟩],
  [⟨6, 1, 919 / 5000, false⟩],
  [⟨6, 2, 249 / 1000, false⟩],
  [⟨6, 2, 249 / 1000, false⟩],
  [⟨6, 2, 249 / 1000, false⟩],
  [⟨6, 2, 249 / 1000, false⟩]
]

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem box4_12_checked : box4_12.all (fun row =>
    verify (dmaxBox ++ selectors4) row.1 row.2) = true := by decide +kernel
set_option maxRecDepth 12000 in
private theorem box4_12_targets : box4_12.map Prod.fst = part4_12.map Prod.fst := by decide +kernel

def box4_13 : List (Guard × List Guard) :=
  (part4_13.map Prod.fst).zip [
  [⟨6, 2, 249 / 1000, false⟩],
  [⟨6, 2, 249 / 1000, false⟩],
  [⟨6, 2, 249 / 1000, false⟩],
  [⟨6, 2, 249 / 1000, false⟩],
  [⟨6, 3, 319 / 1000, false⟩],
  [⟨6, 3, 319 / 1000, false⟩],
  [⟨6, 3, 319 / 1000, false⟩],
  [⟨6, 3, 319 / 1000, false⟩],
  [⟨6, 3, 319 / 1000, false⟩],
  [⟨6, 3, 319 / 1000, false⟩],
  [⟨6, 3, 319 / 1000, false⟩],
  [⟨6, 3, 319 / 1000, false⟩],
  [⟨6, 3, 319 / 1000, false⟩],
  [⟨6, 3, 319 / 1000, false⟩],
  [⟨6, 3, 319 / 1000, false⟩],
  [⟨6, 4, 2019 / 5000, false⟩],
  [⟨6, 4, 2019 / 5000, false⟩],
  [⟨6, 4, 2019 / 5000, false⟩],
  [⟨6, 4, 2019 / 5000, false⟩],
  [⟨6, 4, 2019 / 5000, false⟩],
  [⟨6, 4, 2019 / 5000, false⟩],
  [⟨6, 4, 2019 / 5000, false⟩],
  [⟨6, 4, 2019 / 5000, false⟩],
  [⟨6, 4, 2019 / 5000, false⟩]
]

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem box4_13_checked : box4_13.all (fun row =>
    verify (dmaxBox ++ selectors4) row.1 row.2) = true := by decide +kernel
set_option maxRecDepth 12000 in
private theorem box4_13_targets : box4_13.map Prod.fst = part4_13.map Prod.fst := by decide +kernel

def box4_14 : List (Guard × List Guard) :=
  (part4_14.map Prod.fst).zip [
  [⟨6, 4, 2019 / 5000, false⟩],
  [⟨6, 4, 2019 / 5000, false⟩],
  [⟨6, 3, 319 / 1000, false⟩, ⟨3, 5, 47 / 33, false⟩],
  [⟨6, 3, 319 / 1000, false⟩, ⟨3, 5, 47 / 33, false⟩],
  [⟨6, 3, 319 / 1000, false⟩, ⟨3, 5, 47 / 33, false⟩],
  [⟨6, 3, 319 / 1000, false⟩, ⟨3, 5, 47 / 33, false⟩],
  [⟨6, 3, 319 / 1000, false⟩, ⟨3, 5, 47 / 33, false⟩],
  [⟨6, 3, 319 / 1000, false⟩, ⟨3, 5, 47 / 33, false⟩],
  [⟨6, 3, 319 / 1000, false⟩, ⟨3, 5, 47 / 33, false⟩],
  [⟨6, 3, 319 / 1000, false⟩, ⟨3, 5, 47 / 33, false⟩],
  [⟨6, 3, 319 / 1000, false⟩, ⟨3, 5, 47 / 33, false⟩],
  [⟨6, 3, 319 / 1000, false⟩, ⟨3, 5, 47 / 33, false⟩],
  [⟨6, 3, 319 / 1000, false⟩, ⟨3, 5, 47 / 33, false⟩],
  [],
  [],
  [],
  [],
  [],
  []
]

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem box4_14_checked : box4_14.all (fun row =>
    verify (dmaxBox ++ selectors4) row.1 row.2) = true := by decide +kernel
set_option maxRecDepth 12000 in
private theorem box4_14_targets : box4_14.map Prod.fst = part4_14.map Prod.fst := by decide +kernel

def boxRoute4 := box4_0 ++ box4_1 ++ box4_2 ++ box4_3 ++ box4_4 ++ box4_5 ++ box4_6 ++ box4_7 ++ box4_8 ++ box4_9 ++ box4_10 ++ box4_11 ++ box4_12 ++ box4_13 ++ box4_14

theorem guards4 (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (he : ∀ g ∈ dmaxBox ++ selectors4, g.valid r) :
    ∀ g ∈ route4.map Prod.fst, g.valid r := by
  have hc : boxRoute4.all (fun row =>
      verify (dmaxBox ++ selectors4) row.1 row.2) = true := by
    simp only [boxRoute4, List.all_append, box4_0_checked, box4_1_checked, box4_2_checked, box4_3_checked, box4_4_checked, box4_5_checked, box4_6_checked, box4_7_checked, box4_8_checked, box4_9_checked, box4_10_checked, box4_11_checked, box4_12_checked, box4_13_checked, box4_14_checked, Bool.true_and]
  have ht : boxRoute4.map Prod.fst = route4.map Prod.fst := by
    simp only [boxRoute4, route4, List.map_append, box4_0_targets, box4_1_targets, box4_2_targets, box4_3_targets, box4_4_targets, box4_5_targets, box4_6_targets, box4_7_targets, box4_8_targets, box4_9_targets, box4_10_targets, box4_11_targets, box4_12_targets, box4_13_targets, box4_14_targets]
  intro g hg
  rw [← ht] at hg
  obtain ⟨row, hr, rfl⟩ := List.mem_map.mp hg
  exact verify_all_sound r hp he hc row hr

#print axioms guards4

def box5_0 : List (Guard × List Guard) :=
  (part5_0.map Prod.fst).zip [
  [],
  [],
  [],
  [⟨0, 5, 7 / 1, true⟩, ⟨5, 6, 10000 / 4543, false⟩, ⟨6, 1, 919 / 5000, false⟩],
  [⟨0, 5, 7 / 1, true⟩, ⟨5, 6, 10000 / 4543, false⟩, ⟨6, 1, 919 / 5000, false⟩],
  [⟨0, 5, 7 / 1, true⟩, ⟨5, 6, 10000 / 4543, false⟩, ⟨6, 1, 919 / 5000, false⟩],
  [⟨0, 5, 7 / 1, true⟩, ⟨5, 6, 10000 / 4543, false⟩, ⟨6, 1, 919 / 5000, false⟩],
  [⟨0, 5, 7 / 1, true⟩, ⟨5, 6, 10000 / 4543, false⟩, ⟨6, 2, 249 / 1000, false⟩],
  [⟨0, 5, 7 / 1, true⟩, ⟨5, 6, 10000 / 4543, false⟩, ⟨6, 2, 249 / 1000, false⟩],
  [⟨0, 5, 7 / 1, true⟩, ⟨5, 6, 10000 / 4543, false⟩, ⟨6, 2, 249 / 1000, false⟩],
  [⟨0, 5, 7 / 1, true⟩, ⟨5, 6, 10000 / 4543, false⟩, ⟨6, 2, 249 / 1000, false⟩],
  [⟨0, 5, 7 / 1, true⟩, ⟨5, 6, 10000 / 4543, false⟩, ⟨6, 2, 249 / 1000, false⟩],
  [⟨0, 5, 7 / 1, true⟩, ⟨5, 3, 23 / 33, false⟩],
  [⟨0, 5, 7 / 1, true⟩, ⟨5, 3, 23 / 33, false⟩],
  [⟨0, 5, 7 / 1, true⟩, ⟨5, 3, 23 / 33, false⟩],
  [⟨0, 5, 7 / 1, true⟩, ⟨5, 3, 23 / 33, false⟩],
  [⟨0, 5, 7 / 1, true⟩, ⟨5, 3, 23 / 33, false⟩],
  [⟨0, 5, 7 / 1, true⟩, ⟨5, 3, 23 / 33, false⟩],
  [⟨0, 5, 7 / 1, true⟩, ⟨5, 6, 10000 / 4543, false⟩, ⟨6, 4, 2019 / 5000, false⟩],
  [⟨0, 5, 7 / 1, true⟩, ⟨5, 6, 10000 / 4543, false⟩, ⟨6, 4, 2019 / 5000, false⟩],
  [⟨0, 5, 7 / 1, true⟩, ⟨5, 6, 10000 / 4543, false⟩, ⟨6, 4, 2019 / 5000, false⟩],
  [⟨0, 5, 7 / 1, true⟩, ⟨5, 6, 10000 / 4543, false⟩, ⟨6, 4, 2019 / 5000, false⟩],
  [⟨0, 5, 7 / 1, true⟩, ⟨5, 6, 10000 / 4543, false⟩, ⟨6, 4, 2019 / 5000, false⟩],
  [⟨0, 5, 7 / 1, true⟩, ⟨5, 6, 10000 / 4543, false⟩, ⟨6, 4, 2019 / 5000, false⟩]
]

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem box5_0_checked : box5_0.all (fun row =>
    verify (dmaxBox ++ selectors5) row.1 row.2) = true := by decide +kernel
set_option maxRecDepth 12000 in
private theorem box5_0_targets : box5_0.map Prod.fst = part5_0.map Prod.fst := by decide +kernel

def box5_1 : List (Guard × List Guard) :=
  (part5_1.map Prod.fst).zip [
  [⟨0, 5, 7 / 1, true⟩, ⟨5, 6, 10000 / 4543, false⟩, ⟨6, 4, 2019 / 5000, false⟩],
  [⟨0, 5, 7 / 1, true⟩],
  [⟨0, 5, 7 / 1, true⟩],
  [⟨0, 5, 7 / 1, true⟩],
  [⟨0, 5, 7 / 1, true⟩],
  [⟨0, 5, 7 / 1, true⟩],
  [⟨0, 5, 7 / 1, true⟩],
  [⟨0, 5, 7 / 1, true⟩],
  [⟨0, 5, 7 / 1, true⟩, ⟨5, 6, 10000 / 4543, false⟩],
  [⟨0, 5, 7 / 1, true⟩, ⟨5, 6, 10000 / 4543, false⟩],
  [⟨0, 5, 7 / 1, true⟩, ⟨5, 6, 10000 / 4543, false⟩],
  [⟨0, 5, 7 / 1, true⟩, ⟨5, 6, 10000 / 4543, false⟩],
  [⟨0, 5, 7 / 1, true⟩, ⟨5, 6, 10000 / 4543, false⟩],
  [⟨0, 5, 7 / 1, true⟩, ⟨5, 6, 10000 / 4543, false⟩],
  [⟨1, 6, 10000 / 1837, false⟩, ⟨6, 4, 2019 / 5000, false⟩, ⟨4, 0, 9 / 55, true⟩],
  [⟨1, 6, 10000 / 1837, false⟩, ⟨6, 4, 2019 / 5000, false⟩, ⟨4, 0, 9 / 55, true⟩],
  [⟨1, 6, 10000 / 1837, false⟩, ⟨6, 4, 2019 / 5000, false⟩, ⟨4, 0, 9 / 55, true⟩],
  [⟨1, 6, 10000 / 1837, false⟩, ⟨6, 4, 2019 / 5000, false⟩, ⟨4, 0, 9 / 55, true⟩],
  [⟨1, 6, 10000 / 1837, false⟩, ⟨6, 4, 2019 / 5000, false⟩, ⟨4, 0, 9 / 55, true⟩],
  [],
  [],
  [],
  [⟨1, 6, 10000 / 1837, false⟩, ⟨6, 2, 249 / 1000, false⟩],
  [⟨1, 6, 10000 / 1837, false⟩, ⟨6, 2, 249 / 1000, false⟩]
]

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem box5_1_checked : box5_1.all (fun row =>
    verify (dmaxBox ++ selectors5) row.1 row.2) = true := by decide +kernel
set_option maxRecDepth 12000 in
private theorem box5_1_targets : box5_1.map Prod.fst = part5_1.map Prod.fst := by decide +kernel

def box5_2 : List (Guard × List Guard) :=
  (part5_2.map Prod.fst).zip [
  [⟨1, 6, 10000 / 1837, false⟩, ⟨6, 2, 249 / 1000, false⟩],
  [⟨1, 6, 10000 / 1837, false⟩, ⟨6, 2, 249 / 1000, false⟩],
  [⟨1, 6, 10000 / 1837, false⟩, ⟨6, 2, 249 / 1000, false⟩],
  [⟨1, 6, 10000 / 1837, false⟩, ⟨6, 5, 284 / 625, false⟩, ⟨5, 3, 23 / 33, false⟩],
  [⟨1, 6, 10000 / 1837, false⟩, ⟨6, 5, 284 / 625, false⟩, ⟨5, 3, 23 / 33, false⟩],
  [⟨1, 6, 10000 / 1837, false⟩, ⟨6, 5, 284 / 625, false⟩, ⟨5, 3, 23 / 33, false⟩],
  [⟨1, 6, 10000 / 1837, false⟩, ⟨6, 5, 284 / 625, false⟩, ⟨5, 3, 23 / 33, false⟩],
  [⟨1, 6, 10000 / 1837, false⟩, ⟨6, 5, 284 / 625, false⟩, ⟨5, 3, 23 / 33, false⟩],
  [⟨1, 6, 10000 / 1837, false⟩, ⟨6, 5, 284 / 625, false⟩, ⟨5, 3, 23 / 33, false⟩],
  [⟨1, 6, 10000 / 1837, false⟩, ⟨6, 4, 2019 / 5000, false⟩],
  [⟨1, 6, 10000 / 1837, false⟩, ⟨6, 4, 2019 / 5000, false⟩],
  [⟨1, 6, 10000 / 1837, false⟩, ⟨6, 4, 2019 / 5000, false⟩],
  [⟨1, 6, 10000 / 1837, false⟩, ⟨6, 4, 2019 / 5000, false⟩],
  [⟨1, 6, 10000 / 1837, false⟩, ⟨6, 4, 2019 / 5000, false⟩],
  [⟨1, 6, 10000 / 1837, false⟩, ⟨6, 4, 2019 / 5000, false⟩],
  [⟨1, 6, 10000 / 1837, false⟩, ⟨6, 4, 2019 / 5000, false⟩],
  [⟨1, 6, 10000 / 1837, false⟩, ⟨6, 5, 284 / 625, false⟩],
  [⟨1, 6, 10000 / 1837, false⟩, ⟨6, 5, 284 / 625, false⟩],
  [⟨1, 6, 10000 / 1837, false⟩, ⟨6, 5, 284 / 625, false⟩],
  [⟨1, 6, 10000 / 1837, false⟩, ⟨6, 5, 284 / 625, false⟩],
  [⟨1, 6, 10000 / 1837, false⟩, ⟨6, 5, 284 / 625, false⟩],
  [⟨1, 6, 10000 / 1837, false⟩, ⟨6, 5, 284 / 625, false⟩],
  [⟨1, 6, 10000 / 1837, false⟩, ⟨6, 5, 284 / 625, false⟩],
  [⟨1, 6, 10000 / 1837, false⟩, ⟨6, 5, 284 / 625, false⟩]
]

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem box5_2_checked : box5_2.all (fun row =>
    verify (dmaxBox ++ selectors5) row.1 row.2) = true := by decide +kernel
set_option maxRecDepth 12000 in
private theorem box5_2_targets : box5_2.map Prod.fst = part5_2.map Prod.fst := by decide +kernel

def box5_3 : List (Guard × List Guard) :=
  (part5_3.map Prod.fst).zip [
  [⟨1, 6, 10000 / 1837, false⟩],
  [⟨1, 6, 10000 / 1837, false⟩],
  [⟨1, 6, 10000 / 1837, false⟩],
  [⟨1, 6, 10000 / 1837, false⟩],
  [⟨1, 6, 10000 / 1837, false⟩],
  [⟨1, 6, 10000 / 1837, false⟩],
  [⟨2, 6, 10000 / 2489, false⟩, ⟨6, 4, 2019 / 5000, false⟩, ⟨4, 0, 9 / 55, true⟩],
  [⟨2, 6, 10000 / 2489, false⟩, ⟨6, 4, 2019 / 5000, false⟩, ⟨4, 0, 9 / 55, true⟩],
  [⟨2, 6, 10000 / 2489, false⟩, ⟨6, 4, 2019 / 5000, false⟩, ⟨4, 0, 9 / 55, true⟩],
  [⟨2, 6, 10000 / 2489, false⟩, ⟨6, 4, 2019 / 5000, false⟩, ⟨4, 0, 9 / 55, true⟩],
  [⟨2, 6, 10000 / 2489, false⟩, ⟨6, 4, 2019 / 5000, false⟩, ⟨4, 0, 9 / 55, true⟩],
  [⟨2, 6, 10000 / 2489, false⟩, ⟨6, 1, 919 / 5000, false⟩],
  [⟨2, 6, 10000 / 2489, false⟩, ⟨6, 1, 919 / 5000, false⟩],
  [⟨2, 6, 10000 / 2489, false⟩, ⟨6, 1, 919 / 5000, false⟩],
  [⟨2, 6, 10000 / 2489, false⟩, ⟨6, 1, 919 / 5000, false⟩],
  [⟨2, 6, 10000 / 2489, false⟩, ⟨6, 1, 919 / 5000, false⟩],
  [⟨2, 6, 10000 / 2489, false⟩, ⟨6, 1, 919 / 5000, false⟩],
  [],
  [],
  [],
  [],
  [⟨2, 6, 10000 / 2489, false⟩, ⟨6, 5, 284 / 625, false⟩, ⟨5, 3, 23 / 33, false⟩],
  [⟨2, 6, 10000 / 2489, false⟩, ⟨6, 5, 284 / 625, false⟩, ⟨5, 3, 23 / 33, false⟩],
  [⟨2, 6, 10000 / 2489, false⟩, ⟨6, 5, 284 / 625, false⟩, ⟨5, 3, 23 / 33, false⟩]
]

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem box5_3_checked : box5_3.all (fun row =>
    verify (dmaxBox ++ selectors5) row.1 row.2) = true := by decide +kernel
set_option maxRecDepth 12000 in
private theorem box5_3_targets : box5_3.map Prod.fst = part5_3.map Prod.fst := by decide +kernel

def box5_4 : List (Guard × List Guard) :=
  (part5_4.map Prod.fst).zip [
  [⟨2, 6, 10000 / 2489, false⟩, ⟨6, 5, 284 / 625, false⟩, ⟨5, 3, 23 / 33, false⟩],
  [⟨2, 6, 10000 / 2489, false⟩, ⟨6, 5, 284 / 625, false⟩, ⟨5, 3, 23 / 33, false⟩],
  [⟨2, 6, 10000 / 2489, false⟩, ⟨6, 5, 284 / 625, false⟩, ⟨5, 3, 23 / 33, false⟩],
  [⟨2, 6, 10000 / 2489, false⟩, ⟨6, 5, 284 / 625, false⟩, ⟨5, 3, 23 / 33, false⟩],
  [⟨2, 6, 10000 / 2489, false⟩, ⟨6, 4, 2019 / 5000, false⟩],
  [⟨2, 6, 10000 / 2489, false⟩, ⟨6, 4, 2019 / 5000, false⟩],
  [⟨2, 6, 10000 / 2489, false⟩, ⟨6, 4, 2019 / 5000, false⟩],
  [⟨2, 6, 10000 / 2489, false⟩, ⟨6, 4, 2019 / 5000, false⟩],
  [⟨2, 6, 10000 / 2489, false⟩, ⟨6, 4, 2019 / 5000, false⟩],
  [⟨2, 6, 10000 / 2489, false⟩, ⟨6, 4, 2019 / 5000, false⟩],
  [⟨2, 6, 10000 / 2489, false⟩, ⟨6, 4, 2019 / 5000, false⟩],
  [⟨2, 6, 10000 / 2489, false⟩, ⟨6, 4, 2019 / 5000, false⟩],
  [⟨2, 6, 10000 / 2489, false⟩, ⟨6, 5, 284 / 625, false⟩],
  [⟨2, 6, 10000 / 2489, false⟩, ⟨6, 5, 284 / 625, false⟩],
  [⟨2, 6, 10000 / 2489, false⟩, ⟨6, 5, 284 / 625, false⟩],
  [⟨2, 6, 10000 / 2489, false⟩, ⟨6, 5, 284 / 625, false⟩],
  [⟨2, 6, 10000 / 2489, false⟩, ⟨6, 5, 284 / 625, false⟩],
  [⟨2, 6, 10000 / 2489, false⟩, ⟨6, 5, 284 / 625, false⟩],
  [⟨2, 6, 10000 / 2489, false⟩, ⟨6, 5, 284 / 625, false⟩],
  [⟨2, 6, 10000 / 2489, false⟩, ⟨6, 5, 284 / 625, false⟩],
  [⟨2, 6, 10000 / 2489, false⟩, ⟨6, 5, 284 / 625, false⟩],
  [⟨2, 6, 10000 / 2489, false⟩],
  [⟨2, 6, 10000 / 2489, false⟩],
  [⟨2, 6, 10000 / 2489, false⟩]
]

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem box5_4_checked : box5_4.all (fun row =>
    verify (dmaxBox ++ selectors5) row.1 row.2) = true := by decide +kernel
set_option maxRecDepth 12000 in
private theorem box5_4_targets : box5_4.map Prod.fst = part5_4.map Prod.fst := by decide +kernel

def box5_5 : List (Guard × List Guard) :=
  (part5_5.map Prod.fst).zip [
  [⟨2, 6, 10000 / 2489, false⟩],
  [⟨2, 6, 10000 / 2489, false⟩],
  [⟨2, 6, 10000 / 2489, false⟩],
  [⟨2, 6, 10000 / 2489, false⟩],
  [⟨3, 6, 625 / 197, false⟩, ⟨6, 4, 2019 / 5000, false⟩, ⟨4, 0, 9 / 55, true⟩],
  [⟨3, 6, 625 / 197, false⟩, ⟨6, 4, 2019 / 5000, false⟩, ⟨4, 0, 9 / 55, true⟩],
  [⟨3, 6, 625 / 197, false⟩, ⟨6, 4, 2019 / 5000, false⟩, ⟨4, 0, 9 / 55, true⟩],
  [⟨3, 6, 625 / 197, false⟩, ⟨6, 4, 2019 / 5000, false⟩, ⟨4, 0, 9 / 55, true⟩],
  [⟨3, 6, 625 / 197, false⟩, ⟨6, 4, 2019 / 5000, false⟩, ⟨4, 0, 9 / 55, true⟩],
  [⟨3, 6, 625 / 197, false⟩, ⟨6, 4, 2019 / 5000, false⟩, ⟨4, 0, 9 / 55, true⟩],
  [⟨3, 6, 625 / 197, false⟩, ⟨6, 1, 919 / 5000, false⟩],
  [⟨3, 6, 625 / 197, false⟩, ⟨6, 1, 919 / 5000, false⟩],
  [⟨3, 6, 625 / 197, false⟩, ⟨6, 1, 919 / 5000, false⟩],
  [⟨3, 6, 625 / 197, false⟩, ⟨6, 1, 919 / 5000, false⟩],
  [⟨3, 6, 625 / 197, false⟩, ⟨6, 1, 919 / 5000, false⟩],
  [⟨3, 6, 625 / 197, false⟩, ⟨6, 1, 919 / 5000, false⟩],
  [⟨3, 6, 625 / 197, false⟩, ⟨6, 2, 249 / 1000, false⟩],
  [⟨3, 6, 625 / 197, false⟩, ⟨6, 2, 249 / 1000, false⟩],
  [⟨3, 6, 625 / 197, false⟩, ⟨6, 2, 249 / 1000, false⟩],
  [⟨3, 6, 625 / 197, false⟩, ⟨6, 2, 249 / 1000, false⟩],
  [⟨3, 6, 625 / 197, false⟩, ⟨6, 2, 249 / 1000, false⟩],
  [⟨3, 6, 625 / 197, false⟩, ⟨6, 2, 249 / 1000, false⟩],
  [],
  []
]

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem box5_5_checked : box5_5.all (fun row =>
    verify (dmaxBox ++ selectors5) row.1 row.2) = true := by decide +kernel
set_option maxRecDepth 12000 in
private theorem box5_5_targets : box5_5.map Prod.fst = part5_5.map Prod.fst := by decide +kernel

def box5_6 : List (Guard × List Guard) :=
  (part5_6.map Prod.fst).zip [
  [],
  [],
  [],
  [⟨3, 6, 625 / 197, false⟩, ⟨6, 4, 2019 / 5000, false⟩],
  [⟨3, 6, 625 / 197, false⟩, ⟨6, 4, 2019 / 5000, false⟩],
  [⟨3, 6, 625 / 197, false⟩, ⟨6, 4, 2019 / 5000, false⟩],
  [⟨3, 6, 625 / 197, false⟩, ⟨6, 4, 2019 / 5000, false⟩],
  [⟨3, 6, 625 / 197, false⟩, ⟨6, 4, 2019 / 5000, false⟩],
  [⟨3, 6, 625 / 197, false⟩, ⟨6, 4, 2019 / 5000, false⟩],
  [⟨3, 6, 625 / 197, false⟩, ⟨6, 4, 2019 / 5000, false⟩],
  [⟨3, 6, 625 / 197, false⟩, ⟨6, 4, 2019 / 5000, false⟩],
  [⟨3, 6, 625 / 197, false⟩, ⟨6, 4, 2019 / 5000, false⟩],
  [⟨3, 6, 625 / 197, false⟩, ⟨6, 5, 284 / 625, false⟩],
  [⟨3, 6, 625 / 197, false⟩, ⟨6, 5, 284 / 625, false⟩],
  [⟨3, 6, 625 / 197, false⟩, ⟨6, 5, 284 / 625, false⟩],
  [⟨3, 6, 625 / 197, false⟩, ⟨6, 5, 284 / 625, false⟩],
  [⟨3, 6, 625 / 197, false⟩, ⟨6, 5, 284 / 625, false⟩],
  [⟨3, 6, 625 / 197, false⟩, ⟨6, 5, 284 / 625, false⟩],
  [⟨3, 6, 625 / 197, false⟩, ⟨6, 5, 284 / 625, false⟩],
  [⟨3, 6, 625 / 197, false⟩, ⟨6, 5, 284 / 625, false⟩],
  [⟨3, 6, 625 / 197, false⟩, ⟨6, 5, 284 / 625, false⟩],
  [⟨3, 6, 625 / 197, false⟩, ⟨6, 5, 284 / 625, false⟩],
  [⟨3, 6, 625 / 197, false⟩],
  [⟨3, 6, 625 / 197, false⟩]
]

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem box5_6_checked : box5_6.all (fun row =>
    verify (dmaxBox ++ selectors5) row.1 row.2) = true := by decide +kernel
set_option maxRecDepth 12000 in
private theorem box5_6_targets : box5_6.map Prod.fst = part5_6.map Prod.fst := by decide +kernel

def box5_7 : List (Guard × List Guard) :=
  (part5_7.map Prod.fst).zip [
  [⟨3, 6, 625 / 197, false⟩],
  [⟨3, 6, 625 / 197, false⟩],
  [⟨3, 6, 625 / 197, false⟩],
  [⟨3, 6, 625 / 197, false⟩],
  [⟨3, 6, 625 / 197, false⟩],
  [⟨3, 6, 625 / 197, false⟩],
  [⟨4, 0, 9 / 55, true⟩],
  [⟨4, 0, 9 / 55, true⟩],
  [⟨4, 0, 9 / 55, true⟩],
  [⟨4, 0, 9 / 55, true⟩],
  [⟨4, 0, 9 / 55, true⟩],
  [⟨4, 0, 9 / 55, true⟩],
  [⟨4, 0, 9 / 55, true⟩],
  [⟨4, 6, 10000 / 4037, false⟩, ⟨6, 1, 919 / 5000, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩, ⟨6, 1, 919 / 5000, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩, ⟨6, 1, 919 / 5000, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩, ⟨6, 1, 919 / 5000, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩, ⟨6, 1, 919 / 5000, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩, ⟨6, 1, 919 / 5000, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩, ⟨6, 1, 919 / 5000, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩, ⟨6, 2, 249 / 1000, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩, ⟨6, 2, 249 / 1000, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩, ⟨6, 2, 249 / 1000, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩, ⟨6, 2, 249 / 1000, false⟩]
]

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem box5_7_checked : box5_7.all (fun row =>
    verify (dmaxBox ++ selectors5) row.1 row.2) = true := by decide +kernel
set_option maxRecDepth 12000 in
private theorem box5_7_targets : box5_7.map Prod.fst = part5_7.map Prod.fst := by decide +kernel

def box5_8 : List (Guard × List Guard) :=
  (part5_8.map Prod.fst).zip [
  [⟨4, 6, 10000 / 4037, false⟩, ⟨6, 2, 249 / 1000, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩, ⟨6, 2, 249 / 1000, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩, ⟨6, 2, 249 / 1000, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩, ⟨6, 2, 249 / 1000, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩, ⟨6, 5, 284 / 625, false⟩, ⟨5, 3, 23 / 33, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩, ⟨6, 5, 284 / 625, false⟩, ⟨5, 3, 23 / 33, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩, ⟨6, 5, 284 / 625, false⟩, ⟨5, 3, 23 / 33, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩, ⟨6, 5, 284 / 625, false⟩, ⟨5, 3, 23 / 33, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩, ⟨6, 5, 284 / 625, false⟩, ⟨5, 3, 23 / 33, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩, ⟨6, 5, 284 / 625, false⟩, ⟨5, 3, 23 / 33, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩, ⟨6, 5, 284 / 625, false⟩, ⟨5, 3, 23 / 33, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩, ⟨6, 5, 284 / 625, false⟩, ⟨5, 3, 23 / 33, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩, ⟨6, 5, 284 / 625, false⟩, ⟨5, 3, 23 / 33, false⟩],
  [],
  [],
  [],
  [],
  [],
  [],
  [⟨4, 6, 10000 / 4037, false⟩, ⟨6, 5, 284 / 625, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩, ⟨6, 5, 284 / 625, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩, ⟨6, 5, 284 / 625, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩, ⟨6, 5, 284 / 625, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩, ⟨6, 5, 284 / 625, false⟩]
]

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem box5_8_checked : box5_8.all (fun row =>
    verify (dmaxBox ++ selectors5) row.1 row.2) = true := by decide +kernel
set_option maxRecDepth 12000 in
private theorem box5_8_targets : box5_8.map Prod.fst = part5_8.map Prod.fst := by decide +kernel

def box5_9 : List (Guard × List Guard) :=
  (part5_9.map Prod.fst).zip [
  [⟨4, 6, 10000 / 4037, false⟩, ⟨6, 5, 284 / 625, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩, ⟨6, 5, 284 / 625, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩, ⟨6, 5, 284 / 625, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩, ⟨6, 5, 284 / 625, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩, ⟨6, 5, 284 / 625, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩, ⟨6, 5, 284 / 625, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩],
  [⟨5, 6, 10000 / 4543, false⟩, ⟨6, 4, 2019 / 5000, false⟩, ⟨4, 0, 9 / 55, true⟩],
  [⟨5, 6, 10000 / 4543, false⟩, ⟨6, 4, 2019 / 5000, false⟩, ⟨4, 0, 9 / 55, true⟩],
  [⟨5, 6, 10000 / 4543, false⟩, ⟨6, 4, 2019 / 5000, false⟩, ⟨4, 0, 9 / 55, true⟩],
  [⟨5, 6, 10000 / 4543, false⟩, ⟨6, 4, 2019 / 5000, false⟩, ⟨4, 0, 9 / 55, true⟩],
  [⟨5, 6, 10000 / 4543, false⟩, ⟨6, 4, 2019 / 5000, false⟩, ⟨4, 0, 9 / 55, true⟩],
  [⟨5, 6, 10000 / 4543, false⟩, ⟨6, 4, 2019 / 5000, false⟩, ⟨4, 0, 9 / 55, true⟩],
  [⟨5, 6, 10000 / 4543, false⟩, ⟨6, 4, 2019 / 5000, false⟩, ⟨4, 0, 9 / 55, true⟩],
  [⟨5, 6, 10000 / 4543, false⟩, ⟨6, 4, 2019 / 5000, false⟩, ⟨4, 0, 9 / 55, true⟩],
  [⟨5, 6, 10000 / 4543, false⟩, ⟨6, 1, 919 / 5000, false⟩]
]

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem box5_9_checked : box5_9.all (fun row =>
    verify (dmaxBox ++ selectors5) row.1 row.2) = true := by decide +kernel
set_option maxRecDepth 12000 in
private theorem box5_9_targets : box5_9.map Prod.fst = part5_9.map Prod.fst := by decide +kernel

def box5_10 : List (Guard × List Guard) :=
  (part5_10.map Prod.fst).zip [
  [⟨5, 6, 10000 / 4543, false⟩, ⟨6, 1, 919 / 5000, false⟩],
  [⟨5, 6, 10000 / 4543, false⟩, ⟨6, 1, 919 / 5000, false⟩],
  [⟨5, 6, 10000 / 4543, false⟩, ⟨6, 1, 919 / 5000, false⟩],
  [⟨5, 6, 10000 / 4543, false⟩, ⟨6, 1, 919 / 5000, false⟩],
  [⟨5, 6, 10000 / 4543, false⟩, ⟨6, 1, 919 / 5000, false⟩],
  [⟨5, 6, 10000 / 4543, false⟩, ⟨6, 1, 919 / 5000, false⟩],
  [⟨5, 6, 10000 / 4543, false⟩, ⟨6, 1, 919 / 5000, false⟩],
  [⟨5, 6, 10000 / 4543, false⟩, ⟨6, 2, 249 / 1000, false⟩],
  [⟨5, 6, 10000 / 4543, false⟩, ⟨6, 2, 249 / 1000, false⟩],
  [⟨5, 6, 10000 / 4543, false⟩, ⟨6, 2, 249 / 1000, false⟩],
  [⟨5, 6, 10000 / 4543, false⟩, ⟨6, 2, 249 / 1000, false⟩],
  [⟨5, 6, 10000 / 4543, false⟩, ⟨6, 2, 249 / 1000, false⟩],
  [⟨5, 6, 10000 / 4543, false⟩, ⟨6, 2, 249 / 1000, false⟩],
  [⟨5, 6, 10000 / 4543, false⟩, ⟨6, 2, 249 / 1000, false⟩],
  [⟨5, 6, 10000 / 4543, false⟩, ⟨6, 2, 249 / 1000, false⟩],
  [⟨5, 3, 23 / 33, false⟩],
  [⟨5, 3, 23 / 33, false⟩],
  [⟨5, 3, 23 / 33, false⟩],
  [⟨5, 3, 23 / 33, false⟩],
  [⟨5, 3, 23 / 33, false⟩],
  [⟨5, 3, 23 / 33, false⟩],
  [⟨5, 3, 23 / 33, false⟩],
  [⟨5, 3, 23 / 33, false⟩],
  [⟨5, 3, 23 / 33, false⟩]
]

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem box5_10_checked : box5_10.all (fun row =>
    verify (dmaxBox ++ selectors5) row.1 row.2) = true := by decide +kernel
set_option maxRecDepth 12000 in
private theorem box5_10_targets : box5_10.map Prod.fst = part5_10.map Prod.fst := by decide +kernel

def box5_11 : List (Guard × List Guard) :=
  (part5_11.map Prod.fst).zip [
  [⟨5, 3, 23 / 33, false⟩],
  [⟨5, 6, 10000 / 4543, false⟩, ⟨6, 4, 2019 / 5000, false⟩],
  [⟨5, 6, 10000 / 4543, false⟩, ⟨6, 4, 2019 / 5000, false⟩],
  [⟨5, 6, 10000 / 4543, false⟩, ⟨6, 4, 2019 / 5000, false⟩],
  [⟨5, 6, 10000 / 4543, false⟩, ⟨6, 4, 2019 / 5000, false⟩],
  [⟨5, 6, 10000 / 4543, false⟩, ⟨6, 4, 2019 / 5000, false⟩],
  [⟨5, 6, 10000 / 4543, false⟩, ⟨6, 4, 2019 / 5000, false⟩],
  [⟨5, 6, 10000 / 4543, false⟩, ⟨6, 4, 2019 / 5000, false⟩],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [⟨5, 6, 10000 / 4543, false⟩],
  [⟨5, 6, 10000 / 4543, false⟩],
  [⟨5, 6, 10000 / 4543, false⟩],
  [⟨5, 6, 10000 / 4543, false⟩],
  [⟨5, 6, 10000 / 4543, false⟩],
  [⟨5, 6, 10000 / 4543, false⟩],
  [⟨5, 6, 10000 / 4543, false⟩],
  [⟨5, 6, 10000 / 4543, false⟩],
  [⟨5, 6, 10000 / 4543, false⟩]
]

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem box5_11_checked : box5_11.all (fun row =>
    verify (dmaxBox ++ selectors5) row.1 row.2) = true := by decide +kernel
set_option maxRecDepth 12000 in
private theorem box5_11_targets : box5_11.map Prod.fst = part5_11.map Prod.fst := by decide +kernel

def box5_12 : List (Guard × List Guard) :=
  (part5_12.map Prod.fst).zip [
  [⟨5, 6, 10000 / 4543, false⟩],
  [⟨6, 4, 2019 / 5000, false⟩, ⟨4, 0, 9 / 55, true⟩],
  [⟨6, 4, 2019 / 5000, false⟩, ⟨4, 0, 9 / 55, true⟩],
  [⟨6, 4, 2019 / 5000, false⟩, ⟨4, 0, 9 / 55, true⟩],
  [⟨6, 4, 2019 / 5000, false⟩, ⟨4, 0, 9 / 55, true⟩],
  [⟨6, 4, 2019 / 5000, false⟩, ⟨4, 0, 9 / 55, true⟩],
  [⟨6, 4, 2019 / 5000, false⟩, ⟨4, 0, 9 / 55, true⟩],
  [⟨6, 1, 919 / 5000, false⟩],
  [⟨6, 1, 919 / 5000, false⟩],
  [⟨6, 1, 919 / 5000, false⟩],
  [⟨6, 1, 919 / 5000, false⟩],
  [⟨6, 1, 919 / 5000, false⟩],
  [⟨6, 1, 919 / 5000, false⟩],
  [⟨6, 2, 249 / 1000, false⟩],
  [⟨6, 2, 249 / 1000, false⟩],
  [⟨6, 2, 249 / 1000, false⟩],
  [⟨6, 2, 249 / 1000, false⟩],
  [⟨6, 2, 249 / 1000, false⟩],
  [⟨6, 2, 249 / 1000, false⟩],
  [⟨6, 2, 249 / 1000, false⟩],
  [⟨6, 5, 284 / 625, false⟩, ⟨5, 3, 23 / 33, false⟩],
  [⟨6, 5, 284 / 625, false⟩, ⟨5, 3, 23 / 33, false⟩],
  [⟨6, 5, 284 / 625, false⟩, ⟨5, 3, 23 / 33, false⟩],
  [⟨6, 5, 284 / 625, false⟩, ⟨5, 3, 23 / 33, false⟩]
]

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem box5_12_checked : box5_12.all (fun row =>
    verify (dmaxBox ++ selectors5) row.1 row.2) = true := by decide +kernel
set_option maxRecDepth 12000 in
private theorem box5_12_targets : box5_12.map Prod.fst = part5_12.map Prod.fst := by decide +kernel

def box5_13 : List (Guard × List Guard) :=
  (part5_13.map Prod.fst).zip [
  [⟨6, 5, 284 / 625, false⟩, ⟨5, 3, 23 / 33, false⟩],
  [⟨6, 5, 284 / 625, false⟩, ⟨5, 3, 23 / 33, false⟩],
  [⟨6, 5, 284 / 625, false⟩, ⟨5, 3, 23 / 33, false⟩],
  [⟨6, 5, 284 / 625, false⟩, ⟨5, 3, 23 / 33, false⟩],
  [⟨6, 5, 284 / 625, false⟩, ⟨5, 3, 23 / 33, false⟩],
  [⟨6, 4, 2019 / 5000, false⟩],
  [⟨6, 4, 2019 / 5000, false⟩],
  [⟨6, 4, 2019 / 5000, false⟩],
  [⟨6, 4, 2019 / 5000, false⟩],
  [⟨6, 4, 2019 / 5000, false⟩],
  [⟨6, 4, 2019 / 5000, false⟩],
  [⟨6, 4, 2019 / 5000, false⟩],
  [⟨6, 4, 2019 / 5000, false⟩],
  [⟨6, 4, 2019 / 5000, false⟩],
  [⟨6, 4, 2019 / 5000, false⟩],
  [⟨6, 4, 2019 / 5000, false⟩],
  [⟨6, 5, 284 / 625, false⟩],
  [⟨6, 5, 284 / 625, false⟩],
  [⟨6, 5, 284 / 625, false⟩],
  [⟨6, 5, 284 / 625, false⟩],
  [⟨6, 5, 284 / 625, false⟩],
  [⟨6, 5, 284 / 625, false⟩],
  [⟨6, 5, 284 / 625, false⟩],
  [⟨6, 5, 284 / 625, false⟩]
]

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem box5_13_checked : box5_13.all (fun row =>
    verify (dmaxBox ++ selectors5) row.1 row.2) = true := by decide +kernel
set_option maxRecDepth 12000 in
private theorem box5_13_targets : box5_13.map Prod.fst = part5_13.map Prod.fst := by decide +kernel

def box5_14 : List (Guard × List Guard) :=
  (part5_14.map Prod.fst).zip [
  [⟨6, 5, 284 / 625, false⟩],
  [⟨6, 5, 284 / 625, false⟩],
  [⟨6, 5, 284 / 625, false⟩],
  [],
  [],
  [],
  [],
  []
]

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem box5_14_checked : box5_14.all (fun row =>
    verify (dmaxBox ++ selectors5) row.1 row.2) = true := by decide +kernel
set_option maxRecDepth 12000 in
private theorem box5_14_targets : box5_14.map Prod.fst = part5_14.map Prod.fst := by decide +kernel

def boxRoute5 := box5_0 ++ box5_1 ++ box5_2 ++ box5_3 ++ box5_4 ++ box5_5 ++ box5_6 ++ box5_7 ++ box5_8 ++ box5_9 ++ box5_10 ++ box5_11 ++ box5_12 ++ box5_13 ++ box5_14

theorem guards5 (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (he : ∀ g ∈ dmaxBox ++ selectors5, g.valid r) :
    ∀ g ∈ route5.map Prod.fst, g.valid r := by
  have hc : boxRoute5.all (fun row =>
      verify (dmaxBox ++ selectors5) row.1 row.2) = true := by
    simp only [boxRoute5, List.all_append, box5_0_checked, box5_1_checked, box5_2_checked, box5_3_checked, box5_4_checked, box5_5_checked, box5_6_checked, box5_7_checked, box5_8_checked, box5_9_checked, box5_10_checked, box5_11_checked, box5_12_checked, box5_13_checked, box5_14_checked, Bool.true_and]
  have ht : boxRoute5.map Prod.fst = route5.map Prod.fst := by
    simp only [boxRoute5, route5, List.map_append, box5_0_targets, box5_1_targets, box5_2_targets, box5_3_targets, box5_4_targets, box5_5_targets, box5_6_targets, box5_7_targets, box5_8_targets, box5_9_targets, box5_10_targets, box5_11_targets, box5_12_targets, box5_13_targets, box5_14_targets]
  intro g hg
  rw [← ht] at hg
  obtain ⟨row, hr, rfl⟩ := List.mem_map.mp hg
  exact verify_all_sound r hp he hc row hr

#print axioms guards5

def box6_0 : List (Guard × List Guard) :=
  (part6_0.map Prod.fst).zip [
  [],
  [],
  [],
  [⟨0, 4, 55 / 9, false⟩, ⟨4, 6, 10000 / 4037, false⟩, ⟨6, 1, 919 / 5000, false⟩],
  [⟨0, 4, 55 / 9, false⟩, ⟨4, 6, 10000 / 4037, false⟩, ⟨6, 1, 919 / 5000, false⟩],
  [⟨0, 4, 55 / 9, false⟩, ⟨4, 6, 10000 / 4037, false⟩, ⟨6, 1, 919 / 5000, false⟩],
  [⟨0, 4, 55 / 9, false⟩, ⟨4, 6, 10000 / 4037, false⟩, ⟨6, 1, 919 / 5000, false⟩],
  [⟨0, 4, 55 / 9, false⟩, ⟨4, 6, 10000 / 4037, false⟩, ⟨6, 2, 249 / 1000, false⟩],
  [⟨0, 4, 55 / 9, false⟩, ⟨4, 6, 10000 / 4037, false⟩, ⟨6, 2, 249 / 1000, false⟩],
  [⟨0, 4, 55 / 9, false⟩, ⟨4, 6, 10000 / 4037, false⟩, ⟨6, 2, 249 / 1000, false⟩],
  [⟨0, 4, 55 / 9, false⟩, ⟨4, 6, 10000 / 4037, false⟩, ⟨6, 2, 249 / 1000, false⟩],
  [⟨0, 4, 55 / 9, false⟩, ⟨4, 6, 10000 / 4037, false⟩, ⟨6, 2, 249 / 1000, false⟩],
  [⟨0, 4, 55 / 9, false⟩, ⟨4, 6, 10000 / 4037, false⟩, ⟨6, 5, 284 / 625, false⟩, ⟨5, 3, 23 / 33, false⟩],
  [⟨0, 4, 55 / 9, false⟩, ⟨4, 6, 10000 / 4037, false⟩, ⟨6, 5, 284 / 625, false⟩, ⟨5, 3, 23 / 33, false⟩],
  [⟨0, 4, 55 / 9, false⟩, ⟨4, 6, 10000 / 4037, false⟩, ⟨6, 5, 284 / 625, false⟩, ⟨5, 3, 23 / 33, false⟩],
  [⟨0, 4, 55 / 9, false⟩, ⟨4, 6, 10000 / 4037, false⟩, ⟨6, 5, 284 / 625, false⟩, ⟨5, 3, 23 / 33, false⟩],
  [⟨0, 4, 55 / 9, false⟩, ⟨4, 6, 10000 / 4037, false⟩, ⟨6, 5, 284 / 625, false⟩, ⟨5, 3, 23 / 33, false⟩],
  [⟨0, 4, 55 / 9, false⟩, ⟨4, 6, 10000 / 4037, false⟩, ⟨6, 5, 284 / 625, false⟩, ⟨5, 3, 23 / 33, false⟩],
  [⟨0, 4, 55 / 9, false⟩],
  [⟨0, 4, 55 / 9, false⟩],
  [⟨0, 4, 55 / 9, false⟩],
  [⟨0, 4, 55 / 9, false⟩],
  [⟨0, 4, 55 / 9, false⟩],
  [⟨0, 4, 55 / 9, false⟩]
]

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem box6_0_checked : box6_0.all (fun row =>
    verify (dmaxBox ++ selectors6) row.1 row.2) = true := by decide +kernel
set_option maxRecDepth 12000 in
private theorem box6_0_targets : box6_0.map Prod.fst = part6_0.map Prod.fst := by decide +kernel

def box6_1 : List (Guard × List Guard) :=
  (part6_1.map Prod.fst).zip [
  [⟨0, 4, 55 / 9, false⟩],
  [⟨0, 4, 55 / 9, false⟩, ⟨4, 6, 10000 / 4037, false⟩, ⟨6, 5, 284 / 625, false⟩],
  [⟨0, 4, 55 / 9, false⟩, ⟨4, 6, 10000 / 4037, false⟩, ⟨6, 5, 284 / 625, false⟩],
  [⟨0, 4, 55 / 9, false⟩, ⟨4, 6, 10000 / 4037, false⟩, ⟨6, 5, 284 / 625, false⟩],
  [⟨0, 4, 55 / 9, false⟩, ⟨4, 6, 10000 / 4037, false⟩, ⟨6, 5, 284 / 625, false⟩],
  [⟨0, 4, 55 / 9, false⟩, ⟨4, 6, 10000 / 4037, false⟩, ⟨6, 5, 284 / 625, false⟩],
  [⟨0, 4, 55 / 9, false⟩, ⟨4, 6, 10000 / 4037, false⟩, ⟨6, 5, 284 / 625, false⟩],
  [⟨0, 4, 55 / 9, false⟩, ⟨4, 6, 10000 / 4037, false⟩, ⟨6, 5, 284 / 625, false⟩],
  [⟨0, 4, 55 / 9, false⟩, ⟨4, 6, 10000 / 4037, false⟩],
  [⟨0, 4, 55 / 9, false⟩, ⟨4, 6, 10000 / 4037, false⟩],
  [⟨0, 4, 55 / 9, false⟩, ⟨4, 6, 10000 / 4037, false⟩],
  [⟨0, 4, 55 / 9, false⟩, ⟨4, 6, 10000 / 4037, false⟩],
  [⟨0, 4, 55 / 9, false⟩, ⟨4, 6, 10000 / 4037, false⟩],
  [⟨0, 4, 55 / 9, false⟩, ⟨4, 6, 10000 / 4037, false⟩],
  [⟨0, 4, 55 / 9, false⟩, ⟨4, 6, 10000 / 4037, false⟩],
  [⟨1, 6, 10000 / 1837, false⟩, ⟨6, 0, 661 / 10000, false⟩],
  [⟨1, 6, 10000 / 1837, false⟩, ⟨6, 0, 661 / 10000, false⟩],
  [⟨1, 6, 10000 / 1837, false⟩, ⟨6, 0, 661 / 10000, false⟩],
  [⟨1, 6, 10000 / 1837, false⟩, ⟨6, 0, 661 / 10000, false⟩],
  [⟨1, 6, 10000 / 1837, false⟩, ⟨6, 0, 661 / 10000, false⟩],
  [],
  [],
  [],
  [⟨1, 6, 10000 / 1837, false⟩, ⟨6, 2, 249 / 1000, false⟩]
]

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem box6_1_checked : box6_1.all (fun row =>
    verify (dmaxBox ++ selectors6) row.1 row.2) = true := by decide +kernel
set_option maxRecDepth 12000 in
private theorem box6_1_targets : box6_1.map Prod.fst = part6_1.map Prod.fst := by decide +kernel

def box6_2 : List (Guard × List Guard) :=
  (part6_2.map Prod.fst).zip [
  [⟨1, 6, 10000 / 1837, false⟩, ⟨6, 2, 249 / 1000, false⟩],
  [⟨1, 6, 10000 / 1837, false⟩, ⟨6, 2, 249 / 1000, false⟩],
  [⟨1, 6, 10000 / 1837, false⟩, ⟨6, 2, 249 / 1000, false⟩],
  [⟨1, 6, 10000 / 1837, false⟩, ⟨6, 2, 249 / 1000, false⟩],
  [⟨1, 6, 10000 / 1837, false⟩, ⟨6, 5, 284 / 625, false⟩, ⟨5, 3, 23 / 33, false⟩],
  [⟨1, 6, 10000 / 1837, false⟩, ⟨6, 5, 284 / 625, false⟩, ⟨5, 3, 23 / 33, false⟩],
  [⟨1, 6, 10000 / 1837, false⟩, ⟨6, 5, 284 / 625, false⟩, ⟨5, 3, 23 / 33, false⟩],
  [⟨1, 6, 10000 / 1837, false⟩, ⟨6, 5, 284 / 625, false⟩, ⟨5, 3, 23 / 33, false⟩],
  [⟨1, 6, 10000 / 1837, false⟩, ⟨6, 5, 284 / 625, false⟩, ⟨5, 3, 23 / 33, false⟩],
  [⟨1, 6, 10000 / 1837, false⟩, ⟨6, 5, 284 / 625, false⟩, ⟨5, 3, 23 / 33, false⟩],
  [⟨1, 6, 10000 / 1837, false⟩, ⟨6, 4, 2019 / 5000, false⟩],
  [⟨1, 6, 10000 / 1837, false⟩, ⟨6, 4, 2019 / 5000, false⟩],
  [⟨1, 6, 10000 / 1837, false⟩, ⟨6, 4, 2019 / 5000, false⟩],
  [⟨1, 6, 10000 / 1837, false⟩, ⟨6, 4, 2019 / 5000, false⟩],
  [⟨1, 6, 10000 / 1837, false⟩, ⟨6, 4, 2019 / 5000, false⟩],
  [⟨1, 6, 10000 / 1837, false⟩, ⟨6, 4, 2019 / 5000, false⟩],
  [⟨1, 6, 10000 / 1837, false⟩, ⟨6, 4, 2019 / 5000, false⟩],
  [⟨1, 6, 10000 / 1837, false⟩, ⟨6, 5, 284 / 625, false⟩],
  [⟨1, 6, 10000 / 1837, false⟩, ⟨6, 5, 284 / 625, false⟩],
  [⟨1, 6, 10000 / 1837, false⟩, ⟨6, 5, 284 / 625, false⟩],
  [⟨1, 6, 10000 / 1837, false⟩, ⟨6, 5, 284 / 625, false⟩],
  [⟨1, 6, 10000 / 1837, false⟩, ⟨6, 5, 284 / 625, false⟩],
  [⟨1, 6, 10000 / 1837, false⟩, ⟨6, 5, 284 / 625, false⟩],
  [⟨1, 6, 10000 / 1837, false⟩, ⟨6, 5, 284 / 625, false⟩]
]

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem box6_2_checked : box6_2.all (fun row =>
    verify (dmaxBox ++ selectors6) row.1 row.2) = true := by decide +kernel
set_option maxRecDepth 12000 in
private theorem box6_2_targets : box6_2.map Prod.fst = part6_2.map Prod.fst := by decide +kernel

def box6_3 : List (Guard × List Guard) :=
  (part6_3.map Prod.fst).zip [
  [⟨1, 6, 10000 / 1837, false⟩, ⟨6, 5, 284 / 625, false⟩],
  [⟨1, 6, 10000 / 1837, false⟩],
  [⟨1, 6, 10000 / 1837, false⟩],
  [⟨1, 6, 10000 / 1837, false⟩],
  [⟨1, 6, 10000 / 1837, false⟩],
  [⟨1, 6, 10000 / 1837, false⟩],
  [⟨1, 6, 10000 / 1837, false⟩],
  [⟨1, 6, 10000 / 1837, false⟩],
  [⟨2, 6, 10000 / 2489, false⟩, ⟨6, 0, 661 / 10000, false⟩],
  [⟨2, 6, 10000 / 2489, false⟩, ⟨6, 0, 661 / 10000, false⟩],
  [⟨2, 6, 10000 / 2489, false⟩, ⟨6, 0, 661 / 10000, false⟩],
  [⟨2, 6, 10000 / 2489, false⟩, ⟨6, 0, 661 / 10000, false⟩],
  [⟨2, 6, 10000 / 2489, false⟩, ⟨6, 0, 661 / 10000, false⟩],
  [⟨2, 6, 10000 / 2489, false⟩, ⟨6, 1, 919 / 5000, false⟩],
  [⟨2, 6, 10000 / 2489, false⟩, ⟨6, 1, 919 / 5000, false⟩],
  [⟨2, 6, 10000 / 2489, false⟩, ⟨6, 1, 919 / 5000, false⟩],
  [⟨2, 6, 10000 / 2489, false⟩, ⟨6, 1, 919 / 5000, false⟩],
  [⟨2, 6, 10000 / 2489, false⟩, ⟨6, 1, 919 / 5000, false⟩],
  [⟨2, 6, 10000 / 2489, false⟩, ⟨6, 1, 919 / 5000, false⟩],
  [],
  [],
  [],
  [],
  [⟨2, 6, 10000 / 2489, false⟩, ⟨6, 5, 284 / 625, false⟩, ⟨5, 3, 23 / 33, false⟩]
]

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem box6_3_checked : box6_3.all (fun row =>
    verify (dmaxBox ++ selectors6) row.1 row.2) = true := by decide +kernel
set_option maxRecDepth 12000 in
private theorem box6_3_targets : box6_3.map Prod.fst = part6_3.map Prod.fst := by decide +kernel

def box6_4 : List (Guard × List Guard) :=
  (part6_4.map Prod.fst).zip [
  [⟨2, 6, 10000 / 2489, false⟩, ⟨6, 5, 284 / 625, false⟩, ⟨5, 3, 23 / 33, false⟩],
  [⟨2, 6, 10000 / 2489, false⟩, ⟨6, 5, 284 / 625, false⟩, ⟨5, 3, 23 / 33, false⟩],
  [⟨2, 6, 10000 / 2489, false⟩, ⟨6, 5, 284 / 625, false⟩, ⟨5, 3, 23 / 33, false⟩],
  [⟨2, 6, 10000 / 2489, false⟩, ⟨6, 5, 284 / 625, false⟩, ⟨5, 3, 23 / 33, false⟩],
  [⟨2, 6, 10000 / 2489, false⟩, ⟨6, 5, 284 / 625, false⟩, ⟨5, 3, 23 / 33, false⟩],
  [⟨2, 6, 10000 / 2489, false⟩, ⟨6, 5, 284 / 625, false⟩, ⟨5, 3, 23 / 33, false⟩],
  [⟨2, 6, 10000 / 2489, false⟩, ⟨6, 4, 2019 / 5000, false⟩],
  [⟨2, 6, 10000 / 2489, false⟩, ⟨6, 4, 2019 / 5000, false⟩],
  [⟨2, 6, 10000 / 2489, false⟩, ⟨6, 4, 2019 / 5000, false⟩],
  [⟨2, 6, 10000 / 2489, false⟩, ⟨6, 4, 2019 / 5000, false⟩],
  [⟨2, 6, 10000 / 2489, false⟩, ⟨6, 4, 2019 / 5000, false⟩],
  [⟨2, 6, 10000 / 2489, false⟩, ⟨6, 4, 2019 / 5000, false⟩],
  [⟨2, 6, 10000 / 2489, false⟩, ⟨6, 4, 2019 / 5000, false⟩],
  [⟨2, 6, 10000 / 2489, false⟩, ⟨6, 4, 2019 / 5000, false⟩],
  [⟨2, 6, 10000 / 2489, false⟩, ⟨6, 5, 284 / 625, false⟩],
  [⟨2, 6, 10000 / 2489, false⟩, ⟨6, 5, 284 / 625, false⟩],
  [⟨2, 6, 10000 / 2489, false⟩, ⟨6, 5, 284 / 625, false⟩],
  [⟨2, 6, 10000 / 2489, false⟩, ⟨6, 5, 284 / 625, false⟩],
  [⟨2, 6, 10000 / 2489, false⟩, ⟨6, 5, 284 / 625, false⟩],
  [⟨2, 6, 10000 / 2489, false⟩, ⟨6, 5, 284 / 625, false⟩],
  [⟨2, 6, 10000 / 2489, false⟩, ⟨6, 5, 284 / 625, false⟩],
  [⟨2, 6, 10000 / 2489, false⟩, ⟨6, 5, 284 / 625, false⟩],
  [⟨2, 6, 10000 / 2489, false⟩, ⟨6, 5, 284 / 625, false⟩],
  [⟨2, 6, 10000 / 2489, false⟩]
]

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem box6_4_checked : box6_4.all (fun row =>
    verify (dmaxBox ++ selectors6) row.1 row.2) = true := by decide +kernel
set_option maxRecDepth 12000 in
private theorem box6_4_targets : box6_4.map Prod.fst = part6_4.map Prod.fst := by decide +kernel

def box6_5 : List (Guard × List Guard) :=
  (part6_5.map Prod.fst).zip [
  [⟨2, 6, 10000 / 2489, false⟩],
  [⟨2, 6, 10000 / 2489, false⟩],
  [⟨2, 6, 10000 / 2489, false⟩],
  [⟨2, 6, 10000 / 2489, false⟩],
  [⟨2, 6, 10000 / 2489, false⟩],
  [⟨2, 6, 10000 / 2489, false⟩],
  [⟨2, 6, 10000 / 2489, false⟩],
  [⟨3, 6, 625 / 197, false⟩, ⟨6, 0, 661 / 10000, false⟩],
  [⟨3, 6, 625 / 197, false⟩, ⟨6, 0, 661 / 10000, false⟩],
  [⟨3, 6, 625 / 197, false⟩, ⟨6, 0, 661 / 10000, false⟩],
  [⟨3, 6, 625 / 197, false⟩, ⟨6, 0, 661 / 10000, false⟩],
  [⟨3, 6, 625 / 197, false⟩, ⟨6, 0, 661 / 10000, false⟩],
  [⟨3, 6, 625 / 197, false⟩, ⟨6, 0, 661 / 10000, false⟩],
  [⟨3, 6, 625 / 197, false⟩, ⟨6, 1, 919 / 5000, false⟩],
  [⟨3, 6, 625 / 197, false⟩, ⟨6, 1, 919 / 5000, false⟩],
  [⟨3, 6, 625 / 197, false⟩, ⟨6, 1, 919 / 5000, false⟩],
  [⟨3, 6, 625 / 197, false⟩, ⟨6, 1, 919 / 5000, false⟩],
  [⟨3, 6, 625 / 197, false⟩, ⟨6, 1, 919 / 5000, false⟩],
  [⟨3, 6, 625 / 197, false⟩, ⟨6, 1, 919 / 5000, false⟩],
  [⟨3, 6, 625 / 197, false⟩, ⟨6, 2, 249 / 1000, false⟩],
  [⟨3, 6, 625 / 197, false⟩, ⟨6, 2, 249 / 1000, false⟩],
  [⟨3, 6, 625 / 197, false⟩, ⟨6, 2, 249 / 1000, false⟩],
  [⟨3, 6, 625 / 197, false⟩, ⟨6, 2, 249 / 1000, false⟩],
  [⟨3, 6, 625 / 197, false⟩, ⟨6, 2, 249 / 1000, false⟩]
]

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem box6_5_checked : box6_5.all (fun row =>
    verify (dmaxBox ++ selectors6) row.1 row.2) = true := by decide +kernel
set_option maxRecDepth 12000 in
private theorem box6_5_targets : box6_5.map Prod.fst = part6_5.map Prod.fst := by decide +kernel

def box6_6 : List (Guard × List Guard) :=
  (part6_6.map Prod.fst).zip [
  [⟨3, 6, 625 / 197, false⟩, ⟨6, 2, 249 / 1000, false⟩],
  [],
  [],
  [],
  [],
  [],
  [⟨3, 6, 625 / 197, false⟩, ⟨6, 4, 2019 / 5000, false⟩],
  [⟨3, 6, 625 / 197, false⟩, ⟨6, 4, 2019 / 5000, false⟩],
  [⟨3, 6, 625 / 197, false⟩, ⟨6, 4, 2019 / 5000, false⟩],
  [⟨3, 6, 625 / 197, false⟩, ⟨6, 4, 2019 / 5000, false⟩],
  [⟨3, 6, 625 / 197, false⟩, ⟨6, 4, 2019 / 5000, false⟩],
  [⟨3, 6, 625 / 197, false⟩, ⟨6, 4, 2019 / 5000, false⟩],
  [⟨3, 6, 625 / 197, false⟩, ⟨6, 4, 2019 / 5000, false⟩],
  [⟨3, 6, 625 / 197, false⟩, ⟨6, 4, 2019 / 5000, false⟩],
  [⟨3, 6, 625 / 197, false⟩, ⟨6, 4, 2019 / 5000, false⟩],
  [⟨3, 6, 625 / 197, false⟩, ⟨6, 5, 284 / 625, false⟩],
  [⟨3, 6, 625 / 197, false⟩, ⟨6, 5, 284 / 625, false⟩],
  [⟨3, 6, 625 / 197, false⟩, ⟨6, 5, 284 / 625, false⟩],
  [⟨3, 6, 625 / 197, false⟩, ⟨6, 5, 284 / 625, false⟩],
  [⟨3, 6, 625 / 197, false⟩, ⟨6, 5, 284 / 625, false⟩],
  [⟨3, 6, 625 / 197, false⟩, ⟨6, 5, 284 / 625, false⟩],
  [⟨3, 6, 625 / 197, false⟩, ⟨6, 5, 284 / 625, false⟩],
  [⟨3, 6, 625 / 197, false⟩, ⟨6, 5, 284 / 625, false⟩],
  [⟨3, 6, 625 / 197, false⟩, ⟨6, 5, 284 / 625, false⟩]
]

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem box6_6_checked : box6_6.all (fun row =>
    verify (dmaxBox ++ selectors6) row.1 row.2) = true := by decide +kernel
set_option maxRecDepth 12000 in
private theorem box6_6_targets : box6_6.map Prod.fst = part6_6.map Prod.fst := by decide +kernel

def box6_7 : List (Guard × List Guard) :=
  (part6_7.map Prod.fst).zip [
  [⟨3, 6, 625 / 197, false⟩, ⟨6, 5, 284 / 625, false⟩],
  [⟨3, 6, 625 / 197, false⟩],
  [⟨3, 6, 625 / 197, false⟩],
  [⟨3, 6, 625 / 197, false⟩],
  [⟨3, 6, 625 / 197, false⟩],
  [⟨3, 6, 625 / 197, false⟩],
  [⟨3, 6, 625 / 197, false⟩],
  [⟨3, 6, 625 / 197, false⟩],
  [⟨3, 6, 625 / 197, false⟩],
  [⟨3, 6, 625 / 197, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩, ⟨6, 0, 661 / 10000, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩, ⟨6, 0, 661 / 10000, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩, ⟨6, 0, 661 / 10000, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩, ⟨6, 0, 661 / 10000, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩, ⟨6, 0, 661 / 10000, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩, ⟨6, 0, 661 / 10000, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩, ⟨6, 0, 661 / 10000, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩, ⟨6, 1, 919 / 5000, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩, ⟨6, 1, 919 / 5000, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩, ⟨6, 1, 919 / 5000, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩, ⟨6, 1, 919 / 5000, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩, ⟨6, 1, 919 / 5000, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩, ⟨6, 1, 919 / 5000, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩, ⟨6, 1, 919 / 5000, false⟩]
]

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem box6_7_checked : box6_7.all (fun row =>
    verify (dmaxBox ++ selectors6) row.1 row.2) = true := by decide +kernel
set_option maxRecDepth 12000 in
private theorem box6_7_targets : box6_7.map Prod.fst = part6_7.map Prod.fst := by decide +kernel

def box6_8 : List (Guard × List Guard) :=
  (part6_8.map Prod.fst).zip [
  [⟨4, 6, 10000 / 4037, false⟩, ⟨6, 2, 249 / 1000, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩, ⟨6, 2, 249 / 1000, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩, ⟨6, 2, 249 / 1000, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩, ⟨6, 2, 249 / 1000, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩, ⟨6, 2, 249 / 1000, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩, ⟨6, 2, 249 / 1000, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩, ⟨6, 2, 249 / 1000, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩, ⟨6, 2, 249 / 1000, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩, ⟨6, 5, 284 / 625, false⟩, ⟨5, 3, 23 / 33, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩, ⟨6, 5, 284 / 625, false⟩, ⟨5, 3, 23 / 33, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩, ⟨6, 5, 284 / 625, false⟩, ⟨5, 3, 23 / 33, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩, ⟨6, 5, 284 / 625, false⟩, ⟨5, 3, 23 / 33, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩, ⟨6, 5, 284 / 625, false⟩, ⟨5, 3, 23 / 33, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩, ⟨6, 5, 284 / 625, false⟩, ⟨5, 3, 23 / 33, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩, ⟨6, 5, 284 / 625, false⟩, ⟨5, 3, 23 / 33, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩, ⟨6, 5, 284 / 625, false⟩, ⟨5, 3, 23 / 33, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩, ⟨6, 5, 284 / 625, false⟩, ⟨5, 3, 23 / 33, false⟩],
  [],
  [],
  [],
  [],
  [],
  [],
  [⟨4, 6, 10000 / 4037, false⟩, ⟨6, 5, 284 / 625, false⟩]
]

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem box6_8_checked : box6_8.all (fun row =>
    verify (dmaxBox ++ selectors6) row.1 row.2) = true := by decide +kernel
set_option maxRecDepth 12000 in
private theorem box6_8_targets : box6_8.map Prod.fst = part6_8.map Prod.fst := by decide +kernel

def box6_9 : List (Guard × List Guard) :=
  (part6_9.map Prod.fst).zip [
  [⟨4, 6, 10000 / 4037, false⟩, ⟨6, 5, 284 / 625, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩, ⟨6, 5, 284 / 625, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩, ⟨6, 5, 284 / 625, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩, ⟨6, 5, 284 / 625, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩, ⟨6, 5, 284 / 625, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩, ⟨6, 5, 284 / 625, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩, ⟨6, 5, 284 / 625, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩, ⟨6, 5, 284 / 625, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩, ⟨6, 5, 284 / 625, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩, ⟨6, 5, 284 / 625, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩],
  [⟨4, 6, 10000 / 4037, false⟩],
  [⟨5, 6, 10000 / 4543, false⟩, ⟨6, 0, 661 / 10000, false⟩],
  [⟨5, 6, 10000 / 4543, false⟩, ⟨6, 0, 661 / 10000, false⟩],
  [⟨5, 6, 10000 / 4543, false⟩, ⟨6, 0, 661 / 10000, false⟩],
  [⟨5, 6, 10000 / 4543, false⟩, ⟨6, 0, 661 / 10000, false⟩]
]

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem box6_9_checked : box6_9.all (fun row =>
    verify (dmaxBox ++ selectors6) row.1 row.2) = true := by decide +kernel
set_option maxRecDepth 12000 in
private theorem box6_9_targets : box6_9.map Prod.fst = part6_9.map Prod.fst := by decide +kernel

def box6_10 : List (Guard × List Guard) :=
  (part6_10.map Prod.fst).zip [
  [⟨5, 6, 10000 / 4543, false⟩, ⟨6, 0, 661 / 10000, false⟩],
  [⟨5, 6, 10000 / 4543, false⟩, ⟨6, 0, 661 / 10000, false⟩],
  [⟨5, 6, 10000 / 4543, false⟩, ⟨6, 0, 661 / 10000, false⟩],
  [⟨5, 6, 10000 / 4543, false⟩, ⟨6, 0, 661 / 10000, false⟩],
  [⟨5, 6, 10000 / 4543, false⟩, ⟨6, 1, 919 / 5000, false⟩],
  [⟨5, 6, 10000 / 4543, false⟩, ⟨6, 1, 919 / 5000, false⟩],
  [⟨5, 6, 10000 / 4543, false⟩, ⟨6, 1, 919 / 5000, false⟩],
  [⟨5, 6, 10000 / 4543, false⟩, ⟨6, 1, 919 / 5000, false⟩],
  [⟨5, 6, 10000 / 4543, false⟩, ⟨6, 1, 919 / 5000, false⟩],
  [⟨5, 6, 10000 / 4543, false⟩, ⟨6, 1, 919 / 5000, false⟩],
  [⟨5, 6, 10000 / 4543, false⟩, ⟨6, 1, 919 / 5000, false⟩],
  [⟨5, 6, 10000 / 4543, false⟩, ⟨6, 1, 919 / 5000, false⟩],
  [⟨5, 6, 10000 / 4543, false⟩, ⟨6, 2, 249 / 1000, false⟩],
  [⟨5, 6, 10000 / 4543, false⟩, ⟨6, 2, 249 / 1000, false⟩],
  [⟨5, 6, 10000 / 4543, false⟩, ⟨6, 2, 249 / 1000, false⟩],
  [⟨5, 6, 10000 / 4543, false⟩, ⟨6, 2, 249 / 1000, false⟩],
  [⟨5, 6, 10000 / 4543, false⟩, ⟨6, 2, 249 / 1000, false⟩],
  [⟨5, 6, 10000 / 4543, false⟩, ⟨6, 2, 249 / 1000, false⟩],
  [⟨5, 6, 10000 / 4543, false⟩, ⟨6, 2, 249 / 1000, false⟩],
  [⟨5, 6, 10000 / 4543, false⟩, ⟨6, 2, 249 / 1000, false⟩],
  [⟨5, 3, 23 / 33, false⟩],
  [⟨5, 3, 23 / 33, false⟩],
  [⟨5, 3, 23 / 33, false⟩],
  [⟨5, 3, 23 / 33, false⟩]
]

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem box6_10_checked : box6_10.all (fun row =>
    verify (dmaxBox ++ selectors6) row.1 row.2) = true := by decide +kernel
set_option maxRecDepth 12000 in
private theorem box6_10_targets : box6_10.map Prod.fst = part6_10.map Prod.fst := by decide +kernel

def box6_11 : List (Guard × List Guard) :=
  (part6_11.map Prod.fst).zip [
  [⟨5, 3, 23 / 33, false⟩],
  [⟨5, 3, 23 / 33, false⟩],
  [⟨5, 3, 23 / 33, false⟩],
  [⟨5, 3, 23 / 33, false⟩],
  [⟨5, 3, 23 / 33, false⟩],
  [⟨5, 3, 23 / 33, false⟩],
  [⟨5, 6, 10000 / 4543, false⟩, ⟨6, 4, 2019 / 5000, false⟩],
  [⟨5, 6, 10000 / 4543, false⟩, ⟨6, 4, 2019 / 5000, false⟩],
  [⟨5, 6, 10000 / 4543, false⟩, ⟨6, 4, 2019 / 5000, false⟩],
  [⟨5, 6, 10000 / 4543, false⟩, ⟨6, 4, 2019 / 5000, false⟩],
  [⟨5, 6, 10000 / 4543, false⟩, ⟨6, 4, 2019 / 5000, false⟩],
  [⟨5, 6, 10000 / 4543, false⟩, ⟨6, 4, 2019 / 5000, false⟩],
  [⟨5, 6, 10000 / 4543, false⟩, ⟨6, 4, 2019 / 5000, false⟩],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [⟨5, 6, 10000 / 4543, false⟩],
  [⟨5, 6, 10000 / 4543, false⟩],
  [⟨5, 6, 10000 / 4543, false⟩],
  [⟨5, 6, 10000 / 4543, false⟩]
]

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem box6_11_checked : box6_11.all (fun row =>
    verify (dmaxBox ++ selectors6) row.1 row.2) = true := by decide +kernel
set_option maxRecDepth 12000 in
private theorem box6_11_targets : box6_11.map Prod.fst = part6_11.map Prod.fst := by decide +kernel

def box6_12 : List (Guard × List Guard) :=
  (part6_12.map Prod.fst).zip [
  [⟨5, 6, 10000 / 4543, false⟩],
  [⟨5, 6, 10000 / 4543, false⟩],
  [⟨5, 6, 10000 / 4543, false⟩],
  [⟨5, 6, 10000 / 4543, false⟩],
  [⟨5, 6, 10000 / 4543, false⟩],
  [⟨5, 6, 10000 / 4543, false⟩],
  [⟨5, 6, 10000 / 4543, false⟩],
  [⟨6, 0, 661 / 10000, false⟩],
  [⟨6, 0, 661 / 10000, false⟩],
  [⟨6, 0, 661 / 10000, false⟩],
  [⟨6, 0, 661 / 10000, false⟩],
  [⟨6, 0, 661 / 10000, false⟩],
  [⟨6, 0, 661 / 10000, false⟩],
  [⟨6, 1, 919 / 5000, false⟩],
  [⟨6, 1, 919 / 5000, false⟩],
  [⟨6, 1, 919 / 5000, false⟩],
  [⟨6, 1, 919 / 5000, false⟩],
  [⟨6, 1, 919 / 5000, false⟩],
  [⟨6, 1, 919 / 5000, false⟩],
  [⟨6, 1, 919 / 5000, false⟩],
  [⟨6, 2, 249 / 1000, false⟩],
  [⟨6, 2, 249 / 1000, false⟩],
  [⟨6, 2, 249 / 1000, false⟩],
  [⟨6, 2, 249 / 1000, false⟩]
]

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem box6_12_checked : box6_12.all (fun row =>
    verify (dmaxBox ++ selectors6) row.1 row.2) = true := by decide +kernel
set_option maxRecDepth 12000 in
private theorem box6_12_targets : box6_12.map Prod.fst = part6_12.map Prod.fst := by decide +kernel

def box6_13 : List (Guard × List Guard) :=
  (part6_13.map Prod.fst).zip [
  [⟨6, 2, 249 / 1000, false⟩],
  [⟨6, 2, 249 / 1000, false⟩],
  [⟨6, 2, 249 / 1000, false⟩],
  [⟨6, 2, 249 / 1000, false⟩],
  [⟨6, 5, 284 / 625, false⟩, ⟨5, 3, 23 / 33, false⟩],
  [⟨6, 5, 284 / 625, false⟩, ⟨5, 3, 23 / 33, false⟩],
  [⟨6, 5, 284 / 625, false⟩, ⟨5, 3, 23 / 33, false⟩],
  [⟨6, 5, 284 / 625, false⟩, ⟨5, 3, 23 / 33, false⟩],
  [⟨6, 5, 284 / 625, false⟩, ⟨5, 3, 23 / 33, false⟩],
  [⟨6, 5, 284 / 625, false⟩, ⟨5, 3, 23 / 33, false⟩],
  [⟨6, 5, 284 / 625, false⟩, ⟨5, 3, 23 / 33, false⟩],
  [⟨6, 5, 284 / 625, false⟩, ⟨5, 3, 23 / 33, false⟩],
  [⟨6, 5, 284 / 625, false⟩, ⟨5, 3, 23 / 33, false⟩],
  [⟨6, 5, 284 / 625, false⟩, ⟨5, 3, 23 / 33, false⟩],
  [⟨6, 4, 2019 / 5000, false⟩],
  [⟨6, 4, 2019 / 5000, false⟩],
  [⟨6, 4, 2019 / 5000, false⟩],
  [⟨6, 4, 2019 / 5000, false⟩],
  [⟨6, 4, 2019 / 5000, false⟩],
  [⟨6, 4, 2019 / 5000, false⟩],
  [⟨6, 4, 2019 / 5000, false⟩],
  [⟨6, 4, 2019 / 5000, false⟩],
  [⟨6, 4, 2019 / 5000, false⟩],
  [⟨6, 4, 2019 / 5000, false⟩]
]

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem box6_13_checked : box6_13.all (fun row =>
    verify (dmaxBox ++ selectors6) row.1 row.2) = true := by decide +kernel
set_option maxRecDepth 12000 in
private theorem box6_13_targets : box6_13.map Prod.fst = part6_13.map Prod.fst := by decide +kernel

def box6_14 : List (Guard × List Guard) :=
  (part6_14.map Prod.fst).zip [
  [⟨6, 4, 2019 / 5000, false⟩],
  [⟨6, 5, 284 / 625, false⟩],
  [⟨6, 5, 284 / 625, false⟩],
  [⟨6, 5, 284 / 625, false⟩],
  [⟨6, 5, 284 / 625, false⟩],
  [⟨6, 5, 284 / 625, false⟩],
  [⟨6, 5, 284 / 625, false⟩],
  [⟨6, 5, 284 / 625, false⟩],
  [⟨6, 5, 284 / 625, false⟩],
  [⟨6, 5, 284 / 625, false⟩],
  [⟨6, 5, 284 / 625, false⟩],
  [⟨6, 5, 284 / 625, false⟩],
  [⟨6, 5, 284 / 625, false⟩],
  [],
  [],
  [],
  [],
  [],
  []
]

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem box6_14_checked : box6_14.all (fun row =>
    verify (dmaxBox ++ selectors6) row.1 row.2) = true := by decide +kernel
set_option maxRecDepth 12000 in
private theorem box6_14_targets : box6_14.map Prod.fst = part6_14.map Prod.fst := by decide +kernel

def boxRoute6 := box6_0 ++ box6_1 ++ box6_2 ++ box6_3 ++ box6_4 ++ box6_5 ++ box6_6 ++ box6_7 ++ box6_8 ++ box6_9 ++ box6_10 ++ box6_11 ++ box6_12 ++ box6_13 ++ box6_14

theorem guards6 (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i)
    (he : ∀ g ∈ dmaxBox ++ selectors6, g.valid r) :
    ∀ g ∈ route6.map Prod.fst, g.valid r := by
  have hc : boxRoute6.all (fun row =>
      verify (dmaxBox ++ selectors6) row.1 row.2) = true := by
    simp only [boxRoute6, List.all_append, box6_0_checked, box6_1_checked, box6_2_checked, box6_3_checked, box6_4_checked, box6_5_checked, box6_6_checked, box6_7_checked, box6_8_checked, box6_9_checked, box6_10_checked, box6_11_checked, box6_12_checked, box6_13_checked, box6_14_checked, Bool.true_and]
  have ht : boxRoute6.map Prod.fst = route6.map Prod.fst := by
    simp only [boxRoute6, route6, List.map_append, box6_0_targets, box6_1_targets, box6_2_targets, box6_3_targets, box6_4_targets, box6_5_targets, box6_6_targets, box6_7_targets, box6_8_targets, box6_9_targets, box6_10_targets, box6_11_targets, box6_12_targets, box6_13_targets, box6_14_targets]
  intro g hg
  rw [← ht] at hg
  obtain ⟨row, hr, rfl⟩ := List.mem_map.mp hg
  exact verify_all_sound r hp he hc row hr

#print axioms guards6

end Fresh.NativeJ2DmaxBoxChecked
