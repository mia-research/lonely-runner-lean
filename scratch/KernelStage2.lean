namespace KernelStage2
def exc : List (List Nat) := [[1,4,11,39,43],[1,4,18,22,29],[1,4,18,44,46]]
def lifts (T : List Nat) : List (List Nat) :=
  T.foldr (fun x acc => acc.flatMap fun L => [x :: L, (x+49) :: L]) [[]]
def d6vals : List Nat := (List.range 14).filterMap (fun k =>
  let v := 7*k; if k == 0 || v % 49 == 0 || v ≥ 98 then none else some v)
def gcdAll (L : List Nat) : Nat := L.foldr Nat.gcd 0
def solvable98 (D : List Nat) : Bool :=
  (List.range 98).any fun lam => lam > 0 && D.all fun x => let v := (lam*x)%98; 14 ≤ v && v ≤ 84
/-- configurations with gcd = 1 that admit NO good multiplier mod 98 -/
def bad2 : List (List Nat) :=
  (exc.flatMap fun E => (lifts E).flatMap fun L => d6vals.map fun d6 => d6 :: L)
    |>.filter fun D => gcdAll D == 1 && !solvable98 D

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 8000000 in
/-- BS §7 stage 2, kernel-verified: every gcd = 1 configuration over N' = 98 that
reduces to an exceptional 5-set admits a good multiplier. The configurations BS
could not solve all have gcd ≥ 2 and are excluded by the LRC normalization. -/
theorem stage2_clean : bad2 = [] := by rfl

end KernelStage2
