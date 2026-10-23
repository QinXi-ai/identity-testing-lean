import IdentityTesting.BinaryMultiplierMachine

namespace IdentityTesting.BinaryMultiplierMachine
open BinaryArithmetic

def ready (xs ys acc : List Bool) (r : BinaryAdderMachine.Registers) : State :=
  ⟨.scan, xs, ys, [], acc, BinaryAdderMachine.haltState r []⟩

def terminal (ys acc : List Bool) (r : BinaryAdderMachine.Registers) : State :=
  ⟨.halt, [], ys, [], acc, BinaryAdderMachine.haltState r []⟩

theorem false_iteration (xs ys acc : List Bool) (r : BinaryAdderMachine.Registers) :
    Runs (ready (false :: xs) ys acc r) 2 (ready xs (false :: ys) acc r) := rfl

theorem true_iteration (xs ys acc : List Bool) (r : BinaryAdderMachine.Registers)
    (hlen : acc.length ≤ ys.length) :
    ∃ steps r', steps ≤ 20 * (ys.length + 1) ∧
      Runs (ready (true :: xs) ys acc r) steps
        (ready xs (false :: ys) (BinaryArithmetic.add ys acc false).value r') := by
  let a0 := BinaryAdderMachine.haltState r []
  let ay := { a0 with left := ys }
  let ayacc := { ay with right := acc }
  let ai := BinaryAdderMachine.loopState ys acc { carry := false } []
  let z := (BinaryArithmetic.add ys acc false).value
  obtain ⟨n, r', hn, had⟩ := BinaryAdderMachine.run_add ys acc { carry := false } []
  simp only [List.length_nil, List.reverse_nil, List.nil_append, Nat.add_zero] at hn had
  have hh : (BinaryAdderMachine.advance n ai).phase = .halt := by
    change (BinaryAdderMachine.advance n
      (BinaryAdderMachine.loopState ys acc { carry := false } [])).phase = .halt
    rw [had]
    rfl
  obtain ⟨k, hk, hsub⟩ := forward_add xs ys [] [] ai n hh
  have hsub' : Runs ⟨.adding, xs, ys, [], [], ai⟩ k
      ⟨.outToTmp, xs, ys, [], [], BinaryAdderMachine.haltState r' z⟩ := by
    simpa only [ai, had] using hsub
  have h0 : Runs (ready (true :: xs) ys acc r) 1
      ⟨.yToTmp, xs, ys, [], acc, a0⟩ := rfl
  have h1 : Runs ⟨.yToTmp, xs, ys, [], acc, a0⟩ (ys.length + 1)
      ⟨.tmpToY, xs, [], ys.reverse, acc, a0⟩ := by
    simpa only [List.append_nil] using yToTmp_run xs ys [] acc a0
  have h2 : Runs ⟨.tmpToY, xs, [], ys.reverse, acc, a0⟩ (ys.length + 1)
      ⟨.accToTmp, xs, ys, [], acc, ay⟩ := by
    simpa [a0, ay, BinaryAdderMachine.haltState] using tmpToY_run xs [] ys.reverse acc a0
  have h3 : Runs ⟨.accToTmp, xs, ys, [], acc, ay⟩ (acc.length + 1)
      ⟨.tmpToRight, xs, ys, acc.reverse, [], ay⟩ := by
    simpa only [List.append_nil] using accToTmp_run xs ys [] acc ay
  have h4 : Runs ⟨.tmpToRight, xs, ys, acc.reverse, [], ay⟩ (acc.length + 1)
      ⟨.startAdd, xs, ys, [], [], ayacc⟩ := by
    simpa [a0, ay, ayacc, BinaryAdderMachine.haltState] using
      tmpToRight_run xs ys acc.reverse [] ay
  have h5 : Runs ⟨.startAdd, xs, ys, [], [], ayacc⟩ 1
      ⟨.adding, xs, ys, [], [], ai⟩ := rfl
  have h6 : Runs ⟨.outToTmp, xs, ys, [], [], BinaryAdderMachine.haltState r' z⟩
      (z.length + 1) ⟨.tmpToAcc, xs, ys, z.reverse, [], BinaryAdderMachine.haltState r' []⟩ := by
    simpa [BinaryAdderMachine.haltState] using
      outToTmp_run xs ys [] [] z (BinaryAdderMachine.haltState r' [])
  have h7 : Runs ⟨.tmpToAcc, xs, ys, z.reverse, [], BinaryAdderMachine.haltState r' []⟩
      (z.length + 1) ⟨.shift, xs, ys, [], z, BinaryAdderMachine.haltState r' []⟩ := by
    simpa using tmpToAcc_run xs ys z.reverse [] (BinaryAdderMachine.haltState r' [])
  have h8 : Runs ⟨.shift, xs, ys, [], z, BinaryAdderMachine.haltState r' []⟩ 1
      (ready xs (false :: ys) z r') := rfl
  have whole := ((((((((h0.trans h1).trans h2).trans h3).trans h4).trans h5).trans hsub').trans h6).trans h7).trans h8
  refine ⟨_, r', ?_, whole⟩
  have hz := BinaryArithmetic.add_length ys acc false
  change z.length ≤ max ys.length acc.length + 1 at hz
  have hm : max ys.length acc.length = ys.length := max_eq_left hlen
  rw [hm] at hn hz
  omega

/-- Value-level counterpart of the actual iterative shift/add machine. -/
def productAcc : List Bool → List Bool → List Bool → List Bool
  | [], _, acc => acc
  | b :: bs, ys, acc =>
      productAcc bs (false :: ys) (if b then (BinaryArithmetic.add ys acc false).value else acc)

theorem productAcc_correct (xs ys acc : List Bool) :
    value (productAcc xs ys acc) = value acc + value xs * value ys := by
  induction xs generalizing ys acc with
  | nil => simp [productAcc, value]
  | cons b bs ih =>
      cases b <;> simp only [productAcc, Bool.false_eq_true, ↓reduceIte, ih,
        BinaryArithmetic.add_correct, value, Bool.toNat_false, Bool.toNat_true,
        Nat.add_zero, Nat.zero_add] <;> ring

theorem run_product (xs ys acc : List Bool) (r : BinaryAdderMachine.Registers)
    (hlen : acc.length ≤ ys.length) :
    ∃ steps r' ys', steps ≤ 20 * xs.length * (xs.length + ys.length + 1) + 1 ∧
      Runs (ready xs ys acc r) steps (terminal ys' (productAcc xs ys acc) r') := by
  induction xs generalizing ys acc r with
  | nil => exact ⟨1, r, ys, by simp, rfl⟩
  | cons b bs ih =>
      cases b with
      | false =>
          have hl : acc.length ≤ (false :: ys).length := by simp; omega
          obtain ⟨steps, r', ys', hs, hr⟩ := ih (false :: ys) acc r hl
          refine ⟨2 + steps, r', ys', ?_, ?_⟩
          · simp only [List.length_cons] at *
            nlinarith
          · exact (false_iteration bs ys acc r).trans hr
      | true =>
          let z := (BinaryArithmetic.add ys acc false).value
          obtain ⟨n, rnext, hn, hr⟩ := true_iteration bs ys acc r hlen
          have hl : z.length ≤ (false :: ys).length := by
            have ha := BinaryArithmetic.add_length ys acc false
            rw [max_eq_left hlen] at ha
            exact ha
          obtain ⟨steps, r', ys', hs, ht⟩ := ih (false :: ys) z rnext hl
          refine ⟨n + steps, r', ys', ?_, ?_⟩
          · simp only [List.length_cons] at *
            nlinarith
          · exact hr.trans ht

/-- Primitive actions in the fixed eight-stack multiplier. Copy restoration
reads/pops one saved bit and pushes it to two destinations, costing seven actions.
Adder dispatch includes its finite-control branch and the adder's own actions. -/
def transitionTrace (s : State) : List BitOp :=
  match s.phase with
  | .scan =>
      match s.factor with
      | [] => [.readCell, .branch]
      | _ :: _ => [.readCell, .branch, .moveHead, .branch]
  | .yToTmp =>
      match s.shifted with
      | [] => [.readCell, .branch]
      | _ :: _ => [.readCell, .branch, .moveHead, .writeCell, .moveHead]
  | .tmpToY =>
      match s.temp with
      | [] => [.readCell, .branch]
      | _ :: _ => [.readCell, .branch, .moveHead, .writeCell, .moveHead, .writeCell, .moveHead]
  | .accToTmp =>
      match s.acc with
      | [] => [.readCell, .branch]
      | _ :: _ => [.readCell, .branch, .moveHead, .writeCell, .moveHead]
  | .tmpToRight | .tmpToAcc =>
      match s.temp with
      | [] => [.readCell, .branch]
      | _ :: _ => [.readCell, .branch, .moveHead, .writeCell, .moveHead]
  | .startAdd => [.branch]
  | .adding => if s.adder.phase = .halt then [.branch]
      else .branch :: BinaryAdderMachine.transitionTrace s.adder
  | .outToTmp =>
      match s.adder.out with
      | [] => [.readCell, .branch]
      | _ :: _ => [.readCell, .branch, .moveHead, .writeCell, .moveHead]
  | .shift => [.writeCell, .moveHead]
  | .halt => []

def bitSteps : ℕ → State → ℕ
  | 0, _ => 0
  | n + 1, s => (transitionTrace s).length + bitSteps n (step s)

theorem transition_length (s : State) : (transitionTrace s).length ≤ 7 := by
  have ha := BinaryAdderMachine.transition_length s.adder
  cases hp : s.phase <;> simp only [transitionTrace, hp] <;>
    first | (split <;> simp_all) | simp_all
  omega

theorem bitSteps_le (n : ℕ) (s : State) : bitSteps n s ≤ 7 * n := by
  induction n generalizing s with
  | zero => simp [bitSteps]
  | succ n ih =>
      have ht := transition_length s
      have hi := ih (step s)
      simp only [bitSteps]
      omega

/-- The actual fixed-stack multiplier halts, returns the product of the original
binary inputs, and uses a quadratic number of primitive bit actions. -/
theorem binary_multiplication_machine (m n : ℕ) :
    ∃ steps, let initial := ready m.bits n.bits [] { carry := false }
      (advance steps initial).phase = .halt ∧
      value (advance steps initial).acc = m * n ∧
      bitSteps steps initial ≤ 140 * m.size * (m.size + n.size + 1) + 7 := by
  obtain ⟨steps, r', ys', hs, hr⟩ :=
    run_product m.bits n.bits [] { carry := false } (by simp)
  refine ⟨steps, ?_⟩
  dsimp only
  dsimp only [Runs] at hr
  simp only [Nat.size_eq_bits_len] at hs
  refine ⟨?_, ?_, ?_⟩
  · rw [hr]
    rfl
  · rw [hr]
    simpa [terminal, value] using productAcc_correct m.bits n.bits []
  · have hb := bitSteps_le steps (ready m.bits n.bits [] { carry := false })
    nlinarith

end IdentityTesting.BinaryMultiplierMachine
