import IdentityTesting.RationalInstructionTrace
import IdentityTesting.RationalBisectionEncoding

/-! A concrete finite-register program for the existing coordinate bisection. -/
namespace IdentityTesting.RationalComputation
open RationalOperand

def rationalSequence (xs : List RationalProgram) : RationalProgram :=
  xs.foldr RationalProgram.seq .skip

def rationalAssign (dst : ℕ) (op : RationalOp) (a b : RationalOperand) : RationalProgram :=
  .instr ⟨dst, op, a, b⟩

def coordinatePolynomialProgram : RationalProgram := rationalSequence [
  rationalAssign 5 .mul (.reg 4) (.reg 4),
  rationalAssign 6 .mul (.reg 5) (.reg 4),
  rationalAssign 7 .mul (.reg 5) (.reg 5),
  rationalAssign 8 .sub (.literal 1) (.reg 7),
  rationalAssign 9 .mul (.reg 8) (.reg 8),
  rationalAssign 10 .mul (.reg 0) (.reg 6),
  rationalAssign 11 .mul (.reg 1) (.reg 9),
  rationalAssign 12 .sub (.reg 10) (.reg 11)]

def coordinateClearProgram : RationalProgram := rationalSequence [
  rationalAssign 4 .copy (.literal 0) (.literal 0),
  rationalAssign 5 .copy (.literal 0) (.literal 0),
  rationalAssign 6 .copy (.literal 0) (.literal 0),
  rationalAssign 7 .copy (.literal 0) (.literal 0),
  rationalAssign 8 .copy (.literal 0) (.literal 0),
  rationalAssign 9 .copy (.literal 0) (.literal 0),
  rationalAssign 10 .copy (.literal 0) (.literal 0),
  rationalAssign 11 .copy (.literal 0) (.literal 0),
  rationalAssign 12 .copy (.literal 0) (.literal 0)]

def coordinateStepProgram : RationalProgram := rationalSequence [
  rationalAssign 4 .add (.reg 2) (.reg 3),
  rationalAssign 4 .div (.reg 4) (.literal 2),
  coordinatePolynomialProgram,
  .branchLe (.reg 12) (.literal 0)
    (rationalAssign 2 .copy (.reg 4) (.literal 0))
    (rationalAssign 3 .copy (.reg 4) (.literal 0)),
  coordinateClearProgram]

def coordinateProgram (n : ℕ) : RationalProgram := .repeat n coordinateStepProgram

def coordinateRegisters (a β l u : ℚ) : RationalRegisters :=
  [a, β, l, u, 0, 0, 0, 0, 0, 0, 0, 0, 0]

theorem coordinateStepProgram_exec (a β l u : ℚ) :
    coordinateStepProgram.exec (coordinateRegisters a β l u) =
      let m := (l + u) / 2
      if coordinatePolynomial a β m ≤ 0 then coordinateRegisters a β m u
      else coordinateRegisters a β l m := by
  simp [coordinateStepProgram, coordinatePolynomialProgram, coordinateClearProgram,
    rationalSequence, rationalAssign, coordinateRegisters, RationalProgram.exec,
    RationalInstruction.exec, RationalInstruction.call, RationalOperand.read,
    RationalCall.result, RationalOp.eval, coordinatePolynomial, pow_succ, mul_assoc]
  split <;> simp_all

theorem registerIterate_succ_right (f : RationalRegisters → RationalRegisters)
    (n : ℕ) (s : RationalRegisters) :
    registerIterate f (n + 1) s = f (registerIterate f n s) := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih => simpa only [registerIterate] using ih (f s)

theorem coordinateProgram_exec (a β : ℚ) (n : ℕ) :
    (coordinateProgram n).exec (coordinateRegisters a β 0 1) =
      coordinateRegisters a β (coordinateInterval a β n).1 (coordinateInterval a β n).2 := by
  change registerIterate coordinateStepProgram.exec n _ = _
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [registerIterate_succ_right, ih, coordinateStepProgram_exec, coordinateInterval_step]
    simp only [coordinateQuery]
    split <;> rfl

theorem coordinateProgram_result (a β : ℚ) (n : ℕ) :
    ((coordinateProgram n).run (coordinateRegisters a β 0 1)).1 =
      coordinateRegisters a β (coordinateInterval a β n).1 (coordinateInterval a β n).2 := by
  rw [RationalProgram.run_result, coordinateProgram_exec]

theorem coordinateStepProgram_callBound : coordinateStepProgram.callBound = 21 := by rfl

theorem coordinateProgram_calls (a β : ℚ) (n : ℕ) :
    ((coordinateProgram n).run (coordinateRegisters a β 0 1)).2.length ≤ 21 * n := by
  simpa only [coordinateProgram, RationalProgram.callBound,
    coordinateStepProgram_callBound, Nat.mul_comm] using
    (coordinateProgram n).run_length (coordinateRegisters a β 0 1)

theorem coordinateProgram_slots (n : ℕ) : (coordinateProgram n).slots = 13 := by rfl

end IdentityTesting.RationalComputation
