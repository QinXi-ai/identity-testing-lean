import IdentityTesting.RationalAlgorithmTraceEvaluation
import IdentityTesting.RationalOracleSearch

/-! The bounded-loop control state for the actual interval search. -/
namespace IdentityTesting.RationalComputation

structure OracleSearchControl where
  lower : ℚ
  upper : ℚ
  outLower : ℚ
  outUpper : ℚ
  middle : ℚ
  done : Bool
  deriving Repr

def OracleSearchControl.output (s : OracleSearchControl) : ℚ × ℚ := (s.outLower, s.outUpper)

def OracleSearchControl.finish (objective : ℚ → ℚ × ℚ) (s : OracleSearchControl) :
    OracleSearchControl :=
  if s.done then s else
    {s with outLower := (objective s.lower).1, outUpper := (objective s.upper).2, middle := (objective s.lower).1, done := true}

def OracleSearchControl.step (budget objective : ℚ → ℚ × ℚ) (ζ margin : ℚ)
    (s : OracleSearchControl) : OracleSearchControl :=
  if s.done then s else
  if s.upper - s.lower ≤ ζ * s.lower then s.finish objective else
  let m := (s.lower + s.upper) / 2
  let Q := budget m
  if Q.2 < 1 then {s with lower := m, middle := m, outLower := Q.1, outUpper := Q.2} else
  if 1 < Q.1 then {s with upper := m, middle := m, outLower := Q.1, outUpper := Q.2} else
  {s with middle := m, outLower := (objective m).1 - margin, outUpper := (objective m).2 + margin, done := true}

def OracleSearchControl.loop (budget objective : ℚ → ℚ × ℚ) (ζ margin : ℚ) :
    ℕ → OracleSearchControl → OracleSearchControl
  | 0, s => s
  | n + 1, s => loop budget objective ζ margin n (s.step budget objective ζ margin)

theorem OracleSearchControl.loop_done (budget objective : ℚ → ℚ × ℚ) (ζ margin : ℚ)
    (n : ℕ) (s : OracleSearchControl) (hs : s.done = true) :
    loop budget objective ζ margin n s = s := by
  induction n with
  | zero => rfl
  | succ n ih => simpa only [loop, step, hs, if_true] using ih

theorem OracleSearchControl.loop_correct (budget objective : ℚ → ℚ × ℚ) (ζ margin : ℚ)
    (n : ℕ) (s : OracleSearchControl) :
    ((loop budget objective ζ margin n s).finish objective).output =
      if s.done then s.output else oracleSearch budget objective ζ margin n s.lower s.upper := by
  induction n generalizing s with
  | zero => cases hs : s.done <;> simp [loop, finish, hs, output, oracleSearch]
  | succ n ih =>
    by_cases hd : s.done = true
    · rw [loop_done _ _ _ _ _ _ hd]
      simp [finish, hd]
    · have hf : s.done = false := Bool.eq_false_iff.mpr hd
      rw [loop, ih]
      simp only [step, finish, hf, Bool.false_eq_true, if_false, oracleSearch]
      split_ifs <;> simp_all [output]

def oracleNarrowProgram (k n : ℕ) : RationalProgram := rationalSequence [
  oracleEvaluateProgram true k n 0,
  rationalAssign 7 .copy (.reg 4) (.literal 0),
  oracleEvaluateProgram true k n 1,
  rationalAssign 4 .copy (.reg 7) (.literal 0),
  rationalAssign 6 .copy (.literal 1) (.literal 0)]

def oracleAmbiguousProgram (k n : ℕ) : RationalProgram := rationalSequence [
  oracleEvaluateProgram true k n 7,
  rationalAssign 4 .sub (.reg 4) (.reg 3),
  rationalAssign 5 .add (.reg 5) (.reg 3),
  rationalAssign 6 .copy (.literal 1) (.literal 0)]

def oracleSearchStepProgram (k n : ℕ) : RationalProgram :=
  .branchLe (.reg 6) (.literal 0)
    (rationalSequence [
      rationalAssign 4 .sub (.reg 1) (.reg 0),
      rationalAssign 5 .mul (.reg 2) (.reg 0),
      .branchLe (.reg 4) (.reg 5) (oracleNarrowProgram k n)
        (rationalSequence [
          rationalAssign 7 .add (.reg 0) (.reg 1),
          rationalAssign 7 .div (.reg 7) (.literal 2),
          oracleEvaluateProgram false k n 7,
          .branchLe (.literal 1) (.reg 5)
            (.branchLe (.reg 4) (.literal 1) (oracleAmbiguousProgram k n)
              (rationalAssign 1 .copy (.reg 7) (.literal 0)))
            (rationalAssign 0 .copy (.reg 7) (.literal 0))])]) .skip

def oracleSearchFinishProgram (k n : ℕ) : RationalProgram :=
  .branchLe (.reg 6) (.literal 0) (oracleNarrowProgram k n) .skip

def oracleSearchProgram (k n fuel : ℕ) : RationalProgram :=
  .seq (.repeat fuel (oracleSearchStepProgram k n)) (oracleSearchFinishProgram k n)

def OracleSearchControl.registers {k : ℕ} (s : OracleSearchControl)
    (a : Fin k → ℚ) (t ρ ζ margin : ℚ) : RationalRegisters :=
  oracleMachineState a t ρ s.lower s.upper ζ margin s.outLower s.outUpper
    (if s.done then 1 else 0) s.middle

end IdentityTesting.RationalComputation
