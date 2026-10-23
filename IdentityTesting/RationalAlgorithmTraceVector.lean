import IdentityTesting.RationalAlgorithmTraceOracle

/-! Explicit register reads from the input vector and finite oracle programs. -/
namespace IdentityTesting.RationalComputation
open scoped BigOperators

def oracleLoadAtomProgram (i : ℕ) : RationalProgram := rationalSequence [
  rationalAssign 0 .copy (.reg (17 + i)) (.literal 0),
  rationalAssign 2 .copy (.literal 0) (.literal 0),
  rationalAssign 3 .copy (.literal 1) (.literal 0)]

theorem oracleLoadAtomProgram_exec {k : ℕ} (a : Fin k → ℚ) (i : Fin k)
    (z β l u t ρ sl su : ℚ) :
    (oracleLoadAtomProgram i).exec (oracleRegisters z β l u t ρ sl su ++ List.ofFn a) =
      oracleRegisters (a i) β 0 1 t ρ sl su ++ List.ofFn a := by
  have hr : (RationalOperand.reg (17 + i.val)).read
      (oracleRegisters z β l u t ρ sl su ++ List.ofFn a) = a i := by
    change ((oracleRegisters z β l u t ρ sl su ++ List.ofFn a)[17 + i.val]?).getD 0 = a i
    rw [List.getElem?_append_right (by simp [oracleRegisters, coordinateRegisters])]
    simp [oracleRegisters, coordinateRegisters, List.getElem?_ofFn, i.isLt]
  simp only [oracleLoadAtomProgram, rationalSequence, List.foldr_cons, List.foldr_nil,
    rationalAssign, RationalProgram.exec, RationalInstruction.exec,
    RationalInstruction.call, RationalCall.result, RationalOp.eval]
  rw [hr]
  simp [RationalOperand.read, oracleRegisters, coordinateRegisters]

def oracleAtomProgram (objective : Bool) (n i : ℕ) : RationalProgram :=
  .seq (oracleLoadAtomProgram i) (oracleTermProgram objective n)

theorem oracleAtomProgram_exec {k : ℕ} (objective : Bool) (n : ℕ)
    (a : Fin k → ℚ) (i : Fin k) (z β l u t ρ sl su : ℚ) :
    (oracleAtomProgram objective n i).exec
      (oracleRegisters z β l u t ρ sl su ++ List.ofFn a) =
        oracleRegisters (a i) β (oracleCoordinateInterval (a i) β ρ n).1
          (oracleCoordinateInterval (a i) β ρ n).2 t ρ
          (sl + oracleTermValue objective false (a i) t β ρ n)
          (su + oracleTermValue objective true (a i) t β ρ n) ++ List.ofFn a := by
  change (oracleTermProgram objective n).exec
    ((oracleLoadAtomProgram i).exec _) = _
  rw [oracleLoadAtomProgram_exec]
  have h := congrArg Prod.fst ((oracleTermProgram objective n).run_append
    (oracleRegisters (a i) β 0 1 t ρ sl su) (List.ofFn a)
    (by rw [oracleTermProgram_slots]; rfl))
  simpa only [RationalProgram.run_result, oracleTermProgram_exec] using h

def oracleVectorProgram (objective : Bool) (k n : ℕ) : RationalProgram :=
  rationalSequence ((List.finRange k).map (fun (i : Fin k) => oracleAtomProgram objective n i))

theorem oracleAtomProgram_callBound (objective : Bool) (n i : ℕ) :
    (oracleAtomProgram objective n i).callBound =
      21 * n + if objective then 13 else 45 := by
  simp only [oracleAtomProgram, RationalProgram.callBound, oracleTermProgram_callBound]
  have h : (oracleLoadAtomProgram i).callBound = 3 := rfl
  rw [h]
  cases objective <;> simp <;> nlinarith

theorem rationalSequence_callBound (xs : List RationalProgram) :
    (rationalSequence xs).callBound = (xs.map RationalProgram.callBound).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [rationalSequence, List.foldr_cons,
      RationalProgram.callBound, List.map_cons, List.sum_cons] at *; rw [ih]

theorem oracleVectorProgram_calls (objective : Bool) (k n : ℕ) (s : RationalRegisters) :
    ((oracleVectorProgram objective k n).run s).2.length ≤ k * (21 * n + 45) := by
  apply (RationalProgram.run_length _ _).trans
  rw [oracleVectorProgram, rationalSequence_callBound, List.map_map]
  simp only [Function.comp_def, oracleAtomProgram_callBound]
  cases objective <;> simp <;> nlinarith

end IdentityTesting.RationalComputation
