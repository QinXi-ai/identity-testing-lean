import IdentityTesting.RationalAlgorithmTraceSearchExec

/-! Exact execution of the bounded register loop agrees with oracleSearch. -/
namespace IdentityTesting.RationalComputation

theorem oracleSearchLoop_exec {k : ℕ} (n fuel : ℕ) (a : Fin k → ℚ)
    (t ρ ζ margin : ℚ) (s : OracleSearchControl) :
    registerIterate (oracleSearchStepProgram k n).exec fuel (s.registers a t ρ ζ margin) =
      (OracleSearchControl.loop (fun β => oracleBudgetInterval a t β ρ n)
        (fun β => oracleObjectiveInterval a β ρ n) ζ margin fuel s).registers a t ρ ζ margin := by
  induction fuel generalizing s with
  | zero => rfl
  | succ fuel ih =>
    simp only [registerIterate, oracleSearchStepProgram_exec, OracleSearchControl.loop, ih]

def oracleSearchProgramOutput (s : RationalRegisters) : ℚ × ℚ :=
  ((RationalOperand.reg 4).read s, (RationalOperand.reg 5).read s)

theorem oracleSearchProgram_result {k : ℕ} (n fuel : ℕ) (a : Fin k → ℚ)
    (t ρ ζ margin l u : ℚ) :
    oracleSearchProgramOutput ((oracleSearchProgram k n fuel).run
      (oracleMachineState a t ρ l u ζ margin 0 0 0 0)).1 =
      oracleSearch (fun β => oracleBudgetInterval a t β ρ n)
        (fun β => oracleObjectiveInterval a β ρ n) ζ margin fuel l u := by
  let s : OracleSearchControl := ⟨l, u, 0, 0, 0, false⟩
  have hs : oracleMachineState a t ρ l u ζ margin 0 0 0 0 = s.registers a t ρ ζ margin := rfl
  rw [RationalProgram.run_result, hs]
  simp only [oracleSearchProgram, RationalProgram.exec, oracleSearchLoop_exec,
    oracleSearchFinishProgram_exec]
  change (OracleSearchControl.finish _ (OracleSearchControl.loop _ _ _ _ _ s)).output = _
  simpa only [s, Bool.false_eq_true, if_false] using
    OracleSearchControl.loop_correct (fun β => oracleBudgetInterval a t β ρ n)
      (fun β => oracleObjectiveInterval a β ρ n) ζ margin fuel s

end IdentityTesting.RationalComputation
