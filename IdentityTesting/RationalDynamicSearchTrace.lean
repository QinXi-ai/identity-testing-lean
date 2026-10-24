import IdentityTesting.RationalDynamicSearch
import IdentityTesting.RationalDynamicTrace

/-! The arithmetic projection of the runtime-controlled search is exactly the
previously bounded search trace. Control events remain in the complete trace. -/
namespace IdentityTesting.RationalComputation

set_option maxHeartbeats 1600000

theorem oracleDynamicSearchProgram_calls (k n fuel precisionSlot fuelSlot : ℕ)
    (s : RationalRegisters) (hp : 25 + k ≤ precisionSlot)
    (hn : (RationalOperand.reg precisionSlot).read s = (n : ℚ))
    (hf : (RationalOperand.reg fuelSlot).read s = (fuel : ℚ)) :
    arithmeticCalls ((oracleDynamicSearchProgram k precisionSlot fuelSlot).run s).2 =
      ((oracleSearchProgram k n fuel).run s).2 := by
  let step := oracleSearchStepProgram k n
  let dynamic := (oracleSearchStepProgram k 0).dynamicRepeats precisionSlot
  have hres (t : RationalRegisters) (ht : (RationalOperand.reg precisionSlot).read t = (n : ℚ)) :
      (dynamic.run t).1 = (step.run t).1 := by
    rw [RationalProgram.run_result]
    exact ((oracleSearchStepProgram k 0).dynamicRepeats_result precisionSlot n t
      ((oracleSearchStepProgram_slots k 0).trans hp) ht).trans
      (congrArg (fun p : RationalProgram => p.exec t) (oracleSearchStepProgram_replaceCounts k 0 n))
  have hcall (t : RationalRegisters) (ht : (RationalOperand.reg precisionSlot).read t = (n : ℚ)) :
      arithmeticCalls (dynamic.run t).2 = (step.run t).2 := by
    rw [RationalProgram.dynamicRepeats_calls _ _ n t
      ((oracleSearchStepProgram_slots k 0).trans hp) ht, oracleSearchStepProgram_replaceCounts]
  have hpres (t : RationalRegisters) (ht : (RationalOperand.reg precisionSlot).read t = (n : ℚ)) :
      (RationalOperand.reg precisionSlot).read (step.run t).1 = (n : ℚ) := by
    rw [RationalProgram.run_result, RationalProgram.read_frame _ _ _
      ((oracleSearchStepProgram_slots k n).trans hp)]
    exact ht
  have hi := controlIterate_arithmeticCalls dynamic.run step.run
    (fun t => (RationalOperand.reg precisionSlot).read t = (n : ℚ)) hres hcall hpres fuel s hn
  have hir : (controlIterate dynamic.run fuel s).1 = (traceIterate step.run fuel s).1 := by
    clear hf hi
    induction fuel generalizing s with
    | zero => rfl
    | succ fuel ih =>
      simp only [controlIterate, traceIterate]
      rw [hres s hn]
      exact ih (step.run s).1 (hpres s hn)
  have hcount : (RationalOperand.reg precisionSlot).read (traceIterate step.run fuel s).1 = (n : ℚ) := by
    change (RationalOperand.reg precisionSlot).read ((RationalProgram.repeat fuel step).run s).1 = _
    rw [RationalProgram.run_result]
    exact ((RationalProgram.repeat fuel step).read_frame s precisionSlot
      ((oracleSearchStepProgram_slots k n).trans hp)).trans hn
  simp only [oracleDynamicSearchProgram, RationalControlProgram.run, hf, Nat.floor_natCast,
    oracleSearchProgram, RationalProgram.run, arithmeticCalls_append, arithmeticCalls,
    List.filterMap_cons, List.filterMap_append, RationalControlEvent.arithmeticCall]
  change arithmeticCalls (controlIterate dynamic.run fuel s).2 ++
      arithmeticCalls (((oracleSearchFinishProgram k 0).dynamicRepeats precisionSlot).run
        (controlIterate dynamic.run fuel s).1).2 = _
  rw [hi, hir, RationalProgram.dynamicRepeats_calls _ _ n _
    ((oracleSearchFinishProgram_slots k 0).trans hp) hcount,
    oracleSearchFinishProgram_replaceCounts]

end IdentityTesting.RationalComputation
