import IdentityTesting.RationalDynamicRepeat
import IdentityTesting.RationalAlgorithmTraceSearchStorage

/-! The search skeleton obtains both precision and fuel from registers. -/
namespace IdentityTesting.RationalComputation

set_option maxHeartbeats 1600000

theorem RationalProgram.replaceCounts_shift (p : RationalProgram) (n d : ℕ) :
    (p.shift d).replaceCounts n = (p.replaceCounts n).shift d := by
  induction p <;> simp_all [replaceCounts, shift]

theorem rationalSequence_replaceCounts (ps : List RationalProgram) (n : ℕ) :
    (rationalSequence ps).replaceCounts n = rationalSequence (ps.map (RationalProgram.replaceCounts n)) := by
  induction ps with
  | nil => rfl
  | cons p ps ih => simpa only [rationalSequence, List.foldr_cons, List.map_cons,
      RationalProgram.replaceCounts] using congrArg (RationalProgram.seq (p.replaceCounts n)) ih

theorem oracleAtomProgram_replaceCounts (objective : Bool) (n m i : ℕ) :
    (oracleAtomProgram objective n i).replaceCounts m = oracleAtomProgram objective m i := by
  cases objective <;> rfl

theorem oracleVectorProgram_replaceCounts (objective : Bool) (k n m : ℕ) :
    (oracleVectorProgram objective k n).replaceCounts m = oracleVectorProgram objective k m := by
  simp only [oracleVectorProgram, rationalSequence_replaceCounts, List.map_map,
    Function.comp_def, oracleAtomProgram_replaceCounts]

theorem oracleEvaluateProgram_replaceCounts (objective : Bool) (k n m j : ℕ) :
    (oracleEvaluateProgram objective k n j).replaceCounts m = oracleEvaluateProgram objective k m j := by
  have hc : oracleEvaluateCleanup.replaceCounts m = oracleEvaluateCleanup := rfl
  simp only [oracleEvaluateProgram, rationalSequence, List.foldr_cons, List.foldr_nil,
    RationalProgram.replaceCounts, RationalProgram.replaceCounts_shift,
    oracleVectorProgram_replaceCounts, hc, rationalAssign]

theorem oracleSearchStepProgram_replaceCounts (k n m : ℕ) :
    (oracleSearchStepProgram k n).replaceCounts m = oracleSearchStepProgram k m := by
  simp only [oracleSearchStepProgram, oracleNarrowProgram, oracleAmbiguousProgram,
    rationalSequence, List.foldr_cons, List.foldr_nil, rationalAssign,
    RationalProgram.replaceCounts, oracleEvaluateProgram_replaceCounts]

theorem oracleSearchFinishProgram_replaceCounts (k n m : ℕ) :
    (oracleSearchFinishProgram k n).replaceCounts m = oracleSearchFinishProgram k m := by
  simp only [oracleSearchFinishProgram, oracleNarrowProgram,
    rationalSequence, List.foldr_cons, List.foldr_nil, rationalAssign,
    RationalProgram.replaceCounts, oracleEvaluateProgram_replaceCounts]

private theorem branch_slots (a b : RationalOperand) (p q : RationalProgram) (B : ℕ)
    (ha : a.slots ≤ B) (hb : b.slots ≤ B) (hp : p.slots ≤ B) (hq : q.slots ≤ B) :
    (RationalProgram.branchLe a b p q).slots ≤ B := max_le (max_le ha hb) (max_le hp hq)

theorem oracleNarrowProgram_slots (k n : ℕ) : (oracleNarrowProgram k n).slots ≤ 25 + k := by
  apply rationalSequence_slots_le
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl
  · exact oracleEvaluateProgram_slots true k n 0 (by decide)
  · change 8 ≤ 25 + k; omega
  · exact oracleEvaluateProgram_slots true k n 1 (by decide)
  · change 8 ≤ 25 + k; omega
  · change 7 ≤ 25 + k; omega

theorem oracleAmbiguousProgram_slots (k n : ℕ) : (oracleAmbiguousProgram k n).slots ≤ 25 + k := by
  apply rationalSequence_slots_le
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl
  · exact oracleEvaluateProgram_slots true k n 7 (by decide)
  · change 5 ≤ 25 + k; omega
  · change 6 ≤ 25 + k; omega
  · change 7 ≤ 25 + k; omega

theorem oracleSearchStepProgram_slots (k n : ℕ) : (oracleSearchStepProgram k n).slots ≤ 25 + k := by
  apply branch_slots
  · change 7 ≤ 25 + k; omega
  · exact Nat.zero_le _
  · apply rationalSequence_slots_le
    intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl
    · change 5 ≤ 25 + k; omega
    · change 6 ≤ 25 + k; omega
    · apply branch_slots
      · change 5 ≤ 25 + k; omega
      · change 6 ≤ 25 + k; omega
      · exact oracleNarrowProgram_slots k n
      · apply rationalSequence_slots_le
        intro p hp
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with rfl | rfl | rfl | rfl
        · change 8 ≤ 25 + k; omega
        · change 8 ≤ 25 + k; omega
        · exact oracleEvaluateProgram_slots false k n 7 (by decide)
        · apply branch_slots
          · exact Nat.zero_le _
          · change 6 ≤ 25 + k; omega
          · apply branch_slots
            · change 5 ≤ 25 + k; omega
            · exact Nat.zero_le _
            · exact oracleAmbiguousProgram_slots k n
            · change 8 ≤ 25 + k; omega
          · change 8 ≤ 25 + k; omega
  · exact Nat.zero_le _

theorem oracleSearchFinishProgram_slots (k n : ℕ) : (oracleSearchFinishProgram k n).slots ≤ 25 + k := by
  apply branch_slots
  · change 7 ≤ 25 + k; omega
  · exact Nat.zero_le _
  · exact oracleNarrowProgram_slots k n
  · exact Nat.zero_le _

def oracleDynamicSearchProgram (k precisionSlot fuelSlot : ℕ) : RationalControlProgram :=
  .seq (.repeatRegister fuelSlot ((oracleSearchStepProgram k 0).dynamicRepeats precisionSlot))
    ((oracleSearchFinishProgram k 0).dynamicRepeats precisionSlot)

theorem oracleDynamicSearchProgram_result (k n fuel precisionSlot fuelSlot : ℕ)
    (s : RationalRegisters) (hp : 25 + k ≤ precisionSlot)
    (hn : (RationalOperand.reg precisionSlot).read s = (n : ℚ))
    (hf : (RationalOperand.reg fuelSlot).read s = (fuel : ℚ)) :
    ((oracleDynamicSearchProgram k precisionSlot fuelSlot).run s).1 =
      (oracleSearchProgram k n fuel).exec s := by
  have hstep (t : RationalRegisters) (ht : (RationalOperand.reg precisionSlot).read t = (n : ℚ)) :
      ((oracleSearchStepProgram k 0).dynamicRepeats precisionSlot).exec t =
        (oracleSearchStepProgram k n).exec t := by
    rw [RationalProgram.dynamicRepeats_exec _ _ n t ((oracleSearchStepProgram_slots k 0).trans hp) ht,
      oracleSearchStepProgram_replaceCounts]
  have hpreserve (t : RationalRegisters) :
      (RationalOperand.reg precisionSlot).read ((oracleSearchStepProgram k n).exec t) =
        (RationalOperand.reg precisionSlot).read t :=
    (oracleSearchStepProgram k n).read_frame t precisionSlot ((oracleSearchStepProgram_slots k n).trans hp)
  have hiter (r : ℕ) : ∀ t, (RationalOperand.reg precisionSlot).read t = (n : ℚ) →
      registerIterate ((oracleSearchStepProgram k 0).dynamicRepeats precisionSlot).exec r t =
        registerIterate (oracleSearchStepProgram k n).exec r t := by
    induction r with
    | zero => intro t ht; rfl
    | succ r ih =>
      intro t ht
      simp only [registerIterate, hstep t ht]
      exact ih _ ((hpreserve t).trans ht)
  rw [RationalControlProgram.run_result]
  simp only [oracleDynamicSearchProgram, RationalControlProgram.exec, hf, Nat.floor_natCast,
    hiter fuel s hn]
  have hcount : (RationalOperand.reg precisionSlot).read
      (registerIterate (oracleSearchStepProgram k n).exec fuel s) = (n : ℚ) := by
    have h := (RationalProgram.repeat fuel (oracleSearchStepProgram k n)).read_frame s precisionSlot
      ((oracleSearchStepProgram_slots k n).trans hp)
    exact h.trans hn
  rw [RationalProgram.dynamicRepeats_exec _ _ n _
    ((oracleSearchFinishProgram_slots k 0).trans hp) hcount,
    oracleSearchFinishProgram_replaceCounts]
  rfl

end IdentityTesting.RationalComputation
