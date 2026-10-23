import IdentityTesting.RationalAlgorithmTraceSearchResult

/-! Polynomial counts for the actual bounded-loop oracle program. -/
namespace IdentityTesting.RationalComputation

theorem oracleNarrowProgram_callBound (k n : ℕ) :
    (oracleNarrowProgram k n).callBound ≤ 2 * (k * (21 * n + 45)) + 21 := by
  have h0 := oracleEvaluateProgram_callBound true k n 0
  have h1 := oracleEvaluateProgram_callBound true k n 1
  simp only [oracleNarrowProgram, rationalSequence, List.foldr_cons, List.foldr_nil,
    RationalProgram.callBound, rationalAssign]
  change _ + (1 + (_ + (1 + (1 + 0)))) ≤ _
  omega

theorem oracleAmbiguousProgram_callBound (k n : ℕ) :
    (oracleAmbiguousProgram k n).callBound ≤ k * (21 * n + 45) + 12 := by
  have h := oracleEvaluateProgram_callBound true k n 7
  simp only [oracleAmbiguousProgram, rationalSequence, List.foldr_cons, List.foldr_nil,
    RationalProgram.callBound, rationalAssign]
  change _ + (1 + (1 + (1 + 0))) ≤ _
  omega

theorem oracleSearchStepProgram_callBound (k n : ℕ) :
    (oracleSearchStepProgram k n).callBound ≤ 2 * (k * (21 * n + 45)) + 30 := by
  have hn := oracleNarrowProgram_callBound k n
  have ha := oracleAmbiguousProgram_callBound k n
  have he := oracleEvaluateProgram_callBound false k n 7
  simp only [oracleSearchStepProgram, rationalSequence, List.foldr_cons, List.foldr_nil,
    rationalAssign, RationalProgram.callBound]
  omega

theorem oracleSearchFinishProgram_callBound (k n : ℕ) :
    (oracleSearchFinishProgram k n).callBound ≤ 2 * (k * (21 * n + 45)) + 22 := by
  have h := oracleNarrowProgram_callBound k n
  simp only [oracleSearchFinishProgram, RationalProgram.callBound]
  omega

theorem oracleSearchProgram_calls (k n fuel : ℕ) (s : RationalRegisters) :
    ((oracleSearchProgram k n fuel).run s).2.length ≤
      (fuel + 1) * (2 * (k * (21 * n + 45)) + 30) := by
  apply (RationalProgram.run_length _ _).trans
  have hs := oracleSearchStepProgram_callBound k n
  have hf := oracleSearchFinishProgram_callBound k n
  have hm := Nat.mul_le_mul_left fuel hs
  simp only [oracleSearchProgram, RationalProgram.callBound]
  nlinarith

end IdentityTesting.RationalComputation
