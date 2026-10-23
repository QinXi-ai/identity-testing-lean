import IdentityTesting.RationalAlgorithmTraceVectorResult
import IdentityTesting.RationalAlgorithmTraceCoordinateBounds

/-! Polynomial size of the actual vector program's encoded instruction syntax. -/
namespace IdentityTesting.RationalComputation

private theorem smallProgram_encoding (upper : Bool) :
    (budgetAccumulatorProgram upper).encoding ≤ 10000 ∧
      (objectiveAccumulatorProgram upper).encoding ≤ 10000 ∧
      coordinateClipProgram.encoding ≤ 10000 := by
  have hs (j : ℕ) (hj : j ≤ 16) : j.size ≤ 5 := Nat.size_le.mpr (by omega)
  have hs2 := hs 2 (by decide)
  have hs3 := hs 3 (by decide)
  have hs4 := hs 4 (by decide)
  have hs5 := hs 5 (by decide)
  have hs6 := hs 6 (by decide)
  have hs7 := hs 7 (by decide)
  have hs8 := hs 8 (by decide)
  have hs9 := hs 9 (by decide)
  have hs10 := hs 10 (by decide)
  have hs11 := hs 11 (by decide)
  have hs12 := hs 12 (by decide)
  have hs13 := hs 13 (by decide)
  have hs14 := hs 14 (by decide)
  have hs15 := hs 15 (by decide)
  have hs16 := hs 16 (by decide)
  cases upper <;>
    simp [budgetAccumulatorProgram, allocationCostProgram, objectiveAccumulatorProgram,
      coordinateClipProgram, coordinateClearProgram, rationalSequence, rationalAssign,
      RationalProgram.encoding, RationalOperand.encoding, rationalEncodingLength,
      numeratorBits, denominatorBits] <;> omega

theorem oracleTermProgram_encoding (objective : Bool) (n : ℕ) :
    (oracleTermProgram objective n).encoding ≤ n.size + 30505 := by
  have hc := coordinateProgram_encoding n
  have hf := smallProgram_encoding false
  have ht := smallProgram_encoding true
  cases objective <;>
    simp only [oracleTermProgram, rationalSequence, List.foldr_cons, List.foldr_nil,
      oracleCoordinateProgram, RationalProgram.encoding, Bool.false_eq_true, if_false, if_true] <;>
    omega

theorem oracleLoadAtomProgram_encoding (i : ℕ) :
    (oracleLoadAtomProgram i).encoding ≤ i + 100 := by
  have hi : (17 + i).size ≤ 17 + i := Nat.size_le.mpr (17 + i).lt_two_pow_self
  have h2 : Nat.size 2 ≤ 3 := Nat.size_le.mpr (by decide)
  have h3 : Nat.size 3 ≤ 3 := Nat.size_le.mpr (by decide)
  simp [oracleLoadAtomProgram, rationalSequence, rationalAssign, RationalProgram.encoding,
    RationalOperand.encoding, rationalEncodingLength, numeratorBits, denominatorBits]
  omega

theorem oracleAtomProgram_encoding (objective : Bool) (n i : ℕ) :
    (oracleAtomProgram objective n i).encoding ≤ n.size + i + 40000 := by
  have ht := oracleTermProgram_encoding objective n
  have hl := oracleLoadAtomProgram_encoding i
  simp only [oracleAtomProgram, RationalProgram.encoding]
  omega

theorem rationalSequence_encoding_le (xs : List RationalProgram) (B : ℕ)
    (h : ∀ p ∈ xs, p.encoding ≤ B) :
    (rationalSequence xs).encoding ≤ xs.length * (B + 1) + 1 := by
  induction xs with
  | nil => simp [rationalSequence, RationalProgram.encoding]
  | cons p ps ih =>
    have hp := h p (by simp)
    have ht := ih (fun q hq => h q (by simp [hq]))
    change 1 + p.encoding + (rationalSequence ps).encoding ≤ (ps.length + 1) * (B + 1) + 1
    nlinarith

theorem oracleVectorProgram_encoding (objective : Bool) (k n : ℕ) :
    (oracleVectorProgram objective k n).encoding ≤ k * (n + k + 40001) + 1 := by
  have hn : n.size ≤ n := Nat.size_le.mpr n.lt_two_pow_self
  have h := rationalSequence_encoding_le
    ((List.finRange k).map (fun (i : Fin k) => oracleAtomProgram objective n i))
    (n + k + 40000) (by
      intro p hp
      obtain ⟨i, _, rfl⟩ := List.mem_map.mp hp
      have hi := oracleAtomProgram_encoding objective n i
      have hj := i.isLt
      omega)
  simpa only [List.length_map, List.length_finRange, Nat.add_assoc] using h

end IdentityTesting.RationalComputation
