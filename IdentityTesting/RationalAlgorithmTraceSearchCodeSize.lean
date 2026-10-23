import IdentityTesting.RationalAlgorithmTraceCodeSize
import IdentityTesting.RationalAlgorithmTraceSearchControl

/-! Encoding size of the entire search syntax, including relocated evaluators.
This bound does not by itself charge construction or decoding of that syntax. -/
namespace IdentityTesting.RationalComputation

theorem RationalOperand.shift_encoding_le (o : RationalOperand) (d : ℕ) :
    (o.shift d).encoding ≤ (d + 2) * o.encoding := by
  cases o with
  | literal q => simp only [shift, encoding]; nlinarith
  | reg i =>
    have hs := nat_size_add_le d i
    have hd : d.size ≤ d := Nat.size_le.mpr d.lt_two_pow_self
    simp only [shift, encoding]
    have h : (d + i).size ≤ d + i.size + 1 := by omega
    nlinarith

theorem RationalProgram.shift_encoding_le (p : RationalProgram) (d : ℕ) :
    (p.shift d).encoding ≤ (3 * d + 4) * p.encoding := by
  induction p with
  | skip => simp only [shift, encoding]; omega
  | instr i =>
    have hl := i.lhs.shift_encoding_le d
    have hr := i.rhs.shift_encoding_le d
    have hs := nat_size_add_le d i.dst
    have hd : d.size ≤ d := Nat.size_le.mpr d.lt_two_pow_self
    have h : (d + i.dst).size ≤ d + i.dst.size + 1 := by omega
    simp only [shift, encoding, RationalInstruction.shift]
    nlinarith
  | seq p q hp hq => simp only [shift, encoding]; nlinarith
  | branchLe a b p q hp hq =>
    have ha := a.shift_encoding_le d
    have hb := b.shift_encoding_le d
    simp only [shift, encoding]
    nlinarith
  | «repeat» n p hp => simp only [shift, encoding]; nlinarith

theorem oracleEvaluateProgram_encoding (objective : Bool) (k n betaIndex : ℕ)
    (hb : betaIndex < 8) :
    (oracleEvaluateProgram objective k n betaIndex).encoding ≤
      28 * (k * (n + k + 40001) + 1) + 1000 := by
  have hv := (oracleVectorProgram objective k n).shift_encoding_le 8
  have hvec := oracleVectorProgram_encoding objective k n
  have hi : betaIndex.size ≤ 3 := Nat.size_le.mpr (by omega)
  have hs (j : ℕ) (hj : j ≤ 24) : j.size ≤ 5 := Nat.size_le.mpr (by omega)
  have h4 := hs 4 (by decide)
  have h5 := hs 5 (by decide)
  have h8 := hs 8 (by decide)
  have h9 := hs 9 (by decide)
  have h10 := hs 10 (by decide)
  have h11 := hs 11 (by decide)
  have h23 := hs 23 (by decide)
  have h24 := hs 24 (by decide)
  simp only [oracleEvaluateProgram, oracleEvaluateCleanup, rationalSequence,
    List.foldr_cons, List.foldr_nil, rationalAssign, RationalProgram.encoding,
    RationalOperand.encoding]
  norm_num [rationalEncodingLength, numeratorBits, denominatorBits] at *
  omega

theorem oracleSearchProgram_encoding (k n fuel : ℕ) :
    (oracleSearchProgram k n fuel).encoding ≤
      200 * (k * (n + k + 40001) + 1) + fuel + 10000 := by
  have h0 := oracleEvaluateProgram_encoding true k n 0 (by decide)
  have h1 := oracleEvaluateProgram_encoding true k n 1 (by decide)
  have ht7 := oracleEvaluateProgram_encoding true k n 7 (by decide)
  have hf7 := oracleEvaluateProgram_encoding false k n 7 (by decide)
  have hsize : fuel.size ≤ fuel := Nat.size_le.mpr fuel.lt_two_pow_self
  have hs (j : ℕ) (hj : j ≤ 7) : j.size ≤ 3 := Nat.size_le.mpr (by omega)
  have h2 := hs 2 (by decide)
  have h3 := hs 3 (by decide)
  have h4 := hs 4 (by decide)
  have h5 := hs 5 (by decide)
  have h6 := hs 6 (by decide)
  have h7 := hs 7 (by decide)
  simp only [oracleSearchProgram, oracleSearchStepProgram, oracleSearchFinishProgram,
    oracleNarrowProgram, oracleAmbiguousProgram, rationalSequence,
    List.foldr_cons, List.foldr_nil, rationalAssign, RationalProgram.encoding,
    RationalOperand.encoding]
  norm_num [rationalEncodingLength, numeratorBits, denominatorBits] at *
  omega

end IdentityTesting.RationalComputation
