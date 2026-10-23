import IdentityTesting.RationalAlgorithmTraceVectorResult
import IdentityTesting.RationalAlgorithmTraceTermBounds
import IdentityTesting.RationalOracleParameterEncoding

/-! Polynomial operand bounds for the actual finite vector computation, including
every partial accumulator and every scratch-register arithmetic call. -/
namespace IdentityTesting.RationalComputation
open scoped BigOperators
local notation "L" => rationalEncodingLength
local notation "V" => rationalVectorEncodingLength

theorem rational_list_sum_encoding (xs : List ℚ) :
    L xs.sum ≤ 2 * (xs.map L).sum + 3 := by
  have h := rational_sum_encoding Finset.univ (fun i : Fin xs.length => xs[i.val])
  simpa only [← List.sum_ofFn, List.ofFn_getElem, List.ofFn_getElem_eq_map] using h

theorem rational_list_sum_encoding_of_bound {α : Type*} (xs : List α) (f : α → ℚ)
    (B : ℕ) (h : ∀ i ∈ xs, L (f i) ≤ B) :
    L (xs.map f).sum ≤ 2 * xs.length * B + 3 := by
  have hs : ((xs.map f).map L).sum ≤ xs.length * B := by
    induction xs with
    | nil => simp
    | cons i xs ih =>
      have hi := h i (by simp)
      have ht := ih (fun j hj => h j (by simp [hj]))
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      nlinarith
  have he := rational_list_sum_encoding (xs.map f)
  nlinarith

def oracleTraceSize {k : ℕ} (a : Fin k → ℚ) (β t ρ : ℚ) (n : ℕ) : ℕ :=
  V a + L β + L t + L ρ + n + 1

theorem oracleTermValue_encoding {k : ℕ} (a : Fin k → ℚ) (β t ρ : ℚ)
    (n : ℕ) (objective upper : Bool) (i : Fin k) :
    L (oracleTermValue objective upper (a i) t β ρ n) ≤ 200 * oracleTraceSize a β t ρ n := by
  have ha := rational_entry_encoding_le a i
  have hx := oracleCoordinateInterval_encoding_le (a i) β ρ n
  have hl := rationalAllocationCost_encoding_le t (a i) (oracleCoordinateInterval (a i) β ρ n).1
  have hu := rationalAllocationCost_encoding_le t (a i) (oracleCoordinateInterval (a i) β ρ n).2
  have hml := rational_mul_encoding (a i) (oracleCoordinateInterval (a i) β ρ n).1
  have hmu := rational_mul_encoding (a i) (oracleCoordinateInterval (a i) β ρ n).2
  cases objective <;> cases upper <;>
    simp only [oracleTermValue, Bool.false_eq_true, if_false, if_true, oracleTraceSize] <;> omega

def oraclePartialSum {k : ℕ} (a : Fin k → ℚ) (β t ρ : ℚ) (n : ℕ)
    (objective upper : Bool) (xs : List (Fin k)) : ℚ :=
  (xs.map (fun i => oracleTermValue objective upper (a i) t β ρ n)).sum

theorem oraclePartialSum_encoding {k : ℕ} (a : Fin k → ℚ) (β t ρ : ℚ)
    (n : ℕ) (objective upper : Bool) (xs : List (Fin k)) (hx : xs.length ≤ k) :
    L (oraclePartialSum a β t ρ n objective upper xs) ≤ 400 * k * oracleTraceSize a β t ρ n + 3 := by
  have h := rational_list_sum_encoding_of_bound xs
    (fun i => oracleTermValue objective upper (a i) t β ρ n)
    (200 * oracleTraceSize a β t ρ n) (fun i _ => oracleTermValue_encoding a β t ρ n objective upper i)
  have hm := Nat.mul_le_mul_right (400 * oracleTraceSize a β t ρ n) hx
  change L (oraclePartialSum a β t ρ n objective upper xs) ≤ _ at h
  nlinarith

theorem oracleLoadAtomProgram_trace {k : ℕ} (a : Fin k → ℚ) (i : Fin k)
    (z β l u t ρ sl su : ℚ) :
    ((oracleLoadAtomProgram i).run (oracleRegisters z β l u t ρ sl su ++ List.ofFn a)).2 =
      [⟨.copy, a i, 0⟩, ⟨.copy, 0, 0⟩, ⟨.copy, 1, 0⟩] := by
  have hr : (RationalOperand.reg (17 + i.val)).read
      (oracleRegisters z β l u t ρ sl su ++ List.ofFn a) = a i := by
    change ((oracleRegisters z β l u t ρ sl su ++ List.ofFn a)[17 + i.val]?).getD 0 = a i
    rw [List.getElem?_append_right (by simp [oracleRegisters, coordinateRegisters])]
    simp [oracleRegisters, coordinateRegisters, i.isLt]
  simp only [oracleLoadAtomProgram, rationalSequence, List.foldr_cons, List.foldr_nil,
    rationalAssign, RationalProgram.run, RationalInstruction.exec,
    RationalInstruction.call, RationalCall.result, RationalOp.eval]
  rw [hr]
  simp [RationalOperand.read, oracleRegisters, coordinateRegisters]

theorem oracleAtomProgram_operand_encoding {k : ℕ} (a : Fin k → ℚ) (β t ρ : ℚ)
    (n : ℕ) (objective : Bool) (i : Fin k) (z l u sl su : ℚ) (B : ℕ)
    (hl : L sl ≤ B) (hu : L su ≤ B) (c : RationalCall)
    (hc : c ∈ ((oracleAtomProgram objective n i).run
      (oracleRegisters z β l u t ρ sl su ++ List.ofFn a)).2) :
    L c.lhs ≤ 1000 * (oracleTraceSize a β t ρ n + 2 * B) ∧
      L c.rhs ≤ 1000 * (oracleTraceSize a β t ρ n + 2 * B) := by
  rw [oracleAtomProgram, RationalProgram.run_seq_trace, oracleLoadAtomProgram_exec,
    oracleLoadAtomProgram_trace] at hc
  have hf := (oracleTermProgram objective n).run_append
    (oracleRegisters (a i) β 0 1 t ρ sl su) (List.ofFn a)
    (by rw [oracleTermProgram_slots]; rfl)
  have ht := congrArg Prod.snd hf
  rw [ht] at hc
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc
  have ha := rational_entry_encoding_le a i
  have hz : L 0 = 2 := by norm_num [rationalEncodingLength, numeratorBits, denominatorBits]
  have ho : L 1 = 3 := by norm_num [rationalEncodingLength, numeratorBits, denominatorBits]
  rcases hc with (rfl | rfl | rfl) | hc
  all_goals try { simp only [RationalCall.lhs, RationalCall.rhs]; unfold oracleTraceSize; constructor <;> omega }
  have h := oracleTermProgram_operand_encoding objective (a i) β t ρ sl su n c hc
  unfold oracleTraceSize
  constructor <;> omega

theorem oracleListProgram_operand_encoding {k : ℕ} (a : Fin k → ℚ) (β t ρ : ℚ)
    (n : ℕ) (objective : Bool) (xs ys : List (Fin k))
    (hlen : ys.length + xs.length ≤ k) (z l u : ℚ) (c : RationalCall)
    (hc : c ∈ ((rationalSequence (xs.map (fun (i : Fin k) => oracleAtomProgram objective n i))).run
      (oracleRegisters z β l u t ρ
        (oraclePartialSum a β t ρ n objective false ys)
        (oraclePartialSum a β t ρ n objective true ys) ++ List.ofFn a)).2) :
    L c.lhs ≤ 1000000 * (k + 1) * oracleTraceSize a β t ρ n ∧
      L c.rhs ≤ 1000000 * (k + 1) * oracleTraceSize a β t ρ n := by
  induction xs generalizing ys z l u with
  | nil => simp [rationalSequence, RationalProgram.run] at hc
  | cons i xs ih =>
    change c ∈ ((RationalProgram.seq (oracleAtomProgram objective n i)
      (rationalSequence (xs.map (fun (j : Fin k) => oracleAtomProgram objective n j)))).run _).2 at hc
    rw [RationalProgram.run_seq_trace, oracleAtomProgram_exec] at hc
    rcases List.mem_append.mp hc with hc | hc
    · have hl := oraclePartialSum_encoding a β t ρ n objective false ys (by simp only [List.length_cons] at hlen; omega)
      have hu := oraclePartialSum_encoding a β t ρ n objective true ys (by simp only [List.length_cons] at hlen; omega)
      have h := oracleAtomProgram_operand_encoding a β t ρ n objective i z l u
        _ _ _ hl hu c hc
      have hb : 1 ≤ oracleTraceSize a β t ρ n := by unfold oracleTraceSize; omega
      constructor <;> nlinarith [h.1, h.2]
    · have he (upper : Bool) :
          oraclePartialSum a β t ρ n objective upper ys + oracleTermValue objective upper (a i) t β ρ n =
            oraclePartialSum a β t ρ n objective upper (ys ++ [i]) := by
          simp [oraclePartialSum]
      rw [he false, he true] at hc
      exact ih (ys ++ [i]) (by simp only [List.length_append, List.length_singleton,
        List.length_cons, List.length_nil] at *; omega) (a i) _ _ hc

theorem oracleVectorProgram_operand_encoding {k : ℕ} (a : Fin k → ℚ) (β t ρ : ℚ)
    (n : ℕ) (objective : Bool) (c : RationalCall)
    (hc : c ∈ ((oracleVectorProgram objective k n).run (oracleProgramInput a t β ρ)).2) :
    L c.lhs ≤ 1000000 * (k + 1) * oracleTraceSize a β t ρ n ∧
      L c.rhs ≤ 1000000 * (k + 1) * oracleTraceSize a β t ρ n := by
  exact oracleListProgram_operand_encoding a β t ρ n objective (List.finRange k) []
    (by simp) 0 0 1 c hc

end IdentityTesting.RationalComputation
