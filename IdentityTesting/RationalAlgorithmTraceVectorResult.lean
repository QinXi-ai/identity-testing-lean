import IdentityTesting.RationalAlgorithmTraceVector

/-! The finite-register vector programs compute the existing full budget and
objective interval definitions, rather than an externally supplied sum. -/
namespace IdentityTesting.RationalComputation
open scoped BigOperators

theorem oracleListProgram_exec {k : ℕ} (objective : Bool) (n : ℕ)
    (a : Fin k → ℚ) (xs : List (Fin k)) (z β l u t ρ sl su : ℚ) :
    ∃ z' l' u',
      (rationalSequence (xs.map (fun (i : Fin k) => oracleAtomProgram objective n i))).exec
        (oracleRegisters z β l u t ρ sl su ++ List.ofFn a) =
      oracleRegisters z' β l' u' t ρ
        (sl + (xs.map (fun i => oracleTermValue objective false (a i) t β ρ n)).sum)
        (su + (xs.map (fun i => oracleTermValue objective true (a i) t β ρ n)).sum) ++
        List.ofFn a := by
  induction xs generalizing z l u sl su with
  | nil => exact ⟨z, l, u, by simp [rationalSequence, RationalProgram.exec]⟩
  | cons i xs ih =>
    obtain ⟨z', l', u', h⟩ := ih (a i) (oracleCoordinateInterval (a i) β ρ n).1
      (oracleCoordinateInterval (a i) β ρ n).2
      (sl + oracleTermValue objective false (a i) t β ρ n)
      (su + oracleTermValue objective true (a i) t β ρ n)
    refine ⟨z', l', u', ?_⟩
    change (rationalSequence (xs.map (fun (i : Fin k) => oracleAtomProgram objective n i))).exec
      ((oracleAtomProgram objective n i).exec _) = _
    rw [oracleAtomProgram_exec, h]
    simp only [List.map_cons, List.sum_cons, add_assoc]

def oracleProgramOutput (s : RationalRegisters) : ℚ × ℚ :=
  ((RationalOperand.reg 15).read s, (RationalOperand.reg 16).read s)

def oracleProgramInput {k : ℕ} (a : Fin k → ℚ) (t β ρ : ℚ) : RationalRegisters :=
  oracleRegisters 0 β 0 1 t ρ 0 0 ++ List.ofFn a

theorem oracleVectorProgram_result {k : ℕ} (objective : Bool) (n : ℕ)
    (a : Fin k → ℚ) (t β ρ : ℚ) :
    oracleProgramOutput ((oracleVectorProgram objective k n).run (oracleProgramInput a t β ρ)).1 =
      if objective then oracleObjectiveInterval a β ρ n else oracleBudgetInterval a t β ρ n := by
  rw [RationalProgram.run_result]
  obtain ⟨z, l, u, h⟩ := oracleListProgram_exec objective n a (List.finRange k) 0 β 0 1 t ρ 0 0
  change oracleProgramOutput ((rationalSequence _).exec _) = _
  unfold oracleProgramInput
  rw [h]
  cases objective <;>
    simp [oracleProgramOutput, RationalOperand.read, oracleRegisters, coordinateRegisters,
      List.finRange, List.map_ofFn, List.sum_ofFn, oracleTermValue,
      oracleBudgetInterval, oracleObjectiveInterval]

theorem rationalSequence_slots_le (xs : List RationalProgram) (B : ℕ)
    (h : ∀ p ∈ xs, p.slots ≤ B) : (rationalSequence xs).slots ≤ B := by
  induction xs with
  | nil => exact Nat.zero_le B
  | cons p xs ih =>
    exact max_le (h p (by simp)) (ih (fun q hq => h q (by simp [hq])))

theorem oracleAtomProgram_slots_le (objective : Bool) (n i k : ℕ) (hi : i < k) :
    (oracleAtomProgram objective n i).slots ≤ 17 + k := by
  simp only [oracleAtomProgram, RationalProgram.slots, oracleTermProgram_slots]
  have hload : (oracleLoadAtomProgram i).slots ≤ 17 + k := by
    simp [oracleLoadAtomProgram, rationalSequence, rationalAssign, RationalProgram.slots,
      RationalOperand.slots]
    omega
  exact max_le hload (by omega)

theorem oracleVectorProgram_slots (objective : Bool) (k n : ℕ) :
    (oracleVectorProgram objective k n).slots ≤ 17 + k := by
  apply rationalSequence_slots_le
  intro p hp
  change p ∈ (List.finRange k).map (fun (i : Fin k) => oracleAtomProgram objective n i) at hp
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp hp
  exact oracleAtomProgram_slots_le objective n i k i.isLt

theorem oracleProgramInput_length {k : ℕ} (a : Fin k → ℚ) (t β ρ : ℚ) :
    (oracleProgramInput a t β ρ).length = 17 + k := by
  simp [oracleProgramInput, oracleRegisters, coordinateRegisters]
  omega

end IdentityTesting.RationalComputation
