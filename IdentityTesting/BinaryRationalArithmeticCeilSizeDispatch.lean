import IdentityTesting.BinaryRationalArithmeticCeilSize

namespace IdentityTesting.BinaryRationalArithmeticCeilSize
open BinaryArithmetic

private theorem division_halt (k : ℕ) (s : BinaryDivisionMachine.State) (h : s.phase = .halt) :
    BinaryDivisionMachine.advance k s=s := by
  induction k with
  | zero => rfl
  | succ k ih => simpa [BinaryDivisionMachine.advance,BinaryDivisionMachine.step,h] using ih

theorem forward_division (s : State) (m : BinaryDivisionMachine.State) (k : ℕ)
    (h : (BinaryDivisionMachine.advance k m).phase = .halt) :
    ∃ j, j ≤ k+1 ∧ Runs {s with phase := .dividing,div := m} j
      {s with phase := .quotientCollect,div := BinaryDivisionMachine.advance k m} := by
  induction k generalizing m with
  | zero =>
      simp only [BinaryDivisionMachine.advance] at h
      refine ⟨1,by omega,?_⟩
      simp [Runs,advance,step,h,BinaryDivisionMachine.advance]
  | succ k ih =>
      by_cases hh : m.phase = .halt
      · refine ⟨1,by omega,?_⟩
        rw [division_halt (k+1) m hh]
        simp [Runs,advance,step,hh]
      · obtain ⟨j,hj,he⟩ := ih (BinaryDivisionMachine.step m) h
        refine ⟨j+1,by omega,?_⟩
        dsimp [Runs] at *
        rw [advance]
        simpa [step,hh,BinaryDivisionMachine.advance] using he

private theorem counter_halt (k : ℕ) (s : BinaryRationalArithmeticBitCounter.State) (h : s.phase = .halt) :
    BinaryRationalArithmeticBitCounter.advance k s=s := by
  induction k with
  | zero => rfl
  | succ k ih => simpa [BinaryRationalArithmeticBitCounter.advance,BinaryRationalArithmeticBitCounter.step,h] using ih

theorem forward_counter (s : State) (m : BinaryRationalArithmeticBitCounter.State) (k : ℕ)
    (h : (BinaryRationalArithmeticBitCounter.advance k m).phase = .halt) :
    ∃ j, j ≤ k+1 ∧ Runs {s with phase := .incrementing,counter := m} j
      {s with phase := .roundedCollect,counter := BinaryRationalArithmeticBitCounter.advance k m} := by
  induction k generalizing m with
  | zero =>
      simp only [BinaryRationalArithmeticBitCounter.advance] at h
      refine ⟨1,by omega,?_⟩
      simp [Runs,advance,step,h,BinaryRationalArithmeticBitCounter.advance]
  | succ k ih =>
      by_cases hh : m.phase = .halt
      · refine ⟨1,by omega,?_⟩
        rw [counter_halt (k+1) m hh]
        simp [Runs,advance,step,hh]
      · obtain ⟨j,hj,he⟩ := ih (BinaryRationalArithmeticBitCounter.step m) h
        refine ⟨j+1,by omega,?_⟩
        dsimp [Runs] at *
        rw [advance]
        simpa [step,hh,BinaryRationalArithmeticBitCounter.advance] using he

private theorem normalizer_halt (k : ℕ) (s : BinaryWordNormalization.State) (h : s.phase = .halt) :
    BinaryWordNormalization.advance k s=s := by
  induction k with
  | zero => rfl
  | succ k ih => simpa [BinaryWordNormalization.advance,BinaryWordNormalization.step,h] using ih

theorem forward_normalizer (s : State) (m : BinaryWordNormalization.State) (k : ℕ)
    (h : (BinaryWordNormalization.advance k m).phase = .halt) :
    ∃ j, j ≤ k+1 ∧ Runs {s with phase := .normalize,norm := m} j
      {s with phase := .ceilingCollect,norm := BinaryWordNormalization.advance k m} := by
  induction k generalizing m with
  | zero =>
      simp only [BinaryWordNormalization.advance] at h
      refine ⟨1,by omega,?_⟩
      simp [Runs,advance,step,h,BinaryWordNormalization.advance]
  | succ k ih =>
      by_cases hh : m.phase = .halt
      · refine ⟨1,by omega,?_⟩
        rw [normalizer_halt (k+1) m hh]
        simp [Runs,advance,step,hh]
      · obtain ⟨j,hj,he⟩ := ih (BinaryWordNormalization.step m) h
        refine ⟨j+1,by omega,?_⟩
        dsimp [Runs] at *
        rw [advance]
        simpa [step,hh,BinaryWordNormalization.advance] using he

private theorem measure_halt (k : ℕ) (s : BinaryRationalArithmeticBitLength.State) (h : s.phase = .halt) :
    BinaryRationalArithmeticBitLength.advance k s=s := by
  induction k with
  | zero => rfl
  | succ k ih => simpa [BinaryRationalArithmeticBitLength.advance,BinaryRationalArithmeticBitLength.step,h] using ih

theorem forward_measure (s : State) (m : BinaryRationalArithmeticBitLength.State) (k : ℕ)
    (h : (BinaryRationalArithmeticBitLength.advance k m).phase = .halt) :
    ∃ j, j ≤ k+1 ∧ Runs {s with phase := .measuring,measure := m} j
      {s with phase := .denominator,measure := BinaryRationalArithmeticBitLength.advance k m} := by
  induction k generalizing m with
  | zero =>
      simp only [BinaryRationalArithmeticBitLength.advance] at h
      refine ⟨1,by omega,?_⟩
      simp [Runs,advance,step,h,BinaryRationalArithmeticBitLength.advance]
  | succ k ih =>
      by_cases hh : m.phase = .halt
      · refine ⟨1,by omega,?_⟩
        rw [measure_halt (k+1) m hh]
        simp [Runs,advance,step,hh]
      · obtain ⟨j,hj,he⟩ := ih (BinaryRationalArithmeticBitLength.step m) h
        refine ⟨j+1,by omega,?_⟩
        dsimp [Runs] at *
        rw [advance]
        simpa [step,hh,BinaryRationalArithmeticBitLength.advance] using he

end IdentityTesting.BinaryRationalArithmeticCeilSize
