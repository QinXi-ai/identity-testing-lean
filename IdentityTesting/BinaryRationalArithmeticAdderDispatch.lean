import IdentityTesting.BinaryRationalArithmeticAdder

namespace IdentityTesting.BinaryRationalArithmeticAdder
open BinaryArithmetic

private theorem signed_halt (k : ℕ) (m : BinarySignedMultiplier.State) (h : m.phase = .halt) :
    BinarySignedMultiplier.advance k m = m := by
  induction k with
  | zero => rfl
  | succ k ih => simpa [BinarySignedMultiplier.advance,BinarySignedMultiplier.step,h] using ih

private theorem adder_halt (k : ℕ) (m : BinarySignedAdder.State) (h : m.phase = .halt) :
    BinarySignedAdder.advance k m = m := by
  induction k with
  | zero => rfl
  | succ k ih => simpa [BinarySignedAdder.advance,BinarySignedAdder.step,h] using ih

private theorem base_halt (k : ℕ) (m : BinaryRationalArithmeticMultiplier.State) (h : m.phase = .halt) :
    BinaryRationalArithmeticMultiplier.advance k m = m := by
  induction k with
  | zero => rfl
  | succ k ih => simpa [BinaryRationalArithmeticMultiplier.advance,BinaryRationalArithmeticMultiplier.step,h] using ih

theorem forward_leftProduct (s : State) (m : BinarySignedMultiplier.State) (k : ℕ)
    (h : (BinarySignedMultiplier.advance k m).phase = .halt) :
    ∃ j, j ≤ k+1 ∧ Runs { s with phase := .leftProduct, base := { s.base with num := m } } j
      { s with phase := .rightProduct, base := { s.base with num := BinarySignedMultiplier.advance k m } } := by
  induction k generalizing m with
  | zero =>
      refine ⟨1,by omega,?_⟩
      simp only [BinarySignedMultiplier.advance] at h
      simp [Runs,advance,step,h,BinarySignedMultiplier.advance]
  | succ k ih =>
      by_cases hh : m.phase = .halt
      · refine ⟨1,by omega,?_⟩
        rw [signed_halt (k+1) m hh]
        simp [Runs,advance,step,hh]
      · obtain ⟨j,hj,he⟩ := ih (BinarySignedMultiplier.step m) h
        refine ⟨j+1,by omega,?_⟩
        dsimp [Runs] at *
        rw [advance]
        simpa [step,hh,BinarySignedMultiplier.advance] using he

theorem forward_rightProduct (s : State) (m : BinarySignedMultiplier.State) (k : ℕ)
    (h : (BinarySignedMultiplier.advance k m).phase = .halt) :
    ∃ j, j ≤ k+1 ∧ Runs { s with phase := .rightProduct, right := m } j
      { s with phase := .denominator, right := BinarySignedMultiplier.advance k m } := by
  induction k generalizing m with
  | zero =>
      refine ⟨1,by omega,?_⟩
      simp only [BinarySignedMultiplier.advance] at h
      simp [Runs,advance,step,h,BinarySignedMultiplier.advance]
  | succ k ih =>
      by_cases hh : m.phase = .halt
      · refine ⟨1,by omega,?_⟩
        rw [signed_halt (k+1) m hh]
        simp [Runs,advance,step,hh]
      · obtain ⟨j,hj,he⟩ := ih (BinarySignedMultiplier.step m) h
        refine ⟨j+1,by omega,?_⟩
        dsimp [Runs] at *
        rw [advance]
        simpa [step,hh,BinarySignedMultiplier.advance] using he

theorem forward_denominator (s : State) (m : BinarySignedMultiplier.State) (k : ℕ)
    (h : (BinarySignedMultiplier.advance k m).phase = .halt) :
    ∃ j, j ≤ k+1 ∧ Runs { s with phase := .denominator, base := { s.base with den := m } } j
      { s with phase := .leftCollect, base := { s.base with den := BinarySignedMultiplier.advance k m }, adder := { s.adder with negativeLeft := s.base.num.negative, negativeRight := s.right.negative } } := by
  induction k generalizing m with
  | zero =>
      refine ⟨1,by omega,?_⟩
      simp only [BinarySignedMultiplier.advance] at h
      simp [Runs,advance,step,h,BinarySignedMultiplier.advance]
  | succ k ih =>
      by_cases hh : m.phase = .halt
      · refine ⟨1,by omega,?_⟩
        rw [signed_halt (k+1) m hh]
        simp [Runs,advance,step,hh]
      · obtain ⟨j,hj,he⟩ := ih (BinarySignedMultiplier.step m) h
        refine ⟨j+1,by omega,?_⟩
        dsimp [Runs] at *
        rw [advance]
        simpa [step,hh,BinarySignedMultiplier.advance] using he

theorem forward_add (s : State) (m : BinarySignedAdder.State) (k : ℕ)
    (h : (BinarySignedAdder.advance k m).phase = .halt) :
    ∃ j, j ≤ k+1 ∧ Runs { s with phase := .add, adder := m } j
      { s with phase := .sumCollect, adder := BinarySignedAdder.advance k m } := by
  induction k generalizing m with
  | zero =>
      refine ⟨1,by omega,?_⟩
      simp only [BinarySignedAdder.advance] at h
      simp [Runs,advance,step,h,BinarySignedAdder.advance]
  | succ k ih =>
      by_cases hh : m.phase = .halt
      · refine ⟨1,by omega,?_⟩
        rw [adder_halt (k+1) m hh]
        simp [Runs,advance,step,hh]
      · obtain ⟨j,hj,he⟩ := ih (BinarySignedAdder.step m) h
        refine ⟨j+1,by omega,?_⟩
        dsimp [Runs] at *
        rw [advance]
        simpa [step,hh,BinarySignedAdder.advance] using he

theorem forward_normalize (s : State) (m : BinaryRationalArithmeticMultiplier.State) (k : ℕ)
    (h : (BinaryRationalArithmeticMultiplier.advance k m).phase = .halt) :
    ∃ j, j ≤ k+1 ∧ Runs { s with phase := .normalize, base := m } j
      { s with phase := .halt, base := BinaryRationalArithmeticMultiplier.advance k m } := by
  induction k generalizing m with
  | zero =>
      refine ⟨1,by omega,?_⟩
      simp only [BinaryRationalArithmeticMultiplier.advance] at h
      simp [Runs,advance,step,h,BinaryRationalArithmeticMultiplier.advance]
  | succ k ih =>
      by_cases hh : m.phase = .halt
      · refine ⟨1,by omega,?_⟩
        rw [base_halt (k+1) m hh]
        simp [Runs,advance,step,hh]
      · obtain ⟨j,hj,he⟩ := ih (BinaryRationalArithmeticMultiplier.step m) h
        refine ⟨j+1,by omega,?_⟩
        dsimp [Runs] at *
        rw [advance]
        simpa [step,hh,BinaryRationalArithmeticMultiplier.advance] using he

end IdentityTesting.BinaryRationalArithmeticAdder
