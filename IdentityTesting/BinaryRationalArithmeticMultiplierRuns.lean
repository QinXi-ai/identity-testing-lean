import IdentityTesting.BinaryRationalArithmeticMultiplier

namespace IdentityTesting.BinaryRationalArithmeticMultiplier
open BinaryArithmetic

private theorem signed_halt (k : ℕ) (m : BinarySignedMultiplier.State) (h : m.phase = .halt) :
    BinarySignedMultiplier.advance k m = m := by
  induction k with
  | zero => rfl
  | succ k ih => simpa [BinarySignedMultiplier.advance,BinarySignedMultiplier.step,h] using ih

private theorem normalization_halt (k : ℕ) (m : BinaryRationalNormalizationMachine.State) (h : m.phase = .halt) :
    BinaryRationalNormalizationMachine.advance k m = m := by
  induction k with
  | zero => rfl
  | succ k ih => simpa [BinaryRationalNormalizationMachine.advance,BinaryRationalNormalizationMachine.step,h] using ih


theorem forward_numerator (s : State) (m : BinarySignedMultiplier.State) (k : ℕ)
    (h : (BinarySignedMultiplier.advance k m).phase = .halt) :
    ∃ j, j ≤ k+1 ∧ Runs { s with phase := .numerator, num := m } j
      { s with phase := .denominator, num := BinarySignedMultiplier.advance k m } := by
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
    ∃ j, j ≤ k+1 ∧ Runs { s with phase := .denominator, den := m } j
      { s with phase := .numCollect, den := BinarySignedMultiplier.advance k m, norm := { s.norm with negative := s.num.negative } } := by
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


theorem forward_normalization (s : State) (m : BinaryRationalNormalizationMachine.State) (k : ℕ)
    (h : (BinaryRationalNormalizationMachine.advance k m).phase = .halt) :
    ∃ j, j ≤ k+1 ∧ Runs { s with phase := .normalize, norm := m } j
      { s with phase := .halt, norm := BinaryRationalNormalizationMachine.advance k m } := by
  induction k generalizing m with
  | zero =>
      refine ⟨1,by omega,?_⟩
      simp only [BinaryRationalNormalizationMachine.advance] at h
      simp [Runs,advance,step,h,BinaryRationalNormalizationMachine.advance]
  | succ k ih =>
      by_cases hh : m.phase = .halt
      · refine ⟨1,by omega,?_⟩
        rw [normalization_halt (k+1) m hh]
        simp [Runs,advance,step,hh]
      · obtain ⟨j,hj,he⟩ := ih (BinaryRationalNormalizationMachine.step m) h
        refine ⟨j+1,by omega,?_⟩
        dsimp [Runs] at *
        rw [advance]
        simpa [step,hh,BinaryRationalNormalizationMachine.advance] using he


theorem numCollect_run (s : State) (xs : List Bool) :
    Runs { s with phase := .numCollect, num := { s.num with norm := { s.num.norm with out := xs } } } (xs.length+1)
      { s with phase := .numEmit, num := { s.num with norm := { s.num.norm with out := [] } }, temp := xs.reverse ++ s.temp } := by
  induction xs generalizing s with
  | nil => cases s; rfl
  | cons b xs ih =>
      change advance (xs.length+1+1) _ = _
      rw [advance]
      change advance (xs.length+1)
        { s with phase := .numCollect, num := { s.num with norm := { s.num.norm with out := xs } }, temp := b :: s.temp } = _
      rw [show advance _ _ = _ from ih { s with temp := b :: s.temp }]
      simp [List.reverse_cons,List.append_assoc]


theorem denCollect_run (s : State) (xs : List Bool) :
    Runs { s with phase := .denCollect, den := { s.den with norm := { s.den.norm with out := xs } } } (xs.length+1)
      { s with phase := .denEmit, den := { s.den with norm := { s.den.norm with out := [] } }, temp := xs.reverse ++ s.temp } := by
  induction xs generalizing s with
  | nil => cases s; rfl
  | cons b xs ih =>
      change advance (xs.length+1+1) _ = _
      rw [advance]
      change advance (xs.length+1)
        { s with phase := .denCollect, den := { s.den with norm := { s.den.norm with out := xs } }, temp := b :: s.temp } = _
      rw [show advance _ _ = _ from ih { s with temp := b :: s.temp }]
      simp [List.reverse_cons,List.append_assoc]


theorem numEmit_run (s : State) (xs : List Bool) :
    Runs { s with phase := .numEmit, temp := xs } (xs.length+1)
      { s with phase := .denCollect, temp := [], norm := { s.norm with num := { s.norm.num with source := xs.reverse ++ s.norm.num.source } } } := by
  induction xs generalizing s with
  | nil => cases s; rfl
  | cons b xs ih =>
      change advance (xs.length+1+1) _ = _
      rw [advance]
      change advance (xs.length+1)
        { s with phase := .numEmit, temp := xs, norm := { s.norm with num := { s.norm.num with source := b :: s.norm.num.source } } } = _
      rw [show advance _ _ = _ from ih { s with norm := { s.norm with num := { s.norm.num with source := b :: s.norm.num.source } } }]
      simp [List.reverse_cons,List.append_assoc]


theorem denEmit_run (s : State) (xs : List Bool) :
    Runs { s with phase := .denEmit, temp := xs } (xs.length+1)
      { s with phase := .normalize, temp := [], norm := { s.norm with den := { s.norm.den with source := xs.reverse ++ s.norm.den.source } } } := by
  induction xs generalizing s with
  | nil => cases s; rfl
  | cons b xs ih =>
      change advance (xs.length+1+1) _ = _
      rw [advance]
      change advance (xs.length+1)
        { s with phase := .denEmit, temp := xs, norm := { s.norm with den := { s.norm.den with source := b :: s.norm.den.source } } } = _
      rw [show advance _ _ = _ from ih { s with norm := { s.norm with den := { s.norm.den with source := b :: s.norm.den.source } } }]
      simp [List.reverse_cons,List.append_assoc]

end IdentityTesting.BinaryRationalArithmeticMultiplier
