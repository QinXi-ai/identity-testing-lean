import IdentityTesting.BinaryRationalArithmeticCeilSizeFinish

namespace IdentityTesting.BinaryRationalArithmeticCeilSize
open BinaryArithmetic

def roundStart (d : BinaryDivisionMachine.State) (xs : List Bool) : State :=
  ⟨.round,false,d,⟨.increment,[],xs,[]⟩,⟨.collect,[],[],[]⟩,BinaryRationalArithmeticBitLength.initial [],[],[]⟩

theorem round_run (d : BinaryDivisionMachine.State) (xs : List Bool) :
    ∃ steps cp out, Runs (roundStart d xs) steps (finishStart d cp out) ∧
      steps ≤ 2*xs.length+5 ∧ out.length ≤ xs.length+1 ∧
      value out = value xs + if d.rem.out=[] then 0 else 1 := by
  by_cases hz : d.rem.out=[]
  · refine ⟨1,.increment,xs,?_,by omega,by omega,?_⟩
    · simp [Runs,advance,step,roundStart,finishStart,hz]
    · simp [hz]
  · obtain ⟨k,hk,hr⟩ := BinaryRationalArithmeticBitCounter.increment_run [] xs []
    simp only [List.length_nil,List.reverse_nil,List.nil_append,Nat.add_zero] at hk hr
    let ci : BinaryRationalArithmeticBitCounter.State := ⟨.increment,[],xs,[]⟩
    have he : BinaryRationalArithmeticBitCounter.advance (k+1) ci =
        ⟨.halt,[],BinaryRationalArithmeticBitCounter.increment xs,[]⟩ := by
      rw [BinaryRationalArithmeticBitCounter.advance_add]
      change BinaryRationalArithmeticBitCounter.advance 1
        (BinaryRationalArithmeticBitCounter.advance k ci) = _
      rw [show BinaryRationalArithmeticBitCounter.advance k ci = _ from hr]
      rfl
    have hh : (BinaryRationalArithmeticBitCounter.advance (k+1) ci).phase = .halt := by rw [he]
    obtain ⟨j,hj,hjr⟩ := forward_counter (roundStart d xs) ci (k+1) hh
    rw [he] at hjr
    have hfirst : Runs (roundStart d xs) 1 {(roundStart d xs) with phase := .incrementing} := by
      simp [Runs,advance,step,roundStart,hz]
    refine ⟨1+j,.halt,BinaryRationalArithmeticBitCounter.increment xs,?_,by omega,
      BinaryRationalArithmeticBitCounter.increment_length xs,?_⟩
    · exact hfirst.trans hjr
    · simp [hz,BinaryRationalArithmeticBitCounter.increment_value]

end IdentityTesting.BinaryRationalArithmeticCeilSize
