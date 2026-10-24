import IdentityTesting.BinaryRationalArithmeticCeilSizeDivision

namespace IdentityTesting.BinaryRationalArithmeticCeilSize
open BinaryArithmetic

private theorem trim_length_le (xs : List Bool) : (BinaryWordNormalization.trim xs).length ≤ xs.length := by
  induction xs with
  | nil => simp [BinaryWordNormalization.trim]
  | cons b bs ih =>
      change (BinaryWordNormalization.prependNormalized b (BinaryWordNormalization.trim bs)).length ≤ bs.length+1
      cases h : BinaryWordNormalization.trim bs <;> cases b <;>
        simp_all [BinaryWordNormalization.prependNormalized]

def finishStart (d : BinaryDivisionMachine.State) (cp : BinaryRationalArithmeticBitCounter.Phase)
    (xs : List Bool) : State :=
  ⟨.roundedCollect,false,d,⟨cp,[],xs,[]⟩,⟨.collect,[],[],[]⟩,BinaryRationalArithmeticBitLength.initial [],[],[]⟩

theorem finish_run (d : BinaryDivisionMachine.State) (cp : BinaryRationalArithmeticBitCounter.Phase)
    (xs : List Bool) :
    ∃ steps, (advance steps (finishStart d cp xs)).phase = .halt ∧
      output (advance steps (finishStart d cp xs)) = ⟨⟨false,(value xs).size.bits⟩,[true]⟩ ∧
      steps ≤ 100*(xs.length+1)^2 := by
  let s := finishStart d cp xs
  let ce : BinaryRationalArithmeticBitCounter.State := ⟨cp,[],[],[]⟩
  let le := BinaryRationalArithmeticBitLength.initial []
  let ne : BinaryWordNormalization.State := ⟨.collect,[],[],[]⟩
  let ni : BinaryWordNormalization.State := ⟨.collect,xs,[],[]⟩
  let nf := BinaryWordNormalization.advance (2*xs.length+2) ni
  have h1 := rounded_collect ⟨.roundedCollect,false,d,ce,ne,le,[],[]⟩ xs
  have h2 := rounded_emit ⟨.roundedEmit,false,d,ce,ne,le,[],[]⟩ xs.reverse
  simp only [List.append_nil,List.reverse_reverse,List.length_reverse] at h1 h2
  have ht : Runs s (2*xs.length+2) ⟨.normalize,false,d,ce,ni,le,[],[]⟩ := by
    convert h1.trans h2 using 1 <;> (try simp [s,finishStart,ce,ne,le,ni]) <;> omega
  obtain ⟨hnh,hno,hnv,hnl,hncost⟩ := BinaryWordNormalization.binary_normalization_machine xs
  obtain ⟨jn,hjn,hrn⟩ := forward_normalizer ⟨.normalize,false,d,ce,ni,le,[],[]⟩ ni (2*xs.length+2) hnh
  have h3 := ceiling_collect ⟨.ceilingCollect,false,d,ce,nf,le,[],[]⟩ nf.out
  have h4 := ceiling_emit ⟨.ceilingEmit,false,d,ce,{nf with out := []},le,[],[]⟩ nf.out.reverse
  simp only [List.append_nil,List.reverse_reverse,List.length_reverse] at h3 h4
  let li := BinaryRationalArithmeticBitLength.initial nf.out
  have hu : Runs ⟨.ceilingCollect,false,d,ce,nf,le,[],[]⟩ (2*nf.out.length+2)
      ⟨.measuring,false,d,ce,{nf with out := []},li,[],[]⟩ := by
    convert h3.trans h4 using 1 <;>
      (try simp [li,le,BinaryRationalArithmeticBitLength.initial,BinaryRationalArithmeticBitCounter.initial]) <;> omega
  obtain ⟨kl,hlh,hlo,hlk⟩ := BinaryRationalArithmeticBitLength.bit_length_run nf.out
  obtain ⟨jl,hjl,hrl⟩ := forward_measure ⟨.measuring,false,d,ce,{nf with out := []},li,[],[]⟩ li kl hlh
  let lf := BinaryRationalArithmeticBitLength.advance kl li
  have hend : Runs ⟨.denominator,false,d,ce,{nf with out := []},lf,[],[]⟩ 1
      ⟨.halt,false,d,ce,{nf with out := []},lf,[],[true]⟩ := rfl
  have hall := (((ht.trans hrn).trans hu).trans hrl).trans hend
  refine ⟨2*xs.length+2+jn+(2*nf.out.length+2)+jl+1,?_,?_,?_⟩
  · rw [hall]
  · change output (advance _ s) = _
    rw [hall]
    change (⟨⟨false,BinaryRationalArithmeticBitLength.output lf⟩,[true]⟩ : BinaryRationalArithmetic.Word) = _
    have ho : BinaryRationalArithmeticBitLength.output lf = nf.out.length.bits := hlo
    rw [ho]
    have hn : nf.out=(value xs).bits := hno
    rw [hn,Nat.size_eq_bits_len]
  · have hn : nf.out.length ≤ xs.length := by
      rw [show nf.out=(value xs).bits from hno,← BinaryWordNormalization.trim_eq_bits]
      exact trim_length_le xs
    have hsq := Nat.pow_le_pow_left hn 2
    have hsq' := Nat.pow_le_pow_left (Nat.add_le_add_right hn 1) 2
    nlinarith only [hjn,hjl,hlk,hn,hsq,hsq']

end IdentityTesting.BinaryRationalArithmeticCeilSize
