import IdentityTesting.BinaryRationalArithmeticCeilSizeRounding

namespace IdentityTesting.BinaryRationalArithmeticCeilSize
open BinaryArithmetic

theorem natural_fraction_run (m n : ℕ) (hn : 0<n) :
    ∃ steps, let s := initial ⟨⟨false,m.bits⟩,n.bits⟩
      (advance steps s).phase = .halt ∧
      output (advance steps s) = ⟨⟨false,(Nat.ceil ((m:ℚ)/n)).size.bits⟩,[true]⟩ ∧
      steps ≤ 1000*(m.size+n.size+1)^2 := by
  let s := initial ⟨⟨false,m.bits⟩,n.bits⟩
  let di := BinaryDivisionMachine.initial m.bits n.bits
  obtain ⟨kd,hdh,hdq,hdr,hdk⟩ := division_bounded_run m n hn
  let df := BinaryDivisionMachine.advance kd di
  obtain ⟨jd,hjd,hjr⟩ := forward_division s di kd hdh
  have hfirst : Runs s 1 {s with phase := .dividing} := rfl
  have hstart := hfirst.trans hjr
  let ce : BinaryRationalArithmeticBitCounter.State := ⟨.increment,[],[],[]⟩
  let ne : BinaryWordNormalization.State := ⟨.collect,[],[],[]⟩
  let le := BinaryRationalArithmeticBitLength.initial []
  let de := {df with quot := {df.quot with out := []}}
  have h1 := quotient_collect ⟨.quotientCollect,false,df,ce,ne,le,[],[]⟩ df.quot.out
  have h2 := quotient_emit ⟨.quotientEmit,false,de,ce,ne,le,[],[]⟩ df.quot.out.reverse
  simp only [List.append_nil,List.reverse_reverse,List.length_reverse] at h1 h2
  have ht : Runs ⟨.quotientCollect,false,df,ce,ne,le,[],[]⟩ (2*df.quot.out.length+2)
      (roundStart de df.quot.out) := by
    convert h1.trans h2 using 1 <;> (try simp [roundStart,de,ce,ne,le]) <;> omega
  obtain ⟨kr,cp,out,hrr,hrk,hrol,hrov⟩ := round_run de df.quot.out
  obtain ⟨kf,hfh,hfo,hfk⟩ := finish_run de cp out
  have hall := ((hstart.trans ht).trans hrr)
  have hv : value out = Nat.ceil ((m:ℚ)/n) := by
    have hq : df.quot.out=(m/n).bits := hdq
    have hr : de.rem.out=(m%n).bits := hdr
    have hz : (m%n).bits=[] ↔ m%n=0 := by
      constructor
      · intro h
        have hv := congrArg value h
        simpa only [value_bits,value] using hv
      · intro h; simp [h]
    simp only [hq,hr,value_bits,hz] at hrov
    rw [BinaryRationalArithmetic.nat_ceil_fraction m n hn]
    exact hrov
  refine ⟨1+jd+(2*df.quot.out.length+2)+kr+kf,?_,?_,?_⟩
  · rw [advance_add,show advance _ s = _ from hall]
    exact hfh
  · change output (advance _ s) = _
    rw [advance_add,show advance _ s = _ from hall,hfo,hv]
  · have hql : df.quot.out.length ≤ m.size := by
      rw [show df.quot.out=(m/n).bits from hdq,Nat.size_eq_bits_len]
      exact Nat.size_le_size (Nat.div_le_self m n)
    have hl : out.length+1 ≤ 2*(m.size+n.size+1) := by omega
    have hp := Nat.pow_le_pow_left hl 2
    let S := m.size+n.size+1
    have hS : 1≤S := by dsimp [S]; omega
    have hmS : m.size≤S := by dsimp [S]; omega
    have hSq : S≤S^2 := by nlinarith only [Nat.mul_le_mul_left S hS]
    change kd≤30*S^2 at hdk
    change (out.length+1)^2≤(2*S)^2 at hp
    have hf' : kf≤400*S^2 := by nlinarith only [hfk,hp]
    have ho' : 1+jd+(2*df.quot.out.length+2)+kr ≤ 30*S^2+4*S+9 := by omega
    change _≤1000*S^2
    omega

end IdentityTesting.BinaryRationalArithmeticCeilSize
