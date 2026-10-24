import IdentityTesting.BinaryCodeLiteralLoader

namespace IdentityTesting.BinaryCodeLiteralLoader
open BinaryRegisterMachine

theorem binary_literal_load (w : Word) (code history : List Symbol) :
    ∃ n, n ≤ 2*(w.numerator.magnitude.length+w.denominator.length)+8 ∧
      advance n (initial (encode w++code) history) =
        ⟨.halt,.halt,code,(encode w).reverse++history,[],w.numerator.negative,w.numerator.magnitude,w.denominator⟩ ∧
      bitSteps n (initial (encode w++code) history) ≤
        20*(w.numerator.magnitude.length+w.denominator.length)+80 := by
  let sigHist : List Symbol := .boundary::.cell (.bit w.numerator.negative)::history
  let mid : State := ⟨.numerator,.reading,
    BinaryCodeWordLoader.encode w.numerator.magnitude++(BinaryCodeWordLoader.encode w.denominator++code),
    sigHist,[],w.numerator.negative,[],[]⟩
  let midDen : State := ⟨.denominator,.reading,BinaryCodeWordLoader.encode w.denominator++code,
    (BinaryCodeWordLoader.encode w.numerator.magnitude).reverse++sigHist,[],w.numerator.negative,
    w.numerator.magnitude,[]⟩
  have hsign : advance 2 (initial (encode w++code) history) = mid := by
    simp [advance,step,initial,encode,BinaryCodeWordLoader.encode,mid,sigHist,List.append_assoc]
  let nstart : BinaryCodeWordLoader.State := ⟨.reading,
    BinaryCodeWordLoader.encode w.numerator.magnitude++(BinaryCodeWordLoader.encode w.denominator++code),sigHist,[],[]⟩
  have hnrun := BinaryCodeWordLoader.word_run w.numerator.magnitude []
    (BinaryCodeWordLoader.encode w.denominator++code) sigHist
  change BinaryCodeWordLoader.advance (2*w.numerator.magnitude.length+2) nstart = _ at hnrun
  simp only [List.append_nil] at hnrun
  have hnhalt : (BinaryCodeWordLoader.advance (2*w.numerator.magnitude.length+2) nstart).phase = .halt := by rw [hnrun]
  obtain ⟨kn,hkn,hn⟩ := forward_field mid false nstart (2*w.numerator.magnitude.length+2) hnhalt
  rw [hnrun] at hn
  have hn' : advance kn mid = midDen := by
    simpa [lift,after,setField,phaseOf,nstart,mid,midDen] using hn
  let dstart : BinaryCodeWordLoader.State := ⟨.reading,BinaryCodeWordLoader.encode w.denominator++code,
    (BinaryCodeWordLoader.encode w.numerator.magnitude).reverse++sigHist,[],[]⟩
  have hdrun := BinaryCodeWordLoader.word_run w.denominator [] code
    ((BinaryCodeWordLoader.encode w.numerator.magnitude).reverse++sigHist)
  change BinaryCodeWordLoader.advance (2*w.denominator.length+2) dstart = _ at hdrun
  simp only [List.append_nil] at hdrun
  have hdhalt : (BinaryCodeWordLoader.advance (2*w.denominator.length+2) dstart).phase = .halt := by rw [hdrun]
  obtain ⟨kd,hkd,hd⟩ := forward_field midDen true dstart (2*w.denominator.length+2) hdhalt
  rw [hdrun] at hd
  have hd' : advance kd midDen =
      ⟨.halt,.halt,code,(encode w).reverse++history,[],w.numerator.negative,w.numerator.magnitude,w.denominator⟩ := by
    simpa [lift,after,setField,phaseOf,dstart,midDen,sigHist,encode,BinaryCodeWordLoader.encode,
      List.reverse_append,List.append_assoc] using hd
  refine ⟨2+kn+kd,by omega,?_,?_⟩
  · rw [advance_add,advance_add,hsign,hn',hd']
  · have hc := bitSteps_le (2+kn+kd) (initial (encode w++code) history)
    omega

end IdentityTesting.BinaryCodeLiteralLoader
