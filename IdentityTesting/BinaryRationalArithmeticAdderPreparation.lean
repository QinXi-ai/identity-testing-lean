import IdentityTesting.BinaryRationalArithmeticAdderRuns

namespace IdentityTesting.BinaryRationalArithmeticAdder
open BinaryArithmetic

theorem copy_pden (s : State) (xs : List Bool) :
    Runs { s with phase := .pdenCollect, temp := [], base := { s.base with den := { s.base.den with mul := { s.base.den.mul with factor := xs } } }, right := { s.right with mul := { s.right.mul with shifted := [] } } } (2*xs.length+2)
      { s with phase := .qdenCollect, temp := [], base := { s.base with den := { s.base.den with mul := { s.base.den.mul with factor := xs } } }, right := { s.right with mul := { s.right.mul with shifted := xs } } } := by
  let s0 := { s with temp := [], right := { s.right with mul := { s.right.mul with shifted := [] } } }
  have h1 := pdenCollect_run s0 xs
  have h2 := pdenCopy_run
    { s0 with base := { s0.base with den := { s0.base.den with mul := { s0.base.den.mul with factor := [] } } } } xs.reverse
  simp only [s0,List.append_nil,List.length_reverse,List.reverse_reverse,List.nil_append] at h1 h2
  convert h1.trans h2 using 1 <;> omega

theorem copy_qden (s : State) (xs : List Bool) :
    Runs { s with phase := .qdenCollect, temp := [], base := { s.base with den := { s.base.den with mul := { s.base.den.mul with shifted := xs } }, num := { s.base.num with mul := { s.base.num.mul with shifted := [] } } } } (2*xs.length+2)
      { s with phase := .leftProduct, temp := [], base := { s.base with den := { s.base.den with mul := { s.base.den.mul with shifted := xs } }, num := { s.base.num with mul := { s.base.num.mul with shifted := xs } } } } := by
  let s0 := { s with temp := [], base := { s.base with num := { s.base.num with mul := { s.base.num.mul with shifted := [] } } } }
  have h1 := qdenCollect_run s0 xs
  have h2 := qdenCopy_run
    { s0 with base := { s0.base with den := { s0.base.den with mul := { s0.base.den.mul with shifted := [] } } } } xs.reverse
  simp only [s0,List.append_nil,List.length_reverse,List.reverse_reverse,List.nil_append] at h1 h2
  convert h1.trans h2 using 1 <;> omega

def prepared (p q : BinaryRationalArithmetic.Word) : State :=
  ⟨.leftProduct,
    ⟨.numCollect,
      BinarySignedMultiplier.initial p.numerator.negative false p.numerator.magnitude q.denominator,
      BinarySignedMultiplier.initial false false p.denominator q.denominator,
      BinaryRationalNormalizationMachine.initial false [] [],[]⟩,
    BinarySignedMultiplier.initial q.numerator.negative false q.numerator.magnitude p.denominator,
    BinarySignedAdder.initial ⟨false,[]⟩ ⟨false,[]⟩,[]⟩

theorem prepare (p q : BinaryRationalArithmetic.Word) :
    Runs (initial p q) (2*p.denominator.length+2*q.denominator.length+4) (prepared p q) := by
  let s1 : State := { initial p q with phase := .qdenCollect, right := BinarySignedMultiplier.initial q.numerator.negative false q.numerator.magnitude p.denominator }
  have h1 : Runs (initial p q) (2*p.denominator.length+2) s1 := by
    simpa [initial,s1,BinarySignedMultiplier.initial,BinaryMultiplierMachine.ready] using
      copy_pden (initial p q) p.denominator
  have h2 : Runs s1 (2*q.denominator.length+2) (prepared p q) := by
    simpa [initial,s1,prepared,BinarySignedMultiplier.initial,BinaryMultiplierMachine.ready] using
      copy_qden s1 q.denominator
  convert h1.trans h2 using 1 <;> omega

end IdentityTesting.BinaryRationalArithmeticAdder
