import IdentityTesting.BinaryCodeAddressLoader
import IdentityTesting.BinaryCodeLiteralLoaderRuns
import IdentityTesting.BinaryCodeTagDecoder
import IdentityTesting.RationalProgramTapeCode

namespace IdentityTesting.BinaryCodeMaterialization
open BinaryRegisterMachine RationalComputation

theorem word_encoding (bits : List Bool) :
    RationalProgramCode.word bits = BinaryCodeWordLoader.encode bits := rfl

theorem literal_encoding (q : ℚ) :
    RationalProgramCode.operand (.literal q) = RationalProgramCode.word [true] ++
      BinaryCodeLiteralLoader.encode (BinaryRationalArithmetic.encode q) := by
  simp [RationalProgramCode.operand,RationalProgramCode.word,BinaryCodeLiteralLoader.encode,
    BinaryCodeWordLoader.encode,BinaryRationalArithmetic.encode,BinarySignedWords.encode,List.append_assoc]

theorem materialize_address (a : ℕ) (code history : List Symbol) :
    let start : BinaryCodeWordLoader.State :=
      ⟨.reading,RationalProgramCode.address a++code,history,[],[]⟩
    BinaryCodeWordLoader.advance (2*a+2) start =
      ⟨.halt,code,(RationalProgramCode.address a).reverse++history,[],List.replicate a false⟩ ∧
    BinaryCodeWordLoader.bitSteps (2*a+2) start ≤ 18*a+18 :=
  BinaryCodeWordLoader.binary_unary_address_load a code history

theorem materialize_rational (q : ℚ) (code history : List Symbol) :
    ∃ n,
      let segment := BinaryCodeLiteralLoader.encode (BinaryRationalArithmetic.encode q)
      let start := BinaryCodeLiteralLoader.initial (segment++code) history
      (BinaryCodeLiteralLoader.advance n start).phase = .halt ∧
      (BinaryCodeLiteralLoader.advance n start).code = code ∧
      (BinaryCodeLiteralLoader.advance n start).history = segment.reverse++history ∧
      (BinaryCodeLiteralLoader.advance n start).temp = [] ∧
      BinaryCodeLiteralLoader.output (BinaryCodeLiteralLoader.advance n start) = BinaryRationalArithmetic.encode q ∧
      BinaryCodeLiteralLoader.bitSteps n start ≤ 20*rationalEncodingLength q+80 := by
  obtain ⟨n,_,hr,hc⟩ := BinaryCodeLiteralLoader.binary_literal_load (BinaryRationalArithmetic.encode q) code history
  refine ⟨n,?_,?_,?_,?_,?_,?_⟩
  · rw [hr]
  · rw [hr]
  · rw [hr]
  · rw [hr]
  · rw [hr]
    rfl
  · have hl := BinaryRationalArithmetic.encode_length q
    simp only [BinaryRationalArithmetic.Word.length] at hl
    omega

theorem materialize_tag (a b c : Bool) (code history : List Symbol) :
    BinaryCodeTagDecoder.advance 4 (BinaryCodeTagDecoder.initial (RationalProgramCode.tag a b c++code) history) =
      ⟨.halt,code,(RationalProgramCode.tag a b c).reverse++history,a,b,c⟩ ∧
    BinaryCodeTagDecoder.bitSteps 4 (BinaryCodeTagDecoder.initial (RationalProgramCode.tag a b c++code) history) = 28 :=
  BinaryCodeTagDecoder.binary_code_tag_decode a b c code history

end IdentityTesting.BinaryCodeMaterialization
