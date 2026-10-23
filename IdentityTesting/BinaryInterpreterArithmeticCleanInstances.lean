import IdentityTesting.BinaryInterpreterArithmeticCleanBound
import IdentityTesting.BinaryInterpreterArithmeticStorage

namespace IdentityTesting.BinaryInterpreterArithmeticClean
open BinaryRationalRegisters RationalComputation BinaryInterpreterArithmetic

def initial (op : RationalOp) (tape : List BinaryRegisterMachine.Symbol) (a b dst : List Bool) :
    State (arithmeticStorage op) :=
  runningState (arithmeticStorage op) (BinaryInterpreterArithmetic.initial (arithmeticLayout op) tape a b dst)

theorem binary_register_instruction_with_cleanup (op : RationalOp) (s : RationalRegisters) (a b dst : ℕ)
    (ha : a < s.length) (hb : b < s.length) (hd : dst < s.length) :
    ∃ n,
      let W := arithmeticStorage op
      let start := initial op (tape s) (List.replicate a false) (List.replicate b false) (List.replicate dst false)
      (advance W n start).phase = .halt ∧
      (advance W n start).core.tape = tape ((registerInstruction op a b dst).exec s) ∧
      CleanIO (advance W n start).core ∧
      (∀ i, W.tapes (advance W n start).core.core i = []) ∧
      bitSteps W n start ≤ 3000*(rationalRegisterEncoding s+s.length)+
        100000000*(rationalEncodingLength s[a]+rationalEncodingLength s[b]+1)^3 := by
  let W := arithmeticStorage op
  let r := BinaryInterpreterArithmetic.initial (arithmeticLayout op) (tape s) (List.replicate a false)
    (List.replicate b false) (List.replicate dst false)
  obtain ⟨n,hh,ht,hio,hc⟩ := binary_register_instruction op s a b dst ha hb hd
  change (BinaryInterpreterArithmetic.advance n r).phase = .halt at hh
  change (BinaryInterpreterArithmetic.advance n r).tape = _ at ht
  change CleanIO (BinaryInterpreterArithmetic.advance n r) at hio
  change BinaryInterpreterArithmetic.bitSteps n r ≤ _ at hc
  obtain ⟨k,hk,hkt,hki,hclean,hcost⟩ := cleanup_run W r n hh
  refine ⟨k,hk,hkt.trans ht,hki hio,hclean,?_⟩
  have hzero : W.cells r.core = 0 := W.initial_cells
  have hcount := arithmeticStorage_count op
  change W.count ≤ 96 at hcount
  rw [hzero,add_zero] at hcost
  let S := rationalEncodingLength s[a]+rationalEncodingLength s[b]+1
  have hpos : 0 < S^3 := by dsimp [S]; positivity
  have hone : 1 ≤ S^3 := by omega
  change BinaryInterpreterArithmetic.bitSteps n r ≤
    300*(rationalRegisterEncoding s+s.length)+12000000*S^3 at hc
  change bitSteps W k (runningState W r) ≤
    3000*(rationalRegisterEncoding s+s.length)+100000000*S^3
  nlinarith only [hcost,hcount,hc,hone]

end IdentityTesting.BinaryInterpreterArithmeticClean
