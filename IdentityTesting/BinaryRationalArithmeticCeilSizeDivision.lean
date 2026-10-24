import IdentityTesting.BinaryRationalArithmeticCeilSizeTransport

namespace IdentityTesting.BinaryRationalArithmeticCeilSize
open BinaryArithmetic BinarySubtraction BinaryLongDivision BinaryWordNormalization

theorem division_bounded_run (m n : ℕ) (hn : 0 < n) :
    ∃ steps, (BinaryDivisionMachine.advance steps (BinaryDivisionMachine.initial m.bits n.bits)).phase = .halt ∧
      (BinaryDivisionMachine.advance steps (BinaryDivisionMachine.initial m.bits n.bits)).quot.out = (m/n).bits ∧
      (BinaryDivisionMachine.advance steps (BinaryDivisionMachine.initial m.bits n.bits)).rem.out = (m%n).bits ∧
      steps ≤ 30*(m.size+n.size+1)^2 := by
  obtain ⟨steps,regs,hs,he⟩ := BinaryDivisionMachine.division_run m.bits n.bits
  have hv := divide_binary_inputs m n hn
  have hq : (divide m.bits n.bits).1 = (m/n).bits := by
    have ht := trim_eq_bits (loop m.bits.reverse n.bits [] []).1
    rw [show value (loop m.bits.reverse n.bits [] []).1 = m/n from by
      simpa only [divide,trim_value] using hv.1] at ht
    exact ht
  have hr : (divide m.bits n.bits).2 = (m%n).bits := by
    have ht := trim_eq_bits (loop m.bits.reverse n.bits [] []).2
    rw [show value (loop m.bits.reverse n.bits [] []).2 = m%n from by
      simpa only [divide,trim_value] using hv.2] at ht
    exact ht
  refine ⟨steps,?_,?_,?_,?_⟩
  · rw [show BinaryDivisionMachine.advance steps (BinaryDivisionMachine.initial m.bits n.bits) = _ from he]
    rfl
  · rw [show BinaryDivisionMachine.advance steps (BinaryDivisionMachine.initial m.bits n.bits) = _ from he]
    exact hq
  · rw [show BinaryDivisionMachine.advance steps (BinaryDivisionMachine.initial m.bits n.bits) = _ from he]
    exact hr
  · simpa only [Nat.size_eq_bits_len] using hs

end IdentityTesting.BinaryRationalArithmeticCeilSize
