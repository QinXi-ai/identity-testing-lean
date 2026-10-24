import IdentityTesting.BinaryInterpreterCeilSizeRuns
import IdentityTesting.BinaryInterpreterCeilSizeStorage
import IdentityTesting.BinaryInterpreterArithmeticCleanBound
import IdentityTesting.BinaryInterpreterArithmeticReuse

namespace IdentityTesting.BinaryInterpreterCeilSize
open BinaryRationalRegisters RationalComputation

/-- The source is read twice by the shared two-input loader. The auxiliary
word and all 29 ceiling-machine stacks are physically cleared after writeback;
the extra load and cleanup are included in this bound. -/
theorem binary_register_ceilSize_with_cleanup (s : RationalRegisters) (a dst : ℕ)
    (ha : a < s.length) (hd : dst < s.length) :
    ∃ n,
      let start := BinaryInterpreterArithmeticClean.runningState storage
        (BinaryInterpreterArithmetic.initial layout (tape s)
          (List.replicate a false) (List.replicate a false) (List.replicate dst false))
      let final := BinaryInterpreterArithmeticClean.advance storage n start
      final.phase = .halt ∧
      final.core.tape = tape (s.set dst ((Nat.ceil s[a]).size : ℚ)) ∧
      BinaryInterpreterArithmetic.CleanIO final.core ∧
      (∀ i, storage.tapes final.core.core i = []) ∧
      BinaryInterpreterArithmeticClean.bitSteps storage n start ≤
        2400 * (rationalRegisterEncoding s + s.length) +
        9000000 * (rationalEncodingLength s[a] + 1)^2 := by
  obtain ⟨n, hh, ht, hi, hc⟩ := binary_register_ceilSize s a dst ha hd
  obtain ⟨k, hk, hkt, hki, hclear, hcost⟩ :=
    BinaryInterpreterArithmeticClean.cleanup_run storage _ n hh
  refine ⟨k, hk, hkt.trans ht, hki hi, hclear, ?_⟩
  have hz : storage.cells
      (BinaryInterpreterArithmetic.initial layout (tape s)
        (List.replicate a false) (List.replicate a false) (List.replicate dst false)).core = 0 :=
    storage.initial_cells
  rw [hz] at hcost
  change _ ≤ 8 * _ + 6 * (31 + 0) + 2 at hcost
  have hQ : 1 ≤ (rationalEncodingLength s[a] + 1)^2 := by
    nlinarith [Nat.zero_le (rationalEncodingLength s[a])]
  nlinarith only [hc, hcost, hQ]

theorem rearm_clean (s : BinaryInterpreterArithmetic.State layout)
    (hi : BinaryInterpreterArithmetic.CleanIO s) (hc : ∀ i, storage.tapes s.core i = []) :
    BinaryInterpreterArithmetic.rearm storage s =
      BinaryInterpreterArithmetic.initial layout s.tape [] [] [] :=
  BinaryInterpreterArithmetic.rearm_clean_state storage s hi hc

end IdentityTesting.BinaryInterpreterCeilSize
