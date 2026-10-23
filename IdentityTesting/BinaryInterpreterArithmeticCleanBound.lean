import IdentityTesting.BinaryInterpreterArithmeticClean
import IdentityTesting.BinaryInterpreterArithmeticBound

namespace IdentityTesting.BinaryInterpreterArithmeticClean
open BinaryInterpreterLayout BinaryInterpreterStorage
variable {L : Layout} (W : Storage L)

theorem cleanup_run (r : BinaryInterpreterArithmetic.State L) (n : ℕ)
    (hh : (BinaryInterpreterArithmetic.advance n r).phase = .halt) :
    ∃ k, (advance W k (runningState W r)).phase = .halt ∧
      (advance W k (runningState W r)).core.tape = (BinaryInterpreterArithmetic.advance n r).tape ∧
      (BinaryInterpreterArithmetic.CleanIO (BinaryInterpreterArithmetic.advance n r) →
        BinaryInterpreterArithmetic.CleanIO (advance W k (runningState W r)).core) ∧
      (∀ i, W.tapes (advance W k (runningState W r)).core.core i = []) ∧
      bitSteps W k (runningState W r) ≤ 8*BinaryInterpreterArithmetic.bitSteps n r+
        6*(W.count+W.cells r.core)+2 := by
  let final := BinaryInterpreterArithmetic.advance n r
  let count := W.count+W.cells final.core
  have hclear := BinaryInterpreterStorage.clear_all W final.core
  change (BinaryInterpreterStorage.advance W count (BinaryInterpreterStorage.initial W final.core)).cursor.val = 0 ∧
    (∀ i, W.tapes (BinaryInterpreterStorage.advance W count
      (BinaryInterpreterStorage.initial W final.core)).core i = []) ∧
    BinaryInterpreterStorage.bitSteps W count (BinaryInterpreterStorage.initial W final.core) ≤ 3*count at hclear
  obtain ⟨kr,_,hr,hrc⟩ := forward_running W r n hh
  obtain ⟨kc,_,hcr,hcc⟩ := forward_cleaning W final (BinaryInterpreterStorage.initial W final.core) count hclear.1
  have he : advance W (kr+kc) (runningState W r) =
      {cleaningState W final (BinaryInterpreterStorage.advance W count (BinaryInterpreterStorage.initial W final.core))
        with phase := .halt} := by
    rw [advance_add,hr]
    exact hcr
  refine ⟨kr+kc,?_,?_,?_,?_,?_⟩
  · rw [he]
  · rw [he]
    rfl
  · rw [he]
    exact fun h => h
  · rw [he]
    exact hclear.2.1
  · rw [bitSteps_add,hr]
    change bitSteps W kr (runningState W r)+bitSteps W kc (cleaningState W final
      (BinaryInterpreterStorage.initial W final.core)) ≤ _
    have hgrowth := BinaryInterpreterArithmetic.core_advance_cost W n r
    change W.cells final.core ≤ W.cells r.core+BinaryInterpreterArithmetic.bitSteps n r at hgrowth
    have hcCount : count = W.count+W.cells final.core := rfl
    omega

end IdentityTesting.BinaryInterpreterArithmeticClean
