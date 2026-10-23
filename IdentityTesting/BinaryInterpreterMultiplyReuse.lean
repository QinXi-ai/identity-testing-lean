import IdentityTesting.BinaryInterpreterMultiplyBound
import IdentityTesting.BinaryMultiplierStorage

/-! Reset only the fixed finite control of a cleaned multiplication instruction.
Every physical stack is preserved by the inverse layout; no word is erased or
copied by this reset. The address tapes are populated separately by dispatch. -/
namespace IdentityTesting.BinaryInterpreterMultiply

def rearm (s : State) : State :=
  {s with
    phase := .left
    core := BinaryMultiplierStorage.setTapes
      (BinaryRationalArithmeticMultiplier.initial emptyWord emptyWord)
      (BinaryMultiplierStorage.tapes s.core)
    readPhase := .reading
    seekPhase := .seek
    splitPhase := .sign
    storePhase := .joining
    joinPhase := .denCollect
    writePhase := .seek}

theorem rearm_preserves_arithmetic_tapes (s : State) :
    BinaryMultiplierStorage.tapes (rearm s).core = BinaryMultiplierStorage.tapes s.core := by
  exact BinaryMultiplierStorage.tapes_set _ _

theorem rearm_preserves_io_tapes (s : State) :
    (rearm s).tape = s.tape ∧ (rearm s).leftAddress = s.leftAddress ∧
    (rearm s).rightAddress = s.rightAddress ∧ (rearm s).destination = s.destination ∧
    (rearm s).saved = s.saved ∧ (rearm s).copyTemp = s.copyTemp ∧
    (rearm s).record = s.record ∧ (rearm s).numWork = s.numWork ∧ (rearm s).denWork = s.denWork := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem rearm_clean_state (s : State) (hi : CleanIO s)
    (ha : ∀ i, BinaryMultiplierStorage.tapes s.core i = []) :
    rearm s = initial s.tape [] [] [] := by
  have ht : BinaryMultiplierStorage.tapes s.core = fun _ => [] := funext ha
  have hc : BinaryMultiplierStorage.setTapes
      (BinaryRationalArithmeticMultiplier.initial emptyWord emptyWord)
      (BinaryMultiplierStorage.tapes s.core) =
      BinaryRationalArithmeticMultiplier.initial emptyWord emptyWord := by
    rw [ht]
    rfl
  rcases hi with ⟨hl, hr, hd, hs, ht', hw, hn, hdw⟩
  simp [rearm, initial, hc, hl, hr, hd, hs, ht', hw, hn, hdw]

end IdentityTesting.BinaryInterpreterMultiply
