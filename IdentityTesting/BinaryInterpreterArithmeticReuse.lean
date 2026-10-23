import IdentityTesting.BinaryInterpreterArithmeticGrowth
import IdentityTesting.BinaryInterpreterArithmeticBound

/-! Rearming preserves every physical stack and resets only the finite control.
Address materialization and program dispatch are separate machines. -/
namespace IdentityTesting.BinaryInterpreterArithmetic
open BinaryInterpreterLayout BinaryInterpreterStorage
open scoped BigOperators
variable {L : Layout} (W : Storage L)

theorem initial_tapes_empty (i : Fin W.count) :
    W.tapes (L.initial emptyWord emptyWord) i = [] := by
  have h := Finset.single_le_sum (fun (j : Fin W.count) (_ : j ∈ Finset.univ) =>
    Nat.zero_le (W.tapes (L.initial emptyWord emptyWord) j).length) (Finset.mem_univ i)
  rw [W.tapes_cells] at h
  have hz : W.cells (L.initial emptyWord emptyWord) = 0 := W.initial_cells
  rw [hz] at h
  exact List.length_eq_zero.mp (Nat.eq_zero_of_le_zero h)

def rearm (s : State L) : State L :=
  {s with
    phase := .left
    core := W.setTapes (L.initial emptyWord emptyWord) (W.tapes s.core)
    negative := false
    readPhase := .reading
    seekPhase := .seek
    splitPhase := .sign
    storePhase := .joining
    joinPhase := .denCollect
    writePhase := .seek}

theorem rearm_preserves_arithmetic_tapes (s : State L) :
    W.tapes (rearm W s).core = W.tapes s.core := W.tapes_set _ _

theorem rearm_preserves_io_tapes (s : State L) :
    (rearm W s).tape = s.tape ∧ (rearm W s).leftAddress = s.leftAddress ∧
    (rearm W s).rightAddress = s.rightAddress ∧ (rearm W s).destination = s.destination ∧
    (rearm W s).saved = s.saved ∧ (rearm W s).copyTemp = s.copyTemp ∧
    (rearm W s).record = s.record ∧ (rearm W s).numWork = s.numWork ∧ (rearm W s).denWork = s.denWork := by
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem rearm_clean_state (s : State L) (hi : CleanIO s) (ha : ∀ i, W.tapes s.core i = []) :
    rearm W s = initial L s.tape [] [] [] := by
  have ht : W.tapes s.core = W.tapes (L.initial emptyWord emptyWord) := by
    funext i
    rw [ha i,initial_tapes_empty W i]
  have hc : W.setTapes (L.initial emptyWord emptyWord) (W.tapes s.core) =
      L.initial emptyWord emptyWord := by
    rw [ht,W.set_tapes]
  rcases hi with ⟨hl,hr,hd,hs,ht',hw,hn,hdw⟩
  simp [rearm,initial,hc,hl,hr,hd,hs,ht',hw,hn,hdw]

end IdentityTesting.BinaryInterpreterArithmetic
