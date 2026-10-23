import IdentityTesting.BinaryInterpreterMultiplyBound
import IdentityTesting.BinaryInterpreterMultiplyGrowth
import IdentityTesting.BinaryMultiplierStorage

/-! The multiplication instruction followed by actual cleanup of its 69
arithmetic stacks. The register tape and all IO stacks are preserved as a frame.
The cleanup writes back through the inverse physical-stack layout. -/
namespace IdentityTesting.BinaryInterpreterMultiplyClean
open BinaryWorkspaceAdapters

inductive Phase where
  | running | cleaning | halt
  deriving DecidableEq, Repr

structure State where
  phase : Phase
  core : BinaryInterpreterMultiply.State
  cursor : Fin 70

def storage (s : State) : BinaryMultiplierStorage.State := ⟨s.cursor, s.core.core⟩
def setStorage (s : State) (w : BinaryMultiplierStorage.State) : State :=
  {s with core := {s.core with core := w.core}, cursor := w.cursor}

def step (s : State) : State :=
  match s.phase with
  | .running => if s.core.phase = .halt then {s with phase := .cleaning}
      else {s with core := BinaryInterpreterMultiply.step s.core}
  | .cleaning => if s.cursor.val = 0 then {s with phase := .halt}
      else setStorage s (BinaryMultiplierStorage.step (storage s))
  | .halt => s

def transitionTrace (s : State) : List BinaryArithmetic.BitOp :=
  match s.phase with
  | .running => if s.core.phase = .halt then [.branch]
      else .branch :: BinaryInterpreterMultiply.transitionTrace s.core
  | .cleaning => if s.cursor.val = 0 then [.branch]
      else .branch :: BinaryMultiplierStorage.transitionTrace (storage s)
  | .halt => []

def advance : ℕ → State → State
  | 0,s => s
  | n+1,s => advance n (step s)
def bitSteps : ℕ → State → ℕ
  | 0,_ => 0
  | n+1,s => (transitionTrace s).length + bitSteps n (step s)

theorem advance_add (m n : ℕ) (s : State) : advance (m+n) s = advance n (advance m s) := by
  induction m generalizing s with
  | zero => simp [advance]
  | succ m ih => simpa [Nat.succ_add, advance] using ih (step s)

theorem bitSteps_add (m n : ℕ) (s : State) :
    bitSteps (m+n) s = bitSteps m s + bitSteps n (advance m s) := by
  induction m generalizing s with
  | zero => simp [advance, bitSteps]
  | succ m ih => simp [Nat.succ_add, advance, bitSteps, ih, Nat.add_assoc]

def runningState (r : BinaryInterpreterMultiply.State) : State := ⟨.running, r, ⟨69, by omega⟩⟩
def cleaningState (frame : BinaryInterpreterMultiply.State) (s : BinaryMultiplierStorage.State) : State :=
  ⟨.cleaning, {frame with core := s.core}, s.cursor⟩

theorem multiply_halt (n : ℕ) (s : BinaryInterpreterMultiply.State) (h : s.phase = .halt) :
    BinaryInterpreterMultiply.advance n s = s := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [BinaryInterpreterMultiply.advance, BinaryInterpreterMultiply.step, h] using ih

theorem forward_running (r : BinaryInterpreterMultiply.State) (n : ℕ)
    (h : (BinaryInterpreterMultiply.advance n r).phase = .halt) :
    ∃ k, k ≤ n+1 ∧ advance k (runningState r) =
      cleaningState (BinaryInterpreterMultiply.advance n r)
        (BinaryMultiplierStorage.initial (BinaryInterpreterMultiply.advance n r).core) ∧
      bitSteps k (runningState r) ≤ 2*BinaryInterpreterMultiply.bitSteps n r+1 := by
  induction n generalizing r with
  | zero =>
    simp only [BinaryInterpreterMultiply.advance] at h ⊢
    refine ⟨1, by omega, ?_, ?_⟩
    · simp [advance, step, runningState, cleaningState, BinaryMultiplierStorage.initial, h]
      cases r
      simp_all
    · simp [bitSteps, transitionTrace, runningState, h, BinaryInterpreterMultiply.bitSteps]
  | succ n ih =>
    by_cases hh : r.phase = .halt
    · rw [multiply_halt (n+1) r hh]
      refine ⟨1, by omega, ?_, ?_⟩
      · simp [advance, step, runningState, cleaningState, BinaryMultiplierStorage.initial, hh]
        cases r
        simp_all
      · simp [bitSteps, transitionTrace, runningState, hh]
    · obtain ⟨k, hk, he, hc⟩ := ih (BinaryInterpreterMultiply.step r) h
      refine ⟨k+1, by omega, ?_, ?_⟩
      · rw [advance]
        simpa [step, runningState, hh, BinaryInterpreterMultiply.advance] using he
      · have ht : 1 ≤ (BinaryInterpreterMultiply.transitionTrace r).length := by
          cases hp : r.phase <;> simp_all [BinaryInterpreterMultiply.transitionTrace]
          all_goals split <;> simp_all
        simp only [bitSteps, transitionTrace, step, runningState, if_neg hh, List.length_cons,
          BinaryInterpreterMultiply.bitSteps]
        change (BinaryInterpreterMultiply.transitionTrace r).length+1+
          bitSteps k (runningState (BinaryInterpreterMultiply.step r)) ≤ _
        omega

theorem storage_halt (n : ℕ) (s : BinaryMultiplierStorage.State) (h : s.cursor.val = 0) :
    BinaryMultiplierStorage.advance n s = s := by
  have hs : BinaryMultiplierStorage.step s = s := by
    simp [BinaryMultiplierStorage.step, BinaryMultiplierStorage.view,
      BinaryWorkspaceCleanup.step, h, BinaryMultiplierStorage.set_tapes]
  induction n with
  | zero => rfl
  | succ n ih => simpa [BinaryMultiplierStorage.advance, hs] using ih

theorem forward_cleaning (frame : BinaryInterpreterMultiply.State) (s : BinaryMultiplierStorage.State)
    (n : ℕ) (h : (BinaryMultiplierStorage.advance n s).cursor.val = 0) :
    ∃ k, k ≤ n+1 ∧ advance k (cleaningState frame s) =
      {cleaningState frame (BinaryMultiplierStorage.advance n s) with phase := .halt} ∧
      bitSteps k (cleaningState frame s) ≤ 2*BinaryMultiplierStorage.bitSteps n s+1 := by
  induction n generalizing s with
  | zero =>
    simp only [BinaryMultiplierStorage.advance] at h ⊢
    refine ⟨1, by omega, ?_, ?_⟩
    · simp [advance, step, cleaningState, h]
    · simp [bitSteps, transitionTrace, cleaningState, h, BinaryMultiplierStorage.bitSteps]
  | succ n ih =>
    by_cases hh : s.cursor.val = 0
    · rw [storage_halt (n+1) s hh]
      refine ⟨1, by omega, ?_, ?_⟩
      · simp [advance, step, cleaningState, hh]
      · simp [bitSteps, transitionTrace, cleaningState, hh]
    · obtain ⟨k, hk, he, hc⟩ := ih (BinaryMultiplierStorage.step s) h
      refine ⟨k+1, by omega, ?_, ?_⟩
      · rw [advance]
        simpa [step, cleaningState, setStorage, storage, hh, BinaryMultiplierStorage.advance] using he
      · have ht : 1 ≤ (BinaryMultiplierStorage.transitionTrace s).length := by
          simp only [BinaryMultiplierStorage.transitionTrace, BinaryMultiplierStorage.view,
            BinaryWorkspaceCleanup.transitionTrace, dif_neg hh]
          split <;> simp
        simp only [bitSteps, transitionTrace, step, cleaningState, if_neg hh, List.length_cons,
          BinaryMultiplierStorage.bitSteps]
        change (BinaryMultiplierStorage.transitionTrace s).length+1+
          bitSteps k (cleaningState frame (BinaryMultiplierStorage.step s)) ≤ _
        omega

end IdentityTesting.BinaryInterpreterMultiplyClean
