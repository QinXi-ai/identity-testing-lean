import IdentityTesting.BinaryInterpreterArithmeticGrowth

namespace IdentityTesting.BinaryInterpreterArithmeticClean
open BinaryInterpreterLayout BinaryInterpreterStorage

inductive Phase where
  | running | cleaning | halt
  deriving DecidableEq, Repr

variable {L : Layout} (W : Storage L)

structure State where
  phase : Phase
  core : BinaryInterpreterArithmetic.State L
  cursor : Fin (W.count+1)

def storage (s : State W) : BinaryInterpreterStorage.State W := ⟨s.cursor,s.core.core⟩
def setStorage (s : State W) (w : BinaryInterpreterStorage.State W) : State W :=
  {s with core := {s.core with core := w.core}, cursor := w.cursor}

def step (s : State W) : State W :=
  match s.phase with
  | .running => if s.core.phase = .halt then {s with phase := .cleaning}
      else {s with core := BinaryInterpreterArithmetic.step s.core}
  | .cleaning => if s.cursor.val = 0 then {s with phase := .halt}
      else setStorage W s (BinaryInterpreterStorage.step W (storage W s))
  | .halt => s

def transitionTrace (s : State W) : List BinaryArithmetic.BitOp :=
  match s.phase with
  | .running => if s.core.phase = .halt then [.branch]
      else .branch :: BinaryInterpreterArithmetic.transitionTrace s.core
  | .cleaning => if s.cursor.val = 0 then [.branch]
      else .branch :: BinaryInterpreterStorage.transitionTrace W (storage W s)
  | .halt => []

def advance : ℕ → State W → State W
  | 0,s => s
  | n+1,s => advance n (step W s)
def bitSteps : ℕ → State W → ℕ
  | 0,_ => 0
  | n+1,s => (transitionTrace W s).length + bitSteps n (step W s)

theorem advance_add (m n : ℕ) (s : State W) : advance W (m+n) s = advance W n (advance W m s) := by
  induction m generalizing s with
  | zero => simp [advance]
  | succ m ih => simpa [Nat.succ_add,advance] using ih (step W s)

theorem bitSteps_add (m n : ℕ) (s : State W) :
    bitSteps W (m+n) s = bitSteps W m s+bitSteps W n (advance W m s) := by
  induction m generalizing s with
  | zero => simp [advance,bitSteps]
  | succ m ih => simp [Nat.succ_add,advance,bitSteps,ih,Nat.add_assoc]

def runningState (r : BinaryInterpreterArithmetic.State L) : State W := ⟨.running,r,⟨W.count,by omega⟩⟩
def cleaningState (frame : BinaryInterpreterArithmetic.State L) (s : BinaryInterpreterStorage.State W) : State W :=
  ⟨.cleaning,{frame with core := s.core},s.cursor⟩

theorem arithmetic_halt (n : ℕ) (s : BinaryInterpreterArithmetic.State L) (h : s.phase = .halt) :
    BinaryInterpreterArithmetic.advance n s = s := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [BinaryInterpreterArithmetic.advance,BinaryInterpreterArithmetic.step,h] using ih

theorem forward_running (r : BinaryInterpreterArithmetic.State L) (n : ℕ)
    (h : (BinaryInterpreterArithmetic.advance n r).phase = .halt) :
    ∃ k, k ≤ n+1 ∧ advance W k (runningState W r) =
      cleaningState W (BinaryInterpreterArithmetic.advance n r)
        (BinaryInterpreterStorage.initial W (BinaryInterpreterArithmetic.advance n r).core) ∧
      bitSteps W k (runningState W r) ≤ 2*BinaryInterpreterArithmetic.bitSteps n r+1 := by
  induction n generalizing r with
  | zero =>
    simp only [BinaryInterpreterArithmetic.advance] at h ⊢
    refine ⟨1,by omega,?_,?_⟩
    · simp [advance,step,runningState,cleaningState,BinaryInterpreterStorage.initial,h]
      cases r
      simp_all
    · simp [bitSteps,transitionTrace,runningState,h,BinaryInterpreterArithmetic.bitSteps]
  | succ n ih =>
    by_cases hh : r.phase = .halt
    · rw [arithmetic_halt (n+1) r hh]
      refine ⟨1,by omega,?_,?_⟩
      · simp [advance,step,runningState,cleaningState,BinaryInterpreterStorage.initial,hh]
        cases r
        simp_all
      · simp [bitSteps,transitionTrace,runningState,hh]
    · obtain ⟨k,hk,he,hc⟩ := ih (BinaryInterpreterArithmetic.step r) h
      refine ⟨k+1,by omega,?_,?_⟩
      · rw [advance]
        simpa [step,runningState,hh,BinaryInterpreterArithmetic.advance] using he
      · have ht : 1 ≤ (BinaryInterpreterArithmetic.transitionTrace r).length := by
          cases hp : r.phase <;> simp_all [BinaryInterpreterArithmetic.transitionTrace]
          all_goals split <;> simp_all
        simp only [bitSteps,transitionTrace,step,runningState,if_neg hh,List.length_cons,
          BinaryInterpreterArithmetic.bitSteps]
        change (BinaryInterpreterArithmetic.transitionTrace r).length+1+
          bitSteps W k (runningState W (BinaryInterpreterArithmetic.step r)) ≤ _
        omega

theorem storage_halt (n : ℕ) (s : BinaryInterpreterStorage.State W) (h : s.cursor.val = 0) :
    BinaryInterpreterStorage.advance W n s = s := by
  have hs : BinaryInterpreterStorage.step W s = s := by
    simp [BinaryInterpreterStorage.step,BinaryInterpreterStorage.view,
      BinaryWorkspaceCleanup.step,h,W.set_tapes]
  induction n with
  | zero => rfl
  | succ n ih => simpa [BinaryInterpreterStorage.advance,hs] using ih

theorem forward_cleaning (frame : BinaryInterpreterArithmetic.State L) (s : BinaryInterpreterStorage.State W)
    (n : ℕ) (h : (BinaryInterpreterStorage.advance W n s).cursor.val = 0) :
    ∃ k, k ≤ n+1 ∧ advance W k (cleaningState W frame s) =
      {cleaningState W frame (BinaryInterpreterStorage.advance W n s) with phase := .halt} ∧
      bitSteps W k (cleaningState W frame s) ≤ 2*BinaryInterpreterStorage.bitSteps W n s+1 := by
  induction n generalizing s with
  | zero =>
    simp only [BinaryInterpreterStorage.advance] at h ⊢
    refine ⟨1,by omega,?_,?_⟩
    · simp [advance,step,cleaningState,h]
    · simp [bitSteps,transitionTrace,cleaningState,h,BinaryInterpreterStorage.bitSteps]
  | succ n ih =>
    by_cases hh : s.cursor.val = 0
    · rw [storage_halt W (n+1) s hh]
      refine ⟨1,by omega,?_,?_⟩
      · simp [advance,step,cleaningState,hh]
      · simp [bitSteps,transitionTrace,cleaningState,hh]
    · obtain ⟨k,hk,he,hc⟩ := ih (BinaryInterpreterStorage.step W s) h
      refine ⟨k+1,by omega,?_,?_⟩
      · rw [advance]
        simpa [step,cleaningState,setStorage,storage,hh,BinaryInterpreterStorage.advance] using he
      · have ht : 1 ≤ (BinaryInterpreterStorage.transitionTrace W s).length := by
          simp only [BinaryInterpreterStorage.transitionTrace,BinaryInterpreterStorage.view,
            BinaryWorkspaceCleanup.transitionTrace,dif_neg hh]
          split <;> simp
        simp only [bitSteps,transitionTrace,step,cleaningState,if_neg hh,List.length_cons,
          BinaryInterpreterStorage.bitSteps]
        change (BinaryInterpreterStorage.transitionTrace W s).length+1+
          bitSteps W k (cleaningState W frame (BinaryInterpreterStorage.step W s)) ≤ _
        omega

end IdentityTesting.BinaryInterpreterArithmeticClean
