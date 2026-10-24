import IdentityTesting.BinaryInterpreterOperandExecuteInstances

/-! A read-only branch comparison. The operand loader, comparison operation,
and physical cleanup all share pair.loader.data.core. Only the first bit of
the canonical 0/1 output is retained in finite control; no register is written. -/
namespace IdentityTesting.BinaryInterpreterBranchCompare
open BinaryRegisterMachine BinaryInterpreterLayout BinaryInterpreterArithmetic

abbrev layout : Layout := arithmeticLayout .le
abbrev storage : BinaryInterpreterStorage.Storage layout := arithmeticStorage .le
abbrev Pair := BinaryInterpreterOperandPair.State layout
abbrev Core := layout.Core

inductive Phase where
  | loading | operating | decision | clearing | halt
  deriving DecidableEq, Repr

structure State where
  phase : Phase
  pair : Pair
  decision : Bool
  cursor : Fin (storage.count+1)

def pairCore (p : Pair) : Core := p.loader.data.core
def setPairCore (p : Pair) (c : Core) : Pair :=
  {p with loader := {p.loader with data := {p.loader.data with core := c}}}
def core (s : State) : Core := pairCore s.pair
def setCore (s : State) (c : Core) : State := {s with pair := setPairCore s.pair c}
def readDecision (c : Core) : Bool := (layout.output c).numerator.magnitude.headD false

def storageView (s : State) : BinaryInterpreterStorage.State storage := ⟨s.cursor,core s⟩
def setStorage (s : State) (w : BinaryInterpreterStorage.State storage) : State :=
  {setCore s w.core with cursor := w.cursor}

def step (s : State) : State :=
  match s.phase with
  | .loading => if s.pair.phase = .halt then {s with phase := .operating}
      else {s with pair := BinaryInterpreterOperandPair.step s.pair}
  | .operating => if layout.halted (core s) then {s with phase := .decision}
      else setCore s (layout.step (core s))
  | .decision => {s with phase := .clearing,decision := readDecision (core s)}
  | .clearing => if s.cursor.val = 0 then {s with phase := .halt}
      else setStorage s (BinaryInterpreterStorage.step storage (storageView s))
  | .halt => s

def transitionTrace (s : State) : List BinaryArithmetic.BitOp :=
  match s.phase with
  | .loading => if s.pair.phase = .halt then [.branch]
      else .branch :: BinaryInterpreterOperandPair.transitionTrace s.pair
  | .operating => if layout.halted (core s) then [.branch]
      else .branch :: layout.trace (core s)
  | .decision => [.readCell,.branch]
  | .clearing => if s.cursor.val = 0 then [.branch]
      else .branch :: BinaryInterpreterStorage.transitionTrace storage (storageView s)
  | .halt => []

def advance : ℕ → State → State
  | 0,s => s
  | n+1,s => advance n (step s)
def bitSteps : ℕ → State → ℕ
  | 0,_ => 0
  | n+1,s => (transitionTrace s).length+bitSteps n (step s)

def loadingState (p : Pair) : State := ⟨.loading,p,false,⟨storage.count,by omega⟩⟩
def operatingState (p : Pair) (c : Core) : State := ⟨.operating,setPairCore p c,false,⟨storage.count,by omega⟩⟩
def decisionState (p : Pair) (c : Core) : State := ⟨.decision,setPairCore p c,false,⟨storage.count,by omega⟩⟩
def clearingState (p : Pair) (decision : Bool) (w : BinaryInterpreterStorage.State storage) : State :=
  ⟨.clearing,setPairCore p w.core,decision,w.cursor⟩
def initial (tape code history : List Symbol) : State :=
  loadingState (BinaryInterpreterOperandPair.initial layout tape code history)

theorem setPairCore_self (p : Pair) : setPairCore p (pairCore p) = p := rfl
theorem setPairCore_set (p : Pair) (c d : Core) : setPairCore (setPairCore p c) d = setPairCore p d := rfl
theorem setCore_preserves (s : State) (c : Core) :
    (setCore s c).pair.loader.tape = s.pair.loader.tape ∧
    (setCore s c).pair.loader.data.code = s.pair.loader.data.code ∧
    (setCore s c).pair.loader.data.history = s.pair.loader.data.history ∧
    (setCore s c).decision = s.decision ∧
    (BinaryInterpreterOperand.Clean (setCore s c).pair.loader ↔ BinaryInterpreterOperand.Clean s.pair.loader) :=
  ⟨rfl,rfl,rfl,rfl,Iff.rfl⟩

theorem advance_add (m n : ℕ) (s : State) : advance (m+n) s=advance n (advance m s) := by
  induction m generalizing s with
  | zero => simp [advance]
  | succ m ih => simpa [Nat.succ_add,advance] using ih (step s)
theorem bitSteps_add (m n : ℕ) (s : State) : bitSteps (m+n) s=bitSteps m s+bitSteps n (advance m s) := by
  induction m generalizing s with
  | zero => simp [advance,bitSteps]
  | succ m ih => simp [Nat.succ_add,advance,bitSteps,ih,Nat.add_assoc]

end IdentityTesting.BinaryInterpreterBranchCompare
