import IdentityTesting.BinaryRegisterMachine

/-! A stack of saved binary countdown words. Saving inserts a delimiter then
moves one counter bit per transition. Restoring consumes one saved bit per
transition and stops at that delimiter. No transition copies a whole word.
The temporary stack is retained, untouched, for the surrounding counter machine. -/
namespace IdentityTesting.BinaryCounterStack
open BinaryRegisterMachine BinaryArithmetic

inductive Phase where
  | mark | saving | restoring | halt | invalid
  deriving DecidableEq, Repr

structure State where
  phase : Phase
  counter : List Bool
  saved : List Symbol
  temp : List Bool
  deriving DecidableEq, Repr

def step (s : State) : State :=
  match s.phase with
  | .mark => {s with phase := .saving,saved := .boundary :: s.saved}
  | .saving => match s.counter with
      | [] => {s with phase := .halt}
      | b::bs => {s with counter := bs,saved := .cell (.bit b) :: s.saved}
  | .restoring => match s.saved with
      | .cell (.bit b)::ss => {s with counter := b::s.counter,saved := ss}
      | .boundary::ss => {s with phase := .halt,saved := ss}
      | _ => {s with phase := .invalid}
  | .halt | .invalid => s

def transitionTrace (s : State) : List BitOp :=
  match s.phase with
  | .mark => [.writeCell,.writeCell,.moveHead]
  | .saving => match s.counter with
      | [] => [.readCell,.branch]
      | _::_ => [.readCell,.branch,.moveHead,.writeCell,.writeCell,.moveHead]
  | .restoring => match s.saved with
      | .cell (.bit _)::_ => [.readCell,.readCell,.branch,.moveHead,.writeCell,.moveHead]
      | .boundary::_ => [.readCell,.readCell,.branch,.moveHead]
      | _ => [.readCell,.readCell,.branch]
  | .halt | .invalid => []

def advance : ℕ → State → State
  | 0,s => s
  | n+1,s => advance n (step s)
def bitSteps : ℕ → State → ℕ
  | 0,_ => 0
  | n+1,s => (transitionTrace s).length+bitSteps n (step s)

def initialSave (counter : List Bool) (saved : List Symbol) : State := ⟨.mark,counter,saved,[]⟩
def initialRestore (saved : List Symbol) : State := ⟨.restoring,[],saved,[]⟩
def haltState (counter : List Bool) (saved : List Symbol) : State := ⟨.halt,counter,saved,[]⟩
def rearmSave (s : State) : State := {s with phase := .mark}
def rearmRestore (s : State) : State := {s with phase := .restoring}

/-- Specification of the saved layout, not an executable whole-word action. -/
def frame (bits : List Bool) (suffix : List Symbol) : List Symbol :=
  bits.reverse.map (fun b => Symbol.cell (.bit b)) ++ .boundary :: suffix

theorem rearm_preserves_stacks (s : State) :
    (rearmSave s).counter = s.counter ∧ (rearmSave s).saved = s.saved ∧ (rearmSave s).temp = s.temp ∧
    (rearmRestore s).counter = s.counter ∧ (rearmRestore s).saved = s.saved ∧ (rearmRestore s).temp = s.temp :=
  ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem step_preserves_temp (s : State) : (step s).temp = s.temp := by
  cases hp:s.phase <;> simp only [step,hp]
  all_goals (repeat' first | split | rfl)

theorem advance_preserves_temp (n : ℕ) (s : State) : (advance n s).temp = s.temp := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih => simpa only [advance,step_preserves_temp] using ih (step s)

theorem advance_add (m n : ℕ) (s : State) : advance (m+n) s=advance n (advance m s) := by
  induction m generalizing s with
  | zero => simp [advance]
  | succ m ih => simpa [Nat.succ_add,advance] using ih (step s)

end IdentityTesting.BinaryCounterStack
