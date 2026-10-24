import IdentityTesting.BinaryCodeWordLoader

/-! A reserved component symbol marks a loop checkpoint on the history stack.
Rewind restores one program symbol per transition and consumes only that marker.
The marker is not present in the delimited bit-word program alphabet. -/
namespace IdentityTesting.BinaryCodeRewind
open BinaryRegisterMachine BinaryArithmetic

def marker : Symbol := .cell .component

structure State where
  halted : Bool
  code : List Symbol
  history : List Symbol
  deriving DecidableEq, Repr

def step (s : State) : State :=
  if s.halted then s else
  match s.history with
  | [] => {s with halted := true}
  | .cell .component::hs => {s with halted := true,history := hs}
  | x::hs => {s with code := x::s.code,history := hs}

def transitionTrace (s : State) : List BitOp :=
  if s.halted then [] else
  match s.history with
  | [] => [.readCell,.readCell,.branch]
  | .cell .component::_ => [.readCell,.readCell,.branch,.moveHead]
  | _::_ => [.readCell,.readCell,.branch,.moveHead,.writeCell,.writeCell,.moveHead]

def advance : ℕ → State → State
  | 0,s => s
  | n+1,s => advance n (step s)
def bitSteps : ℕ → State → ℕ
  | 0,_ => 0
  | n+1,s => (transitionTrace s).length+bitSteps n (step s)

theorem rewind_run (consumed code history : List Symbol) (h : marker ∉ consumed) :
    advance (consumed.length+1) ⟨false,code,consumed++marker::history⟩ =
      ⟨true,consumed.reverse++code,history⟩ := by
  induction consumed generalizing code with
  | nil => rfl
  | cons x xs ih =>
    have hx : x ≠ marker := by intro hx; exact h (by simp [hx])
    have hxs : marker ∉ xs := by intro hm; exact h (List.mem_cons_of_mem _ hm)
    have hs : step ⟨false,code,(x::xs)++marker::history⟩ = ⟨false,x::code,xs++marker::history⟩ := by
      cases x with
      | boundary => rfl
      | cell c => cases c with
        | component => exact (hx rfl).elim
        | bit b => rfl
    change advance (xs.length+1+1) _=_
    rw [advance,hs]
    simpa [List.reverse_cons,List.append_assoc] using ih (x::code) hxs

theorem transition_length (s : State) : (transitionTrace s).length ≤ 7 := by
  simp only [transitionTrace]
  split
  · simp
  · split <;> simp

theorem bitSteps_le (n : ℕ) (s : State) : bitSteps n s ≤ 7*n := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    have hs := transition_length s
    have hi := ih (step s)
    simp only [bitSteps]
    omega

theorem marker_not_word (bits : List Bool) : marker ∉ BinaryCodeWordLoader.encode bits := by
  simp [BinaryCodeWordLoader.encode,marker]

theorem binary_code_rewind (segment code history : List Symbol) (h : marker ∉ segment) :
    advance (segment.length+1) ⟨false,code,segment.reverse++marker::history⟩ =
      ⟨true,segment++code,history⟩ ∧
    bitSteps (segment.length+1) ⟨false,code,segment.reverse++marker::history⟩ ≤ 7*segment.length+7 := by
  refine ⟨?_,?_⟩
  · simpa using rewind_run segment.reverse code history (by simpa using h)
  · have hc := bitSteps_le (segment.length+1) (State.mk false code (segment.reverse++marker::history))
    omega

end IdentityTesting.BinaryCodeRewind
