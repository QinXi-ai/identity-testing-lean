import IdentityTesting.BinaryCodeWordLoader
import IdentityTesting.BinaryRationalArithmeticWords

namespace IdentityTesting.BinaryCodeLiteralLoader
open BinaryRegisterMachine BinaryArithmetic
abbrev Word := BinaryRationalArithmetic.Word

inductive Phase where
  | sign | signEnd | numerator | denominator | halt | invalid
  deriving DecidableEq, Repr

structure State where
  phase : Phase
  fieldPhase : BinaryCodeWordLoader.Phase
  code : List Symbol
  history : List Symbol
  temp : List Bool
  negative : Bool
  num : List Bool
  den : List Bool
  deriving DecidableEq, Repr

def field (s : State) (right : Bool) : BinaryCodeWordLoader.State :=
  ⟨s.fieldPhase,s.code,s.history,s.temp,if right then s.den else s.num⟩
def setField (s : State) (right : Bool) (w : BinaryCodeWordLoader.State) : State :=
  {s with fieldPhase := w.phase,code := w.code,history := w.history,temp := w.temp,num := if right then s.num else w.out,den := if right then w.out else s.den}

def step (s : State) : State :=
  match s.phase with
  | .sign => match s.code with
      | .cell (.bit b)::cs => {s with phase := .signEnd,code := cs,history := .cell (.bit b)::s.history,negative := b}
      | _ => {s with phase := .invalid}
  | .signEnd => match s.code with
      | .boundary::cs => {s with phase := .numerator,code := cs,history := .boundary::s.history}
      | _ => {s with phase := .invalid}
  | .numerator => if s.fieldPhase = .halt then {s with phase := .denominator,fieldPhase := .reading}
      else setField s false (BinaryCodeWordLoader.step (field s false))
  | .denominator => if s.fieldPhase = .halt then {s with phase := .halt}
      else setField s true (BinaryCodeWordLoader.step (field s true))
  | .halt | .invalid => s

def transitionTrace (s : State) : List BitOp :=
  match s.phase with
  | .sign | .signEnd => [.readCell,.readCell,.branch,.moveHead,.writeCell,.writeCell,.moveHead]
  | .numerator => if s.fieldPhase = .halt then [.branch]
      else .branch::BinaryCodeWordLoader.transitionTrace (field s false)
  | .denominator => if s.fieldPhase = .halt then [.branch]
      else .branch::BinaryCodeWordLoader.transitionTrace (field s true)
  | .halt | .invalid => []

def advance : ℕ → State → State
  | 0,s => s
  | n+1,s => advance n (step s)
def bitSteps : ℕ → State → ℕ
  | 0,_ => 0
  | n+1,s => (transitionTrace s).length+bitSteps n (step s)

theorem advance_add (m n : ℕ) (s : State) : advance (m+n) s=advance n (advance m s) := by
  induction m generalizing s with
  | zero => simp [advance]
  | succ m ih => simpa [Nat.succ_add,advance] using ih (step s)

def phaseOf (right : Bool) : Phase := if right then .denominator else .numerator
def lift (frame : State) (right : Bool) (w : BinaryCodeWordLoader.State) : State :=
  {setField frame right w with phase := phaseOf right}
def after (frame : State) (right : Bool) (w : BinaryCodeWordLoader.State) : State :=
  if right then {lift frame right w with phase := .halt}
  else {lift frame right w with phase := .denominator,fieldPhase := .reading}

theorem lift_step (frame : State) (right : Bool) (w : BinaryCodeWordLoader.State) (h : w.phase ≠ .halt) :
    step (lift frame right w) = lift frame right (BinaryCodeWordLoader.step w) := by
  cases right <;> cases w <;> simp_all [step,lift,phaseOf,setField,field]

theorem lift_halt (frame : State) (right : Bool) (w : BinaryCodeWordLoader.State) (h : w.phase = .halt) :
    step (lift frame right w) = after frame right w := by
  cases right <;> simp [step,lift,phaseOf,setField,after,h]

theorem word_halt (n : ℕ) (w : BinaryCodeWordLoader.State) (h : w.phase = .halt) :
    BinaryCodeWordLoader.advance n w = w := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [BinaryCodeWordLoader.advance,BinaryCodeWordLoader.step,h] using ih

theorem forward_field (frame : State) (right : Bool) (w : BinaryCodeWordLoader.State) (n : ℕ)
    (h : (BinaryCodeWordLoader.advance n w).phase = .halt) :
    ∃ k, k ≤ n+1 ∧ advance k (lift frame right w) = after frame right (BinaryCodeWordLoader.advance n w) := by
  induction n generalizing w with
  | zero =>
    refine ⟨1,by omega,?_⟩
    exact lift_halt frame right w h
  | succ n ih =>
    by_cases hh : w.phase = .halt
    · rw [word_halt (n+1) w hh]
      exact ⟨1,by omega,lift_halt frame right w hh⟩
    · obtain ⟨k,hk,he⟩ := ih (BinaryCodeWordLoader.step w) h
      refine ⟨k+1,by omega,?_⟩
      rw [advance,lift_step frame right w hh]
      exact he

theorem transition_length (s : State) : (transitionTrace s).length ≤ 10 := by
  have hn := BinaryCodeWordLoader.transition_length (field s false)
  have hd := BinaryCodeWordLoader.transition_length (field s true)
  cases hp : s.phase <;> simp only [transitionTrace,hp]
  all_goals (first | (split <;> simp_all) | simp)

theorem bitSteps_le (n : ℕ) (s : State) : bitSteps n s ≤ 10*n := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    have hs := transition_length s
    have hi := ih (step s)
    simp only [bitSteps]
    omega

def encode (w : Word) : List Symbol :=
  BinaryCodeWordLoader.encode [w.numerator.negative] ++ BinaryCodeWordLoader.encode w.numerator.magnitude ++
    BinaryCodeWordLoader.encode w.denominator
def initial (code history : List Symbol) : State := ⟨.sign,.reading,code,history,[],false,[],[]⟩
def output (s : State) : Word := ⟨⟨s.negative,s.num⟩,s.den⟩

end IdentityTesting.BinaryCodeLiteralLoader
