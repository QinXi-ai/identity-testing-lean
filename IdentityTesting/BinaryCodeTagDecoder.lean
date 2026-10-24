import IdentityTesting.BinaryCodeWordLoader

namespace IdentityTesting.BinaryCodeTagDecoder
open BinaryRegisterMachine BinaryArithmetic

inductive Phase where
  | first | second | third | delimiter | halt | invalid
  deriving DecidableEq, Repr
structure State where
  phase : Phase
  code : List Symbol
  history : List Symbol
  first : Bool
  second : Bool
  third : Bool
  deriving DecidableEq, Repr

def step (s : State) : State :=
  match s.phase with
  | .first => match s.code with
      | .cell (.bit b)::cs => {s with phase := .second,code := cs,history := .cell (.bit b)::s.history,first := b}
      | _ => {s with phase := .invalid}
  | .second => match s.code with
      | .cell (.bit b)::cs => {s with phase := .third,code := cs,history := .cell (.bit b)::s.history,second := b}
      | _ => {s with phase := .invalid}
  | .third => match s.code with
      | .cell (.bit b)::cs => {s with phase := .delimiter,code := cs,history := .cell (.bit b)::s.history,third := b}
      | _ => {s with phase := .invalid}
  | .delimiter => match s.code with
      | .boundary::cs => {s with phase := .halt,code := cs,history := .boundary::s.history}
      | _ => {s with phase := .invalid}
  | .halt | .invalid => s

def transitionTrace (s : State) : List BitOp :=
  match s.phase with
  | .first | .second | .third | .delimiter => [.readCell,.readCell,.branch,.moveHead,.writeCell,.writeCell,.moveHead]
  | .halt | .invalid => []
def advance : ℕ → State → State
  | 0,s => s
  | n+1,s => advance n (step s)
def bitSteps : ℕ → State → ℕ
  | 0,_ => 0
  | n+1,s => (transitionTrace s).length+bitSteps n (step s)

def initial (code history : List Symbol) : State := ⟨.first,code,history,false,false,false⟩

theorem binary_code_tag_decode (a b c : Bool) (code history : List Symbol) :
    let segment := BinaryCodeWordLoader.encode [a,b,c]
    advance 4 (initial (segment++code) history) =
      ⟨.halt,code,segment.reverse++history,a,b,c⟩ ∧
    bitSteps 4 (initial (segment++code) history) = 28 := by
  simp [advance,step,initial,BinaryCodeWordLoader.encode,bitSteps,transitionTrace]

end IdentityTesting.BinaryCodeTagDecoder
