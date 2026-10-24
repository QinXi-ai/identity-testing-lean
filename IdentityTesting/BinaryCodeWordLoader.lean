import IdentityTesting.BinaryRegisterMachine

/-! Reading a delimited bit word from the program tape. Every consumed symbol
is copied to the history tape, so a later rewind can restore the code by actual
head operations. The word is reversed through a temporary stack; no whole-word
assignment is an executable operation. -/
namespace IdentityTesting.BinaryCodeWordLoader
open BinaryRegisterMachine BinaryArithmetic

def encode (bits : List Bool) : List Symbol := bits.map (fun b => .cell (.bit b)) ++ [.boundary]

inductive Phase where
  | reading | restore | halt | invalid
  deriving DecidableEq, Repr

structure State where
  phase : Phase
  code : List Symbol
  history : List Symbol
  temp : List Bool
  out : List Bool
  deriving DecidableEq, Repr

def step (s : State) : State :=
  match s.phase with
  | .reading => match s.code with
      | .cell (.bit b)::rest => {s with code := rest,history := .cell (.bit b)::s.history,temp := b::s.temp}
      | .boundary::rest => {s with phase := .restore,code := rest,history := .boundary::s.history}
      | _ => {s with phase := .invalid}
  | .restore => match s.temp with
      | [] => {s with phase := .halt}
      | b::bs => {s with temp := bs,out := b::s.out}
  | .halt | .invalid => s

def transitionTrace (s : State) : List BitOp :=
  match s.phase with
  | .reading => match s.code with
      | .cell (.bit _)::_ => [.readCell,.readCell,.branch,.moveHead,.writeCell,.writeCell,.moveHead,.writeCell,.moveHead]
      | .boundary::_ => [.readCell,.readCell,.branch,.moveHead,.writeCell,.writeCell,.moveHead]
      | _ => [.readCell,.readCell,.branch]
  | .restore => if s.temp = [] then [.readCell,.branch]
      else [.readCell,.branch,.moveHead,.writeCell,.moveHead]
  | .halt | .invalid => []

def advance : ℕ → State → State
  | 0,s => s
  | n+1,s => advance n (step s)
def bitSteps : ℕ → State → ℕ
  | 0,_ => 0
  | n+1,s => (transitionTrace s).length+bitSteps n (step s)
def Runs (s : State) (n : ℕ) (t : State) : Prop := advance n s=t

theorem advance_add (m n : ℕ) (s : State) : advance (m+n) s=advance n (advance m s) := by
  induction m generalizing s with
  | zero => simp [advance]
  | succ m ih => simpa [Nat.succ_add,advance] using ih (step s)

theorem Runs.trans {s t u : State} {m n : ℕ} (h : Runs s m t) (j : Runs t n u) : Runs s (m+n) u := by
  dsimp [Runs] at *
  rw [advance_add,h,j]

theorem restore_run (code history : List Symbol) (tmp out : List Bool) :
    Runs ⟨.restore,code,history,tmp,out⟩ (tmp.length+1) ⟨.halt,code,history,[],tmp.reverse++out⟩ := by
  induction tmp generalizing out with
  | nil => rfl
  | cons b bs ih =>
    change advance (bs.length+1+1) _=_
    rw [advance]
    simpa [step,List.reverse_cons,List.append_assoc] using ih (b::out)

theorem read_run (bits tmp out : List Bool) (code history : List Symbol) :
    Runs ⟨.reading,encode bits++code,history,tmp,out⟩ (bits.length+1)
      ⟨.restore,code,(encode bits).reverse++history,bits.reverse++tmp,out⟩ := by
  induction bits generalizing tmp history with
  | nil => rfl
  | cons b bs ih =>
    change advance (bs.length+1+1) _=_
    rw [advance]
    simpa [step,encode,List.reverse_cons,List.append_assoc] using ih (b::tmp) (.cell (.bit b)::history)

theorem word_run (bits out : List Bool) (code history : List Symbol) :
    Runs ⟨.reading,encode bits++code,history,[],out⟩ (2*bits.length+2)
      ⟨.halt,code,(encode bits).reverse++history,[],bits++out⟩ := by
  have hr := read_run bits [] out code history
  simp only [List.append_nil] at hr
  have hs := restore_run code ((encode bits).reverse++history) bits.reverse out
  simp only [List.length_reverse,List.reverse_reverse] at hs
  convert hr.trans hs using 1 <;> omega

theorem transition_length (s : State) : (transitionTrace s).length ≤ 9 := by
  cases hp : s.phase <;> simp only [transitionTrace,hp]
  · split <;> simp
  · split <;> simp
  · simp
  · simp

theorem bitSteps_le (n : ℕ) (s : State) : bitSteps n s ≤ 9*n := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    have hs := transition_length s
    have hi := ih (step s)
    simp only [bitSteps]
    omega

theorem binary_code_word_load (bits out : List Bool) (code history : List Symbol) :
    let start : State := ⟨.reading,encode bits++code,history,[],out⟩
    advance (2*bits.length+2) start = ⟨.halt,code,(encode bits).reverse++history,[],bits++out⟩ ∧
      bitSteps (2*bits.length+2) start ≤ 18*bits.length+18 := by
  refine ⟨word_run bits out code history,?_⟩
  have h := bitSteps_le (2*bits.length+2) (State.mk .reading (encode bits++code) history [] out)
  omega

end IdentityTesting.BinaryCodeWordLoader
