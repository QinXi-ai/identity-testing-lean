import IdentityTesting.BinaryCodeMaterialization

/-! A syntax-directed code skipper. Only finite control and a stack over the
four task symbols are retained; the source AST appears only in correctness
theorems. Word payloads are consumed to their own delimiter, so payload bits
cannot be confused with a node's end tag. -/
namespace IdentityTesting.BinaryCodeSkip
open BinaryRegisterMachine BinaryArithmetic RationalComputation

inductive Task where
  | node | word | operand | endTag
  deriving DecidableEq, Repr
inductive Phase where
  | start | dispatch | word | operandFirst | operandDelimiter (literal : Bool)
  | tag (ending : Bool) | halt | invalid
  deriving DecidableEq, Repr
structure State where
  phase : Phase
  code : List Symbol
  history : List Symbol
  tasks : List Task
  tagPhase : BinaryCodeTagDecoder.Phase
  first : Bool
  second : Bool
  third : Bool
  deriving DecidableEq, Repr

def ready (tasks : List Task) (code history : List Symbol) : State :=
  ⟨.dispatch,code,history,tasks,.first,false,false,false⟩
def initial (code history : List Symbol) : State := {ready [] code history with phase := .start}
def haltState (code history : List Symbol) : State := {ready [] code history with phase := .halt}

def schedule : Bool → Bool → Bool → Option (List Task)
  | false,false,false => some []
  | true,false,false => some [.word,.word,.operand,.operand]
  | false,true,false => some [.node,.node,.endTag]
  | true,true,false => some [.operand,.operand,.node,.node,.endTag]
  | false,false,true => some [.word,.node,.endTag]
  | true,false,true => some [.word,.operand]
  | false,true,true => some [.word,.node,.endTag]
  | true,true,true => none

def tagView (s : State) : BinaryCodeTagDecoder.State :=
  ⟨s.tagPhase,s.code,s.history,s.first,s.second,s.third⟩
def setTag (s : State) (t : BinaryCodeTagDecoder.State) : State :=
  {s with
    code := t.code,history := t.history,tagPhase := t.phase,
    first := t.first,second := t.second,third := t.third}

def step (s : State) : State :=
  match s.phase with
  | .start => ready (.node::s.tasks) s.code s.history
  | .dispatch => match s.tasks with
      | [] => {s with phase := .halt}
      | task::tasks =>
        let next := ready tasks s.code s.history
        match task with
        | .node => {next with phase := .tag false}
        | .endTag => {next with phase := .tag true}
        | .word => {next with phase := .word}
        | .operand => {next with phase := .operandFirst}
  | .word => match s.code with
      | .cell (.bit b)::code => {s with code := code,history := .cell (.bit b)::s.history}
      | .boundary::code => ready s.tasks code (.boundary::s.history)
      | _ => {s with phase := .invalid}
  | .operandFirst => match s.code with
      | .cell (.bit b)::code => {s with
          phase := .operandDelimiter b,code := code,
          history := .cell (.bit b)::s.history}
      | _ => {s with phase := .invalid}
  | .operandDelimiter literal => match s.code with
      | .boundary::code => ready
          (if literal then .word::.word::.word::s.tasks else .word::s.tasks)
          code (.boundary::s.history)
      | _ => {s with phase := .invalid}
  | .tag ending => if s.tagPhase = .halt then
      if ending then
        if s.first && s.second && s.third then ready s.tasks s.code s.history
        else {s with phase := .invalid}
      else match schedule s.first s.second s.third with
        | some tasks => ready (tasks++s.tasks) s.code s.history
        | none => {s with phase := .invalid}
    else setTag s (BinaryCodeTagDecoder.step (tagView s))
  | .halt | .invalid => s

def pushTrace (tasks : List Task) : List BitOp := tasks.flatMap (fun _ => [.writeCell,.moveHead])
def symbolTrace : List BitOp := [.readCell,.readCell,.branch,.moveHead,.writeCell,.writeCell,.moveHead]
def transitionTrace (s : State) : List BitOp :=
  match s.phase with
  | .start => [.writeCell,.moveHead]
  | .dispatch => if s.tasks = [] then [.readCell,.branch] else [.readCell,.branch,.moveHead]
  | .word => match s.code with
      | .cell (.bit _)::_ | .boundary::_ => symbolTrace
      | _ => [.readCell,.readCell,.branch]
  | .operandFirst => match s.code with
      | .cell (.bit _)::_ => symbolTrace
      | _ => [.readCell,.readCell,.branch]
  | .operandDelimiter literal => match s.code with
      | .boundary::_ => symbolTrace ++ pushTrace (if literal then [.word,.word,.word] else [.word])
      | _ => [.readCell,.readCell,.branch]
  | .tag ending => if s.tagPhase = .halt then
      if ending then [.branch]
      else match schedule s.first s.second s.third with
        | some tasks => .branch :: pushTrace tasks
        | none => [.branch]
    else .branch :: BinaryCodeTagDecoder.transitionTrace (tagView s)
  | .halt | .invalid => []

def advance : ℕ → State → State
  | 0,s => s
  | n+1,s => advance n (step s)
def bitSteps : ℕ → State → ℕ
  | 0,_ => 0
  | n+1,s => (transitionTrace s).length + bitSteps n (step s)

theorem advance_add (m n : ℕ) (s : State) : advance (m+n) s = advance n (advance m s) := by
  induction m generalizing s with
  | zero => simp [advance]
  | succ m ih => simpa [Nat.succ_add,advance] using ih (step s)

theorem scheduled_trace_length (a b c : Bool) :
    (match schedule a b c with
      | some tasks => BitOp.branch :: pushTrace tasks
      | none => [BitOp.branch]).length ≤ 11 := by
  cases a <;> cases b <;> cases c <;> simp [schedule,pushTrace]

theorem transition_length (s : State) : (transitionTrace s).length ≤ 16 := by
  have hs := scheduled_trace_length s.first s.second s.third
  have ht : (BinaryCodeTagDecoder.transitionTrace (tagView s)).length ≤ 7 := by
    cases hp : s.tagPhase <;> simp [BinaryCodeTagDecoder.transitionTrace,tagView,hp]
  cases hp : s.phase <;> simp only [transitionTrace,hp]
  all_goals (repeat' first | split | simp_all [pushTrace,symbolTrace] | omega)

theorem bitSteps_le (n : ℕ) (s : State) : bitSteps n s ≤ 16*n := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    have ht := transition_length s
    have hi := ih (step s)
    simp only [bitSteps]
    omega

end IdentityTesting.BinaryCodeSkip
