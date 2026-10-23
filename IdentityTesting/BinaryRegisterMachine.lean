import IdentityTesting.BinaryArithmeticCost

/-! Sequential register access over a delimiter tape. No list index or whole
word copy is an executable operation. The alphabet has four symbols, each with
an explicit two-bit code; reads and writes are charged two bit-cell actions.
An address is an explicit unary Bool tape, consumed one cell per crossed record. -/

namespace IdentityTesting.BinaryRegisterMachine
open BinaryArithmetic

inductive Cell where
  | bit (b : Bool) | component
  deriving DecidableEq, Repr

inductive Symbol where
  | cell (c : Cell) | boundary
  deriving DecidableEq, Repr

def symbolCode : Symbol → Bool × Bool
  | .cell (.bit false) => (false, false)
  | .cell (.bit true) => (false, true)
  | .cell .component => (true, false)
  | .boundary => (true, true)

theorem symbolCode_injective : Function.Injective symbolCode := by
  intro a b h
  cases a with
  | boundary => cases b with
    | boundary => rfl
    | cell c => cases c with
      | component => cases h
      | bit q => cases q <;> cases h
  | cell c => cases c with
    | component => cases b with
      | boundary => cases h
      | cell d => cases d with
        | component => rfl
        | bit q => cases q <;> cases h
    | bit p => cases b with
      | boundary => cases p <;> cases h
      | cell d => cases d with
        | component => cases p <;> cases h
        | bit q => cases p <;> cases q <;> first | rfl | cases h

def encode : List (List Cell) → List Symbol
  | [] => []
  | word :: rest => word.map Symbol.cell ++ .boundary :: encode rest

theorem encode_append (xs ys : List (List Cell)) : encode (xs ++ ys) = encode xs ++ encode ys := by
  induction xs with
  | nil => rfl
  | cons word rest ih => simp [encode, ih, List.append_assoc]

inductive Phase where
  | seek | copy | restore | output | halt
  deriving DecidableEq, Repr

structure State where
  phase : Phase
  tape : List Symbol
  address : List Bool
  saved : List Symbol
  temp : List Cell
  out : List Cell
  deriving DecidableEq, Repr

def step (s : State) : State :=
  match s.phase with
  | .seek => match s.address with
    | [] => {s with phase := .copy}
    | _ :: addr => match s.tape with
      | [] => {s with phase := .restore}
      | .boundary :: rest => {s with tape := rest, saved := .boundary :: s.saved, address := addr}
      | (.cell c) :: rest => {s with tape := rest, saved := .cell c :: s.saved}
  | .copy => match s.tape with
    | [] => {s with phase := .restore}
    | .boundary :: _ => {s with phase := .restore}
    | (.cell c) :: rest => {s with tape := rest, saved := .cell c :: s.saved, temp := c :: s.temp}
  | .restore => match s.saved with
    | [] => {s with phase := .output}
    | c :: rest => {s with tape := c :: s.tape, saved := rest}
  | .output => match s.temp with
    | [] => {s with phase := .halt}
    | c :: rest => {s with temp := rest, out := c :: s.out}
  | .halt => s

def transitionTrace (s : State) : List BitOp :=
  match s.phase with
  | .seek => match s.address with
    | [] => [.readCell, .branch]
    | _ :: _ => match s.tape with
      | [] => [.readCell, .readCell, .branch]
      | .boundary :: _ => [.readCell, .branch, .readCell, .readCell, .branch,
          .moveHead, .moveHead, .writeCell, .moveHead, .writeCell, .moveHead, .moveHead]
      | (.cell _) :: _ => [.readCell, .branch, .readCell, .readCell, .branch,
          .moveHead, .moveHead, .writeCell, .moveHead, .writeCell, .moveHead]
  | .copy => match s.tape with
    | [] | .boundary :: _ => [.readCell, .readCell, .branch]
    | (.cell _) :: _ => [.readCell, .readCell, .branch, .moveHead, .moveHead,
        .writeCell, .moveHead, .writeCell, .moveHead, .writeCell, .moveHead, .writeCell, .moveHead]
  | .restore => match s.saved with
    | [] => [.readCell, .readCell, .branch]
    | _ :: _ => [.readCell, .readCell, .branch, .moveHead, .moveHead,
        .writeCell, .moveHead, .writeCell, .moveHead]
  | .output => match s.temp with
    | [] => [.readCell, .readCell, .branch]
    | _ :: _ => [.readCell, .readCell, .branch, .moveHead, .moveHead,
        .writeCell, .moveHead, .writeCell, .moveHead]
  | .halt => []

def advance : ℕ → State → State
  | 0, s => s
  | n + 1, s => advance n (step s)

def bitSteps : ℕ → State → ℕ
  | 0, _ => 0
  | n + 1, s => (transitionTrace s).length + bitSteps n (step s)

theorem advance_add (m n : ℕ) (s : State) : advance (m + n) s = advance n (advance m s) := by
  induction m generalizing s with
  | zero => simp [advance]
  | succ m ih => simpa [Nat.succ_add, advance] using ih (step s)

def seekState (tape : List Symbol) (address : List Bool) (saved : List Symbol) : State :=
  ⟨.seek, tape, address, saved, [], []⟩
def copyState (tape saved : List Symbol) (temp out : List Cell) : State :=
  ⟨.copy, tape, [], saved, temp, out⟩
def restoreState (tape saved : List Symbol) (temp out : List Cell) : State :=
  ⟨.restore, tape, [], saved, temp, out⟩
def outputState (tape : List Symbol) (temp out : List Cell) : State :=
  ⟨.output, tape, [], [], temp, out⟩
def haltState (tape : List Symbol) (out : List Cell) : State :=
  ⟨.halt, tape, [], [], [], out⟩

theorem seek_word (word : List Cell) (tape : List Symbol) (addr : List Bool) (saved : List Symbol) :
    advance (word.length + 1) (seekState (word.map Symbol.cell ++ .boundary :: tape)
      (false :: addr) saved) =
      seekState tape addr ((word.map Symbol.cell ++ [Symbol.boundary]).reverse ++ saved) := by
  induction word generalizing saved with
  | nil => rfl
  | cons c rest ih =>
    change advance (rest.length + 1 + 1) (seekState
      (.cell c :: (rest.map Symbol.cell ++ .boundary :: tape)) (false :: addr) saved) = _
    rw [advance]
    change advance (rest.length + 1) (seekState (rest.map Symbol.cell ++ .boundary :: tape)
      (false :: addr) (.cell c :: saved)) = _
    rw [ih]
    simp [List.reverse_cons, List.append_assoc]

theorem seek_prefix (before : List (List Cell)) (tape saved : List Symbol) :
    advance (encode before).length (seekState (encode before ++ tape)
      (List.replicate before.length false) saved) =
      seekState tape [] ((encode before).reverse ++ saved) := by
  induction before generalizing saved with
  | nil => rfl
  | cons word rest ih =>
    have hlen : (encode (word :: rest)).length = word.length + 1 + (encode rest).length := by simp [encode]; omega
    rw [hlen, advance_add]
    simp only [encode, List.length_cons, List.replicate_succ, List.append_assoc, List.cons_append]
    rw [seek_word, ih]
    simp [List.reverse_append, List.reverse_cons, List.append_assoc]

theorem copy_word (word : List Cell) (tape saved : List Symbol) (temp out : List Cell) :
    advance (word.length + 1) (copyState (word.map Symbol.cell ++ .boundary :: tape) saved temp out) =
      restoreState (.boundary :: tape) ((word.map Symbol.cell).reverse ++ saved) (word.reverse ++ temp) out := by
  induction word generalizing saved temp with
  | nil => rfl
  | cons c rest ih =>
    change advance (rest.length + 1 + 1) (copyState
      (.cell c :: (rest.map Symbol.cell ++ .boundary :: tape)) saved temp out) = _
    rw [advance]
    change advance (rest.length + 1) (copyState (rest.map Symbol.cell ++ .boundary :: tape)
      (.cell c :: saved) (c :: temp) out) = _
    rw [ih]
    simp [List.reverse_cons, List.append_assoc]

theorem restore_run (saved tape : List Symbol) (temp out : List Cell) :
    advance (saved.length + 1) (restoreState tape saved temp out) =
      outputState (saved.reverse ++ tape) temp out := by
  induction saved generalizing tape with
  | nil => rfl
  | cons c rest ih =>
    change advance (rest.length + 1 + 1) (restoreState tape (c :: rest) temp out) = _
    rw [advance]
    change advance (rest.length + 1) (restoreState (c :: tape) rest temp out) = _
    rw [ih]
    simp [List.reverse_cons, List.append_assoc]

theorem output_run (temp out : List Cell) (tape : List Symbol) :
    advance (temp.length + 1) (outputState tape temp out) = haltState tape (temp.reverse ++ out) := by
  induction temp generalizing out with
  | nil => rfl
  | cons c rest ih =>
    change advance (rest.length + 1 + 1) (outputState tape (c :: rest) out) = _
    rw [advance]
    change advance (rest.length + 1) (outputState tape rest (c :: out)) = _
    rw [ih]
    simp [List.reverse_cons, List.append_assoc]

end IdentityTesting.BinaryRegisterMachine
