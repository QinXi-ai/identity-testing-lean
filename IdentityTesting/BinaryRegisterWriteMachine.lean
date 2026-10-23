import IdentityTesting.BinaryRegisterMachineRuns

namespace IdentityTesting.BinaryRegisterWriteMachine
open BinaryArithmetic BinaryRegisterMachine

inductive Phase where
  | seek | erase | load | insert | restore | halt
  deriving DecidableEq, Repr

structure State where
  phase : Phase
  tape : List Symbol
  address : List Bool
  saved : List Symbol
  replacement : List Cell
  temp : List Cell
  deriving DecidableEq, Repr

def step (s : State) : State :=
  match s.phase with
  | .seek => match s.address with
    | [] => {s with phase := .erase}
    | _ :: addr => match s.tape with
      | [] => {s with phase := .restore}
      | .boundary :: rest => {s with tape := rest, saved := .boundary :: s.saved, address := addr}
      | (.cell c) :: rest => {s with tape := rest, saved := .cell c :: s.saved}
  | .erase => match s.tape with
    | [] | .boundary :: _ => {s with phase := .load}
    | (.cell _) :: rest => {s with tape := rest}
  | .load => match s.replacement with
    | [] => {s with phase := .insert}
    | c :: rest => {s with replacement := rest, temp := c :: s.temp}
  | .insert => match s.temp with
    | [] => {s with phase := .restore}
    | c :: rest => {s with temp := rest, tape := .cell c :: s.tape}
  | .restore => match s.saved with
    | [] => {s with phase := .halt}
    | c :: rest => {s with tape := c :: s.tape, saved := rest}
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
  | .erase => match s.tape with
    | [] | .boundary :: _ => [.readCell, .readCell, .branch]
    | (.cell _) :: _ => [.readCell, .readCell, .branch, .moveHead, .moveHead]
  | .load => match s.replacement with
    | [] => [.readCell, .readCell, .branch]
    | _ :: _ => [.readCell, .readCell, .branch, .moveHead, .moveHead,
        .writeCell, .moveHead, .writeCell, .moveHead]
  | .insert => match s.temp with
    | [] => [.readCell, .readCell, .branch]
    | _ :: _ => [.readCell, .readCell, .branch, .moveHead, .moveHead,
        .writeCell, .moveHead, .writeCell, .moveHead]
  | .restore => match s.saved with
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

def seekState (tape : List Symbol) (addr : List Bool) (saved : List Symbol) (word : List Cell) : State :=
  ⟨.seek, tape, addr, saved, word, []⟩
def eraseState (tape saved : List Symbol) (word : List Cell) : State :=
  ⟨.erase, tape, [], saved, word, []⟩
def loadState (tape saved : List Symbol) (word temp : List Cell) : State :=
  ⟨.load, tape, [], saved, word, temp⟩
def insertState (tape saved : List Symbol) (temp : List Cell) : State :=
  ⟨.insert, tape, [], saved, [], temp⟩
def restoreState (tape saved : List Symbol) : State :=
  ⟨.restore, tape, [], saved, [], []⟩
def haltState (tape : List Symbol) : State := ⟨.halt, tape, [], [], [], []⟩

theorem seek_word (word : List Cell) (tape : List Symbol) (addr : List Bool)
    (saved : List Symbol) (newWord : List Cell) :
    advance (word.length + 1) (seekState (word.map Symbol.cell ++ .boundary :: tape)
      (false :: addr) saved newWord) =
      seekState tape addr ((word.map Symbol.cell ++ [Symbol.boundary]).reverse ++ saved) newWord := by
  induction word generalizing saved with
  | nil => rfl
  | cons c rest ih =>
    change advance (rest.length + 1 + 1) (seekState
      (.cell c :: (rest.map Symbol.cell ++ .boundary :: tape)) (false :: addr) saved newWord) = _
    rw [advance]
    change advance (rest.length + 1) (seekState (rest.map Symbol.cell ++ .boundary :: tape)
      (false :: addr) (.cell c :: saved) newWord) = _
    rw [ih]
    simp [List.reverse_cons, List.append_assoc]

theorem seek_prefix (before : List (List Cell)) (tape saved : List Symbol) (newWord : List Cell) :
    advance (encode before).length (seekState (encode before ++ tape)
      (List.replicate before.length false) saved newWord) =
      seekState tape [] ((encode before).reverse ++ saved) newWord := by
  induction before generalizing saved with
  | nil => rfl
  | cons word rest ih =>
    have hlen : (encode (word :: rest)).length = word.length + 1 + (encode rest).length := by simp [encode]; omega
    rw [hlen, advance_add]
    simp only [encode, List.length_cons, List.replicate_succ, List.append_assoc, List.cons_append]
    rw [seek_word, ih]
    simp [List.reverse_append, List.reverse_cons, List.append_assoc]

theorem erase_word (word : List Cell) (tape saved : List Symbol) (newWord : List Cell) :
    advance (word.length + 1) (eraseState (word.map Symbol.cell ++ .boundary :: tape) saved newWord) =
      loadState (.boundary :: tape) saved newWord [] := by
  induction word with
  | nil => rfl
  | cons c rest ih => simpa only [List.length_cons, List.map_cons, List.cons_append, advance,
      eraseState, step] using ih

theorem load_word (word temp : List Cell) (tape saved : List Symbol) :
    advance (word.length + 1) (loadState tape saved word temp) =
      insertState tape saved (word.reverse ++ temp) := by
  induction word generalizing temp with
  | nil => rfl
  | cons c rest ih =>
    change advance (rest.length + 1 + 1) (loadState tape saved (c :: rest) temp) = _
    rw [advance]
    change advance (rest.length + 1) (loadState tape saved rest (c :: temp)) = _
    rw [ih]
    simp [List.reverse_cons, List.append_assoc]

theorem insert_word (temp : List Cell) (tape saved : List Symbol) :
    advance (temp.length + 1) (insertState tape saved temp) =
      restoreState (temp.reverse.map Symbol.cell ++ tape) saved := by
  induction temp generalizing tape with
  | nil => rfl
  | cons c rest ih =>
    change advance (rest.length + 1 + 1) (insertState tape saved (c :: rest)) = _
    rw [advance]
    change advance (rest.length + 1) (insertState (.cell c :: tape) saved rest) = _
    rw [ih]
    simp [List.reverse_cons, List.map_append, List.append_assoc]

theorem restore_run (saved tape : List Symbol) :
    advance (saved.length + 1) (restoreState tape saved) = haltState (saved.reverse ++ tape) := by
  induction saved generalizing tape with
  | nil => rfl
  | cons c rest ih =>
    change advance (rest.length + 1 + 1) (restoreState tape (c :: rest)) = _
    rw [advance]
    change advance (rest.length + 1) (restoreState (c :: tape) rest) = _
    rw [ih]
    simp [List.reverse_cons, List.append_assoc]

end IdentityTesting.BinaryRegisterWriteMachine
