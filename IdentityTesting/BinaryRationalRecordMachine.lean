import IdentityTesting.BinaryRationalRegisters

namespace IdentityTesting.BinaryRationalRecordMachine
open BinaryRegisterMachine BinaryRationalRegisters BinaryArithmetic

inductive Phase where
  | sign | numerator | denominator | reverseNum | reverseDen | halt
  deriving DecidableEq, Repr

structure State where
  phase : Phase
  input : List Cell
  negative : Bool
  numWork : List Bool
  denWork : List Bool
  num : List Bool
  den : List Bool
  deriving DecidableEq, Repr

def step (s : State) : State :=
  match s.phase with
  | .sign => match s.input with
    | .bit b :: rest => {s with phase := .numerator, input := rest, negative := b}
    | _ => {s with phase := .halt}
  | .numerator => match s.input with
    | [] => {s with phase := .halt}
    | .component :: rest => {s with phase := .denominator, input := rest}
    | .bit b :: rest => {s with input := rest, numWork := b :: s.numWork}
  | .denominator => match s.input with
    | [] => {s with phase := .reverseNum}
    | .component :: _ => {s with phase := .halt}
    | .bit b :: rest => {s with input := rest, denWork := b :: s.denWork}
  | .reverseNum => match s.numWork with
    | [] => {s with phase := .reverseDen}
    | b :: rest => {s with numWork := rest, num := b :: s.num}
  | .reverseDen => match s.denWork with
    | [] => {s with phase := .halt}
    | b :: rest => {s with denWork := rest, den := b :: s.den}
  | .halt => s

def transitionTrace (s : State) : List BitOp :=
  match s.phase with
  | .sign => [.readCell, .readCell, .branch, .moveHead, .moveHead, .writeCell]
  | .numerator => match s.input with
    | [] => [.readCell, .readCell, .branch]
    | .component :: _ => [.readCell, .readCell, .branch, .moveHead, .moveHead]
    | .bit _ :: _ => [.readCell, .readCell, .branch, .moveHead, .moveHead, .writeCell, .moveHead]
  | .denominator => match s.input with
    | [] | .component :: _ => [.readCell, .readCell, .branch]
    | .bit _ :: _ => [.readCell, .readCell, .branch, .moveHead, .moveHead, .writeCell, .moveHead]
  | .reverseNum => match s.numWork with
    | [] => [.readCell, .branch]
    | _ :: _ => [.readCell, .branch, .moveHead, .writeCell, .moveHead]
  | .reverseDen => match s.denWork with
    | [] => [.readCell, .branch]
    | _ :: _ => [.readCell, .branch, .moveHead, .writeCell, .moveHead]
  | .halt => []

def advance : ℕ → State → State
  | 0, s => s
  | n+1, s => advance n (step s)
def bitSteps : ℕ → State → ℕ
  | 0, _ => 0
  | n+1, s => (transitionTrace s).length + bitSteps n (step s)

theorem advance_add (m n : ℕ) (s : State) : advance (m+n) s = advance n (advance m s) := by
  induction m generalizing s with
  | zero => simp [advance]
  | succ m ih => simpa [Nat.succ_add, advance] using ih (step s)

def numState (input : List Cell) (sign : Bool) (nw dw n d : List Bool) : State :=
  ⟨.numerator, input, sign, nw, dw, n, d⟩
def denState (input : List Cell) (sign : Bool) (nw dw n d : List Bool) : State :=
  ⟨.denominator, input, sign, nw, dw, n, d⟩
def revNumState (sign : Bool) (nw dw n d : List Bool) : State :=
  ⟨.reverseNum, [], sign, nw, dw, n, d⟩
def revDenState (sign : Bool) (dw n d : List Bool) : State :=
  ⟨.reverseDen, [], sign, [], dw, n, d⟩
def haltState (sign : Bool) (n d : List Bool) : State := ⟨.halt, [], sign, [], [], n, d⟩
def initial (input : List Cell) : State := ⟨.sign, input, false, [], [], [], []⟩
def output (s : State) : BinaryRationalArithmetic.Word := ⟨⟨s.negative, s.num⟩, s.den⟩

theorem numerator_run (xs : List Bool) (tail : List Cell) (sign : Bool) (nw dw n d : List Bool) :
    advance (xs.length+1) (numState (xs.map Cell.bit ++ .component :: tail) sign nw dw n d) =
      denState tail sign (xs.reverse ++ nw) dw n d := by
  induction xs generalizing nw with
  | nil => rfl
  | cons b bs ih =>
    change advance (bs.length+1+1) (numState (.bit b :: (bs.map Cell.bit ++ .component :: tail)) sign nw dw n d) = _
    rw [advance]
    change advance (bs.length+1) (numState (bs.map Cell.bit ++ .component :: tail) sign (b::nw) dw n d) = _
    rw [ih]
    simp [List.reverse_cons, List.append_assoc]

theorem denominator_run (xs : List Bool) (sign : Bool) (nw dw n d : List Bool) :
    advance (xs.length+1) (denState (xs.map Cell.bit) sign nw dw n d) =
      revNumState sign nw (xs.reverse ++ dw) n d := by
  induction xs generalizing dw with
  | nil => rfl
  | cons b bs ih =>
    change advance (bs.length+1+1) (denState (.bit b :: bs.map Cell.bit) sign nw dw n d) = _
    rw [advance]
    change advance (bs.length+1) (denState (bs.map Cell.bit) sign nw (b::dw) n d) = _
    rw [ih]
    simp [List.reverse_cons, List.append_assoc]

theorem reverseNum_run (nw dw n d : List Bool) (sign : Bool) :
    advance (nw.length+1) (revNumState sign nw dw n d) = revDenState sign dw (nw.reverse ++ n) d := by
  induction nw generalizing n with
  | nil => rfl
  | cons b bs ih =>
    change advance (bs.length+1+1) (revNumState sign (b::bs) dw n d) = _
    rw [advance]
    change advance (bs.length+1) (revNumState sign bs dw (b::n) d) = _
    rw [ih]
    simp [List.reverse_cons, List.append_assoc]

theorem reverseDen_run (dw n d : List Bool) (sign : Bool) :
    advance (dw.length+1) (revDenState sign dw n d) = haltState sign n (dw.reverse ++ d) := by
  induction dw generalizing d with
  | nil => rfl
  | cons b bs ih =>
    change advance (bs.length+1+1) (revDenState sign (b::bs) n d) = _
    rw [advance]
    change advance (bs.length+1) (revDenState sign bs n (b::d)) = _
    rw [ih]
    simp [List.reverse_cons, List.append_assoc]

end IdentityTesting.BinaryRationalRecordMachine
