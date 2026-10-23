import IdentityTesting.BinaryRationalRecordRuns

namespace IdentityTesting.BinaryRationalRecordJoin
open BinaryRegisterMachine BinaryRationalRegisters BinaryArithmetic

inductive Phase where
  | denCollect | denEmit | delimiter | numCollect | numEmit | sign | halt
  deriving DecidableEq, Repr

structure State where
  phase : Phase
  negative : Bool
  num : List Bool
  den : List Bool
  temp : List Bool
  out : List Cell
  deriving DecidableEq, Repr

def step (s : State) : State :=
  match s.phase with
  | .denCollect => match s.den with
    | [] => {s with phase := .denEmit}
    | b :: rest => {s with den := rest, temp := b :: s.temp}
  | .denEmit => match s.temp with
    | [] => {s with phase := .delimiter}
    | b :: rest => {s with temp := rest, out := .bit b :: s.out}
  | .delimiter => {s with phase := .numCollect, out := .component :: s.out}
  | .numCollect => match s.num with
    | [] => {s with phase := .numEmit}
    | b :: rest => {s with num := rest, temp := b :: s.temp}
  | .numEmit => match s.temp with
    | [] => {s with phase := .sign}
    | b :: rest => {s with temp := rest, out := .bit b :: s.out}
  | .sign => {s with phase := .halt, out := .bit s.negative :: s.out}
  | .halt => s

def transitionTrace (s : State) : List BitOp :=
  match s.phase with
  | .denCollect => match s.den with
    | [] => [.readCell, .branch]
    | _ :: _ => [.readCell, .branch, .moveHead, .writeCell, .moveHead]
  | .numCollect => match s.num with
    | [] => [.readCell, .branch]
    | _ :: _ => [.readCell, .branch, .moveHead, .writeCell, .moveHead]
  | .denEmit | .numEmit => match s.temp with
    | [] => [.readCell, .branch]
    | _ :: _ => [.readCell, .branch, .moveHead, .writeCell, .moveHead, .writeCell, .moveHead]
  | .delimiter | .sign => [.writeCell, .moveHead, .writeCell, .moveHead]
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

theorem denCollect_run (den temp num : List Bool) (out : List Cell) (sign : Bool) :
    advance (den.length+1) ⟨.denCollect, sign, num, den, temp, out⟩ =
      ⟨.denEmit, sign, num, [], den.reverse ++ temp, out⟩ := by
  induction den generalizing temp with
  | nil => rfl
  | cons b bs ih =>
    change advance (bs.length+1+1) _ = _
    rw [advance]
    change advance (bs.length+1) ⟨.denCollect, sign, num, bs, b::temp, out⟩ = _
    rw [ih]
    simp [List.reverse_cons, List.append_assoc]

theorem denEmit_run (temp num : List Bool) (out : List Cell) (sign : Bool) :
    advance (temp.length+1) ⟨.denEmit, sign, num, [], temp, out⟩ =
      ⟨.delimiter, sign, num, [], [], temp.reverse.map Cell.bit ++ out⟩ := by
  induction temp generalizing out with
  | nil => rfl
  | cons b bs ih =>
    change advance (bs.length+1+1) _ = _
    rw [advance]
    change advance (bs.length+1) ⟨.denEmit, sign, num, [], bs, .bit b::out⟩ = _
    rw [ih]
    simp [List.reverse_cons, List.map_append, List.append_assoc]

theorem numCollect_run (num temp : List Bool) (out : List Cell) (sign : Bool) :
    advance (num.length+1) ⟨.numCollect, sign, num, [], temp, out⟩ =
      ⟨.numEmit, sign, [], [], num.reverse ++ temp, out⟩ := by
  induction num generalizing temp with
  | nil => rfl
  | cons b bs ih =>
    change advance (bs.length+1+1) _ = _
    rw [advance]
    change advance (bs.length+1) ⟨.numCollect, sign, bs, [], b::temp, out⟩ = _
    rw [ih]
    simp [List.reverse_cons, List.append_assoc]

theorem numEmit_run (temp : List Bool) (out : List Cell) (sign : Bool) :
    advance (temp.length+1) ⟨.numEmit, sign, [], [], temp, out⟩ =
      ⟨.sign, sign, [], [], [], temp.reverse.map Cell.bit ++ out⟩ := by
  induction temp generalizing out with
  | nil => rfl
  | cons b bs ih =>
    change advance (bs.length+1+1) _ = _
    rw [advance]
    change advance (bs.length+1) ⟨.numEmit, sign, [], [], bs, .bit b::out⟩ = _
    rw [ih]
    simp [List.reverse_cons, List.map_append, List.append_assoc]

def initial (w : BinaryRationalArithmetic.Word) : State :=
  ⟨.denCollect, w.numerator.negative, w.numerator.magnitude, w.denominator, [], []⟩
def haltState (sign : Bool) (out : List Cell) : State := ⟨.halt, sign, [], [], [], out⟩
def joinFuel (w : BinaryRationalArithmetic.Word) : ℕ :=
  (w.denominator.length+1) + ((w.denominator.reverse.length+1) +
    (1+((w.numerator.magnitude.length+1) + ((w.numerator.magnitude.reverse.length+1)+1))))

theorem join_run (w : BinaryRationalArithmetic.Word) :
    advance (joinFuel w) (initial w) = haltState w.numerator.negative (wordCells w) := by
  unfold joinFuel initial
  rw [advance_add, denCollect_run]
  simp only [List.append_nil]
  rw [advance_add, denEmit_run]
  simp only [List.reverse_reverse, List.append_nil]
  rw [advance_add]
  change advance ((w.numerator.magnitude.length+1) + ((w.numerator.magnitude.reverse.length+1)+1))
    ⟨.numCollect, w.numerator.negative, w.numerator.magnitude, [], [],
      .component :: w.denominator.map Cell.bit⟩ = _
  rw [advance_add, numCollect_run]
  simp only [List.append_nil]
  rw [advance_add, numEmit_run]
  simp only [List.reverse_reverse]
  rfl

theorem transitionTrace_length (s : State) : (transitionTrace s).length ≤ 7 := by
  unfold transitionTrace
  split <;> (repeat' first | split | decide)

theorem bitSteps_le (n : ℕ) (s : State) : bitSteps n s ≤ 7*n := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    have ht := transitionTrace_length s
    have hi := ih (step s)
    simp only [bitSteps, Nat.mul_succ]
    omega

theorem binary_rational_record_join (w : BinaryRationalArithmetic.Word) :
    ∃ fuel, advance fuel (initial w) = haltState w.numerator.negative (wordCells w) ∧
      bitSteps fuel (initial w) ≤ 14*w.length+28 := by
  refine ⟨joinFuel w, join_run w, ?_⟩
  have h := bitSteps_le (joinFuel w) (initial w)
  have hf : joinFuel w = 2*w.length+4 := by
    simp [joinFuel, BinaryRationalArithmetic.Word.length]
    omega
  rw [hf] at h ⊢
  omega

end IdentityTesting.BinaryRationalRecordJoin
