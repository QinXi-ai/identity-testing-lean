import IdentityTesting.BinarySignedWords

/-! Signed comparison by a finite controller and two input bit stacks.
The last unequal pair seen in a little-endian scan determines magnitude order.
Every read, branch, pop, and Boolean update is charged below. -/
namespace IdentityTesting.BinarySignedComparison
open BinaryArithmetic BinarySignedWords

inductive Phase where
  | scan | finish | halt
  deriving DecidableEq, Repr

structure State where
  phase : Phase
  left : List Bool
  right : List Bool
  negativeLeft : Bool
  negativeRight : Bool
  less : Bool
  greater : Bool
  nonzero : Bool
  result : Bool
  deriving DecidableEq, Repr

def update (a b : Bool) (s : State) : State :=
  { s with
    left := s.left.tail
    right := s.right.tail
    less := if a = b then s.less else b
    greater := if a = b then s.greater else a
    nonzero := s.nonzero || a || b }

def step (s : State) : State :=
  match s.phase with
  | .scan => if s.left = [] ∧ s.right = [] then { s with phase := .finish }
      else update (s.left.headD false) (s.right.headD false) s
  | .finish => { s with
      phase := .halt
      result := if s.negativeLeft = s.negativeRight then
        (if s.negativeLeft then s.greater else s.less)
        else s.negativeLeft && s.nonzero }
  | .halt => s

def advance : ℕ → State → State
  | 0, s => s
  | n + 1, s => advance n (step s)

def initial (x y : Word) : State :=
  ⟨.scan, x.magnitude, y.magnitude, x.negative, y.negative, false, false, false, false⟩

def transitionTrace (s : State) : List BitOp :=
  match s.phase with
  | .scan => if s.left = [] ∧ s.right = [] then [.readCell, .readCell, .branch]
      else [.readCell, .readCell, .branch, .readCell, .readCell,
        .moveHead, .moveHead, .xorGate, .branch, .orGate, .orGate]
  | .finish => [.xorGate, .branch, .branch, .andGate]
  | .halt => []

def bitSteps : ℕ → State → ℕ
  | 0, _ => 0
  | n + 1, s => (transitionTrace s).length + bitSteps n (step s)

theorem bitSteps_le (n : ℕ) (s : State) : bitSteps n s ≤ 11 * n := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
      have ht : (transitionTrace s).length ≤ 11 := by
        cases hp : s.phase <;> simp only [transitionTrace, hp]
        · split <;> simp
        all_goals simp
      have hi := ih (step s)
      simp only [bitSteps]
      omega

def scan : List Bool → List Bool → Bool → Bool → Bool → Bool × Bool × Bool
  | [], [], l, g, z => (l, g, z)
  | [], b :: ys, l, g, z =>
      scan [] ys (if false = b then l else b) (if false = b then g else false) (z || false || b)
  | a :: xs, [], l, g, z =>
      scan xs [] (if a = false then l else false) (if a = false then g else a) (z || a || false)
  | a :: xs, b :: ys, l, g, z =>
      scan xs ys (if a = b then l else b) (if a = b then g else a) (z || a || b)
termination_by xs ys => xs.length + ys.length
decreasing_by all_goals simp_wf <;> omega

theorem scan_correct (xs ys : List Bool) (l g z : Bool) :
    (scan xs ys l g z).1 = decide (value xs < value ys ∨ (value xs = value ys ∧ l = true)) ∧
    (scan xs ys l g z).2.1 = decide (value ys < value xs ∨ (value xs = value ys ∧ g = true)) ∧
    (scan xs ys l g z).2.2 = decide (0 < value xs + value ys ∨ z = true) := by
  cases xs with
  | nil =>
      cases ys with
      | nil => cases l <;> cases g <;> cases z <;> simp [scan, value]
      | cons b ys =>
          have ih := scan_correct [] ys (if false = b then l else b)
            (if false = b then g else false) (z || false || b)
          cases b <;> simp_all [scan, value]
          · simp only [eq_comm (a := (0 : ℕ)) (b := value ys), and_self]
          · omega
  | cons a xs =>
      cases ys with
      | nil =>
          have ih := scan_correct xs [] (if a = false then l else false)
            (if a = false then g else a) (z || a || false)
          cases a <;> simp_all [scan, value] <;> omega
      | cons b ys =>
          have ih := scan_correct xs ys (if a = b then l else b)
            (if a = b then g else a) (z || a || b)
          cases a <;> cases b <;> simp_all [scan, value]
          all_goals constructor <;> rw [Bool.eq_iff_iff] <;>
            simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] <;> omega
termination_by xs.length + ys.length
decreasing_by all_goals simp_all <;> omega

theorem scan_run (xs ys : List Bool) (a b l g z out : Bool) :
    advance (max xs.length ys.length + 1) ⟨.scan, xs, ys, a, b, l, g, z, out⟩ =
      ⟨.finish, [], [], a, b, (scan xs ys l g z).1,
        (scan xs ys l g z).2.1, (scan xs ys l g z).2.2, out⟩ := by
  cases xs with
  | nil =>
      cases ys with
      | nil => simp [advance, step, scan]
      | cons y ys =>
          simpa [advance, step, update, scan] using
            scan_run [] ys a b (if false = y then l else y)
              (if false = y then g else false) (z || false || y) out
  | cons x xs =>
      cases ys with
      | nil =>
          simpa [advance, step, update, scan] using
            scan_run xs [] a b (if x = false then l else false)
              (if x = false then g else x) (z || x || false) out
      | cons y ys =>
          simpa only [List.length_cons, max_add_add_right, Nat.add_assoc, advance,
            step, List.cons_ne_nil, false_and, ↓reduceIte, update, List.tail_cons,
            List.headD_cons, scan] using
            scan_run xs ys a b (if x = y then l else y)
              (if x = y then g else x) (z || x || y) out
termination_by xs.length + ys.length
decreasing_by all_goals simp_all <;> omega

theorem advance_add (m n : ℕ) (s : State) : advance (m + n) s = advance n (advance m s) := by
  induction m generalizing s with
  | zero => simp [advance]
  | succ m ih => simpa [Nat.succ_add, advance] using ih (step s)

theorem signed_comparison_machine (x y : Word) :
    let steps := max x.magnitude.length y.magnitude.length + 2
    (advance steps (initial x y)).phase = .halt ∧
    ((advance steps (initial x y)).result = true ↔ x.value < y.value) ∧
    bitSteps steps (initial x y) ≤ 11 * max x.magnitude.length y.magnitude.length + 22 := by
  have h := scan_run x.magnitude y.magnitude x.negative y.negative false false false false
  have hc := scan_correct x.magnitude y.magnitude false false false
  dsimp only
  have hr : advance (max x.magnitude.length y.magnitude.length + 2) (initial x y) =
      step ⟨.finish, [], [], x.negative, y.negative,
        (scan x.magnitude y.magnitude false false false).1,
        (scan x.magnitude y.magnitude false false false).2.1,
        (scan x.magnitude y.magnitude false false false).2.2, false⟩ := by
    rw [show max x.magnitude.length y.magnitude.length + 2 =
      (max x.magnitude.length y.magnitude.length + 1) + 1 by omega,
      advance_add]
    change advance 1 (advance _ _) = _
    unfold initial
    rw [h]
    rfl
  refine ⟨by rw [hr]; rfl, ?_, ?_⟩
  · rw [hr]
    rcases hc with ⟨hl, hg, hz⟩
    simp only [Bool.false_eq_true, and_false, or_false] at hl hg hz
    simp only [step, hl, hg, hz]
    cases hx : x.negative <;> cases hy : y.negative <;>
      simp [hx, hy, Word.value, signedValue] <;> omega
  · have hb := bitSteps_le (max x.magnitude.length y.magnitude.length + 2) (initial x y)
    omega

theorem binary_signed_comparison_machine (x y : ℤ) :
    let steps := max x.natAbs.size y.natAbs.size + 2
    (advance steps (initial (encode x) (encode y))).phase = .halt ∧
    ((advance steps (initial (encode x) (encode y))).result = true ↔ x < y) ∧
    bitSteps steps (initial (encode x) (encode y)) ≤ 11 * max x.natAbs.size y.natAbs.size + 22 := by
  have h := signed_comparison_machine (encode x) (encode y)
  simp only [encode_value] at h
  simpa only [encode, Nat.size_eq_bits_len] using h

end IdentityTesting.BinarySignedComparison
