import IdentityTesting.BinaryInterpreterOperandBound

/-! Two operands are consumed in sequence using one loader and the same
arithmetic core. Switching operands preserves all stacks and changes control. -/
namespace IdentityTesting.BinaryInterpreterOperandPair
open BinaryInterpreterLayout BinaryRegisterMachine
variable {L : Layout}

inductive Phase where
  | left | right | halt
  deriving DecidableEq, Repr
structure State (L : Layout) where
  phase : Phase
  loader : BinaryInterpreterOperand.State L

def step (s : State L) : State L :=
  match s.phase with
  | .left => if s.loader.phase = .halt then ⟨.right, BinaryInterpreterOperand.rearm s.loader⟩
      else ⟨.left, BinaryInterpreterOperand.step false s.loader⟩
  | .right => if s.loader.phase = .halt then {s with phase := .halt}
      else ⟨.right, BinaryInterpreterOperand.step true s.loader⟩
  | .halt => s
def transitionTrace (s : State L) : List BinaryArithmetic.BitOp :=
  match s.phase with
  | .left => if s.loader.phase = .halt then [.branch]
      else .branch :: BinaryInterpreterOperand.transitionTrace false s.loader
  | .right => if s.loader.phase = .halt then [.branch]
      else .branch :: BinaryInterpreterOperand.transitionTrace true s.loader
  | .halt => []
def advance : ℕ → State L → State L
  | 0, s => s
  | n+1, s => advance n (step s)
def bitSteps : ℕ → State L → ℕ
  | 0, _ => 0
  | n+1, s => (transitionTrace s).length + bitSteps n (step s)
def initial (L : Layout) (tape code history : List Symbol) : State L :=
  ⟨.left, BinaryInterpreterOperand.initial
    (L.initial BinaryInterpreterArithmetic.emptyWord BinaryInterpreterArithmetic.emptyWord) tape code history⟩

theorem advance_add (m n : ℕ) (s : State L) : advance (m+n) s = advance n (advance m s) := by
  induction m generalizing s with
  | zero => simp [advance]
  | succ m ih => simpa [Nat.succ_add, advance] using ih (step s)

def lift (right : Bool) (s : BinaryInterpreterOperand.State L) : State L :=
  ⟨if right then .right else .left, s⟩
def after (right : Bool) (s : BinaryInterpreterOperand.State L) : State L :=
  if right then ⟨.halt, s⟩ else ⟨.right, BinaryInterpreterOperand.rearm s⟩

theorem lift_step (right : Bool) (s : BinaryInterpreterOperand.State L) (h : s.phase ≠ .halt) :
    step (lift right s) = lift right (BinaryInterpreterOperand.step right s) := by
  cases right <;> simp [step, lift, h]
theorem lift_halt (right : Bool) (s : BinaryInterpreterOperand.State L) (h : s.phase = .halt) :
    step (lift right s) = after right s := by
  cases right <;> simp [step, lift, after, h]
theorem operand_halt (right : Bool) (n : ℕ) (s : BinaryInterpreterOperand.State L) (h : s.phase = .halt) :
    BinaryInterpreterOperand.advance right n s = s := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [BinaryInterpreterOperand.advance, BinaryInterpreterOperand.step, h] using ih

theorem forward (right : Bool) (s : BinaryInterpreterOperand.State L) (n : ℕ)
    (h : (BinaryInterpreterOperand.advance right n s).phase = .halt) :
    ∃ k, k ≤ n+1 ∧ advance k (lift right s) = after right (BinaryInterpreterOperand.advance right n s) := by
  induction n generalizing s with
  | zero => exact ⟨1, by omega, lift_halt right s h⟩
  | succ n ih =>
      by_cases hh : s.phase = .halt
      · rw [operand_halt right (n+1) s hh]
        exact ⟨1, by omega, lift_halt right s hh⟩
      · obtain ⟨k, hk, he⟩ := ih (BinaryInterpreterOperand.step right s) h
        refine ⟨k+1, by omega, ?_⟩
        rw [advance, lift_step right s hh]
        exact he

theorem transition_length (s : State L) : (transitionTrace s).length ≤ 16 := by
  have hl := BinaryInterpreterOperand.transition_length false s.loader
  have hr := BinaryInterpreterOperand.transition_length true s.loader
  cases hp : s.phase <;> simp only [transitionTrace, hp]
  all_goals (repeat' first | split | simp_all | omega)
theorem bitSteps_le (n : ℕ) (s : State L) : bitSteps n s ≤ 16*n := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
      have ht := transition_length s
      have hi := ih (step s)
      simp only [bitSteps]
      omega

end IdentityTesting.BinaryInterpreterOperandPair
