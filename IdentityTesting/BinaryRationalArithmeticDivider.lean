import IdentityTesting.BinaryRationalArithmeticMultiplierBound
import IdentityTesting.BinaryRationalArithmeticInverseWords

/-! Division uses a fixed input-stack layout with the right numerator and
denominator assigned to reciprocal roles. A charged end-marker test handles
division by zero before entering multiplication; its denominator one is written
to a fresh empty stack in one charged transition. -/
namespace IdentityTesting.BinaryRationalArithmeticDivider
open BinaryArithmetic

inductive Phase where
  | test | zeroWrite | multiplying | zeroHalt | halt
  deriving DecidableEq, Repr

structure State where
  phase : Phase
  core : BinaryRationalArithmeticMultiplier.State
  zeroDen : List Bool
  deriving DecidableEq, Repr

def reciprocalLayout (q : BinaryRationalArithmetic.Word) : BinaryRationalArithmetic.Word :=
  ⟨⟨q.numerator.negative,q.denominator⟩,q.numerator.magnitude⟩

def initial (p q : BinaryRationalArithmetic.Word) : State :=
  ⟨.test,BinaryRationalArithmeticMultiplier.initial p (reciprocalLayout q),[]⟩

def step (s : State) : State :=
  match s.phase with
  | .test => if s.core.den.mul.shifted = [] then { s with phase := .zeroWrite }
      else { s with phase := .multiplying }
  | .zeroWrite => { s with phase := .zeroHalt, zeroDen := true :: s.zeroDen }
  | .multiplying => if s.core.phase = .halt then { s with phase := .halt }
      else { s with core := BinaryRationalArithmeticMultiplier.step s.core }
  | .zeroHalt | .halt => s

def output (s : State) : BinaryRationalArithmetic.Word :=
  if s.phase = .zeroHalt then ⟨⟨false,s.core.den.mul.shifted⟩,s.zeroDen⟩
  else BinaryRationalArithmeticMultiplier.output s.core

def advance : ℕ → State → State
  | 0,s => s
  | n+1,s => advance n (step s)

def transitionTrace (s : State) : List BitOp :=
  match s.phase with
  | .test => [.readCell,.branch]
  | .zeroWrite => [.writeCell,.moveHead]
  | .multiplying => if s.core.phase = .halt then [.branch]
      else .branch :: BinaryRationalArithmeticMultiplier.transitionTrace s.core
  | .zeroHalt | .halt => []

def bitSteps : ℕ → State → ℕ
  | 0,_ => 0
  | n+1,s => (transitionTrace s).length+bitSteps n (step s)

theorem bitSteps_le (n : ℕ) (s : State) : bitSteps n s ≤ 11*n := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
      have hc := BinaryRationalArithmeticMultiplier.transition_length s.core
      have ht : (transitionTrace s).length ≤ 11 := by
        cases hp : s.phase <;> simp only [transitionTrace,hp]
        all_goals first | (split <;> simp_all) | simp_all
      have hi := ih (step s)
      simp only [bitSteps]
      omega

private theorem core_halt (k : ℕ) (s : BinaryRationalArithmeticMultiplier.State) (h : s.phase = .halt) :
    BinaryRationalArithmeticMultiplier.advance k s = s := by
  induction k with
  | zero => rfl
  | succ k ih => simpa [BinaryRationalArithmeticMultiplier.advance,BinaryRationalArithmeticMultiplier.step,h] using ih

theorem forward (s : BinaryRationalArithmeticMultiplier.State) (k : ℕ)
    (h : (BinaryRationalArithmeticMultiplier.advance k s).phase = .halt) :
    ∃ j, j ≤ k+1 ∧ advance j ⟨.multiplying,s,[]⟩ =
      ⟨.halt,BinaryRationalArithmeticMultiplier.advance k s,[]⟩ ∧
      bitSteps j ⟨.multiplying,s,[]⟩ ≤ 2*BinaryRationalArithmeticMultiplier.bitSteps k s + 1 := by
  induction k generalizing s with
  | zero =>
      simp only [BinaryRationalArithmeticMultiplier.advance] at h
      refine ⟨1,by omega,?_,?_⟩
      · simp [advance,step,h,BinaryRationalArithmeticMultiplier.advance]
      · simp [bitSteps,transitionTrace,h,BinaryRationalArithmeticMultiplier.bitSteps]
  | succ k ih =>
      by_cases hh : s.phase = .halt
      · refine ⟨1,by omega,?_,?_⟩
        · rw [core_halt (k+1) s hh]
          simp [advance,step,hh]
        · simp [bitSteps,transitionTrace,hh]
      · obtain ⟨j,hj,he,hc⟩ := ih (BinaryRationalArithmeticMultiplier.step s) h
        refine ⟨j+1,by omega,?_,?_⟩
        · rw [advance]
          simpa [step,hh,BinaryRationalArithmeticMultiplier.advance] using he
        · have ht : 1 ≤ (BinaryRationalArithmeticMultiplier.transitionTrace s).length := by
            cases hp : s.phase <;> simp_all [BinaryRationalArithmeticMultiplier.transitionTrace]
            all_goals split <;> simp_all
          simp only [bitSteps,transitionTrace,step,if_neg hh,List.length_cons,
            BinaryRationalArithmeticMultiplier.bitSteps]
          omega

end IdentityTesting.BinaryRationalArithmeticDivider
