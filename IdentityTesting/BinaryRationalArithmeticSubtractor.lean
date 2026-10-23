import IdentityTesting.BinaryRationalArithmeticAdderBound
import IdentityTesting.BinaryRationalArithmeticNegationWords

namespace IdentityTesting.BinaryRationalArithmeticSubtractor
open BinaryArithmetic

inductive Phase where
  | negate | adding | halt
  deriving DecidableEq, Repr

structure State where
  phase : Phase
  core : BinaryRationalArithmeticAdder.State
  deriving DecidableEq, Repr

def initial (p q : BinaryRationalArithmetic.Word) : State :=
  ⟨.negate,BinaryRationalArithmeticAdder.initial p q⟩

def step (s : State) : State :=
  match s.phase with
  | .negate => { s with phase := .adding, core := { s.core with right := { s.core.right with signLeft := if s.core.right.mul.factor = [] then false else xor s.core.right.signLeft true } } }
  | .adding => if s.core.phase = .halt then { s with phase := .halt }
      else { s with core := BinaryRationalArithmeticAdder.step s.core }
  | .halt => s

def output (s : State) : BinaryRationalArithmetic.Word := BinaryRationalArithmeticAdder.output s.core

def advance : ℕ → State → State
  | 0,s => s
  | n+1,s => advance n (step s)

def transitionTrace (s : State) : List BitOp :=
  match s.phase with
  | .negate => [.readCell,.branch,.xorGate,.writeCell]
  | .adding => if s.core.phase = .halt then [.branch]
      else .branch :: BinaryRationalArithmeticAdder.transitionTrace s.core
  | .halt => []

def bitSteps : ℕ → State → ℕ
  | 0,_ => 0
  | n+1,s => (transitionTrace s).length+bitSteps n (step s)

private theorem core_halt (k : ℕ) (s : BinaryRationalArithmeticAdder.State) (h : s.phase = .halt) :
    BinaryRationalArithmeticAdder.advance k s = s := by
  induction k with
  | zero => rfl
  | succ k ih => simpa [BinaryRationalArithmeticAdder.advance,BinaryRationalArithmeticAdder.step,h] using ih

theorem forward (s : BinaryRationalArithmeticAdder.State) (k : ℕ)
    (h : (BinaryRationalArithmeticAdder.advance k s).phase = .halt) :
    ∃ j, j ≤ k+1 ∧ advance j ⟨.adding,s⟩ =
      ⟨.halt,BinaryRationalArithmeticAdder.advance k s⟩ ∧
      bitSteps j ⟨.adding,s⟩ ≤ 2*BinaryRationalArithmeticAdder.bitSteps k s+1 := by
  induction k generalizing s with
  | zero =>
      simp only [BinaryRationalArithmeticAdder.advance] at h
      refine ⟨1,by omega,?_,?_⟩
      · simp [advance,step,h,BinaryRationalArithmeticAdder.advance]
      · simp [bitSteps,transitionTrace,h,BinaryRationalArithmeticAdder.bitSteps]
  | succ k ih =>
      by_cases hh : s.phase = .halt
      · refine ⟨1,by omega,?_,?_⟩
        · rw [core_halt (k+1) s hh]
          simp [advance,step,hh]
        · simp [bitSteps,transitionTrace,hh]
      · obtain ⟨j,hj,he,hc⟩ := ih (BinaryRationalArithmeticAdder.step s) h
        refine ⟨j+1,by omega,?_,?_⟩
        · rw [advance]
          simpa [step,hh,BinaryRationalArithmeticAdder.advance] using he
        · have ht : 1 ≤ (BinaryRationalArithmeticAdder.transitionTrace s).length := by
            cases hp : s.phase <;> simp_all [BinaryRationalArithmeticAdder.transitionTrace]
            all_goals split <;> simp_all
          simp only [bitSteps,transitionTrace,step,if_neg hh,List.length_cons,
            BinaryRationalArithmeticAdder.bitSteps]
          omega

theorem binary_rational_subtraction_machine (p q : ℚ) :
    ∃ steps, let s := initial (BinaryRationalArithmetic.encode p) (BinaryRationalArithmetic.encode q)
      (advance steps s).phase = .halt ∧
      (output (advance steps s)).value = p-q ∧
      (output (advance steps s)).numerator.magnitude = (p-q).num.natAbs.bits ∧
      (output (advance steps s)).denominator = (p-q).den.bits ∧
      ((output (advance steps s)).numerator.magnitude = [] → (output (advance steps s)).numerator.negative = false) ∧
      bitSteps steps s ≤ 2700000*(RationalComputation.rationalEncodingLength p+RationalComputation.rationalEncodingLength q+1)^3 := by
  let c := BinaryRationalArithmeticAdder.initial (BinaryRationalArithmetic.encode p) (BinaryRationalArithmetic.encode (-q))
  let s := initial (BinaryRationalArithmetic.encode p) (BinaryRationalArithmetic.encode q)
  have hs : step s = ⟨.adding,c⟩ := by
    rw [show c = BinaryRationalArithmeticAdder.initial (BinaryRationalArithmetic.encode p)
      ⟨BinarySignedNegation.step (BinaryRationalArithmetic.encode q).numerator,
        (BinaryRationalArithmetic.encode q).denominator⟩ from
          congrArg (BinaryRationalArithmeticAdder.initial (BinaryRationalArithmetic.encode p))
            (BinaryRationalArithmetic.encode_negation q)]
    rfl
  obtain ⟨k,hh,hv,hm,hd,hz,hb⟩ := BinaryRationalArithmeticAdder.binary_rational_addition_machine p (-q)
  obtain ⟨j,hj,hr,hcost⟩ := forward c k hh
  have hw : advance (j+1) s = ⟨.halt,BinaryRationalArithmeticAdder.advance k c⟩ := by rw [advance,hs,hr]
  refine ⟨j+1,?_,?_,?_,?_,?_,?_⟩
  · exact congrArg State.phase hw
  · change (output (advance _ s)).value = _
    rw [hw]
    simpa only [output,sub_eq_add_neg] using hv
  · change (output (advance _ s)).numerator.magnitude = _
    rw [hw]
    simpa only [output,sub_eq_add_neg] using hm
  · change (output (advance _ s)).denominator = _
    rw [hw]
    simpa only [output,sub_eq_add_neg] using hd
  · change (output (advance _ s)).numerator.magnitude = [] → (output (advance _ s)).numerator.negative = false
    rw [hw]
    exact hz
  · have ht : (transitionTrace s).length = 4 := rfl
    change bitSteps (j+1) s ≤ _
    rw [bitSteps,hs,ht]
    rw [RationalComputation.rational_neg_encoding] at hb
    change BinaryRationalArithmeticAdder.bitSteps k c ≤
      1300000*(RationalComputation.rationalEncodingLength p+RationalComputation.rationalEncodingLength q+1)^3 at hb
    have hone : 0 < (RationalComputation.rationalEncodingLength p+RationalComputation.rationalEncodingLength q+1)^3 := by positivity
    omega

end IdentityTesting.BinaryRationalArithmeticSubtractor
