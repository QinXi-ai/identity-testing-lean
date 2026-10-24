import IdentityTesting.BinaryInterpreterInputLocal
import IdentityTesting.BinaryCodeLiteralLoaderRuns

/-! The literal loader's output aliases a primitive's physical input stacks.
Every code-loader step writes through the proved local input wiring. -/
namespace IdentityTesting.BinaryInterpreterLiteralInput
open BinaryInterpreterLayout BinaryRegisterMachine
variable {L : Layout}

structure State (L : Layout) where
  core : L.Core
  phase : BinaryCodeLiteralLoader.Phase
  fieldPhase : BinaryCodeWordLoader.Phase
  code : List Symbol
  history : List Symbol
  temp : List Bool

def view (right : Bool) (s : State L) : BinaryCodeLiteralLoader.State :=
  ⟨s.phase,s.fieldPhase,s.code,s.history,s.temp,(L.input right s.core).numerator.negative,
    (L.input right s.core).numerator.magnitude,(L.input right s.core).denominator⟩
def lift (right : Bool) (c : L.Core) (w : BinaryCodeLiteralLoader.State) : State L :=
  ⟨L.setInput right c (BinaryCodeLiteralLoader.output w),w.phase,w.fieldPhase,w.code,w.history,w.temp⟩
def step (right : Bool) (s : State L) : State L :=
  lift right s.core (BinaryCodeLiteralLoader.step (view right s))
def transitionTrace (right : Bool) (s : State L) : List BinaryArithmetic.BitOp :=
  BinaryCodeLiteralLoader.transitionTrace (view right s)
def advance (right : Bool) : ℕ → State L → State L
  | 0,s => s
  | n+1,s => advance right n (step right s)
def bitSteps (right : Bool) : ℕ → State L → ℕ
  | 0,_ => 0
  | n+1,s => (transitionTrace right s).length+bitSteps right n (step right s)

variable (I : InputLocal L)
include I

theorem view_lift (right : Bool) (c : L.Core) (w : BinaryCodeLiteralLoader.State) :
    view right (lift right c w) = w := by
  simp only [view,lift,I.get_set,BinaryCodeLiteralLoader.output]

theorem lift_view (right : Bool) (s : State L) : lift right s.core (view right s) = s := by
  have hw : BinaryCodeLiteralLoader.output (view right s) = L.input right s.core := rfl
  simp only [lift,hw,I.set_self]
  rfl

theorem step_lift (right : Bool) (c : L.Core) (w : BinaryCodeLiteralLoader.State) :
    step right (lift right c w) = lift right c (BinaryCodeLiteralLoader.step w) := by
  rw [step, view_lift I]
  simp only [lift, I.set_set]

theorem advance_lift (right : Bool) (n : ℕ) (c : L.Core) (w : BinaryCodeLiteralLoader.State) :
    advance right n (lift right c w) = lift right c (BinaryCodeLiteralLoader.advance n w) := by
  induction n generalizing w with
  | zero => rfl
  | succ n ih => simpa only [advance,step_lift I,BinaryCodeLiteralLoader.advance] using ih (BinaryCodeLiteralLoader.step w)

theorem bitSteps_lift (right : Bool) (n : ℕ) (c : L.Core) (w : BinaryCodeLiteralLoader.State) :
    bitSteps right n (lift right c w) = BinaryCodeLiteralLoader.bitSteps n w := by
  induction n generalizing w with
  | zero => rfl
  | succ n ih => simp only [bitSteps,transitionTrace,view_lift I,step_lift I,ih,BinaryCodeLiteralLoader.bitSteps]

def initial (c : L.Core) (code history : List Symbol) : State L := ⟨c,.sign,.reading,code,history,[]⟩

theorem initial_lift (right : Bool) (c : L.Core) (code history : List Symbol)
    (h : L.input right c = ⟨⟨false,[]⟩,[]⟩) :
    initial c code history = lift right c (BinaryCodeLiteralLoader.initial code history) := by
  have hs := I.set_self right c
  rw [h] at hs
  simp only [initial,lift,BinaryCodeLiteralLoader.initial,BinaryCodeLiteralLoader.output,hs]

theorem literal_into_input (right : Bool) (c : L.Core) (code history : List Symbol) (w : Word)
    (h : L.input right c = ⟨⟨false,[]⟩,[]⟩) :
    ∃ n,
      let start := initial c (BinaryCodeLiteralLoader.encode w++code) history
      (advance right n start).phase = .halt ∧
      (advance right n start).code = code ∧
      (advance right n start).history = (BinaryCodeLiteralLoader.encode w).reverse++history ∧
      (advance right n start).temp = [] ∧
      (advance right n start).core = L.setInput right c w ∧
      bitSteps right n start ≤ 20*(w.numerator.magnitude.length+w.denominator.length)+80 := by
  obtain ⟨n,_,hr,hc⟩ := BinaryCodeLiteralLoader.binary_literal_load w code history
  have hi := initial_lift I right c (BinaryCodeLiteralLoader.encode w++code) history h
  refine ⟨n,?_,?_,?_,?_,?_,?_⟩
  all_goals rw [hi]
  · rw [advance_lift I,hr]; rfl
  · rw [advance_lift I,hr]; rfl
  · rw [advance_lift I,hr]; rfl
  · rw [advance_lift I,hr]; rfl
  · rw [advance_lift I,hr]
    rfl
  · rw [bitSteps_lift I]
    exact hc

theorem other_input_step (right : Bool) (s : State L) :
    L.input (!right) (step right s).core = L.input (!right) s.core := I.other right s.core _

omit I in
/-- Literal payload loading into each concrete arithmetic primitive, beginning
with empty input stacks. The operand discriminator is decoded separately. -/
theorem arithmetic_literal_into_input (op : RationalComputation.RationalOp)
    (right : Bool) (q : ℚ) (code history : List Symbol) :
    ∃ n,
      let L := BinaryInterpreterArithmetic.arithmeticLayout op
      let c := L.initial BinaryInterpreterArithmetic.emptyWord BinaryInterpreterArithmetic.emptyWord
      let segment := BinaryCodeLiteralLoader.encode (BinaryRationalArithmetic.encode q)
      let start := initial c (segment ++ code) history
      (advance right n start).phase = .halt ∧
      (advance right n start).code = code ∧
      (advance right n start).history = segment.reverse ++ history ∧
      (advance right n start).temp = [] ∧
      L.input right (advance right n start).core = BinaryRationalArithmetic.encode q ∧
      L.input (!right) (advance right n start).core = BinaryInterpreterArithmetic.emptyWord ∧
      bitSteps right n start ≤ 20 * RationalComputation.rationalEncodingLength q + 80 := by
  let L := BinaryInterpreterArithmetic.arithmeticLayout op
  let c := L.initial BinaryInterpreterArithmetic.emptyWord BinaryInterpreterArithmetic.emptyWord
  let J := BinaryInterpreterArithmetic.arithmeticInputLocal op
  have hi : ∀ b, L.input b c = BinaryInterpreterArithmetic.emptyWord := by
    intro b
    simp only [c, L.input_initial, ite_self]
  obtain ⟨n, hh, hc, hs, ht, hcore, hcost⟩ := literal_into_input J right c code history
    (BinaryRationalArithmetic.encode q) (hi right)
  refine ⟨n, hh, hc, hs, ht, ?_, ?_, ?_⟩
  · rw [hcore, J.get_set]
  · rw [hcore, J.other, hi]
  · have hlen := BinaryRationalArithmetic.encode_length q
    dsimp only [BinaryRationalArithmetic.Word.length] at hlen
    change bitSteps right n
      (initial c (BinaryCodeLiteralLoader.encode (BinaryRationalArithmetic.encode q) ++ code) history) ≤ _
    omega

end IdentityTesting.BinaryInterpreterLiteralInput
